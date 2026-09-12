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
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___redArg();
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg();
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___redArg(){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(1);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___redArg___boxed(lean_object* v___dummy_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_ExtTreeMap_empty___redArg();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_cmp_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(1);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___boxed(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_cmp_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_ExtTreeMap_empty(v_00_u03b1_83_, v_00_u03b2_84_, v_cmp_85_);
lean_dec_ref(v_cmp_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(1);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_ExtTreeMap_instEmptyCollection___redArg();
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_cmp_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(1);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_cmp_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_ExtTreeMap_instEmptyCollection(v_00_u03b1_95_, v_00_u03b2_96_, v_cmp_97_);
lean_dec_ref(v_cmp_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_box(1);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited___redArg___boxed(lean_object* v___dummy_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_ExtTreeMap_instInhabited___redArg();
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited(lean_object* v_00_u03b1_103_, lean_object* v_00_u03b2_104_, lean_object* v_cmp_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(1);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited___boxed(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_cmp_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_ExtTreeMap_instInhabited(v_00_u03b1_107_, v_00_u03b2_108_, v_cmp_109_);
lean_dec_ref(v_cmp_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insert___redArg(lean_object* v_cmp_111_, lean_object* v_l_112_, lean_object* v_a_113_, lean_object* v_b_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_111_, v_a_113_, v_b_114_, v_l_112_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insert(lean_object* v_00_u03b1_116_, lean_object* v_00_u03b2_117_, lean_object* v_cmp_118_, lean_object* v_inst_119_, lean_object* v_l_120_, lean_object* v_a_121_, lean_object* v_b_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_118_, v_a_121_, v_b_122_, v_l_120_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0(lean_object* v_cmp_124_, lean_object* v_e_125_){
_start:
{
lean_object* v_fst_126_; lean_object* v_snd_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_fst_126_ = lean_ctor_get(v_e_125_, 0);
lean_inc(v_fst_126_);
v_snd_127_ = lean_ctor_get(v_e_125_, 1);
lean_inc(v_snd_127_);
lean_dec_ref(v_e_125_);
v___x_128_ = lean_box(1);
v___x_129_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_124_, v_fst_126_, v_snd_127_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg(lean_object* v_cmp_130_){
_start:
{
lean_object* v___f_131_; 
v___f_131_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_131_, 0, v_cmp_130_);
return v___f_131_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v_cmp_134_, lean_object* v_inst_135_){
_start:
{
lean_object* v___f_136_; 
v___f_136_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_136_, 0, v_cmp_134_);
return v___f_136_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0(lean_object* v_cmp_137_, lean_object* v_e_138_, lean_object* v_s_139_){
_start:
{
lean_object* v_fst_140_; lean_object* v_snd_141_; lean_object* v___x_142_; 
v_fst_140_ = lean_ctor_get(v_e_138_, 0);
lean_inc(v_fst_140_);
v_snd_141_ = lean_ctor_get(v_e_138_, 1);
lean_inc(v_snd_141_);
lean_dec_ref(v_e_138_);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_137_, v_fst_140_, v_snd_141_, v_s_139_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg(lean_object* v_cmp_143_){
_start:
{
lean_object* v___f_144_; 
v___f_144_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_144_, 0, v_cmp_143_);
return v___f_144_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp(lean_object* v_00_u03b1_145_, lean_object* v_00_u03b2_146_, lean_object* v_cmp_147_, lean_object* v_inst_148_){
_start:
{
lean_object* v___f_149_; 
v___f_149_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_149_, 0, v_cmp_147_);
return v___f_149_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertIfNew___redArg(lean_object* v_cmp_150_, lean_object* v_t_151_, lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint8_t v___x_154_; 
lean_inc(v_t_151_);
lean_inc(v_a_152_);
lean_inc_ref(v_cmp_150_);
v___x_154_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_150_, v_a_152_, v_t_151_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
v___x_155_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_150_, v_a_152_, v_b_153_, v_t_151_);
return v___x_155_;
}
else
{
lean_dec(v_b_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_cmp_150_);
return v_t_151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertIfNew(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_cmp_158_, lean_object* v_inst_159_, lean_object* v_t_160_, lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
uint8_t v___x_163_; 
lean_inc(v_t_160_);
lean_inc(v_a_161_);
lean_inc_ref(v_cmp_158_);
v___x_163_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_158_, v_a_161_, v_t_160_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_158_, v_a_161_, v_b_162_, v_t_160_);
return v___x_164_;
}
else
{
lean_dec(v_b_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_cmp_158_);
return v_t_160_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsert___redArg(lean_object* v_cmp_165_, lean_object* v_t_166_, lean_object* v_a_167_, lean_object* v_b_168_){
_start:
{
lean_object* v_sz_169_; lean_object* v_m_170_; lean_object* v___y_172_; 
v_sz_169_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_166_);
v_m_170_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_165_, v_a_167_, v_b_168_, v_t_166_);
if (lean_obj_tag(v_m_170_) == 0)
{
lean_object* v_size_176_; 
v_size_176_ = lean_ctor_get(v_m_170_, 0);
lean_inc(v_size_176_);
v___y_172_ = v_size_176_;
goto v___jp_171_;
}
else
{
lean_object* v___x_177_; 
v___x_177_ = lean_unsigned_to_nat(0u);
v___y_172_ = v___x_177_;
goto v___jp_171_;
}
v___jp_171_:
{
uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_nat_dec_eq(v_sz_169_, v___y_172_);
lean_dec(v___y_172_);
lean_dec(v_sz_169_);
v___x_174_ = lean_box(v___x_173_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v_m_170_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsert(lean_object* v_00_u03b1_178_, lean_object* v_00_u03b2_179_, lean_object* v_cmp_180_, lean_object* v_inst_181_, lean_object* v_t_182_, lean_object* v_a_183_, lean_object* v_b_184_){
_start:
{
lean_object* v_sz_185_; lean_object* v_m_186_; lean_object* v___y_188_; 
v_sz_185_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_182_);
v_m_186_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_180_, v_a_183_, v_b_184_, v_t_182_);
if (lean_obj_tag(v_m_186_) == 0)
{
lean_object* v_size_192_; 
v_size_192_ = lean_ctor_get(v_m_186_, 0);
lean_inc(v_size_192_);
v___y_188_ = v_size_192_;
goto v___jp_187_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___y_188_ = v___x_193_;
goto v___jp_187_;
}
v___jp_187_:
{
uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_nat_dec_eq(v_sz_185_, v___y_188_);
lean_dec(v___y_188_);
lean_dec(v_sz_185_);
v___x_190_ = lean_box(v___x_189_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_m_186_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_194_, lean_object* v_t_195_, lean_object* v_a_196_, lean_object* v_b_197_){
_start:
{
uint8_t v___x_198_; 
lean_inc(v_t_195_);
lean_inc(v_a_196_);
lean_inc_ref(v_cmp_194_);
v___x_198_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_194_, v_a_196_, v_t_195_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_194_, v_a_196_, v_b_197_, v_t_195_);
v___x_200_ = lean_box(v___x_198_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
return v___x_201_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_b_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_cmp_194_);
v___x_202_ = lean_box(v___x_198_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_t_195_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_204_, lean_object* v_00_u03b2_205_, lean_object* v_cmp_206_, lean_object* v_inst_207_, lean_object* v_t_208_, lean_object* v_a_209_, lean_object* v_b_210_){
_start:
{
uint8_t v___x_211_; 
lean_inc(v_t_208_);
lean_inc(v_a_209_);
lean_inc_ref(v_cmp_206_);
v___x_211_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_206_, v_a_209_, v_t_208_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_206_, v_a_209_, v_b_210_, v_t_208_);
v___x_213_ = lean_box(v___x_211_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_212_);
return v___x_214_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec(v_b_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_cmp_206_);
v___x_215_ = lean_box(v___x_211_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v_t_208_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_217_, lean_object* v_t_218_, lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
lean_object* v___x_221_; 
lean_inc(v_a_219_);
lean_inc(v_t_218_);
lean_inc_ref(v_cmp_217_);
v___x_221_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_217_, v_t_218_, v_a_219_);
if (lean_obj_tag(v___x_221_) == 0)
{
uint8_t v___x_222_; 
lean_inc(v_t_218_);
lean_inc(v_a_219_);
lean_inc_ref(v_cmp_217_);
v___x_222_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_217_, v_a_219_, v_t_218_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_217_, v_a_219_, v_b_220_, v_t_218_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_221_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
return v___x_224_;
}
else
{
lean_object* v___x_225_; 
lean_dec(v_b_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_cmp_217_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_221_);
lean_ctor_set(v___x_225_, 1, v_t_218_);
return v___x_225_;
}
}
else
{
lean_object* v___x_226_; 
lean_dec(v_b_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_cmp_217_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_221_);
lean_ctor_set(v___x_226_, 1, v_t_218_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_227_, lean_object* v_00_u03b2_228_, lean_object* v_cmp_229_, lean_object* v_inst_230_, lean_object* v_t_231_, lean_object* v_a_232_, lean_object* v_b_233_){
_start:
{
lean_object* v___x_234_; 
lean_inc(v_a_232_);
lean_inc(v_t_231_);
lean_inc_ref(v_cmp_229_);
v___x_234_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_229_, v_t_231_, v_a_232_);
if (lean_obj_tag(v___x_234_) == 0)
{
uint8_t v___x_235_; 
lean_inc(v_t_231_);
lean_inc(v_a_232_);
lean_inc_ref(v_cmp_229_);
v___x_235_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_229_, v_a_232_, v_t_231_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_229_, v_a_232_, v_b_233_, v_t_231_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_234_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; 
lean_dec(v_b_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_cmp_229_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_234_);
lean_ctor_set(v___x_238_, 1, v_t_231_);
return v___x_238_;
}
}
else
{
lean_object* v___x_239_; 
lean_dec(v_b_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_cmp_229_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_234_);
lean_ctor_set(v___x_239_, 1, v_t_231_);
return v___x_239_;
}
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_contains___redArg(lean_object* v_cmp_240_, lean_object* v_l_241_, lean_object* v_a_242_){
_start:
{
uint8_t v___x_243_; 
v___x_243_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_240_, v_a_242_, v_l_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_contains___redArg___boxed(lean_object* v_cmp_244_, lean_object* v_l_245_, lean_object* v_a_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Std_ExtTreeMap_contains___redArg(v_cmp_244_, v_l_245_, v_a_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_contains(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_cmp_251_, lean_object* v_inst_252_, lean_object* v_l_253_, lean_object* v_a_254_){
_start:
{
uint8_t v___x_255_; 
v___x_255_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_251_, v_a_254_, v_l_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_contains___boxed(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_cmp_258_, lean_object* v_inst_259_, lean_object* v_l_260_, lean_object* v_a_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Std_ExtTreeMap_contains(v_00_u03b1_256_, v_00_u03b2_257_, v_cmp_258_, v_inst_259_, v_l_260_, v_a_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg(){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = lean_box(0);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg___boxed(lean_object* v___dummy_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg();
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp(lean_object* v_00_u03b1_268_, lean_object* v_00_u03b2_269_, lean_object* v_cmp_270_, lean_object* v_inst_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_box(0);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___boxed(lean_object* v_00_u03b1_273_, lean_object* v_00_u03b2_274_, lean_object* v_cmp_275_, lean_object* v_inst_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_ExtTreeMap_instMembershipOfTransCmp(v_00_u03b1_273_, v_00_u03b2_274_, v_cmp_275_, v_inst_276_);
lean_dec_ref(v_cmp_275_);
return v_res_277_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableMem___redArg(lean_object* v_cmp_278_, lean_object* v_m_279_, lean_object* v_a_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_278_, v_a_280_, v_m_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_282_, lean_object* v_m_283_, lean_object* v_a_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Std_ExtTreeMap_instDecidableMem___redArg(v_cmp_282_, v_m_283_, v_a_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableMem(lean_object* v_00_u03b1_287_, lean_object* v_00_u03b2_288_, lean_object* v_cmp_289_, lean_object* v_inst_290_, lean_object* v_m_291_, lean_object* v_a_292_){
_start:
{
uint8_t v___x_293_; 
v___x_293_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_289_, v_a_292_, v_m_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_294_, lean_object* v_00_u03b2_295_, lean_object* v_cmp_296_, lean_object* v_inst_297_, lean_object* v_m_298_, lean_object* v_a_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Std_ExtTreeMap_instDecidableMem(v_00_u03b1_294_, v_00_u03b2_295_, v_cmp_296_, v_inst_297_, v_m_298_, v_a_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___redArg(lean_object* v_t_302_){
_start:
{
if (lean_obj_tag(v_t_302_) == 0)
{
lean_object* v_size_303_; 
v_size_303_ = lean_ctor_get(v_t_302_, 0);
lean_inc(v_size_303_);
return v_size_303_;
}
else
{
lean_object* v___x_304_; 
v___x_304_ = lean_unsigned_to_nat(0u);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___redArg___boxed(lean_object* v_t_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_ExtTreeMap_size___redArg(v_t_305_);
lean_dec(v_t_305_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size(lean_object* v_00_u03b1_307_, lean_object* v_00_u03b2_308_, lean_object* v_cmp_309_, lean_object* v_t_310_){
_start:
{
if (lean_obj_tag(v_t_310_) == 0)
{
lean_object* v_size_311_; 
v_size_311_ = lean_ctor_get(v_t_310_, 0);
lean_inc(v_size_311_);
return v_size_311_;
}
else
{
lean_object* v___x_312_; 
v___x_312_ = lean_unsigned_to_nat(0u);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___boxed(lean_object* v_00_u03b1_313_, lean_object* v_00_u03b2_314_, lean_object* v_cmp_315_, lean_object* v_t_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_ExtTreeMap_size(v_00_u03b1_313_, v_00_u03b2_314_, v_cmp_315_, v_t_316_);
lean_dec(v_t_316_);
lean_dec_ref(v_cmp_315_);
return v_res_317_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_isEmpty___redArg(lean_object* v_t_318_){
_start:
{
if (lean_obj_tag(v_t_318_) == 0)
{
uint8_t v___x_319_; 
v___x_319_ = 0;
return v___x_319_;
}
else
{
uint8_t v___x_320_; 
v___x_320_ = 1;
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_isEmpty___redArg___boxed(lean_object* v_t_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Std_ExtTreeMap_isEmpty___redArg(v_t_321_);
lean_dec(v_t_321_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_isEmpty(lean_object* v_00_u03b1_324_, lean_object* v_00_u03b2_325_, lean_object* v_cmp_326_, lean_object* v_t_327_){
_start:
{
if (lean_obj_tag(v_t_327_) == 0)
{
uint8_t v___x_328_; 
v___x_328_ = 0;
return v___x_328_;
}
else
{
uint8_t v___x_329_; 
v___x_329_ = 1;
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_330_, lean_object* v_00_u03b2_331_, lean_object* v_cmp_332_, lean_object* v_t_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Std_ExtTreeMap_isEmpty(v_00_u03b1_330_, v_00_u03b2_331_, v_cmp_332_, v_t_333_);
lean_dec(v_t_333_);
lean_dec_ref(v_cmp_332_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_erase___redArg(lean_object* v_cmp_336_, lean_object* v_t_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_336_, v_a_338_, v_t_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_erase(lean_object* v_00_u03b1_340_, lean_object* v_00_u03b2_341_, lean_object* v_cmp_342_, lean_object* v_inst_343_, lean_object* v_t_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_342_, v_a_345_, v_t_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x3f___redArg(lean_object* v_cmp_347_, lean_object* v_t_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_347_, v_t_348_, v_a_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x3f(lean_object* v_00_u03b1_351_, lean_object* v_00_u03b2_352_, lean_object* v_cmp_353_, lean_object* v_inst_354_, lean_object* v_t_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_353_, v_t_355_, v_a_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get___redArg(lean_object* v_cmp_358_, lean_object* v_t_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_358_, v_t_359_, v_a_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get(lean_object* v_00_u03b1_362_, lean_object* v_00_u03b2_363_, lean_object* v_cmp_364_, lean_object* v_inst_365_, lean_object* v_t_366_, lean_object* v_a_367_, lean_object* v_h_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_364_, v_t_366_, v_a_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___redArg(lean_object* v_cmp_370_, lean_object* v_inst_371_, lean_object* v_t_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_370_, v_inst_371_, v_t_372_, v_a_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___redArg___boxed(lean_object* v_cmp_375_, lean_object* v_inst_376_, lean_object* v_t_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_ExtTreeMap_get_x21___redArg(v_cmp_375_, v_inst_376_, v_t_377_, v_a_378_);
lean_dec(v_inst_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21(lean_object* v_00_u03b1_380_, lean_object* v_00_u03b2_381_, lean_object* v_cmp_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_t_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_382_, v_inst_384_, v_t_385_, v_a_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___boxed(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_cmp_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_t_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_ExtTreeMap_get_x21(v_00_u03b1_388_, v_00_u03b2_389_, v_cmp_390_, v_inst_391_, v_inst_392_, v_t_393_, v_a_394_);
lean_dec(v_inst_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg(lean_object* v_cmp_396_, lean_object* v_t_397_, lean_object* v_a_398_, lean_object* v_fallback_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_396_, v_t_397_, v_a_398_, v_fallback_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg___boxed(lean_object* v_cmp_401_, lean_object* v_t_402_, lean_object* v_a_403_, lean_object* v_fallback_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_ExtTreeMap_getD___redArg(v_cmp_401_, v_t_402_, v_a_403_, v_fallback_404_);
lean_dec(v_fallback_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD(lean_object* v_00_u03b1_406_, lean_object* v_00_u03b2_407_, lean_object* v_cmp_408_, lean_object* v_inst_409_, lean_object* v_t_410_, lean_object* v_a_411_, lean_object* v_fallback_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_408_, v_t_410_, v_a_411_, v_fallback_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___boxed(lean_object* v_00_u03b1_414_, lean_object* v_00_u03b2_415_, lean_object* v_cmp_416_, lean_object* v_inst_417_, lean_object* v_t_418_, lean_object* v_a_419_, lean_object* v_fallback_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_ExtTreeMap_getD(v_00_u03b1_414_, v_00_u03b2_415_, v_cmp_416_, v_inst_417_, v_t_418_, v_a_419_, v_fallback_420_);
lean_dec(v_fallback_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_cmp_422_, lean_object* v_m_423_, lean_object* v_a_424_, lean_object* v_h_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_422_, v_m_423_, v_a_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_cmp_427_, lean_object* v_m_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_427_, v_m_428_, v_a_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_cmp_431_, lean_object* v_inst_432_, lean_object* v_m_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_431_, v_inst_432_, v_m_433_, v_a_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_cmp_436_, lean_object* v_inst_437_, lean_object* v_m_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(v_cmp_436_, v_inst_437_, v_m_438_, v_a_439_);
lean_dec(v_inst_437_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(lean_object* v_cmp_441_){
_start:
{
lean_object* v___f_442_; lean_object* v___f_443_; lean_object* v___f_444_; lean_object* v___x_445_; 
lean_inc_ref_n(v_cmp_441_, 2);
v___f_442_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0), 4, 1);
lean_closure_set(v___f_442_, 0, v_cmp_441_);
v___f_443_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1), 3, 1);
lean_closure_set(v___f_443_, 0, v_cmp_441_);
v___f_444_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_444_, 0, v_cmp_441_);
v___x_445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_445_, 0, v___f_442_);
lean_ctor_set(v___x_445_, 1, v___f_443_);
lean_ctor_set(v___x_445_, 2, v___f_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem(lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_cmp_448_, lean_object* v_inst_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(v_cmp_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f___redArg(lean_object* v_cmp_451_, lean_object* v_t_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_451_, v_t_452_, v_a_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f(lean_object* v_00_u03b1_455_, lean_object* v_00_u03b2_456_, lean_object* v_cmp_457_, lean_object* v_inst_458_, lean_object* v_t_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_457_, v_t_459_, v_a_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey___redArg(lean_object* v_cmp_462_, lean_object* v_t_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_462_, v_t_463_, v_a_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey(lean_object* v_00_u03b1_466_, lean_object* v_00_u03b2_467_, lean_object* v_cmp_468_, lean_object* v_inst_469_, lean_object* v_t_470_, lean_object* v_a_471_, lean_object* v_h_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_468_, v_t_470_, v_a_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___redArg(lean_object* v_cmp_474_, lean_object* v_inst_475_, lean_object* v_t_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_474_, v_t_476_, v_a_477_, v_inst_475_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___redArg___boxed(lean_object* v_cmp_479_, lean_object* v_inst_480_, lean_object* v_t_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_ExtTreeMap_getKey_x21___redArg(v_cmp_479_, v_inst_480_, v_t_481_, v_a_482_);
lean_dec(v_inst_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_cmp_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_t_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_486_, v_t_489_, v_a_490_, v_inst_488_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___boxed(lean_object* v_00_u03b1_492_, lean_object* v_00_u03b2_493_, lean_object* v_cmp_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_t_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_ExtTreeMap_getKey_x21(v_00_u03b1_492_, v_00_u03b2_493_, v_cmp_494_, v_inst_495_, v_inst_496_, v_t_497_, v_a_498_);
lean_dec(v_inst_496_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___redArg(lean_object* v_cmp_500_, lean_object* v_t_501_, lean_object* v_a_502_, lean_object* v_fallback_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_500_, v_t_501_, v_a_502_, v_fallback_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_505_, lean_object* v_t_506_, lean_object* v_a_507_, lean_object* v_fallback_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_ExtTreeMap_getKeyD___redArg(v_cmp_505_, v_t_506_, v_a_507_, v_fallback_508_);
lean_dec(v_fallback_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD(lean_object* v_00_u03b1_510_, lean_object* v_00_u03b2_511_, lean_object* v_cmp_512_, lean_object* v_inst_513_, lean_object* v_t_514_, lean_object* v_a_515_, lean_object* v_fallback_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_512_, v_t_514_, v_a_515_, v_fallback_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_518_, lean_object* v_00_u03b2_519_, lean_object* v_cmp_520_, lean_object* v_inst_521_, lean_object* v_t_522_, lean_object* v_a_523_, lean_object* v_fallback_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_ExtTreeMap_getKeyD(v_00_u03b1_518_, v_00_u03b2_519_, v_cmp_520_, v_inst_521_, v_t_522_, v_a_523_, v_fallback_524_);
lean_dec(v_fallback_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___redArg(lean_object* v_t_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_ExtTreeMap_minEntry_x3f___redArg(v_t_528_);
lean_dec(v_t_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_cmp_532_, lean_object* v_inst_533_, lean_object* v_t_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_cmp_538_, lean_object* v_inst_539_, lean_object* v_t_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_ExtTreeMap_minEntry_x3f(v_00_u03b1_536_, v_00_u03b2_537_, v_cmp_538_, v_inst_539_, v_t_540_);
lean_dec(v_t_540_);
lean_dec_ref(v_cmp_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___redArg(lean_object* v_t_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___redArg___boxed(lean_object* v_t_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Std_ExtTreeMap_minEntry___redArg(v_t_544_);
lean_dec(v_t_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_cmp_548_, lean_object* v_inst_549_, lean_object* v_t_550_, lean_object* v_h_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___boxed(lean_object* v_00_u03b1_553_, lean_object* v_00_u03b2_554_, lean_object* v_cmp_555_, lean_object* v_inst_556_, lean_object* v_t_557_, lean_object* v_h_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_ExtTreeMap_minEntry(v_00_u03b1_553_, v_00_u03b2_554_, v_cmp_555_, v_inst_556_, v_t_557_, v_h_558_);
lean_dec(v_t_557_);
lean_dec_ref(v_cmp_555_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___redArg(lean_object* v_inst_560_, lean_object* v_t_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_560_, v_t_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_563_, lean_object* v_t_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Std_ExtTreeMap_minEntry_x21___redArg(v_inst_563_, v_t_564_);
lean_dec(v_t_564_);
lean_dec_ref(v_inst_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21(lean_object* v_00_u03b1_566_, lean_object* v_00_u03b2_567_, lean_object* v_cmp_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_t_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_570_, v_t_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_573_, lean_object* v_00_u03b2_574_, lean_object* v_cmp_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_t_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_ExtTreeMap_minEntry_x21(v_00_u03b1_573_, v_00_u03b2_574_, v_cmp_575_, v_inst_576_, v_inst_577_, v_t_578_);
lean_dec(v_t_578_);
lean_dec_ref(v_inst_577_);
lean_dec_ref(v_cmp_575_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___redArg(lean_object* v_t_580_, lean_object* v_fallback_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_580_, v_fallback_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___redArg___boxed(lean_object* v_t_583_, lean_object* v_fallback_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_ExtTreeMap_minEntryD___redArg(v_t_583_, v_fallback_584_);
lean_dec_ref(v_fallback_584_);
lean_dec(v_t_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD(lean_object* v_00_u03b1_586_, lean_object* v_00_u03b2_587_, lean_object* v_cmp_588_, lean_object* v_inst_589_, lean_object* v_t_590_, lean_object* v_fallback_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_590_, v_fallback_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_593_, lean_object* v_00_u03b2_594_, lean_object* v_cmp_595_, lean_object* v_inst_596_, lean_object* v_t_597_, lean_object* v_fallback_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_ExtTreeMap_minEntryD(v_00_u03b1_593_, v_00_u03b2_594_, v_cmp_595_, v_inst_596_, v_t_597_, v_fallback_598_);
lean_dec_ref(v_fallback_598_);
lean_dec(v_t_597_);
lean_dec_ref(v_cmp_595_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___redArg(lean_object* v_t_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_ExtTreeMap_maxEntry_x3f___redArg(v_t_602_);
lean_dec(v_t_602_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_604_, lean_object* v_00_u03b2_605_, lean_object* v_cmp_606_, lean_object* v_inst_607_, lean_object* v_t_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_610_, lean_object* v_00_u03b2_611_, lean_object* v_cmp_612_, lean_object* v_inst_613_, lean_object* v_t_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Std_ExtTreeMap_maxEntry_x3f(v_00_u03b1_610_, v_00_u03b2_611_, v_cmp_612_, v_inst_613_, v_t_614_);
lean_dec(v_t_614_);
lean_dec_ref(v_cmp_612_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___redArg(lean_object* v_t_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___redArg___boxed(lean_object* v_t_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_ExtTreeMap_maxEntry___redArg(v_t_618_);
lean_dec(v_t_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry(lean_object* v_00_u03b1_620_, lean_object* v_00_u03b2_621_, lean_object* v_cmp_622_, lean_object* v_inst_623_, lean_object* v_t_624_, lean_object* v_h_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_624_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_627_, lean_object* v_00_u03b2_628_, lean_object* v_cmp_629_, lean_object* v_inst_630_, lean_object* v_t_631_, lean_object* v_h_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_ExtTreeMap_maxEntry(v_00_u03b1_627_, v_00_u03b2_628_, v_cmp_629_, v_inst_630_, v_t_631_, v_h_632_);
lean_dec(v_t_631_);
lean_dec_ref(v_cmp_629_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___redArg(lean_object* v_inst_634_, lean_object* v_t_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_634_, v_t_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_637_, lean_object* v_t_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_ExtTreeMap_maxEntry_x21___redArg(v_inst_637_, v_t_638_);
lean_dec(v_t_638_);
lean_dec_ref(v_inst_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21(lean_object* v_00_u03b1_640_, lean_object* v_00_u03b2_641_, lean_object* v_cmp_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_t_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_644_, v_t_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_647_, lean_object* v_00_u03b2_648_, lean_object* v_cmp_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_t_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Std_ExtTreeMap_maxEntry_x21(v_00_u03b1_647_, v_00_u03b2_648_, v_cmp_649_, v_inst_650_, v_inst_651_, v_t_652_);
lean_dec(v_t_652_);
lean_dec_ref(v_inst_651_);
lean_dec_ref(v_cmp_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___redArg(lean_object* v_t_654_, lean_object* v_fallback_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_654_, v_fallback_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_657_, lean_object* v_fallback_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_ExtTreeMap_maxEntryD___redArg(v_t_657_, v_fallback_658_);
lean_dec_ref(v_fallback_658_);
lean_dec(v_t_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD(lean_object* v_00_u03b1_660_, lean_object* v_00_u03b2_661_, lean_object* v_cmp_662_, lean_object* v_inst_663_, lean_object* v_t_664_, lean_object* v_fallback_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_664_, v_fallback_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_667_, lean_object* v_00_u03b2_668_, lean_object* v_cmp_669_, lean_object* v_inst_670_, lean_object* v_t_671_, lean_object* v_fallback_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_ExtTreeMap_maxEntryD(v_00_u03b1_667_, v_00_u03b2_668_, v_cmp_669_, v_inst_670_, v_t_671_, v_fallback_672_);
lean_dec_ref(v_fallback_672_);
lean_dec(v_t_671_);
lean_dec_ref(v_cmp_669_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___redArg(lean_object* v_t_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_ExtTreeMap_minKey_x3f___redArg(v_t_676_);
lean_dec(v_t_676_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_cmp_680_, lean_object* v_inst_681_, lean_object* v_t_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_684_, lean_object* v_00_u03b2_685_, lean_object* v_cmp_686_, lean_object* v_inst_687_, lean_object* v_t_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Std_ExtTreeMap_minKey_x3f(v_00_u03b1_684_, v_00_u03b2_685_, v_cmp_686_, v_inst_687_, v_t_688_);
lean_dec(v_t_688_);
lean_dec_ref(v_cmp_686_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___redArg(lean_object* v_t_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___redArg___boxed(lean_object* v_t_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_ExtTreeMap_minKey___redArg(v_t_692_);
lean_dec(v_t_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey(lean_object* v_00_u03b1_694_, lean_object* v_00_u03b2_695_, lean_object* v_cmp_696_, lean_object* v_inst_697_, lean_object* v_t_698_, lean_object* v_h_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___boxed(lean_object* v_00_u03b1_701_, lean_object* v_00_u03b2_702_, lean_object* v_cmp_703_, lean_object* v_inst_704_, lean_object* v_t_705_, lean_object* v_h_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Std_ExtTreeMap_minKey(v_00_u03b1_701_, v_00_u03b2_702_, v_cmp_703_, v_inst_704_, v_t_705_, v_h_706_);
lean_dec(v_t_705_);
lean_dec_ref(v_cmp_703_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___redArg(lean_object* v_inst_708_, lean_object* v_t_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_708_, v_t_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_711_, lean_object* v_t_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Std_ExtTreeMap_minKey_x21___redArg(v_inst_711_, v_t_712_);
lean_dec(v_t_712_);
lean_dec(v_inst_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21(lean_object* v_00_u03b1_714_, lean_object* v_00_u03b2_715_, lean_object* v_cmp_716_, lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_t_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_718_, v_t_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_721_, lean_object* v_00_u03b2_722_, lean_object* v_cmp_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_t_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_ExtTreeMap_minKey_x21(v_00_u03b1_721_, v_00_u03b2_722_, v_cmp_723_, v_inst_724_, v_inst_725_, v_t_726_);
lean_dec(v_t_726_);
lean_dec(v_inst_725_);
lean_dec_ref(v_cmp_723_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___redArg(lean_object* v_t_728_, lean_object* v_fallback_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_728_, v_fallback_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___redArg___boxed(lean_object* v_t_731_, lean_object* v_fallback_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Std_ExtTreeMap_minKeyD___redArg(v_t_731_, v_fallback_732_);
lean_dec(v_fallback_732_);
lean_dec(v_t_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD(lean_object* v_00_u03b1_734_, lean_object* v_00_u03b2_735_, lean_object* v_cmp_736_, lean_object* v_inst_737_, lean_object* v_t_738_, lean_object* v_fallback_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_738_, v_fallback_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_741_, lean_object* v_00_u03b2_742_, lean_object* v_cmp_743_, lean_object* v_inst_744_, lean_object* v_t_745_, lean_object* v_fallback_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_ExtTreeMap_minKeyD(v_00_u03b1_741_, v_00_u03b2_742_, v_cmp_743_, v_inst_744_, v_t_745_, v_fallback_746_);
lean_dec(v_fallback_746_);
lean_dec(v_t_745_);
lean_dec_ref(v_cmp_743_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___redArg(lean_object* v_t_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_ExtTreeMap_maxKey_x3f___redArg(v_t_750_);
lean_dec(v_t_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f(lean_object* v_00_u03b1_752_, lean_object* v_00_u03b2_753_, lean_object* v_cmp_754_, lean_object* v_inst_755_, lean_object* v_t_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_758_, lean_object* v_00_u03b2_759_, lean_object* v_cmp_760_, lean_object* v_inst_761_, lean_object* v_t_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_ExtTreeMap_maxKey_x3f(v_00_u03b1_758_, v_00_u03b2_759_, v_cmp_760_, v_inst_761_, v_t_762_);
lean_dec(v_t_762_);
lean_dec_ref(v_cmp_760_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___redArg(lean_object* v_t_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___redArg___boxed(lean_object* v_t_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_ExtTreeMap_maxKey___redArg(v_t_766_);
lean_dec(v_t_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey(lean_object* v_00_u03b1_768_, lean_object* v_00_u03b2_769_, lean_object* v_cmp_770_, lean_object* v_inst_771_, lean_object* v_t_772_, lean_object* v_h_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___boxed(lean_object* v_00_u03b1_775_, lean_object* v_00_u03b2_776_, lean_object* v_cmp_777_, lean_object* v_inst_778_, lean_object* v_t_779_, lean_object* v_h_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Std_ExtTreeMap_maxKey(v_00_u03b1_775_, v_00_u03b2_776_, v_cmp_777_, v_inst_778_, v_t_779_, v_h_780_);
lean_dec(v_t_779_);
lean_dec_ref(v_cmp_777_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___redArg(lean_object* v_inst_782_, lean_object* v_t_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_782_, v_t_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_785_, lean_object* v_t_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Std_ExtTreeMap_maxKey_x21___redArg(v_inst_785_, v_t_786_);
lean_dec(v_t_786_);
lean_dec(v_inst_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21(lean_object* v_00_u03b1_788_, lean_object* v_00_u03b2_789_, lean_object* v_cmp_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_t_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_792_, v_t_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_795_, lean_object* v_00_u03b2_796_, lean_object* v_cmp_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_t_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_ExtTreeMap_maxKey_x21(v_00_u03b1_795_, v_00_u03b2_796_, v_cmp_797_, v_inst_798_, v_inst_799_, v_t_800_);
lean_dec(v_t_800_);
lean_dec(v_inst_799_);
lean_dec_ref(v_cmp_797_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___redArg(lean_object* v_t_802_, lean_object* v_fallback_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_802_, v_fallback_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_805_, lean_object* v_fallback_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_ExtTreeMap_maxKeyD___redArg(v_t_805_, v_fallback_806_);
lean_dec(v_fallback_806_);
lean_dec(v_t_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD(lean_object* v_00_u03b1_808_, lean_object* v_00_u03b2_809_, lean_object* v_cmp_810_, lean_object* v_inst_811_, lean_object* v_t_812_, lean_object* v_fallback_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_812_, v_fallback_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_815_, lean_object* v_00_u03b2_816_, lean_object* v_cmp_817_, lean_object* v_inst_818_, lean_object* v_t_819_, lean_object* v_fallback_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Std_ExtTreeMap_maxKeyD(v_00_u03b1_815_, v_00_u03b2_816_, v_cmp_817_, v_inst_818_, v_t_819_, v_fallback_820_);
lean_dec(v_fallback_820_);
lean_dec(v_t_819_);
lean_dec_ref(v_cmp_817_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_822_, lean_object* v_n_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_822_, v_n_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_825_, lean_object* v_n_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(v_t_825_, v_n_826_);
lean_dec(v_t_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_cmp_830_, lean_object* v_inst_831_, lean_object* v_t_832_, lean_object* v_n_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_832_, v_n_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_835_, lean_object* v_00_u03b2_836_, lean_object* v_cmp_837_, lean_object* v_inst_838_, lean_object* v_t_839_, lean_object* v_n_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_ExtTreeMap_entryAtIdx_x3f(v_00_u03b1_835_, v_00_u03b2_836_, v_cmp_837_, v_inst_838_, v_t_839_, v_n_840_);
lean_dec(v_t_839_);
lean_dec_ref(v_cmp_837_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___redArg(lean_object* v_t_842_, lean_object* v_n_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_842_, v_n_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_845_, lean_object* v_n_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_ExtTreeMap_entryAtIdx___redArg(v_t_845_, v_n_846_);
lean_dec(v_t_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx(lean_object* v_00_u03b1_848_, lean_object* v_00_u03b2_849_, lean_object* v_cmp_850_, lean_object* v_inst_851_, lean_object* v_t_852_, lean_object* v_n_853_, lean_object* v_h_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_852_, v_n_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_856_, lean_object* v_00_u03b2_857_, lean_object* v_cmp_858_, lean_object* v_inst_859_, lean_object* v_t_860_, lean_object* v_n_861_, lean_object* v_h_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_ExtTreeMap_entryAtIdx(v_00_u03b1_856_, v_00_u03b2_857_, v_cmp_858_, v_inst_859_, v_t_860_, v_n_861_, v_h_862_);
lean_dec(v_t_860_);
lean_dec_ref(v_cmp_858_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_864_, lean_object* v_t_865_, lean_object* v_n_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_864_, v_t_865_, v_n_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_868_, lean_object* v_t_869_, lean_object* v_n_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_ExtTreeMap_entryAtIdx_x21___redArg(v_inst_868_, v_t_869_, v_n_870_);
lean_dec(v_t_869_);
lean_dec_ref(v_inst_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_872_, lean_object* v_00_u03b2_873_, lean_object* v_cmp_874_, lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_t_877_, lean_object* v_n_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_876_, v_t_877_, v_n_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_880_, lean_object* v_00_u03b2_881_, lean_object* v_cmp_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_t_885_, lean_object* v_n_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Std_ExtTreeMap_entryAtIdx_x21(v_00_u03b1_880_, v_00_u03b2_881_, v_cmp_882_, v_inst_883_, v_inst_884_, v_t_885_, v_n_886_);
lean_dec(v_t_885_);
lean_dec_ref(v_inst_884_);
lean_dec_ref(v_cmp_882_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___redArg(lean_object* v_t_888_, lean_object* v_n_889_, lean_object* v_fallback_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_888_, v_n_889_, v_fallback_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_892_, lean_object* v_n_893_, lean_object* v_fallback_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_ExtTreeMap_entryAtIdxD___redArg(v_t_892_, v_n_893_, v_fallback_894_);
lean_dec_ref(v_fallback_894_);
lean_dec(v_t_892_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD(lean_object* v_00_u03b1_896_, lean_object* v_00_u03b2_897_, lean_object* v_cmp_898_, lean_object* v_inst_899_, lean_object* v_t_900_, lean_object* v_n_901_, lean_object* v_fallback_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_900_, v_n_901_, v_fallback_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_904_, lean_object* v_00_u03b2_905_, lean_object* v_cmp_906_, lean_object* v_inst_907_, lean_object* v_t_908_, lean_object* v_n_909_, lean_object* v_fallback_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Std_ExtTreeMap_entryAtIdxD(v_00_u03b1_904_, v_00_u03b2_905_, v_cmp_906_, v_inst_907_, v_t_908_, v_n_909_, v_fallback_910_);
lean_dec_ref(v_fallback_910_);
lean_dec(v_t_908_);
lean_dec_ref(v_cmp_906_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_912_, lean_object* v_n_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_912_, v_n_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_915_, lean_object* v_n_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(v_t_915_, v_n_916_);
lean_dec(v_t_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_918_, lean_object* v_00_u03b2_919_, lean_object* v_cmp_920_, lean_object* v_inst_921_, lean_object* v_t_922_, lean_object* v_n_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_922_, v_n_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_cmp_927_, lean_object* v_inst_928_, lean_object* v_t_929_, lean_object* v_n_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_ExtTreeMap_keyAtIdx_x3f(v_00_u03b1_925_, v_00_u03b2_926_, v_cmp_927_, v_inst_928_, v_t_929_, v_n_930_);
lean_dec(v_t_929_);
lean_dec_ref(v_cmp_927_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___redArg(lean_object* v_t_932_, lean_object* v_n_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_932_, v_n_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_935_, lean_object* v_n_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_ExtTreeMap_keyAtIdx___redArg(v_t_935_, v_n_936_);
lean_dec(v_t_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx(lean_object* v_00_u03b1_938_, lean_object* v_00_u03b2_939_, lean_object* v_cmp_940_, lean_object* v_inst_941_, lean_object* v_t_942_, lean_object* v_n_943_, lean_object* v_h_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_942_, v_n_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_cmp_948_, lean_object* v_inst_949_, lean_object* v_t_950_, lean_object* v_n_951_, lean_object* v_h_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_ExtTreeMap_keyAtIdx(v_00_u03b1_946_, v_00_u03b2_947_, v_cmp_948_, v_inst_949_, v_t_950_, v_n_951_, v_h_952_);
lean_dec(v_t_950_);
lean_dec_ref(v_cmp_948_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_954_, lean_object* v_t_955_, lean_object* v_n_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_954_, v_t_955_, v_n_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_958_, lean_object* v_t_959_, lean_object* v_n_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std_ExtTreeMap_keyAtIdx_x21___redArg(v_inst_958_, v_t_959_, v_n_960_);
lean_dec(v_t_959_);
lean_dec(v_inst_958_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_962_, lean_object* v_00_u03b2_963_, lean_object* v_cmp_964_, lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_t_967_, lean_object* v_n_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_966_, v_t_967_, v_n_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_970_, lean_object* v_00_u03b2_971_, lean_object* v_cmp_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_t_975_, lean_object* v_n_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_ExtTreeMap_keyAtIdx_x21(v_00_u03b1_970_, v_00_u03b2_971_, v_cmp_972_, v_inst_973_, v_inst_974_, v_t_975_, v_n_976_);
lean_dec(v_t_975_);
lean_dec(v_inst_974_);
lean_dec_ref(v_cmp_972_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___redArg(lean_object* v_t_978_, lean_object* v_n_979_, lean_object* v_fallback_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_978_, v_n_979_, v_fallback_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_982_, lean_object* v_n_983_, lean_object* v_fallback_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_ExtTreeMap_keyAtIdxD___redArg(v_t_982_, v_n_983_, v_fallback_984_);
lean_dec(v_fallback_984_);
lean_dec(v_t_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD(lean_object* v_00_u03b1_986_, lean_object* v_00_u03b2_987_, lean_object* v_cmp_988_, lean_object* v_inst_989_, lean_object* v_t_990_, lean_object* v_n_991_, lean_object* v_fallback_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_990_, v_n_991_, v_fallback_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_994_, lean_object* v_00_u03b2_995_, lean_object* v_cmp_996_, lean_object* v_inst_997_, lean_object* v_t_998_, lean_object* v_n_999_, lean_object* v_fallback_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Std_ExtTreeMap_keyAtIdxD(v_00_u03b1_994_, v_00_u03b2_995_, v_cmp_996_, v_inst_997_, v_t_998_, v_n_999_, v_fallback_1000_);
lean_dec(v_fallback_1000_);
lean_dec(v_t_998_);
lean_dec_ref(v_cmp_996_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1002_, lean_object* v_t_1003_, lean_object* v_k_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_box(0);
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1002_, v_k_1004_, v___x_1005_, v_t_1003_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1007_, lean_object* v_00_u03b2_1008_, lean_object* v_cmp_1009_, lean_object* v_inst_1010_, lean_object* v_t_1011_, lean_object* v_k_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1009_, v_k_1012_, v___x_1013_, v_t_1011_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1015_, lean_object* v_t_1016_, lean_object* v_k_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_box(0);
v___x_1019_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1015_, v_k_1017_, v___x_1018_, v_t_1016_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1020_, lean_object* v_00_u03b2_1021_, lean_object* v_cmp_1022_, lean_object* v_inst_1023_, lean_object* v_t_1024_, lean_object* v_k_1025_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1022_, v_k_1025_, v___x_1026_, v_t_1024_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1028_, lean_object* v_t_1029_, lean_object* v_k_1030_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_box(0);
v___x_1032_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1028_, v_k_1030_, v___x_1031_, v_t_1029_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1033_, lean_object* v_00_u03b2_1034_, lean_object* v_cmp_1035_, lean_object* v_inst_1036_, lean_object* v_t_1037_, lean_object* v_k_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1035_, v_k_1038_, v___x_1039_, v_t_1037_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1041_, lean_object* v_t_1042_, lean_object* v_k_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1041_, v_k_1043_, v___x_1044_, v_t_1042_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1046_, lean_object* v_00_u03b2_1047_, lean_object* v_cmp_1048_, lean_object* v_inst_1049_, lean_object* v_t_1050_, lean_object* v_k_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1048_, v_k_1051_, v___x_1052_, v_t_1050_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE___redArg(lean_object* v_cmp_1054_, lean_object* v_t_1055_, lean_object* v_k_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_1054_, v_k_1056_, v_t_1055_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE(lean_object* v_00_u03b1_1058_, lean_object* v_00_u03b2_1059_, lean_object* v_cmp_1060_, lean_object* v_inst_1061_, lean_object* v_t_1062_, lean_object* v_k_1063_, lean_object* v_h_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_1060_, v_k_1063_, v_t_1062_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT___redArg(lean_object* v_cmp_1066_, lean_object* v_t_1067_, lean_object* v_k_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_1066_, v_k_1068_, v_t_1067_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT(lean_object* v_00_u03b1_1070_, lean_object* v_00_u03b2_1071_, lean_object* v_cmp_1072_, lean_object* v_inst_1073_, lean_object* v_t_1074_, lean_object* v_k_1075_, lean_object* v_h_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_1072_, v_k_1075_, v_t_1074_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE___redArg(lean_object* v_cmp_1078_, lean_object* v_t_1079_, lean_object* v_k_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_1078_, v_k_1080_, v_t_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE(lean_object* v_00_u03b1_1082_, lean_object* v_00_u03b2_1083_, lean_object* v_cmp_1084_, lean_object* v_inst_1085_, lean_object* v_t_1086_, lean_object* v_k_1087_, lean_object* v_h_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_1084_, v_k_1087_, v_t_1086_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT___redArg(lean_object* v_cmp_1090_, lean_object* v_t_1091_, lean_object* v_k_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_1090_, v_k_1092_, v_t_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT(lean_object* v_00_u03b1_1094_, lean_object* v_00_u03b2_1095_, lean_object* v_cmp_1096_, lean_object* v_inst_1097_, lean_object* v_t_1098_, lean_object* v_k_1099_, lean_object* v_h_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_1096_, v_k_1099_, v_t_1098_);
return v___x_1101_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1105_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1106_ = lean_unsigned_to_nat(14u);
v___x_1107_ = lean_unsigned_to_nat(22u);
v___x_1108_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1109_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1110_ = l_mkPanicMessageWithDecl(v___x_1109_, v___x_1108_, v___x_1107_, v___x_1106_, v___x_1105_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1111_, lean_object* v_inst_1112_, lean_object* v_t_1113_, lean_object* v_k_1114_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_box(0);
v___x_1116_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1111_, v_k_1114_, v___x_1115_, v_t_1113_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1118_ = l_panic___redArg(v_inst_1112_, v___x_1117_);
return v___x_1118_;
}
else
{
lean_object* v_val_1119_; 
v_val_1119_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_val_1119_);
lean_dec_ref_known(v___x_1116_, 1);
return v_val_1119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1120_, lean_object* v_inst_1121_, lean_object* v_t_1122_, lean_object* v_k_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Std_ExtTreeMap_getEntryGE_x21___redArg(v_cmp_1120_, v_inst_1121_, v_t_1122_, v_k_1123_);
lean_dec_ref(v_inst_1121_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_cmp_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_t_1130_, lean_object* v_k_1131_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_box(0);
v___x_1133_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1127_, v_k_1131_, v___x_1132_, v_t_1130_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1135_ = l_panic___redArg(v_inst_1129_, v___x_1134_);
return v___x_1135_;
}
else
{
lean_object* v_val_1136_; 
v_val_1136_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_val_1136_);
lean_dec_ref_known(v___x_1133_, 1);
return v_val_1136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1137_, lean_object* v_00_u03b2_1138_, lean_object* v_cmp_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_t_1142_, lean_object* v_k_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_ExtTreeMap_getEntryGE_x21(v_00_u03b1_1137_, v_00_u03b2_1138_, v_cmp_1139_, v_inst_1140_, v_inst_1141_, v_t_1142_, v_k_1143_);
lean_dec_ref(v_inst_1141_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1145_, lean_object* v_inst_1146_, lean_object* v_t_1147_, lean_object* v_k_1148_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_box(0);
v___x_1150_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1145_, v_k_1148_, v___x_1149_, v_t_1147_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1152_ = l_panic___redArg(v_inst_1146_, v___x_1151_);
return v___x_1152_;
}
else
{
lean_object* v_val_1153_; 
v_val_1153_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_val_1153_);
lean_dec_ref_known(v___x_1150_, 1);
return v_val_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1154_, lean_object* v_inst_1155_, lean_object* v_t_1156_, lean_object* v_k_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Std_ExtTreeMap_getEntryGT_x21___redArg(v_cmp_1154_, v_inst_1155_, v_t_1156_, v_k_1157_);
lean_dec_ref(v_inst_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1159_, lean_object* v_00_u03b2_1160_, lean_object* v_cmp_1161_, lean_object* v_inst_1162_, lean_object* v_inst_1163_, lean_object* v_t_1164_, lean_object* v_k_1165_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_box(0);
v___x_1167_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1161_, v_k_1165_, v___x_1166_, v_t_1164_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1169_ = l_panic___redArg(v_inst_1163_, v___x_1168_);
return v___x_1169_;
}
else
{
lean_object* v_val_1170_; 
v_val_1170_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_val_1170_);
lean_dec_ref_known(v___x_1167_, 1);
return v_val_1170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_00_u03b2_1172_, lean_object* v_cmp_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_t_1176_, lean_object* v_k_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Std_ExtTreeMap_getEntryGT_x21(v_00_u03b1_1171_, v_00_u03b2_1172_, v_cmp_1173_, v_inst_1174_, v_inst_1175_, v_t_1176_, v_k_1177_);
lean_dec_ref(v_inst_1175_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1179_, lean_object* v_inst_1180_, lean_object* v_t_1181_, lean_object* v_k_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_box(0);
v___x_1184_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1179_, v_k_1182_, v___x_1183_, v_t_1181_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1186_ = l_panic___redArg(v_inst_1180_, v___x_1185_);
return v___x_1186_;
}
else
{
lean_object* v_val_1187_; 
v_val_1187_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_val_1187_);
lean_dec_ref_known(v___x_1184_, 1);
return v_val_1187_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1188_, lean_object* v_inst_1189_, lean_object* v_t_1190_, lean_object* v_k_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Std_ExtTreeMap_getEntryLE_x21___redArg(v_cmp_1188_, v_inst_1189_, v_t_1190_, v_k_1191_);
lean_dec_ref(v_inst_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1193_, lean_object* v_00_u03b2_1194_, lean_object* v_cmp_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_t_1198_, lean_object* v_k_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_box(0);
v___x_1201_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1195_, v_k_1199_, v___x_1200_, v_t_1198_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1203_ = l_panic___redArg(v_inst_1197_, v___x_1202_);
return v___x_1203_;
}
else
{
lean_object* v_val_1204_; 
v_val_1204_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v___x_1201_, 1);
return v_val_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1205_, lean_object* v_00_u03b2_1206_, lean_object* v_cmp_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_t_1210_, lean_object* v_k_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Std_ExtTreeMap_getEntryLE_x21(v_00_u03b1_1205_, v_00_u03b2_1206_, v_cmp_1207_, v_inst_1208_, v_inst_1209_, v_t_1210_, v_k_1211_);
lean_dec_ref(v_inst_1209_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1213_, lean_object* v_inst_1214_, lean_object* v_t_1215_, lean_object* v_k_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_box(0);
v___x_1218_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1213_, v_k_1216_, v___x_1217_, v_t_1215_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1220_ = l_panic___redArg(v_inst_1214_, v___x_1219_);
return v___x_1220_;
}
else
{
lean_object* v_val_1221_; 
v_val_1221_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_val_1221_);
lean_dec_ref_known(v___x_1218_, 1);
return v_val_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1222_, lean_object* v_inst_1223_, lean_object* v_t_1224_, lean_object* v_k_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Std_ExtTreeMap_getEntryLT_x21___redArg(v_cmp_1222_, v_inst_1223_, v_t_1224_, v_k_1225_);
lean_dec_ref(v_inst_1223_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1227_, lean_object* v_00_u03b2_1228_, lean_object* v_cmp_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_t_1232_, lean_object* v_k_1233_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_box(0);
v___x_1235_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1229_, v_k_1233_, v___x_1234_, v_t_1232_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1237_ = l_panic___redArg(v_inst_1231_, v___x_1236_);
return v___x_1237_;
}
else
{
lean_object* v_val_1238_; 
v_val_1238_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v___x_1235_, 1);
return v_val_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1239_, lean_object* v_00_u03b2_1240_, lean_object* v_cmp_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_t_1244_, lean_object* v_k_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Std_ExtTreeMap_getEntryLT_x21(v_00_u03b1_1239_, v_00_u03b2_1240_, v_cmp_1241_, v_inst_1242_, v_inst_1243_, v_t_1244_, v_k_1245_);
lean_dec_ref(v_inst_1243_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___redArg(lean_object* v_cmp_1247_, lean_object* v_t_1248_, lean_object* v_k_1249_, lean_object* v_fallback_1250_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_box(0);
v___x_1252_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1247_, v_k_1249_, v___x_1251_, v_t_1248_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_inc_ref(v_fallback_1250_);
return v_fallback_1250_;
}
else
{
lean_object* v_val_1253_; 
v_val_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_val_1253_);
lean_dec_ref_known(v___x_1252_, 1);
return v_val_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1254_, lean_object* v_t_1255_, lean_object* v_k_1256_, lean_object* v_fallback_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Std_ExtTreeMap_getEntryGED___redArg(v_cmp_1254_, v_t_1255_, v_k_1256_, v_fallback_1257_);
lean_dec_ref(v_fallback_1257_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED(lean_object* v_00_u03b1_1259_, lean_object* v_00_u03b2_1260_, lean_object* v_cmp_1261_, lean_object* v_inst_1262_, lean_object* v_t_1263_, lean_object* v_k_1264_, lean_object* v_fallback_1265_){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_box(0);
v___x_1267_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1261_, v_k_1264_, v___x_1266_, v_t_1263_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_inc_ref(v_fallback_1265_);
return v_fallback_1265_;
}
else
{
lean_object* v_val_1268_; 
v_val_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_val_1268_);
lean_dec_ref_known(v___x_1267_, 1);
return v_val_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1269_, lean_object* v_00_u03b2_1270_, lean_object* v_cmp_1271_, lean_object* v_inst_1272_, lean_object* v_t_1273_, lean_object* v_k_1274_, lean_object* v_fallback_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_ExtTreeMap_getEntryGED(v_00_u03b1_1269_, v_00_u03b2_1270_, v_cmp_1271_, v_inst_1272_, v_t_1273_, v_k_1274_, v_fallback_1275_);
lean_dec_ref(v_fallback_1275_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1277_, lean_object* v_t_1278_, lean_object* v_k_1279_, lean_object* v_fallback_1280_){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_box(0);
v___x_1282_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1277_, v_k_1279_, v___x_1281_, v_t_1278_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_inc_ref(v_fallback_1280_);
return v_fallback_1280_;
}
else
{
lean_object* v_val_1283_; 
v_val_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_val_1283_);
lean_dec_ref_known(v___x_1282_, 1);
return v_val_1283_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1284_, lean_object* v_t_1285_, lean_object* v_k_1286_, lean_object* v_fallback_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Std_ExtTreeMap_getEntryGTD___redArg(v_cmp_1284_, v_t_1285_, v_k_1286_, v_fallback_1287_);
lean_dec_ref(v_fallback_1287_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD(lean_object* v_00_u03b1_1289_, lean_object* v_00_u03b2_1290_, lean_object* v_cmp_1291_, lean_object* v_inst_1292_, lean_object* v_t_1293_, lean_object* v_k_1294_, lean_object* v_fallback_1295_){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1291_, v_k_1294_, v___x_1296_, v_t_1293_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_inc_ref(v_fallback_1295_);
return v_fallback_1295_;
}
else
{
lean_object* v_val_1298_; 
v_val_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v___x_1297_, 1);
return v_val_1298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1299_, lean_object* v_00_u03b2_1300_, lean_object* v_cmp_1301_, lean_object* v_inst_1302_, lean_object* v_t_1303_, lean_object* v_k_1304_, lean_object* v_fallback_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Std_ExtTreeMap_getEntryGTD(v_00_u03b1_1299_, v_00_u03b2_1300_, v_cmp_1301_, v_inst_1302_, v_t_1303_, v_k_1304_, v_fallback_1305_);
lean_dec_ref(v_fallback_1305_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___redArg(lean_object* v_cmp_1307_, lean_object* v_t_1308_, lean_object* v_k_1309_, lean_object* v_fallback_1310_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_box(0);
v___x_1312_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1307_, v_k_1309_, v___x_1311_, v_t_1308_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_inc_ref(v_fallback_1310_);
return v_fallback_1310_;
}
else
{
lean_object* v_val_1313_; 
v_val_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v___x_1312_, 1);
return v_val_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1314_, lean_object* v_t_1315_, lean_object* v_k_1316_, lean_object* v_fallback_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Std_ExtTreeMap_getEntryLED___redArg(v_cmp_1314_, v_t_1315_, v_k_1316_, v_fallback_1317_);
lean_dec_ref(v_fallback_1317_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED(lean_object* v_00_u03b1_1319_, lean_object* v_00_u03b2_1320_, lean_object* v_cmp_1321_, lean_object* v_inst_1322_, lean_object* v_t_1323_, lean_object* v_k_1324_, lean_object* v_fallback_1325_){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_box(0);
v___x_1327_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1321_, v_k_1324_, v___x_1326_, v_t_1323_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_inc_ref(v_fallback_1325_);
return v_fallback_1325_;
}
else
{
lean_object* v_val_1328_; 
v_val_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_val_1328_);
lean_dec_ref_known(v___x_1327_, 1);
return v_val_1328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1329_, lean_object* v_00_u03b2_1330_, lean_object* v_cmp_1331_, lean_object* v_inst_1332_, lean_object* v_t_1333_, lean_object* v_k_1334_, lean_object* v_fallback_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_ExtTreeMap_getEntryLED(v_00_u03b1_1329_, v_00_u03b2_1330_, v_cmp_1331_, v_inst_1332_, v_t_1333_, v_k_1334_, v_fallback_1335_);
lean_dec_ref(v_fallback_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1337_, lean_object* v_t_1338_, lean_object* v_k_1339_, lean_object* v_fallback_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_box(0);
v___x_1342_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1337_, v_k_1339_, v___x_1341_, v_t_1338_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_inc_ref(v_fallback_1340_);
return v_fallback_1340_;
}
else
{
lean_object* v_val_1343_; 
v_val_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_val_1343_);
lean_dec_ref_known(v___x_1342_, 1);
return v_val_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1344_, lean_object* v_t_1345_, lean_object* v_k_1346_, lean_object* v_fallback_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Std_ExtTreeMap_getEntryLTD___redArg(v_cmp_1344_, v_t_1345_, v_k_1346_, v_fallback_1347_);
lean_dec_ref(v_fallback_1347_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD(lean_object* v_00_u03b1_1349_, lean_object* v_00_u03b2_1350_, lean_object* v_cmp_1351_, lean_object* v_inst_1352_, lean_object* v_t_1353_, lean_object* v_k_1354_, lean_object* v_fallback_1355_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_box(0);
v___x_1357_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1351_, v_k_1354_, v___x_1356_, v_t_1353_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_inc_ref(v_fallback_1355_);
return v_fallback_1355_;
}
else
{
lean_object* v_val_1358_; 
v_val_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_val_1358_);
lean_dec_ref_known(v___x_1357_, 1);
return v_val_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1359_, lean_object* v_00_u03b2_1360_, lean_object* v_cmp_1361_, lean_object* v_inst_1362_, lean_object* v_t_1363_, lean_object* v_k_1364_, lean_object* v_fallback_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Std_ExtTreeMap_getEntryLTD(v_00_u03b1_1359_, v_00_u03b2_1360_, v_cmp_1361_, v_inst_1362_, v_t_1363_, v_k_1364_, v_fallback_1365_);
lean_dec_ref(v_fallback_1365_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1367_, lean_object* v_t_1368_, lean_object* v_k_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_box(0);
v___x_1371_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1367_, v_k_1369_, v___x_1370_, v_t_1368_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1372_, lean_object* v_00_u03b2_1373_, lean_object* v_cmp_1374_, lean_object* v_inst_1375_, lean_object* v_t_1376_, lean_object* v_k_1377_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1374_, v_k_1377_, v___x_1378_, v_t_1376_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1380_, lean_object* v_t_1381_, lean_object* v_k_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1380_, v_k_1382_, v___x_1383_, v_t_1381_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1385_, lean_object* v_00_u03b2_1386_, lean_object* v_cmp_1387_, lean_object* v_inst_1388_, lean_object* v_t_1389_, lean_object* v_k_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_box(0);
v___x_1392_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1387_, v_k_1390_, v___x_1391_, v_t_1389_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1393_, lean_object* v_t_1394_, lean_object* v_k_1395_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_box(0);
v___x_1397_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1393_, v_k_1395_, v___x_1396_, v_t_1394_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1398_, lean_object* v_00_u03b2_1399_, lean_object* v_cmp_1400_, lean_object* v_inst_1401_, lean_object* v_t_1402_, lean_object* v_k_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_box(0);
v___x_1405_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1400_, v_k_1403_, v___x_1404_, v_t_1402_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1406_, lean_object* v_t_1407_, lean_object* v_k_1408_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_box(0);
v___x_1410_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1406_, v_k_1408_, v___x_1409_, v_t_1407_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1411_, lean_object* v_00_u03b2_1412_, lean_object* v_cmp_1413_, lean_object* v_inst_1414_, lean_object* v_t_1415_, lean_object* v_k_1416_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_box(0);
v___x_1418_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1413_, v_k_1416_, v___x_1417_, v_t_1415_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE___redArg(lean_object* v_cmp_1419_, lean_object* v_t_1420_, lean_object* v_k_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1419_, v_k_1421_, v_t_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE(lean_object* v_00_u03b1_1423_, lean_object* v_00_u03b2_1424_, lean_object* v_cmp_1425_, lean_object* v_inst_1426_, lean_object* v_t_1427_, lean_object* v_k_1428_, lean_object* v_h_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1425_, v_k_1428_, v_t_1427_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT___redArg(lean_object* v_cmp_1431_, lean_object* v_t_1432_, lean_object* v_k_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1431_, v_k_1433_, v_t_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT(lean_object* v_00_u03b1_1435_, lean_object* v_00_u03b2_1436_, lean_object* v_cmp_1437_, lean_object* v_inst_1438_, lean_object* v_t_1439_, lean_object* v_k_1440_, lean_object* v_h_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1437_, v_k_1440_, v_t_1439_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE___redArg(lean_object* v_cmp_1443_, lean_object* v_t_1444_, lean_object* v_k_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1443_, v_k_1445_, v_t_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE(lean_object* v_00_u03b1_1447_, lean_object* v_00_u03b2_1448_, lean_object* v_cmp_1449_, lean_object* v_inst_1450_, lean_object* v_t_1451_, lean_object* v_k_1452_, lean_object* v_h_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1449_, v_k_1452_, v_t_1451_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT___redArg(lean_object* v_cmp_1455_, lean_object* v_t_1456_, lean_object* v_k_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1455_, v_k_1457_, v_t_1456_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT(lean_object* v_00_u03b1_1459_, lean_object* v_00_u03b2_1460_, lean_object* v_cmp_1461_, lean_object* v_inst_1462_, lean_object* v_t_1463_, lean_object* v_k_1464_, lean_object* v_h_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1461_, v_k_1464_, v_t_1463_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1467_, lean_object* v_inst_1468_, lean_object* v_t_1469_, lean_object* v_k_1470_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1467_, v_k_1470_, v___x_1471_, v_t_1469_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1474_ = l_panic___redArg(v_inst_1468_, v___x_1473_);
return v___x_1474_;
}
else
{
lean_object* v_val_1475_; 
v_val_1475_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_val_1475_);
lean_dec_ref_known(v___x_1472_, 1);
return v_val_1475_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1476_, lean_object* v_inst_1477_, lean_object* v_t_1478_, lean_object* v_k_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Std_ExtTreeMap_getKeyGE_x21___redArg(v_cmp_1476_, v_inst_1477_, v_t_1478_, v_k_1479_);
lean_dec(v_inst_1477_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1481_, lean_object* v_00_u03b2_1482_, lean_object* v_cmp_1483_, lean_object* v_inst_1484_, lean_object* v_inst_1485_, lean_object* v_t_1486_, lean_object* v_k_1487_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_box(0);
v___x_1489_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1483_, v_k_1487_, v___x_1488_, v_t_1486_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1491_ = l_panic___redArg(v_inst_1485_, v___x_1490_);
return v___x_1491_;
}
else
{
lean_object* v_val_1492_; 
v_val_1492_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v___x_1489_, 1);
return v_val_1492_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1493_, lean_object* v_00_u03b2_1494_, lean_object* v_cmp_1495_, lean_object* v_inst_1496_, lean_object* v_inst_1497_, lean_object* v_t_1498_, lean_object* v_k_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Std_ExtTreeMap_getKeyGE_x21(v_00_u03b1_1493_, v_00_u03b2_1494_, v_cmp_1495_, v_inst_1496_, v_inst_1497_, v_t_1498_, v_k_1499_);
lean_dec(v_inst_1497_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1501_, lean_object* v_inst_1502_, lean_object* v_t_1503_, lean_object* v_k_1504_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_box(0);
v___x_1506_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1501_, v_k_1504_, v___x_1505_, v_t_1503_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1508_ = l_panic___redArg(v_inst_1502_, v___x_1507_);
return v___x_1508_;
}
else
{
lean_object* v_val_1509_; 
v_val_1509_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_val_1509_);
lean_dec_ref_known(v___x_1506_, 1);
return v_val_1509_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1510_, lean_object* v_inst_1511_, lean_object* v_t_1512_, lean_object* v_k_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Std_ExtTreeMap_getKeyGT_x21___redArg(v_cmp_1510_, v_inst_1511_, v_t_1512_, v_k_1513_);
lean_dec(v_inst_1511_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1515_, lean_object* v_00_u03b2_1516_, lean_object* v_cmp_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_t_1520_, lean_object* v_k_1521_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_box(0);
v___x_1523_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1517_, v_k_1521_, v___x_1522_, v_t_1520_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1525_ = l_panic___redArg(v_inst_1519_, v___x_1524_);
return v___x_1525_;
}
else
{
lean_object* v_val_1526_; 
v_val_1526_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_val_1526_);
lean_dec_ref_known(v___x_1523_, 1);
return v_val_1526_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1527_, lean_object* v_00_u03b2_1528_, lean_object* v_cmp_1529_, lean_object* v_inst_1530_, lean_object* v_inst_1531_, lean_object* v_t_1532_, lean_object* v_k_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Std_ExtTreeMap_getKeyGT_x21(v_00_u03b1_1527_, v_00_u03b2_1528_, v_cmp_1529_, v_inst_1530_, v_inst_1531_, v_t_1532_, v_k_1533_);
lean_dec(v_inst_1531_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1535_, lean_object* v_inst_1536_, lean_object* v_t_1537_, lean_object* v_k_1538_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_box(0);
v___x_1540_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1535_, v_k_1538_, v___x_1539_, v_t_1537_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1542_ = l_panic___redArg(v_inst_1536_, v___x_1541_);
return v___x_1542_;
}
else
{
lean_object* v_val_1543_; 
v_val_1543_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_val_1543_);
lean_dec_ref_known(v___x_1540_, 1);
return v_val_1543_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1544_, lean_object* v_inst_1545_, lean_object* v_t_1546_, lean_object* v_k_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Std_ExtTreeMap_getKeyLE_x21___redArg(v_cmp_1544_, v_inst_1545_, v_t_1546_, v_k_1547_);
lean_dec(v_inst_1545_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1549_, lean_object* v_00_u03b2_1550_, lean_object* v_cmp_1551_, lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_t_1554_, lean_object* v_k_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_box(0);
v___x_1557_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1551_, v_k_1555_, v___x_1556_, v_t_1554_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1559_ = l_panic___redArg(v_inst_1553_, v___x_1558_);
return v___x_1559_;
}
else
{
lean_object* v_val_1560_; 
v_val_1560_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1560_);
lean_dec_ref_known(v___x_1557_, 1);
return v_val_1560_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1561_, lean_object* v_00_u03b2_1562_, lean_object* v_cmp_1563_, lean_object* v_inst_1564_, lean_object* v_inst_1565_, lean_object* v_t_1566_, lean_object* v_k_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Std_ExtTreeMap_getKeyLE_x21(v_00_u03b1_1561_, v_00_u03b2_1562_, v_cmp_1563_, v_inst_1564_, v_inst_1565_, v_t_1566_, v_k_1567_);
lean_dec(v_inst_1565_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1569_, lean_object* v_inst_1570_, lean_object* v_t_1571_, lean_object* v_k_1572_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1569_, v_k_1572_, v___x_1573_, v_t_1571_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1576_ = l_panic___redArg(v_inst_1570_, v___x_1575_);
return v___x_1576_;
}
else
{
lean_object* v_val_1577_; 
v_val_1577_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v___x_1574_, 1);
return v_val_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1578_, lean_object* v_inst_1579_, lean_object* v_t_1580_, lean_object* v_k_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Std_ExtTreeMap_getKeyLT_x21___redArg(v_cmp_1578_, v_inst_1579_, v_t_1580_, v_k_1581_);
lean_dec(v_inst_1579_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1583_, lean_object* v_00_u03b2_1584_, lean_object* v_cmp_1585_, lean_object* v_inst_1586_, lean_object* v_inst_1587_, lean_object* v_t_1588_, lean_object* v_k_1589_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_box(0);
v___x_1591_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1585_, v_k_1589_, v___x_1590_, v_t_1588_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1593_ = l_panic___redArg(v_inst_1587_, v___x_1592_);
return v___x_1593_;
}
else
{
lean_object* v_val_1594_; 
v_val_1594_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v___x_1591_, 1);
return v_val_1594_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1595_, lean_object* v_00_u03b2_1596_, lean_object* v_cmp_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_t_1600_, lean_object* v_k_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Std_ExtTreeMap_getKeyLT_x21(v_00_u03b1_1595_, v_00_u03b2_1596_, v_cmp_1597_, v_inst_1598_, v_inst_1599_, v_t_1600_, v_k_1601_);
lean_dec(v_inst_1599_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___redArg(lean_object* v_cmp_1603_, lean_object* v_t_1604_, lean_object* v_k_1605_, lean_object* v_fallback_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_box(0);
v___x_1608_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1603_, v_k_1605_, v___x_1607_, v_t_1604_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_inc(v_fallback_1606_);
return v_fallback_1606_;
}
else
{
lean_object* v_val_1609_; 
v_val_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_val_1609_);
lean_dec_ref_known(v___x_1608_, 1);
return v_val_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1610_, lean_object* v_t_1611_, lean_object* v_k_1612_, lean_object* v_fallback_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Std_ExtTreeMap_getKeyGED___redArg(v_cmp_1610_, v_t_1611_, v_k_1612_, v_fallback_1613_);
lean_dec(v_fallback_1613_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED(lean_object* v_00_u03b1_1615_, lean_object* v_00_u03b2_1616_, lean_object* v_cmp_1617_, lean_object* v_inst_1618_, lean_object* v_t_1619_, lean_object* v_k_1620_, lean_object* v_fallback_1621_){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_box(0);
v___x_1623_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1617_, v_k_1620_, v___x_1622_, v_t_1619_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_inc(v_fallback_1621_);
return v_fallback_1621_;
}
else
{
lean_object* v_val_1624_; 
v_val_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v___x_1623_, 1);
return v_val_1624_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1625_, lean_object* v_00_u03b2_1626_, lean_object* v_cmp_1627_, lean_object* v_inst_1628_, lean_object* v_t_1629_, lean_object* v_k_1630_, lean_object* v_fallback_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Std_ExtTreeMap_getKeyGED(v_00_u03b1_1625_, v_00_u03b2_1626_, v_cmp_1627_, v_inst_1628_, v_t_1629_, v_k_1630_, v_fallback_1631_);
lean_dec(v_fallback_1631_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1633_, lean_object* v_t_1634_, lean_object* v_k_1635_, lean_object* v_fallback_1636_){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_box(0);
v___x_1638_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1633_, v_k_1635_, v___x_1637_, v_t_1634_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_inc(v_fallback_1636_);
return v_fallback_1636_;
}
else
{
lean_object* v_val_1639_; 
v_val_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_val_1639_);
lean_dec_ref_known(v___x_1638_, 1);
return v_val_1639_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1640_, lean_object* v_t_1641_, lean_object* v_k_1642_, lean_object* v_fallback_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Std_ExtTreeMap_getKeyGTD___redArg(v_cmp_1640_, v_t_1641_, v_k_1642_, v_fallback_1643_);
lean_dec(v_fallback_1643_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD(lean_object* v_00_u03b1_1645_, lean_object* v_00_u03b2_1646_, lean_object* v_cmp_1647_, lean_object* v_inst_1648_, lean_object* v_t_1649_, lean_object* v_k_1650_, lean_object* v_fallback_1651_){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1647_, v_k_1650_, v___x_1652_, v_t_1649_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_inc(v_fallback_1651_);
return v_fallback_1651_;
}
else
{
lean_object* v_val_1654_; 
v_val_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_val_1654_);
lean_dec_ref_known(v___x_1653_, 1);
return v_val_1654_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1655_, lean_object* v_00_u03b2_1656_, lean_object* v_cmp_1657_, lean_object* v_inst_1658_, lean_object* v_t_1659_, lean_object* v_k_1660_, lean_object* v_fallback_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Std_ExtTreeMap_getKeyGTD(v_00_u03b1_1655_, v_00_u03b2_1656_, v_cmp_1657_, v_inst_1658_, v_t_1659_, v_k_1660_, v_fallback_1661_);
lean_dec(v_fallback_1661_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___redArg(lean_object* v_cmp_1663_, lean_object* v_t_1664_, lean_object* v_k_1665_, lean_object* v_fallback_1666_){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_box(0);
v___x_1668_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1663_, v_k_1665_, v___x_1667_, v_t_1664_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_inc(v_fallback_1666_);
return v_fallback_1666_;
}
else
{
lean_object* v_val_1669_; 
v_val_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_val_1669_);
lean_dec_ref_known(v___x_1668_, 1);
return v_val_1669_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1670_, lean_object* v_t_1671_, lean_object* v_k_1672_, lean_object* v_fallback_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Std_ExtTreeMap_getKeyLED___redArg(v_cmp_1670_, v_t_1671_, v_k_1672_, v_fallback_1673_);
lean_dec(v_fallback_1673_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED(lean_object* v_00_u03b1_1675_, lean_object* v_00_u03b2_1676_, lean_object* v_cmp_1677_, lean_object* v_inst_1678_, lean_object* v_t_1679_, lean_object* v_k_1680_, lean_object* v_fallback_1681_){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_box(0);
v___x_1683_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1677_, v_k_1680_, v___x_1682_, v_t_1679_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_inc(v_fallback_1681_);
return v_fallback_1681_;
}
else
{
lean_object* v_val_1684_; 
v_val_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_val_1684_);
lean_dec_ref_known(v___x_1683_, 1);
return v_val_1684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1685_, lean_object* v_00_u03b2_1686_, lean_object* v_cmp_1687_, lean_object* v_inst_1688_, lean_object* v_t_1689_, lean_object* v_k_1690_, lean_object* v_fallback_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Std_ExtTreeMap_getKeyLED(v_00_u03b1_1685_, v_00_u03b2_1686_, v_cmp_1687_, v_inst_1688_, v_t_1689_, v_k_1690_, v_fallback_1691_);
lean_dec(v_fallback_1691_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1693_, lean_object* v_t_1694_, lean_object* v_k_1695_, lean_object* v_fallback_1696_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_box(0);
v___x_1698_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1693_, v_k_1695_, v___x_1697_, v_t_1694_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_inc(v_fallback_1696_);
return v_fallback_1696_;
}
else
{
lean_object* v_val_1699_; 
v_val_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_val_1699_);
lean_dec_ref_known(v___x_1698_, 1);
return v_val_1699_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1700_, lean_object* v_t_1701_, lean_object* v_k_1702_, lean_object* v_fallback_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Std_ExtTreeMap_getKeyLTD___redArg(v_cmp_1700_, v_t_1701_, v_k_1702_, v_fallback_1703_);
lean_dec(v_fallback_1703_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD(lean_object* v_00_u03b1_1705_, lean_object* v_00_u03b2_1706_, lean_object* v_cmp_1707_, lean_object* v_inst_1708_, lean_object* v_t_1709_, lean_object* v_k_1710_, lean_object* v_fallback_1711_){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_box(0);
v___x_1713_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1707_, v_k_1710_, v___x_1712_, v_t_1709_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_inc(v_fallback_1711_);
return v_fallback_1711_;
}
else
{
lean_object* v_val_1714_; 
v_val_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_val_1714_);
lean_dec_ref_known(v___x_1713_, 1);
return v_val_1714_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1715_, lean_object* v_00_u03b2_1716_, lean_object* v_cmp_1717_, lean_object* v_inst_1718_, lean_object* v_t_1719_, lean_object* v_k_1720_, lean_object* v_fallback_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Std_ExtTreeMap_getKeyLTD(v_00_u03b1_1715_, v_00_u03b2_1716_, v_cmp_1717_, v_inst_1718_, v_t_1719_, v_k_1720_, v_fallback_1721_);
lean_dec(v_fallback_1721_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter___redArg(lean_object* v_f_1723_, lean_object* v_m_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_1723_, v_m_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter(lean_object* v_00_u03b1_1726_, lean_object* v_00_u03b2_1727_, lean_object* v_cmp_1728_, lean_object* v_f_1729_, lean_object* v_m_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_1729_, v_m_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter___boxed(lean_object* v_00_u03b1_1732_, lean_object* v_00_u03b2_1733_, lean_object* v_cmp_1734_, lean_object* v_f_1735_, lean_object* v_m_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Std_ExtTreeMap_filter(v_00_u03b1_1732_, v_00_u03b2_1733_, v_cmp_1734_, v_f_1735_, v_m_1736_);
lean_dec_ref(v_cmp_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap___redArg(lean_object* v_f_1738_, lean_object* v_m_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_1738_, v_m_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap(lean_object* v_00_u03b1_1741_, lean_object* v_00_u03b2_1742_, lean_object* v_00_u03b3_1743_, lean_object* v_cmp_1744_, lean_object* v_f_1745_, lean_object* v_m_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_1745_, v_m_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap___boxed(lean_object* v_00_u03b1_1748_, lean_object* v_00_u03b2_1749_, lean_object* v_00_u03b3_1750_, lean_object* v_cmp_1751_, lean_object* v_f_1752_, lean_object* v_m_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Std_ExtTreeMap_filterMap(v_00_u03b1_1748_, v_00_u03b2_1749_, v_00_u03b3_1750_, v_cmp_1751_, v_f_1752_, v_m_1753_);
lean_dec_ref(v_cmp_1751_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map___redArg(lean_object* v_f_1755_, lean_object* v_t_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_1755_, v_t_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map(lean_object* v_00_u03b1_1758_, lean_object* v_00_u03b2_1759_, lean_object* v_00_u03b3_1760_, lean_object* v_cmp_1761_, lean_object* v_f_1762_, lean_object* v_t_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_1762_, v_t_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map___boxed(lean_object* v_00_u03b1_1765_, lean_object* v_00_u03b2_1766_, lean_object* v_00_u03b3_1767_, lean_object* v_cmp_1768_, lean_object* v_f_1769_, lean_object* v_t_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Std_ExtTreeMap_map(v_00_u03b1_1765_, v_00_u03b2_1766_, v_00_u03b3_1767_, v_cmp_1768_, v_f_1769_, v_t_1770_);
lean_dec_ref(v_cmp_1768_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM___redArg(lean_object* v_inst_1772_, lean_object* v_f_1773_, lean_object* v_init_1774_, lean_object* v_t_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1772_, v_f_1773_, v_init_1774_, v_t_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM(lean_object* v_00_u03b1_1777_, lean_object* v_00_u03b2_1778_, lean_object* v_cmp_1779_, lean_object* v_00_u03b4_1780_, lean_object* v_m_1781_, lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_f_1785_, lean_object* v_init_1786_, lean_object* v_t_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1782_, v_f_1785_, v_init_1786_, v_t_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM___boxed(lean_object* v_00_u03b1_1789_, lean_object* v_00_u03b2_1790_, lean_object* v_cmp_1791_, lean_object* v_00_u03b4_1792_, lean_object* v_m_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_f_1797_, lean_object* v_init_1798_, lean_object* v_t_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Std_ExtTreeMap_foldlM(v_00_u03b1_1789_, v_00_u03b2_1790_, v_cmp_1791_, v_00_u03b4_1792_, v_m_1793_, v_inst_1794_, v_inst_1795_, v_inst_1796_, v_f_1797_, v_init_1798_, v_t_1799_);
lean_dec_ref(v_cmp_1791_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl___redArg(lean_object* v_f_1801_, lean_object* v_init_1802_, lean_object* v_t_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1801_, v_init_1802_, v_t_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl(lean_object* v_00_u03b1_1805_, lean_object* v_00_u03b2_1806_, lean_object* v_cmp_1807_, lean_object* v_00_u03b4_1808_, lean_object* v_inst_1809_, lean_object* v_f_1810_, lean_object* v_init_1811_, lean_object* v_t_1812_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1810_, v_init_1811_, v_t_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl___boxed(lean_object* v_00_u03b1_1814_, lean_object* v_00_u03b2_1815_, lean_object* v_cmp_1816_, lean_object* v_00_u03b4_1817_, lean_object* v_inst_1818_, lean_object* v_f_1819_, lean_object* v_init_1820_, lean_object* v_t_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Std_ExtTreeMap_foldl(v_00_u03b1_1814_, v_00_u03b2_1815_, v_cmp_1816_, v_00_u03b4_1817_, v_inst_1818_, v_f_1819_, v_init_1820_, v_t_1821_);
lean_dec_ref(v_cmp_1816_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM___redArg(lean_object* v_inst_1823_, lean_object* v_f_1824_, lean_object* v_init_1825_, lean_object* v_t_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1823_, v_f_1824_, v_init_1825_, v_t_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM(lean_object* v_00_u03b1_1828_, lean_object* v_00_u03b2_1829_, lean_object* v_cmp_1830_, lean_object* v_00_u03b4_1831_, lean_object* v_m_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_f_1836_, lean_object* v_init_1837_, lean_object* v_t_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1833_, v_f_1836_, v_init_1837_, v_t_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM___boxed(lean_object* v_00_u03b1_1840_, lean_object* v_00_u03b2_1841_, lean_object* v_cmp_1842_, lean_object* v_00_u03b4_1843_, lean_object* v_m_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_inst_1847_, lean_object* v_f_1848_, lean_object* v_init_1849_, lean_object* v_t_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Std_ExtTreeMap_foldrM(v_00_u03b1_1840_, v_00_u03b2_1841_, v_cmp_1842_, v_00_u03b4_1843_, v_m_1844_, v_inst_1845_, v_inst_1846_, v_inst_1847_, v_f_1848_, v_init_1849_, v_t_1850_);
lean_dec_ref(v_cmp_1842_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___redArg___lam__0(lean_object* v_f_1852_, lean_object* v_x1_1853_, lean_object* v_x2_1854_, lean_object* v_x3_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_apply_3(v_f_1852_, v_x1_1853_, v_x2_1854_, v_x3_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___redArg(lean_object* v_f_1876_, lean_object* v_init_1877_, lean_object* v_t_1878_){
_start:
{
lean_object* v___f_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___f_1879_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1879_, 0, v_f_1876_);
v___x_1880_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_1881_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1880_, v___f_1879_, v_init_1877_, v_t_1878_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr(lean_object* v_00_u03b1_1882_, lean_object* v_00_u03b2_1883_, lean_object* v_cmp_1884_, lean_object* v_00_u03b4_1885_, lean_object* v_inst_1886_, lean_object* v_f_1887_, lean_object* v_init_1888_, lean_object* v_t_1889_){
_start:
{
lean_object* v___f_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___f_1890_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1890_, 0, v_f_1887_);
v___x_1891_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_1892_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1891_, v___f_1890_, v_init_1888_, v_t_1889_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___boxed(lean_object* v_00_u03b1_1893_, lean_object* v_00_u03b2_1894_, lean_object* v_cmp_1895_, lean_object* v_00_u03b4_1896_, lean_object* v_inst_1897_, lean_object* v_f_1898_, lean_object* v_init_1899_, lean_object* v_t_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Std_ExtTreeMap_foldr(v_00_u03b1_1893_, v_00_u03b2_1894_, v_cmp_1895_, v_00_u03b4_1896_, v_inst_1897_, v_f_1898_, v_init_1899_, v_t_1900_);
lean_dec_ref(v_cmp_1895_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition___redArg___lam__0(lean_object* v_f_1902_, lean_object* v_cmp_1903_, lean_object* v_x_1904_, lean_object* v_a_1905_, lean_object* v_b_1906_){
_start:
{
lean_object* v_fst_1907_; lean_object* v_snd_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1922_; 
v_fst_1907_ = lean_ctor_get(v_x_1904_, 0);
v_snd_1908_ = lean_ctor_get(v_x_1904_, 1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_x_1904_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1910_ = v_x_1904_;
v_isShared_1911_ = v_isSharedCheck_1922_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_snd_1908_);
lean_inc(v_fst_1907_);
lean_dec(v_x_1904_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1922_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; uint8_t v___x_1913_; 
lean_inc(v_b_1906_);
lean_inc(v_a_1905_);
v___x_1912_ = lean_apply_2(v_f_1902_, v_a_1905_, v_b_1906_);
v___x_1913_ = lean_unbox(v___x_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1903_, v_a_1905_, v_b_1906_, v_snd_1908_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v___x_1914_);
v___x_1916_ = v___x_1910_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_fst_1907_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1918_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1903_, v_a_1905_, v_b_1906_, v_fst_1907_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1918_);
v___x_1920_ = v___x_1910_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_snd_1908_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition___redArg(lean_object* v_cmp_1925_, lean_object* v_f_1926_, lean_object* v_t_1927_){
_start:
{
lean_object* v___f_1928_; lean_object* v___x_1929_; lean_object* v_p_1930_; lean_object* v_fst_1931_; lean_object* v_snd_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v___f_1928_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1928_, 0, v_f_1926_);
lean_closure_set(v___f_1928_, 1, v_cmp_1925_);
v___x_1929_ = ((lean_object*)(l_Std_ExtTreeMap_partition___redArg___closed__0));
v_p_1930_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1928_, v___x_1929_, v_t_1927_);
v_fst_1931_ = lean_ctor_get(v_p_1930_, 0);
v_snd_1932_ = lean_ctor_get(v_p_1930_, 1);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_p_1930_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v_p_1930_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_snd_1932_);
lean_inc(v_fst_1931_);
lean_dec(v_p_1930_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_fst_1931_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_snd_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition(lean_object* v_00_u03b1_1940_, lean_object* v_00_u03b2_1941_, lean_object* v_cmp_1942_, lean_object* v_inst_1943_, lean_object* v_f_1944_, lean_object* v_t_1945_){
_start:
{
lean_object* v___f_1946_; lean_object* v___x_1947_; lean_object* v_p_1948_; lean_object* v_fst_1949_; lean_object* v_snd_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
v___f_1946_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1946_, 0, v_f_1944_);
lean_closure_set(v___f_1946_, 1, v_cmp_1942_);
v___x_1947_ = ((lean_object*)(l_Std_ExtTreeMap_partition___redArg___closed__0));
v_p_1948_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1946_, v___x_1947_, v_t_1945_);
v_fst_1949_ = lean_ctor_get(v_p_1948_, 0);
v_snd_1950_ = lean_ctor_get(v_p_1948_, 1);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_p_1948_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v_p_1948_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_snd_1950_);
lean_inc(v_fst_1949_);
lean_dec(v_p_1948_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_fst_1949_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_snd_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___redArg___lam__0(lean_object* v_f_1958_, lean_object* v_x_1959_, lean_object* v_k_1960_, lean_object* v_v_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = lean_apply_2(v_f_1958_, v_k_1960_, v_v_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___redArg(lean_object* v_inst_1963_, lean_object* v_f_1964_, lean_object* v_t_1965_){
_start:
{
lean_object* v___f_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___f_1966_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1966_, 0, v_f_1964_);
v___x_1967_ = lean_box(0);
v___x_1968_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1963_, v___f_1966_, v___x_1967_, v_t_1965_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM(lean_object* v_00_u03b1_1969_, lean_object* v_00_u03b2_1970_, lean_object* v_cmp_1971_, lean_object* v_m_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_f_1976_, lean_object* v_t_1977_){
_start:
{
lean_object* v___f_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___f_1978_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1978_, 0, v_f_1976_);
v___x_1979_ = lean_box(0);
v___x_1980_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1973_, v___f_1978_, v___x_1979_, v_t_1977_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___boxed(lean_object* v_00_u03b1_1981_, lean_object* v_00_u03b2_1982_, lean_object* v_cmp_1983_, lean_object* v_m_1984_, lean_object* v_inst_1985_, lean_object* v_inst_1986_, lean_object* v_inst_1987_, lean_object* v_f_1988_, lean_object* v_t_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Std_ExtTreeMap_forM(v_00_u03b1_1981_, v_00_u03b2_1982_, v_cmp_1983_, v_m_1984_, v_inst_1985_, v_inst_1986_, v_inst_1987_, v_f_1988_, v_t_1989_);
lean_dec_ref(v_cmp_1983_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg___lam__0(lean_object* v_f_1991_, lean_object* v_a_1992_, lean_object* v_b_1993_, lean_object* v_c_1994_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_apply_3(v_f_1991_, v_a_1992_, v_b_1993_, v_c_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg___lam__1(lean_object* v_toPure_1996_, lean_object* v_____do__lift_1997_){
_start:
{
lean_object* v_a_1998_; lean_object* v___x_1999_; 
v_a_1998_ = lean_ctor_get(v_____do__lift_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref(v_____do__lift_1997_);
v___x_1999_ = lean_apply_2(v_toPure_1996_, lean_box(0), v_a_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg(lean_object* v_inst_2000_, lean_object* v_f_2001_, lean_object* v_init_2002_, lean_object* v_t_2003_){
_start:
{
lean_object* v_toApplicative_2004_; lean_object* v_toBind_2005_; lean_object* v_toPure_2006_; lean_object* v___f_2007_; lean_object* v___x_2008_; lean_object* v___f_2009_; lean_object* v___x_2010_; 
v_toApplicative_2004_ = lean_ctor_get(v_inst_2000_, 0);
v_toBind_2005_ = lean_ctor_get(v_inst_2000_, 1);
lean_inc(v_toBind_2005_);
v_toPure_2006_ = lean_ctor_get(v_toApplicative_2004_, 1);
lean_inc(v_toPure_2006_);
v___f_2007_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2007_, 0, v_f_2001_);
v___x_2008_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2000_, v___f_2007_, v_init_2002_, v_t_2003_);
v___f_2009_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2009_, 0, v_toPure_2006_);
v___x_2010_ = lean_apply_4(v_toBind_2005_, lean_box(0), lean_box(0), v___x_2008_, v___f_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn(lean_object* v_00_u03b1_2011_, lean_object* v_00_u03b2_2012_, lean_object* v_cmp_2013_, lean_object* v_00_u03b4_2014_, lean_object* v_m_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_f_2019_, lean_object* v_init_2020_, lean_object* v_t_2021_){
_start:
{
lean_object* v_toApplicative_2022_; lean_object* v_toBind_2023_; lean_object* v_toPure_2024_; lean_object* v___f_2025_; lean_object* v___x_2026_; lean_object* v___f_2027_; lean_object* v___x_2028_; 
v_toApplicative_2022_ = lean_ctor_get(v_inst_2016_, 0);
v_toBind_2023_ = lean_ctor_get(v_inst_2016_, 1);
lean_inc(v_toBind_2023_);
v_toPure_2024_ = lean_ctor_get(v_toApplicative_2022_, 1);
lean_inc(v_toPure_2024_);
v___f_2025_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2025_, 0, v_f_2019_);
v___x_2026_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2016_, v___f_2025_, v_init_2020_, v_t_2021_);
v___f_2027_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2027_, 0, v_toPure_2024_);
v___x_2028_ = lean_apply_4(v_toBind_2023_, lean_box(0), lean_box(0), v___x_2026_, v___f_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___boxed(lean_object* v_00_u03b1_2029_, lean_object* v_00_u03b2_2030_, lean_object* v_cmp_2031_, lean_object* v_00_u03b4_2032_, lean_object* v_m_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_f_2037_, lean_object* v_init_2038_, lean_object* v_t_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Std_ExtTreeMap_forIn(v_00_u03b1_2029_, v_00_u03b2_2030_, v_cmp_2031_, v_00_u03b4_2032_, v_m_2033_, v_inst_2034_, v_inst_2035_, v_inst_2036_, v_f_2037_, v_init_2038_, v_t_2039_);
lean_dec_ref(v_cmp_2031_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2041_, lean_object* v_x_2042_, lean_object* v_k_2043_, lean_object* v_v_2044_){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v_k_2043_);
lean_ctor_set(v___x_2045_, 1, v_v_2044_);
v___x_2046_ = lean_apply_1(v_f_2041_, v___x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_2047_, lean_object* v_t_2048_, lean_object* v_f_2049_){
_start:
{
lean_object* v___f_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___f_2050_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2050_, 0, v_f_2049_);
v___x_2051_ = lean_box(0);
v___x_2052_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2047_, v___f_2050_, v___x_2051_, v_t_2048_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2053_){
_start:
{
lean_object* v___f_2054_; 
v___f_2054_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2054_, 0, v_inst_2053_);
return v___f_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2055_, lean_object* v_00_u03b2_2056_, lean_object* v_cmp_2057_, lean_object* v_m_2058_, lean_object* v_inst_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_){
_start:
{
lean_object* v___f_2062_; 
v___f_2062_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2062_, 0, v_inst_2060_);
return v___f_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2063_, lean_object* v_00_u03b2_2064_, lean_object* v_cmp_2065_, lean_object* v_m_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_inst_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(v_00_u03b1_2063_, v_00_u03b2_2064_, v_cmp_2065_, v_m_2066_, v_inst_2067_, v_inst_2068_, v_inst_2069_);
lean_dec_ref(v_cmp_2065_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2071_, lean_object* v_a_2072_, lean_object* v_b_2073_, lean_object* v_c_2074_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_a_2072_);
lean_ctor_set(v___x_2075_, 1, v_b_2073_);
v___x_2076_ = lean_apply_2(v_f_2071_, v___x_2075_, v_c_2074_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_2077_, lean_object* v_00_u03b2_2078_, lean_object* v_m_2079_, lean_object* v_init_2080_, lean_object* v_f_2081_){
_start:
{
lean_object* v_toApplicative_2082_; lean_object* v_toBind_2083_; lean_object* v_toPure_2084_; lean_object* v___f_2085_; lean_object* v___x_2086_; lean_object* v___f_2087_; lean_object* v___x_2088_; 
v_toApplicative_2082_ = lean_ctor_get(v_inst_2077_, 0);
v_toBind_2083_ = lean_ctor_get(v_inst_2077_, 1);
lean_inc(v_toBind_2083_);
v_toPure_2084_ = lean_ctor_get(v_toApplicative_2082_, 1);
lean_inc(v_toPure_2084_);
v___f_2085_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2085_, 0, v_f_2081_);
v___x_2086_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2077_, v___f_2085_, v_init_2080_, v_m_2079_);
v___f_2087_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2087_, 0, v_toPure_2084_);
v___x_2088_ = lean_apply_4(v_toBind_2083_, lean_box(0), lean_box(0), v___x_2086_, v___f_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2089_){
_start:
{
lean_object* v___f_2090_; 
v___f_2090_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2090_, 0, v_inst_2089_);
return v___f_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2091_, lean_object* v_00_u03b2_2092_, lean_object* v_cmp_2093_, lean_object* v_m_2094_, lean_object* v_inst_2095_, lean_object* v_inst_2096_, lean_object* v_inst_2097_){
_start:
{
lean_object* v___f_2098_; 
v___f_2098_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2098_, 0, v_inst_2096_);
return v___f_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_cmp_2101_, lean_object* v_m_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_inst_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(v_00_u03b1_2099_, v_00_u03b2_2100_, v_cmp_2101_, v_m_2102_, v_inst_2103_, v_inst_2104_, v_inst_2105_);
lean_dec_ref(v_cmp_2101_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___lam__0(lean_object* v_p_2107_, lean_object* v___x_2108_, lean_object* v___x_2109_, lean_object* v_a_2110_, lean_object* v_b_2111_, lean_object* v_acc_2112_){
_start:
{
lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = lean_apply_2(v_p_2107_, v_a_2110_, v_b_2111_);
v___x_2114_ = lean_unbox(v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; 
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2108_);
return v___x_2115_;
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec_ref(v___x_2108_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2113_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set(v___x_2117_, 1, v___x_2109_);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2119_, lean_object* v___x_2120_, lean_object* v___x_2121_, lean_object* v_a_2122_, lean_object* v_b_2123_, lean_object* v_acc_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Std_ExtTreeMap_any___redArg___lam__0(v_p_2119_, v___x_2120_, v___x_2121_, v_a_2122_, v_b_2123_, v_acc_2124_);
lean_dec_ref(v_acc_2124_);
return v_res_2125_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_any___redArg(lean_object* v_t_2129_, lean_object* v_p_2130_){
_start:
{
lean_object* v___y_2132_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___f_2140_; lean_object* v___x_2141_; lean_object* v_a_2142_; 
v___x_2137_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2138_ = lean_box(0);
v___x_2139_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2140_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2140_, 0, v_p_2130_);
lean_closure_set(v___f_2140_, 1, v___x_2139_);
lean_closure_set(v___f_2140_, 2, v___x_2138_);
v___x_2141_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2137_, v___f_2140_, v___x_2139_, v_t_2129_);
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___y_2132_ = v_a_2142_;
goto v___jp_2131_;
v___jp_2131_:
{
lean_object* v_fst_2133_; 
v_fst_2133_ = lean_ctor_get(v___y_2132_, 0);
lean_inc(v_fst_2133_);
lean_dec_ref(v___y_2132_);
if (lean_obj_tag(v_fst_2133_) == 0)
{
uint8_t v___x_2134_; 
v___x_2134_ = 0;
return v___x_2134_;
}
else
{
lean_object* v_val_2135_; uint8_t v___x_2136_; 
v_val_2135_ = lean_ctor_get(v_fst_2133_, 0);
lean_inc(v_val_2135_);
lean_dec_ref_known(v_fst_2133_, 1);
v___x_2136_ = lean_unbox(v_val_2135_);
lean_dec(v_val_2135_);
return v___x_2136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___boxed(lean_object* v_t_2143_, lean_object* v_p_2144_){
_start:
{
uint8_t v_res_2145_; lean_object* v_r_2146_; 
v_res_2145_ = l_Std_ExtTreeMap_any___redArg(v_t_2143_, v_p_2144_);
v_r_2146_ = lean_box(v_res_2145_);
return v_r_2146_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_any(lean_object* v_00_u03b1_2147_, lean_object* v_00_u03b2_2148_, lean_object* v_cmp_2149_, lean_object* v_inst_2150_, lean_object* v_t_2151_, lean_object* v_p_2152_){
_start:
{
lean_object* v___y_2154_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___f_2162_; lean_object* v___x_2163_; lean_object* v_a_2164_; 
v___x_2159_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2160_ = lean_box(0);
v___x_2161_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2162_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2162_, 0, v_p_2152_);
lean_closure_set(v___f_2162_, 1, v___x_2161_);
lean_closure_set(v___f_2162_, 2, v___x_2160_);
v___x_2163_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2159_, v___f_2162_, v___x_2161_, v_t_2151_);
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___y_2154_ = v_a_2164_;
goto v___jp_2153_;
v___jp_2153_:
{
lean_object* v_fst_2155_; 
v_fst_2155_ = lean_ctor_get(v___y_2154_, 0);
lean_inc(v_fst_2155_);
lean_dec_ref(v___y_2154_);
if (lean_obj_tag(v_fst_2155_) == 0)
{
uint8_t v___x_2156_; 
v___x_2156_ = 0;
return v___x_2156_;
}
else
{
lean_object* v_val_2157_; uint8_t v___x_2158_; 
v_val_2157_ = lean_ctor_get(v_fst_2155_, 0);
lean_inc(v_val_2157_);
lean_dec_ref_known(v_fst_2155_, 1);
v___x_2158_ = lean_unbox(v_val_2157_);
lean_dec(v_val_2157_);
return v___x_2158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___boxed(lean_object* v_00_u03b1_2165_, lean_object* v_00_u03b2_2166_, lean_object* v_cmp_2167_, lean_object* v_inst_2168_, lean_object* v_t_2169_, lean_object* v_p_2170_){
_start:
{
uint8_t v_res_2171_; lean_object* v_r_2172_; 
v_res_2171_ = l_Std_ExtTreeMap_any(v_00_u03b1_2165_, v_00_u03b2_2166_, v_cmp_2167_, v_inst_2168_, v_t_2169_, v_p_2170_);
lean_dec_ref(v_cmp_2167_);
v_r_2172_ = lean_box(v_res_2171_);
return v_r_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___lam__0(lean_object* v_p_2173_, lean_object* v___x_2174_, lean_object* v___x_2175_, lean_object* v_a_2176_, lean_object* v_b_2177_, lean_object* v_acc_2178_){
_start:
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = lean_apply_2(v_p_2173_, v_a_2176_, v_b_2177_);
v___x_2180_ = lean_unbox(v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec_ref(v___x_2175_);
v___x_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2179_);
v___x_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2174_);
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
return v___x_2183_;
}
else
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2175_);
return v___x_2184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_2185_, lean_object* v___x_2186_, lean_object* v___x_2187_, lean_object* v_a_2188_, lean_object* v_b_2189_, lean_object* v_acc_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Std_ExtTreeMap_all___redArg___lam__0(v_p_2185_, v___x_2186_, v___x_2187_, v_a_2188_, v_b_2189_, v_acc_2190_);
lean_dec_ref(v_acc_2190_);
return v_res_2191_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_all___redArg(lean_object* v_t_2192_, lean_object* v_p_2193_){
_start:
{
lean_object* v___y_2195_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; lean_object* v_a_2205_; 
v___x_2200_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2201_ = lean_box(0);
v___x_2202_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2203_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2203_, 0, v_p_2193_);
lean_closure_set(v___f_2203_, 1, v___x_2201_);
lean_closure_set(v___f_2203_, 2, v___x_2202_);
v___x_2204_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2200_, v___f_2203_, v___x_2202_, v_t_2192_);
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___y_2195_ = v_a_2205_;
goto v___jp_2194_;
v___jp_2194_:
{
lean_object* v_fst_2196_; 
v_fst_2196_ = lean_ctor_get(v___y_2195_, 0);
lean_inc(v_fst_2196_);
lean_dec_ref(v___y_2195_);
if (lean_obj_tag(v_fst_2196_) == 0)
{
uint8_t v___x_2197_; 
v___x_2197_ = 1;
return v___x_2197_;
}
else
{
lean_object* v_val_2198_; uint8_t v___x_2199_; 
v_val_2198_ = lean_ctor_get(v_fst_2196_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v_fst_2196_, 1);
v___x_2199_ = lean_unbox(v_val_2198_);
lean_dec(v_val_2198_);
return v___x_2199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___boxed(lean_object* v_t_2206_, lean_object* v_p_2207_){
_start:
{
uint8_t v_res_2208_; lean_object* v_r_2209_; 
v_res_2208_ = l_Std_ExtTreeMap_all___redArg(v_t_2206_, v_p_2207_);
v_r_2209_ = lean_box(v_res_2208_);
return v_r_2209_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_all(lean_object* v_00_u03b1_2210_, lean_object* v_00_u03b2_2211_, lean_object* v_cmp_2212_, lean_object* v_inst_2213_, lean_object* v_t_2214_, lean_object* v_p_2215_){
_start:
{
lean_object* v___y_2217_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___f_2225_; lean_object* v___x_2226_; lean_object* v_a_2227_; 
v___x_2222_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2223_ = lean_box(0);
v___x_2224_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2225_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2225_, 0, v_p_2215_);
lean_closure_set(v___f_2225_, 1, v___x_2223_);
lean_closure_set(v___f_2225_, 2, v___x_2224_);
v___x_2226_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2222_, v___f_2225_, v___x_2224_, v_t_2214_);
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___y_2217_ = v_a_2227_;
goto v___jp_2216_;
v___jp_2216_:
{
lean_object* v_fst_2218_; 
v_fst_2218_ = lean_ctor_get(v___y_2217_, 0);
lean_inc(v_fst_2218_);
lean_dec_ref(v___y_2217_);
if (lean_obj_tag(v_fst_2218_) == 0)
{
uint8_t v___x_2219_; 
v___x_2219_ = 1;
return v___x_2219_;
}
else
{
lean_object* v_val_2220_; uint8_t v___x_2221_; 
v_val_2220_ = lean_ctor_get(v_fst_2218_, 0);
lean_inc(v_val_2220_);
lean_dec_ref_known(v_fst_2218_, 1);
v___x_2221_ = lean_unbox(v_val_2220_);
lean_dec(v_val_2220_);
return v___x_2221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___boxed(lean_object* v_00_u03b1_2228_, lean_object* v_00_u03b2_2229_, lean_object* v_cmp_2230_, lean_object* v_inst_2231_, lean_object* v_t_2232_, lean_object* v_p_2233_){
_start:
{
uint8_t v_res_2234_; lean_object* v_r_2235_; 
v_res_2234_ = l_Std_ExtTreeMap_all(v_00_u03b1_2228_, v_00_u03b2_2229_, v_cmp_2230_, v_inst_2231_, v_t_2232_, v_p_2233_);
lean_dec_ref(v_cmp_2230_);
v_r_2235_ = lean_box(v_res_2234_);
return v_r_2235_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg___lam__0(lean_object* v_x1_2236_, lean_object* v_x2_2237_, lean_object* v_x3_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_x1_2236_);
lean_ctor_set(v___x_2239_, 1, v_x3_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_2240_, lean_object* v_x2_2241_, lean_object* v_x3_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Std_ExtTreeMap_keys___redArg___lam__0(v_x1_2240_, v_x2_2241_, v_x3_2242_);
lean_dec(v_x2_2241_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg(lean_object* v_t_2245_){
_start:
{
lean_object* v___f_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___f_2246_ = ((lean_object*)(l_Std_ExtTreeMap_keys___redArg___closed__0));
v___x_2247_ = lean_box(0);
v___x_2248_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2249_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2248_, v___f_2246_, v___x_2247_, v_t_2245_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys(lean_object* v_00_u03b1_2250_, lean_object* v_00_u03b2_2251_, lean_object* v_cmp_2252_, lean_object* v_inst_2253_, lean_object* v_t_2254_){
_start:
{
lean_object* v___f_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___f_2255_ = ((lean_object*)(l_Std_ExtTreeMap_keys___redArg___closed__0));
v___x_2256_ = lean_box(0);
v___x_2257_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2258_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2257_, v___f_2255_, v___x_2256_, v_t_2254_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___boxed(lean_object* v_00_u03b1_2259_, lean_object* v_00_u03b2_2260_, lean_object* v_cmp_2261_, lean_object* v_inst_2262_, lean_object* v_t_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Std_ExtTreeMap_keys(v_00_u03b1_2259_, v_00_u03b2_2260_, v_cmp_2261_, v_inst_2262_, v_t_2263_);
lean_dec_ref(v_cmp_2261_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg___lam__0(lean_object* v_l_2265_, lean_object* v_k_2266_, lean_object* v_x_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_array_push(v_l_2265_, v_k_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_2269_, lean_object* v_k_2270_, lean_object* v_x_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Std_ExtTreeMap_keysArray___redArg___lam__0(v_l_2269_, v_k_2270_, v_x_2271_);
lean_dec(v_x_2271_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg(lean_object* v_t_2274_){
_start:
{
lean_object* v___f_2275_; lean_object* v___y_2277_; 
v___f_2275_ = ((lean_object*)(l_Std_ExtTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2274_) == 0)
{
lean_object* v_size_2280_; 
v_size_2280_ = lean_ctor_get(v_t_2274_, 0);
lean_inc(v_size_2280_);
v___y_2277_ = v_size_2280_;
goto v___jp_2276_;
}
else
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_unsigned_to_nat(0u);
v___y_2277_ = v___x_2281_;
goto v___jp_2276_;
}
v___jp_2276_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_mk_empty_array_with_capacity(v___y_2277_);
lean_dec(v___y_2277_);
v___x_2279_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2275_, v___x_2278_, v_t_2274_);
return v___x_2279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray(lean_object* v_00_u03b1_2282_, lean_object* v_00_u03b2_2283_, lean_object* v_cmp_2284_, lean_object* v_inst_2285_, lean_object* v_t_2286_){
_start:
{
lean_object* v___f_2287_; lean_object* v___y_2289_; 
v___f_2287_ = ((lean_object*)(l_Std_ExtTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2286_) == 0)
{
lean_object* v_size_2292_; 
v_size_2292_ = lean_ctor_get(v_t_2286_, 0);
lean_inc(v_size_2292_);
v___y_2289_ = v_size_2292_;
goto v___jp_2288_;
}
else
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_unsigned_to_nat(0u);
v___y_2289_ = v___x_2293_;
goto v___jp_2288_;
}
v___jp_2288_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_mk_empty_array_with_capacity(v___y_2289_);
lean_dec(v___y_2289_);
v___x_2291_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2287_, v___x_2290_, v_t_2286_);
return v___x_2291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___boxed(lean_object* v_00_u03b1_2294_, lean_object* v_00_u03b2_2295_, lean_object* v_cmp_2296_, lean_object* v_inst_2297_, lean_object* v_t_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Std_ExtTreeMap_keysArray(v_00_u03b1_2294_, v_00_u03b2_2295_, v_cmp_2296_, v_inst_2297_, v_t_2298_);
lean_dec_ref(v_cmp_2296_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg___lam__0(lean_object* v_x1_2300_, lean_object* v_x2_2301_, lean_object* v_x3_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2303_, 0, v_x2_2301_);
lean_ctor_set(v___x_2303_, 1, v_x3_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_2304_, lean_object* v_x2_2305_, lean_object* v_x3_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Std_ExtTreeMap_values___redArg___lam__0(v_x1_2304_, v_x2_2305_, v_x3_2306_);
lean_dec(v_x1_2304_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg(lean_object* v_t_2309_){
_start:
{
lean_object* v___f_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___f_2310_ = ((lean_object*)(l_Std_ExtTreeMap_values___redArg___closed__0));
v___x_2311_ = lean_box(0);
v___x_2312_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2313_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2312_, v___f_2310_, v___x_2311_, v_t_2309_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values(lean_object* v_00_u03b1_2314_, lean_object* v_00_u03b2_2315_, lean_object* v_cmp_2316_, lean_object* v_inst_2317_, lean_object* v_t_2318_){
_start:
{
lean_object* v___f_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___f_2319_ = ((lean_object*)(l_Std_ExtTreeMap_values___redArg___closed__0));
v___x_2320_ = lean_box(0);
v___x_2321_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2322_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2321_, v___f_2319_, v___x_2320_, v_t_2318_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___boxed(lean_object* v_00_u03b1_2323_, lean_object* v_00_u03b2_2324_, lean_object* v_cmp_2325_, lean_object* v_inst_2326_, lean_object* v_t_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Std_ExtTreeMap_values(v_00_u03b1_2323_, v_00_u03b2_2324_, v_cmp_2325_, v_inst_2326_, v_t_2327_);
lean_dec_ref(v_cmp_2325_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_2329_, lean_object* v_x_2330_, lean_object* v_v_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_array_push(v_l_2329_, v_v_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2333_, lean_object* v_x_2334_, lean_object* v_v_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Std_ExtTreeMap_valuesArray___redArg___lam__0(v_l_2333_, v_x_2334_, v_v_2335_);
lean_dec(v_x_2334_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg(lean_object* v_t_2338_){
_start:
{
lean_object* v___f_2339_; lean_object* v___y_2341_; 
v___f_2339_ = ((lean_object*)(l_Std_ExtTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2338_) == 0)
{
lean_object* v_size_2344_; 
v_size_2344_ = lean_ctor_get(v_t_2338_, 0);
lean_inc(v_size_2344_);
v___y_2341_ = v_size_2344_;
goto v___jp_2340_;
}
else
{
lean_object* v___x_2345_; 
v___x_2345_ = lean_unsigned_to_nat(0u);
v___y_2341_ = v___x_2345_;
goto v___jp_2340_;
}
v___jp_2340_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_mk_empty_array_with_capacity(v___y_2341_);
lean_dec(v___y_2341_);
v___x_2343_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2339_, v___x_2342_, v_t_2338_);
return v___x_2343_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray(lean_object* v_00_u03b1_2346_, lean_object* v_00_u03b2_2347_, lean_object* v_cmp_2348_, lean_object* v_inst_2349_, lean_object* v_t_2350_){
_start:
{
lean_object* v___f_2351_; lean_object* v___y_2353_; 
v___f_2351_ = ((lean_object*)(l_Std_ExtTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2350_) == 0)
{
lean_object* v_size_2356_; 
v_size_2356_ = lean_ctor_get(v_t_2350_, 0);
lean_inc(v_size_2356_);
v___y_2353_ = v_size_2356_;
goto v___jp_2352_;
}
else
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_unsigned_to_nat(0u);
v___y_2353_ = v___x_2357_;
goto v___jp_2352_;
}
v___jp_2352_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_mk_empty_array_with_capacity(v___y_2353_);
lean_dec(v___y_2353_);
v___x_2355_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2351_, v___x_2354_, v_t_2350_);
return v___x_2355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_2358_, lean_object* v_00_u03b2_2359_, lean_object* v_cmp_2360_, lean_object* v_inst_2361_, lean_object* v_t_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Std_ExtTreeMap_valuesArray(v_00_u03b1_2358_, v_00_u03b2_2359_, v_cmp_2360_, v_inst_2361_, v_t_2362_);
lean_dec_ref(v_cmp_2360_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___redArg___lam__0(lean_object* v_x1_2364_, lean_object* v_x2_2365_, lean_object* v_x3_2366_){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2367_, 0, v_x1_2364_);
lean_ctor_set(v___x_2367_, 1, v_x2_2365_);
v___x_2368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
lean_ctor_set(v___x_2368_, 1, v_x3_2366_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___redArg(lean_object* v_t_2370_){
_start:
{
lean_object* v___f_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___f_2371_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___x_2372_ = lean_box(0);
v___x_2373_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2374_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2373_, v___f_2371_, v___x_2372_, v_t_2370_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList(lean_object* v_00_u03b1_2375_, lean_object* v_00_u03b2_2376_, lean_object* v_cmp_2377_, lean_object* v_inst_2378_, lean_object* v_t_2379_){
_start:
{
lean_object* v___f_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___f_2380_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___x_2381_ = lean_box(0);
v___x_2382_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2383_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2382_, v___f_2380_, v___x_2381_, v_t_2379_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___boxed(lean_object* v_00_u03b1_2384_, lean_object* v_00_u03b2_2385_, lean_object* v_cmp_2386_, lean_object* v_inst_2387_, lean_object* v_t_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Std_ExtTreeMap_toList(v_00_u03b1_2384_, v_00_u03b2_2385_, v_cmp_2386_, v_inst_2387_, v_t_2388_);
lean_dec_ref(v_cmp_2386_);
return v_res_2389_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_2391_, lean_object* v_a_2392_, lean_object* v_x_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_fst_2395_; lean_object* v_snd_2396_; lean_object* v_r_2397_; lean_object* v___x_2398_; 
v_fst_2395_ = lean_ctor_get(v_a_2392_, 0);
lean_inc(v_fst_2395_);
v_snd_2396_ = lean_ctor_get(v_a_2392_, 1);
lean_inc(v_snd_2396_);
lean_dec_ref(v_a_2392_);
v_r_2397_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2391_, v_fst_2395_, v_snd_2396_, v___y_2394_);
v___x_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2398_, 0, v_r_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg(lean_object* v_l_2399_, lean_object* v_cmp_2400_){
_start:
{
lean_object* v___f_2401_; lean_object* v___x_2402_; lean_object* v_r_2403_; lean_object* v___x_2404_; 
v___f_2401_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2401_, 0, v_cmp_2400_);
v___x_2402_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2403_ = lean_box(1);
v___x_2404_ = l_List_forIn_x27_loop___redArg(v___x_2402_, v___f_2401_, v_l_2399_, v_r_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg___boxed(lean_object* v_l_2405_, lean_object* v_cmp_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Std_ExtTreeMap_ofList___redArg(v_l_2405_, v_cmp_2406_);
lean_dec(v_l_2405_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList(lean_object* v_00_u03b1_2408_, lean_object* v_00_u03b2_2409_, lean_object* v_l_2410_, lean_object* v_cmp_2411_){
_start:
{
lean_object* v___f_2412_; lean_object* v___x_2413_; lean_object* v_r_2414_; lean_object* v___x_2415_; 
v___f_2412_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2412_, 0, v_cmp_2411_);
v___x_2413_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2414_ = lean_box(1);
v___x_2415_ = l_List_forIn_x27_loop___redArg(v___x_2413_, v___f_2412_, v_l_2410_, v_r_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___boxed(lean_object* v_00_u03b1_2416_, lean_object* v_00_u03b2_2417_, lean_object* v_l_2418_, lean_object* v_cmp_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Std_ExtTreeMap_ofList(v_00_u03b1_2416_, v_00_u03b2_2417_, v_l_2418_, v_cmp_2419_);
lean_dec(v_l_2418_);
return v_res_2420_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg___lam__0(lean_object* v_cmp_2422_, lean_object* v_a_2423_, lean_object* v_x_2424_, lean_object* v___y_2425_){
_start:
{
uint8_t v___x_2426_; 
lean_inc(v___y_2425_);
lean_inc(v_a_2423_);
lean_inc_ref(v_cmp_2422_);
v___x_2426_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2422_, v_a_2423_, v___y_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_box(0);
v___x_2428_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2422_, v_a_2423_, v___x_2427_, v___y_2425_);
v___x_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
return v___x_2429_;
}
else
{
lean_object* v___x_2430_; 
lean_dec(v_a_2423_);
lean_dec_ref(v_cmp_2422_);
v___x_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2430_, 0, v___y_2425_);
return v___x_2430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg(lean_object* v_l_2431_, lean_object* v_cmp_2432_){
_start:
{
lean_object* v___f_2433_; lean_object* v___x_2434_; lean_object* v_r_2435_; lean_object* v___x_2436_; 
v___f_2433_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2433_, 0, v_cmp_2432_);
v___x_2434_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2435_ = lean_box(1);
v___x_2436_ = l_List_forIn_x27_loop___redArg(v___x_2434_, v___f_2433_, v_l_2431_, v_r_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg___boxed(lean_object* v_l_2437_, lean_object* v_cmp_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Std_ExtTreeMap_unitOfList___redArg(v_l_2437_, v_cmp_2438_);
lean_dec(v_l_2437_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList(lean_object* v_00_u03b1_2440_, lean_object* v_l_2441_, lean_object* v_cmp_2442_){
_start:
{
lean_object* v___f_2443_; lean_object* v___x_2444_; lean_object* v_r_2445_; lean_object* v___x_2446_; 
v___f_2443_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2443_, 0, v_cmp_2442_);
v___x_2444_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2445_ = lean_box(1);
v___x_2446_ = l_List_forIn_x27_loop___redArg(v___x_2444_, v___f_2443_, v_l_2441_, v_r_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___boxed(lean_object* v_00_u03b1_2447_, lean_object* v_l_2448_, lean_object* v_cmp_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Std_ExtTreeMap_unitOfList(v_00_u03b1_2447_, v_l_2448_, v_cmp_2449_);
lean_dec(v_l_2448_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___redArg___lam__0(lean_object* v_acc_2451_, lean_object* v_k_2452_, lean_object* v_v_2453_){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v_k_2452_);
lean_ctor_set(v___x_2454_, 1, v_v_2453_);
v___x_2455_ = lean_array_push(v_acc_2451_, v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___redArg(lean_object* v_t_2459_){
_start:
{
lean_object* v___f_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___f_2460_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__0));
v___x_2461_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__1));
v___x_2462_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2460_, v___x_2461_, v_t_2459_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray(lean_object* v_00_u03b1_2463_, lean_object* v_00_u03b2_2464_, lean_object* v_cmp_2465_, lean_object* v_inst_2466_, lean_object* v_t_2467_){
_start:
{
lean_object* v___f_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___f_2468_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__0));
v___x_2469_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__1));
v___x_2470_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2468_, v___x_2469_, v_t_2467_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___boxed(lean_object* v_00_u03b1_2471_, lean_object* v_00_u03b2_2472_, lean_object* v_cmp_2473_, lean_object* v_inst_2474_, lean_object* v_t_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Std_ExtTreeMap_toArray(v_00_u03b1_2471_, v_00_u03b2_2472_, v_cmp_2473_, v_inst_2474_, v_t_2475_);
lean_dec_ref(v_cmp_2473_);
return v_res_2476_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray___redArg(lean_object* v_a_2478_, lean_object* v_cmp_2479_){
_start:
{
lean_object* v___f_2480_; lean_object* v___x_2481_; lean_object* v_r_2482_; size_t v_sz_2483_; size_t v___x_2484_; lean_object* v___x_2485_; 
v___f_2480_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2480_, 0, v_cmp_2479_);
v___x_2481_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2482_ = lean_box(1);
v_sz_2483_ = lean_array_size(v_a_2478_);
v___x_2484_ = ((size_t)0ULL);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2481_, v_a_2478_, v___f_2480_, v_sz_2483_, v___x_2484_, v_r_2482_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray(lean_object* v_00_u03b1_2486_, lean_object* v_00_u03b2_2487_, lean_object* v_a_2488_, lean_object* v_cmp_2489_){
_start:
{
lean_object* v___f_2490_; lean_object* v___x_2491_; lean_object* v_r_2492_; size_t v_sz_2493_; size_t v___x_2494_; lean_object* v___x_2495_; 
v___f_2490_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2490_, 0, v_cmp_2489_);
v___x_2491_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2492_ = lean_box(1);
v_sz_2493_ = lean_array_size(v_a_2488_);
v___x_2494_ = ((size_t)0ULL);
v___x_2495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2491_, v_a_2488_, v___f_2490_, v_sz_2493_, v___x_2494_, v_r_2492_);
return v___x_2495_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray___redArg(lean_object* v_a_2497_, lean_object* v_cmp_2498_){
_start:
{
lean_object* v___f_2499_; lean_object* v___x_2500_; lean_object* v_r_2501_; size_t v_sz_2502_; size_t v___x_2503_; lean_object* v___x_2504_; 
v___f_2499_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2499_, 0, v_cmp_2498_);
v___x_2500_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2501_ = lean_box(1);
v_sz_2502_ = lean_array_size(v_a_2497_);
v___x_2503_ = ((size_t)0ULL);
v___x_2504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2500_, v_a_2497_, v___f_2499_, v_sz_2502_, v___x_2503_, v_r_2501_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray(lean_object* v_00_u03b1_2505_, lean_object* v_a_2506_, lean_object* v_cmp_2507_){
_start:
{
lean_object* v___f_2508_; lean_object* v___x_2509_; lean_object* v_r_2510_; size_t v_sz_2511_; size_t v___x_2512_; lean_object* v___x_2513_; 
v___f_2508_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2508_, 0, v_cmp_2507_);
v___x_2509_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2510_ = lean_box(1);
v_sz_2511_ = lean_array_size(v_a_2506_);
v___x_2512_ = ((size_t)0ULL);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2509_, v_a_2506_, v___f_2508_, v_sz_2511_, v___x_2512_, v_r_2510_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_modify___redArg(lean_object* v_cmp_2514_, lean_object* v_t_2515_, lean_object* v_a_2516_, lean_object* v_f_2517_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2514_, v_a_2516_, v_f_2517_, v_t_2515_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_modify(lean_object* v_00_u03b1_2519_, lean_object* v_00_u03b2_2520_, lean_object* v_cmp_2521_, lean_object* v_inst_2522_, lean_object* v_t_2523_, lean_object* v_a_2524_, lean_object* v_f_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2521_, v_a_2524_, v_f_2525_, v_t_2523_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_alter___redArg(lean_object* v_cmp_2527_, lean_object* v_t_2528_, lean_object* v_a_2529_, lean_object* v_f_2530_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2527_, v_a_2529_, v_f_2530_, v_t_2528_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_alter(lean_object* v_00_u03b1_2532_, lean_object* v_00_u03b2_2533_, lean_object* v_cmp_2534_, lean_object* v_inst_2535_, lean_object* v_t_2536_, lean_object* v_a_2537_, lean_object* v_f_2538_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2534_, v_a_2537_, v_f_2538_, v_t_2536_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2540_, lean_object* v_mergeFn_2541_, lean_object* v_a_2542_, lean_object* v_x_2543_){
_start:
{
if (lean_obj_tag(v_x_2543_) == 0)
{
lean_object* v___x_2544_; 
lean_dec(v_a_2542_);
lean_dec(v_mergeFn_2541_);
v___x_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2544_, 0, v_b_u2082_2540_);
return v___x_2544_;
}
else
{
lean_object* v_val_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2553_; 
v_val_2545_ = lean_ctor_get(v_x_2543_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_x_2543_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2547_ = v_x_2543_;
v_isShared_2548_ = v_isSharedCheck_2553_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_val_2545_);
lean_dec(v_x_2543_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2553_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2549_ = lean_apply_3(v_mergeFn_2541_, v_a_2542_, v_val_2545_, v_b_u2082_2540_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2549_);
v___x_2551_ = v___x_2547_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2554_, lean_object* v_cmp_2555_, lean_object* v_t_2556_, lean_object* v_a_2557_, lean_object* v_b_u2082_2558_){
_start:
{
lean_object* v___f_2559_; lean_object* v___x_2560_; 
lean_inc(v_a_2557_);
v___f_2559_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2559_, 0, v_b_u2082_2558_);
lean_closure_set(v___f_2559_, 1, v_mergeFn_2554_);
lean_closure_set(v___f_2559_, 2, v_a_2557_);
v___x_2560_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2555_, v_a_2557_, v___f_2559_, v_t_2556_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg(lean_object* v_cmp_2561_, lean_object* v_mergeFn_2562_, lean_object* v_t_u2081_2563_, lean_object* v_t_u2082_2564_){
_start:
{
lean_object* v___f_2565_; lean_object* v___x_2566_; 
v___f_2565_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2565_, 0, v_mergeFn_2562_);
lean_closure_set(v___f_2565_, 1, v_cmp_2561_);
v___x_2566_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2565_, v_t_u2081_2563_, v_t_u2082_2564_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith(lean_object* v_00_u03b1_2567_, lean_object* v_00_u03b2_2568_, lean_object* v_cmp_2569_, lean_object* v_inst_2570_, lean_object* v_mergeFn_2571_, lean_object* v_t_u2081_2572_, lean_object* v_t_u2082_2573_){
_start:
{
lean_object* v___f_2574_; lean_object* v___x_2575_; 
v___f_2574_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2574_, 0, v_mergeFn_2571_);
lean_closure_set(v___f_2574_, 1, v_cmp_2569_);
v___x_2575_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2574_, v_t_u2081_2572_, v_t_u2082_2573_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_2576_, lean_object* v_x_2577_, lean_object* v_____s_2578_){
_start:
{
lean_object* v_fst_2579_; lean_object* v_snd_2580_; lean_object* v_acc_2581_; lean_object* v___x_2582_; 
v_fst_2579_ = lean_ctor_get(v_x_2577_, 0);
lean_inc(v_fst_2579_);
v_snd_2580_ = lean_ctor_get(v_x_2577_, 1);
lean_inc(v_snd_2580_);
lean_dec_ref(v_x_2577_);
v_acc_2581_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2576_, v_fst_2579_, v_snd_2580_, v_____s_2578_);
v___x_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2582_, 0, v_acc_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany___redArg(lean_object* v_cmp_2583_, lean_object* v_inst_2584_, lean_object* v_t_2585_, lean_object* v_l_2586_){
_start:
{
lean_object* v___f_2587_; lean_object* v___x_2588_; 
v___f_2587_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2587_, 0, v_cmp_2583_);
v___x_2588_ = lean_apply_4(v_inst_2584_, lean_box(0), v_l_2586_, v_t_2585_, v___f_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany(lean_object* v_00_u03b1_2589_, lean_object* v_00_u03b2_2590_, lean_object* v_cmp_2591_, lean_object* v_inst_2592_, lean_object* v_00_u03c1_2593_, lean_object* v_inst_2594_, lean_object* v_t_2595_, lean_object* v_l_2596_){
_start:
{
lean_object* v___f_2597_; lean_object* v___x_2598_; 
v___f_2597_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2597_, 0, v_cmp_2591_);
v___x_2598_ = lean_apply_4(v_inst_2594_, lean_box(0), v_l_2596_, v_t_2595_, v___f_2597_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_2599_, lean_object* v_a_2600_, lean_object* v_____s_2601_){
_start:
{
uint8_t v___x_2602_; 
lean_inc(v_____s_2601_);
lean_inc(v_a_2600_);
lean_inc_ref(v_cmp_2599_);
v___x_2602_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2599_, v_a_2600_, v_____s_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = lean_box(0);
v___x_2604_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2599_, v_a_2600_, v___x_2603_, v_____s_2601_);
v___x_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
return v___x_2605_;
}
else
{
lean_object* v___x_2606_; 
lean_dec(v_a_2600_);
lean_dec_ref(v_cmp_2599_);
v___x_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2606_, 0, v_____s_2601_);
return v___x_2606_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit___redArg(lean_object* v_cmp_2607_, lean_object* v_inst_2608_, lean_object* v_t_2609_, lean_object* v_l_2610_){
_start:
{
lean_object* v___f_2611_; lean_object* v___x_2612_; 
v___f_2611_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2611_, 0, v_cmp_2607_);
v___x_2612_ = lean_apply_4(v_inst_2608_, lean_box(0), v_l_2610_, v_t_2609_, v___f_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit(lean_object* v_00_u03b1_2613_, lean_object* v_cmp_2614_, lean_object* v_inst_2615_, lean_object* v_00_u03c1_2616_, lean_object* v_inst_2617_, lean_object* v_t_2618_, lean_object* v_l_2619_){
_start:
{
lean_object* v___f_2620_; lean_object* v___x_2621_; 
v___f_2620_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2620_, 0, v_cmp_2614_);
v___x_2621_ = lean_apply_4(v_inst_2617_, lean_box(0), v_l_2619_, v_t_2618_, v___f_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_union___redArg(lean_object* v_cmp_2622_, lean_object* v_t_u2081_2623_, lean_object* v_t_u2082_2624_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_2622_, v_t_u2081_2623_, v_t_u2082_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_union(lean_object* v_00_u03b1_2626_, lean_object* v_00_u03b2_2627_, lean_object* v_cmp_2628_, lean_object* v_inst_2629_, lean_object* v_t_u2081_2630_, lean_object* v_t_u2082_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_2628_, v_t_u2081_2630_, v_t_u2082_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instUnionOfTransCmp___redArg(lean_object* v_cmp_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_union), 6, 4);
lean_closure_set(v___x_2634_, 0, lean_box(0));
lean_closure_set(v___x_2634_, 1, lean_box(0));
lean_closure_set(v___x_2634_, 2, v_cmp_2633_);
lean_closure_set(v___x_2634_, 3, lean_box(0));
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instUnionOfTransCmp(lean_object* v_00_u03b1_2635_, lean_object* v_00_u03b2_2636_, lean_object* v_cmp_2637_, lean_object* v_inst_2638_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_union), 6, 4);
lean_closure_set(v___x_2639_, 0, lean_box(0));
lean_closure_set(v___x_2639_, 1, lean_box(0));
lean_closure_set(v___x_2639_, 2, v_cmp_2637_);
lean_closure_set(v___x_2639_, 3, lean_box(0));
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_inter___redArg(lean_object* v_cmp_2640_, lean_object* v_t_u2081_2641_, lean_object* v_t_u2082_2642_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_2640_, v_t_u2081_2641_, v_t_u2082_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_inter(lean_object* v_00_u03b1_2644_, lean_object* v_00_u03b2_2645_, lean_object* v_cmp_2646_, lean_object* v_inst_2647_, lean_object* v_t_u2081_2648_, lean_object* v_t_u2082_2649_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_2646_, v_t_u2081_2648_, v_t_u2082_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInterOfTransCmp___redArg(lean_object* v_cmp_2651_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_inter), 6, 4);
lean_closure_set(v___x_2652_, 0, lean_box(0));
lean_closure_set(v___x_2652_, 1, lean_box(0));
lean_closure_set(v___x_2652_, 2, v_cmp_2651_);
lean_closure_set(v___x_2652_, 3, lean_box(0));
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInterOfTransCmp(lean_object* v_00_u03b1_2653_, lean_object* v_00_u03b2_2654_, lean_object* v_cmp_2655_, lean_object* v_inst_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_inter), 6, 4);
lean_closure_set(v___x_2657_, 0, lean_box(0));
lean_closure_set(v___x_2657_, 1, lean_box(0));
lean_closure_set(v___x_2657_, 2, v_cmp_2655_);
lean_closure_set(v___x_2657_, 3, lean_box(0));
return v___x_2657_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(lean_object* v_cmp_2658_, lean_object* v_inst_2659_, lean_object* v_m_u2081_2660_, lean_object* v_m_u2082_2661_){
_start:
{
uint8_t v___x_2662_; 
v___x_2662_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2658_, v_inst_2659_, v_m_u2081_2660_, v_m_u2082_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_2663_, lean_object* v_inst_2664_, lean_object* v_m_u2081_2665_, lean_object* v_m_u2082_2666_){
_start:
{
uint8_t v_res_2667_; lean_object* v_r_2668_; 
v_res_2667_ = l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(v_cmp_2663_, v_inst_2664_, v_m_u2081_2665_, v_m_u2082_2666_);
v_r_2668_ = lean_box(v_res_2667_);
return v_r_2668_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp___redArg(lean_object* v_cmp_2669_, lean_object* v_inst_2670_){
_start:
{
lean_object* v___f_2671_; 
v___f_2671_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2671_, 0, v_cmp_2669_);
lean_closure_set(v___f_2671_, 1, v_inst_2670_);
return v___f_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp(lean_object* v_00_u03b1_2672_, lean_object* v_00_u03b2_2673_, lean_object* v_cmp_2674_, lean_object* v_inst_2675_, lean_object* v_inst_2676_){
_start:
{
lean_object* v___f_2677_; 
v___f_2677_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2677_, 0, v_cmp_2674_);
lean_closure_set(v___f_2677_, 1, v_inst_2676_);
return v___f_2677_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_diff___redArg(lean_object* v_cmp_2678_, lean_object* v_t_u2081_2679_, lean_object* v_t_u2082_2680_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2678_, v_t_u2081_2679_, v_t_u2082_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_diff(lean_object* v_00_u03b1_2682_, lean_object* v_00_u03b2_2683_, lean_object* v_cmp_2684_, lean_object* v_inst_2685_, lean_object* v_t_u2081_2686_, lean_object* v_t_u2082_2687_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2684_, v_t_u2081_2686_, v_t_u2082_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSDiffOfTransCmp___redArg(lean_object* v_cmp_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_diff), 6, 4);
lean_closure_set(v___x_2690_, 0, lean_box(0));
lean_closure_set(v___x_2690_, 1, lean_box(0));
lean_closure_set(v___x_2690_, 2, v_cmp_2689_);
lean_closure_set(v___x_2690_, 3, lean_box(0));
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSDiffOfTransCmp(lean_object* v_00_u03b1_2691_, lean_object* v_00_u03b2_2692_, lean_object* v_cmp_2693_, lean_object* v_inst_2694_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_diff), 6, 4);
lean_closure_set(v___x_2695_, 0, lean_box(0));
lean_closure_set(v___x_2695_, 1, lean_box(0));
lean_closure_set(v___x_2695_, 2, v_cmp_2693_);
lean_closure_set(v___x_2695_, 3, lean_box(0));
return v___x_2695_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(lean_object* v_cmp_2696_, lean_object* v_inst_2697_, lean_object* v_x_2698_, lean_object* v_x_2699_){
_start:
{
uint8_t v___x_2700_; 
v___x_2700_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2696_, v_inst_2697_, v_x_2698_, v_x_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_2701_, lean_object* v_inst_2702_, lean_object* v_x_2703_, lean_object* v_x_2704_){
_start:
{
uint8_t v_res_2705_; lean_object* v_r_2706_; 
v_res_2705_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(v_cmp_2701_, v_inst_2702_, v_x_2703_, v_x_2704_);
v_r_2706_ = lean_box(v_res_2705_);
return v_r_2706_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(lean_object* v_00_u03b1_2707_, lean_object* v_00_u03b2_2708_, lean_object* v_cmp_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_x_2714_, lean_object* v_x_2715_){
_start:
{
uint8_t v___x_2716_; 
v___x_2716_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2709_, v_inst_2712_, v_x_2714_, v_x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_2717_, lean_object* v_00_u03b2_2718_, lean_object* v_cmp_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_x_2724_, lean_object* v_x_2725_){
_start:
{
uint8_t v_res_2726_; lean_object* v_r_2727_; 
v_res_2726_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(v_00_u03b1_2717_, v_00_u03b2_2718_, v_cmp_2719_, v_inst_2720_, v_inst_2721_, v_inst_2722_, v_inst_2723_, v_x_2724_, v_x_2725_);
v_r_2727_ = lean_box(v_res_2726_);
return v_r_2727_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_2728_, lean_object* v_a_2729_, lean_object* v_____s_2730_){
_start:
{
lean_object* v_acc_2731_; lean_object* v___x_2732_; 
v_acc_2731_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2728_, v_a_2729_, v_____s_2730_);
v___x_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2732_, 0, v_acc_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany___redArg(lean_object* v_cmp_2733_, lean_object* v_inst_2734_, lean_object* v_t_2735_, lean_object* v_l_2736_){
_start:
{
lean_object* v___f_2737_; lean_object* v___x_2738_; 
v___f_2737_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2737_, 0, v_cmp_2733_);
v___x_2738_ = lean_apply_4(v_inst_2734_, lean_box(0), v_l_2736_, v_t_2735_, v___f_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany(lean_object* v_00_u03b1_2739_, lean_object* v_00_u03b2_2740_, lean_object* v_cmp_2741_, lean_object* v_inst_2742_, lean_object* v_00_u03c1_2743_, lean_object* v_inst_2744_, lean_object* v_t_2745_, lean_object* v_l_2746_){
_start:
{
lean_object* v___f_2747_; lean_object* v___x_2748_; 
v___f_2747_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2747_, 0, v_cmp_2741_);
v___x_2748_ = lean_apply_4(v_inst_2744_, lean_box(0), v_l_2746_, v_t_2745_, v___f_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_2752_, lean_object* v___x_2753_, lean_object* v_m_2754_, lean_object* v_prec_2755_){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2756_ = ((lean_object*)(l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_2757_ = lean_box(0);
v___x_2758_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2759_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2758_, v___f_2752_, v___x_2757_, v_m_2754_);
v___x_2760_ = l_List_repr___redArg(v___x_2753_, v___x_2759_);
v___x_2761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2756_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = l_Repr_addAppParen(v___x_2761_, v_prec_2755_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_2763_, lean_object* v___x_2764_, lean_object* v_m_2765_, lean_object* v_prec_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(v___f_2763_, v___x_2764_, v_m_2765_, v_prec_2766_);
lean_dec(v_prec_2766_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg(lean_object* v_inst_2768_, lean_object* v_inst_2769_){
_start:
{
lean_object* v___f_2770_; lean_object* v___f_2771_; lean_object* v___x_2772_; lean_object* v___f_2773_; 
v___f_2770_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___f_2771_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2771_, 0, v_inst_2769_);
v___x_2772_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2772_, 0, lean_box(0));
lean_closure_set(v___x_2772_, 1, lean_box(0));
lean_closure_set(v___x_2772_, 2, v_inst_2768_);
lean_closure_set(v___x_2772_, 3, v___f_2771_);
v___f_2773_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2773_, 0, v___f_2770_);
lean_closure_set(v___f_2773_, 1, v___x_2772_);
return v___f_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp(lean_object* v_00_u03b1_2774_, lean_object* v_00_u03b2_2775_, lean_object* v_cmp_2776_, lean_object* v_inst_2777_, lean_object* v_inst_2778_, lean_object* v_inst_2779_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg(v_inst_2778_, v_inst_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_2781_, lean_object* v_00_u03b2_2782_, lean_object* v_cmp_2783_, lean_object* v_inst_2784_, lean_object* v_inst_2785_, lean_object* v_inst_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Std_ExtTreeMap_instReprOfTransCmp(v_00_u03b1_2781_, v_00_u03b2_2782_, v_cmp_2783_, v_inst_2784_, v_inst_2785_, v_inst_2786_);
lean_dec_ref(v_cmp_2783_);
return v_res_2787_;
}
}
lean_object* runtime_initialize_Std_Data_ExtDTreeMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ExtTreeMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
