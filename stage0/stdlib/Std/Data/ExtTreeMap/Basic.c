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
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__15 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__15_value;
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__16 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__16_value;
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__15_value),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__17));
v___x_45_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__13, &l_Std_ExtTreeMap___auto__1___closed__13_once, _init_l_Std_ExtTreeMap___auto__1___closed__13);
v___x_46_ = lean_array_push(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__18, &l_Std_ExtTreeMap___auto__1___closed__18_once, _init_l_Std_ExtTreeMap___auto__1___closed__18);
v___x_48_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__11));
v___x_49_ = lean_box(2);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__19, &l_Std_ExtTreeMap___auto__1___closed__19_once, _init_l_Std_ExtTreeMap___auto__1___closed__19);
v___x_52_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__5));
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__21(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__20, &l_Std_ExtTreeMap___auto__1___closed__20_once, _init_l_Std_ExtTreeMap___auto__1___closed__20);
v___x_55_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__9));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__22(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__21, &l_Std_ExtTreeMap___auto__1___closed__21_once, _init_l_Std_ExtTreeMap___auto__1___closed__21);
v___x_59_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__5));
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__23(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__22, &l_Std_ExtTreeMap___auto__1___closed__22_once, _init_l_Std_ExtTreeMap___auto__1___closed__22);
v___x_62_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__7));
v___x_63_ = lean_box(2);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__24(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__23, &l_Std_ExtTreeMap___auto__1___closed__23_once, _init_l_Std_ExtTreeMap___auto__1___closed__23);
v___x_66_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__25(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__24, &l_Std_ExtTreeMap___auto__1___closed__24_once, _init_l_Std_ExtTreeMap___auto__1___closed__24);
v___x_69_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__4));
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__25, &l_Std_ExtTreeMap___auto__1___closed__25_once, _init_l_Std_ExtTreeMap___auto__1___closed__25);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(1);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___redArg___boxed(lean_object* v___dummy_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_ExtTreeMap_empty___redArg();
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_cmp_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(1);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___boxed(lean_object* v_00_u03b1_81_, lean_object* v_00_u03b2_82_, lean_object* v_cmp_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_ExtTreeMap_empty(v_00_u03b1_81_, v_00_u03b2_82_, v_cmp_83_);
lean_dec_ref(v_cmp_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(1);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_ExtTreeMap_instEmptyCollection___redArg();
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b2_90_, lean_object* v_cmp_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(1);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_cmp_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_ExtTreeMap_instEmptyCollection(v_00_u03b1_93_, v_00_u03b2_94_, v_cmp_95_);
lean_dec_ref(v_cmp_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_box(1);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited___redArg___boxed(lean_object* v___dummy_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_ExtTreeMap_instInhabited___redArg();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_cmp_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(1);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited___boxed(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b2_106_, lean_object* v_cmp_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_ExtTreeMap_instInhabited(v_00_u03b1_105_, v_00_u03b2_106_, v_cmp_107_);
lean_dec_ref(v_cmp_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insert___redArg(lean_object* v_cmp_109_, lean_object* v_l_110_, lean_object* v_a_111_, lean_object* v_b_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_109_, v_a_111_, v_b_112_, v_l_110_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insert(lean_object* v_00_u03b1_114_, lean_object* v_00_u03b2_115_, lean_object* v_cmp_116_, lean_object* v_inst_117_, lean_object* v_l_118_, lean_object* v_a_119_, lean_object* v_b_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_116_, v_a_119_, v_b_120_, v_l_118_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0(lean_object* v_cmp_122_, lean_object* v_e_123_){
_start:
{
lean_object* v_fst_124_; lean_object* v_snd_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_fst_124_ = lean_ctor_get(v_e_123_, 0);
lean_inc(v_fst_124_);
v_snd_125_ = lean_ctor_get(v_e_123_, 1);
lean_inc(v_snd_125_);
lean_dec_ref(v_e_123_);
v___x_126_ = lean_box(1);
v___x_127_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_122_, v_fst_124_, v_snd_125_, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg(lean_object* v_cmp_128_){
_start:
{
lean_object* v___f_129_; 
v___f_129_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_129_, 0, v_cmp_128_);
return v___f_129_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp(lean_object* v_00_u03b1_130_, lean_object* v_00_u03b2_131_, lean_object* v_cmp_132_, lean_object* v_inst_133_){
_start:
{
lean_object* v___f_134_; 
v___f_134_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_134_, 0, v_cmp_132_);
return v___f_134_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0(lean_object* v_cmp_135_, lean_object* v_e_136_, lean_object* v_s_137_){
_start:
{
lean_object* v_fst_138_; lean_object* v_snd_139_; lean_object* v___x_140_; 
v_fst_138_ = lean_ctor_get(v_e_136_, 0);
lean_inc(v_fst_138_);
v_snd_139_ = lean_ctor_get(v_e_136_, 1);
lean_inc(v_snd_139_);
lean_dec_ref(v_e_136_);
v___x_140_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_135_, v_fst_138_, v_snd_139_, v_s_137_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg(lean_object* v_cmp_141_){
_start:
{
lean_object* v___f_142_; 
v___f_142_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_142_, 0, v_cmp_141_);
return v___f_142_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp(lean_object* v_00_u03b1_143_, lean_object* v_00_u03b2_144_, lean_object* v_cmp_145_, lean_object* v_inst_146_){
_start:
{
lean_object* v___f_147_; 
v___f_147_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_147_, 0, v_cmp_145_);
return v___f_147_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertIfNew___redArg(lean_object* v_cmp_148_, lean_object* v_t_149_, lean_object* v_a_150_, lean_object* v_b_151_){
_start:
{
uint8_t v___x_152_; 
lean_inc(v_t_149_);
lean_inc(v_a_150_);
lean_inc_ref(v_cmp_148_);
v___x_152_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_148_, v_a_150_, v_t_149_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
v___x_153_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_148_, v_a_150_, v_b_151_, v_t_149_);
return v___x_153_;
}
else
{
lean_dec(v_b_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_cmp_148_);
return v_t_149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertIfNew(lean_object* v_00_u03b1_154_, lean_object* v_00_u03b2_155_, lean_object* v_cmp_156_, lean_object* v_inst_157_, lean_object* v_t_158_, lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
uint8_t v___x_161_; 
lean_inc(v_t_158_);
lean_inc(v_a_159_);
lean_inc_ref(v_cmp_156_);
v___x_161_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_156_, v_a_159_, v_t_158_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
v___x_162_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_156_, v_a_159_, v_b_160_, v_t_158_);
return v___x_162_;
}
else
{
lean_dec(v_b_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_cmp_156_);
return v_t_158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsert___redArg(lean_object* v_cmp_163_, lean_object* v_t_164_, lean_object* v_a_165_, lean_object* v_b_166_){
_start:
{
lean_object* v_sz_167_; lean_object* v_m_168_; lean_object* v___y_170_; 
v_sz_167_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_164_);
v_m_168_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_163_, v_a_165_, v_b_166_, v_t_164_);
if (lean_obj_tag(v_m_168_) == 0)
{
lean_object* v_size_174_; 
v_size_174_ = lean_ctor_get(v_m_168_, 0);
lean_inc(v_size_174_);
v___y_170_ = v_size_174_;
goto v___jp_169_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___y_170_ = v___x_175_;
goto v___jp_169_;
}
v___jp_169_:
{
uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_nat_dec_eq(v_sz_167_, v___y_170_);
lean_dec(v___y_170_);
lean_dec(v_sz_167_);
v___x_172_ = lean_box(v___x_171_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v_m_168_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsert(lean_object* v_00_u03b1_176_, lean_object* v_00_u03b2_177_, lean_object* v_cmp_178_, lean_object* v_inst_179_, lean_object* v_t_180_, lean_object* v_a_181_, lean_object* v_b_182_){
_start:
{
lean_object* v_sz_183_; lean_object* v_m_184_; lean_object* v___y_186_; 
v_sz_183_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_180_);
v_m_184_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_178_, v_a_181_, v_b_182_, v_t_180_);
if (lean_obj_tag(v_m_184_) == 0)
{
lean_object* v_size_190_; 
v_size_190_ = lean_ctor_get(v_m_184_, 0);
lean_inc(v_size_190_);
v___y_186_ = v_size_190_;
goto v___jp_185_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v___y_186_ = v___x_191_;
goto v___jp_185_;
}
v___jp_185_:
{
uint8_t v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_nat_dec_eq(v_sz_183_, v___y_186_);
lean_dec(v___y_186_);
lean_dec(v_sz_183_);
v___x_188_ = lean_box(v___x_187_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_m_184_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_192_, lean_object* v_t_193_, lean_object* v_a_194_, lean_object* v_b_195_){
_start:
{
uint8_t v___x_196_; 
lean_inc(v_t_193_);
lean_inc(v_a_194_);
lean_inc_ref(v_cmp_192_);
v___x_196_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_192_, v_a_194_, v_t_193_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_192_, v_a_194_, v_b_195_, v_t_193_);
v___x_198_ = lean_box(v___x_196_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
return v___x_199_;
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v_b_195_);
lean_dec(v_a_194_);
lean_dec_ref(v_cmp_192_);
v___x_200_ = lean_box(v___x_196_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v_t_193_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_202_, lean_object* v_00_u03b2_203_, lean_object* v_cmp_204_, lean_object* v_inst_205_, lean_object* v_t_206_, lean_object* v_a_207_, lean_object* v_b_208_){
_start:
{
uint8_t v___x_209_; 
lean_inc(v_t_206_);
lean_inc(v_a_207_);
lean_inc_ref(v_cmp_204_);
v___x_209_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_204_, v_a_207_, v_t_206_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_204_, v_a_207_, v_b_208_, v_t_206_);
v___x_211_ = lean_box(v___x_209_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v_b_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_cmp_204_);
v___x_213_ = lean_box(v___x_209_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v_t_206_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_215_, lean_object* v_t_216_, lean_object* v_a_217_, lean_object* v_b_218_){
_start:
{
lean_object* v___x_219_; 
lean_inc(v_a_217_);
lean_inc(v_t_216_);
lean_inc_ref(v_cmp_215_);
v___x_219_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_215_, v_t_216_, v_a_217_);
if (lean_obj_tag(v___x_219_) == 0)
{
uint8_t v___x_220_; 
lean_inc(v_t_216_);
lean_inc(v_a_217_);
lean_inc_ref(v_cmp_215_);
v___x_220_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_215_, v_a_217_, v_t_216_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_215_, v_a_217_, v_b_218_, v_t_216_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_219_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; 
lean_dec(v_b_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_cmp_215_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_219_);
lean_ctor_set(v___x_223_, 1, v_t_216_);
return v___x_223_;
}
}
else
{
lean_object* v___x_224_; 
lean_dec(v_b_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_cmp_215_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_219_);
lean_ctor_set(v___x_224_, 1, v_t_216_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_225_, lean_object* v_00_u03b2_226_, lean_object* v_cmp_227_, lean_object* v_inst_228_, lean_object* v_t_229_, lean_object* v_a_230_, lean_object* v_b_231_){
_start:
{
lean_object* v___x_232_; 
lean_inc(v_a_230_);
lean_inc(v_t_229_);
lean_inc_ref(v_cmp_227_);
v___x_232_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_227_, v_t_229_, v_a_230_);
if (lean_obj_tag(v___x_232_) == 0)
{
uint8_t v___x_233_; 
lean_inc(v_t_229_);
lean_inc(v_a_230_);
lean_inc_ref(v_cmp_227_);
v___x_233_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_227_, v_a_230_, v_t_229_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_227_, v_a_230_, v_b_231_, v_t_229_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_232_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
return v___x_235_;
}
else
{
lean_object* v___x_236_; 
lean_dec(v_b_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_cmp_227_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_232_);
lean_ctor_set(v___x_236_, 1, v_t_229_);
return v___x_236_;
}
}
else
{
lean_object* v___x_237_; 
lean_dec(v_b_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_cmp_227_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_232_);
lean_ctor_set(v___x_237_, 1, v_t_229_);
return v___x_237_;
}
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_contains___redArg(lean_object* v_cmp_238_, lean_object* v_l_239_, lean_object* v_a_240_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_238_, v_a_240_, v_l_239_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_contains___redArg___boxed(lean_object* v_cmp_242_, lean_object* v_l_243_, lean_object* v_a_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Std_ExtTreeMap_contains___redArg(v_cmp_242_, v_l_243_, v_a_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_contains(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_cmp_249_, lean_object* v_inst_250_, lean_object* v_l_251_, lean_object* v_a_252_){
_start:
{
uint8_t v___x_253_; 
v___x_253_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_249_, v_a_252_, v_l_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_contains___boxed(lean_object* v_00_u03b1_254_, lean_object* v_00_u03b2_255_, lean_object* v_cmp_256_, lean_object* v_inst_257_, lean_object* v_l_258_, lean_object* v_a_259_){
_start:
{
uint8_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l_Std_ExtTreeMap_contains(v_00_u03b1_254_, v_00_u03b2_255_, v_cmp_256_, v_inst_257_, v_l_258_, v_a_259_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg(){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg___boxed(lean_object* v___dummy_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg();
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b2_267_, lean_object* v_cmp_268_, lean_object* v_inst_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = lean_box(0);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___boxed(lean_object* v_00_u03b1_271_, lean_object* v_00_u03b2_272_, lean_object* v_cmp_273_, lean_object* v_inst_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_ExtTreeMap_instMembershipOfTransCmp(v_00_u03b1_271_, v_00_u03b2_272_, v_cmp_273_, v_inst_274_);
lean_dec_ref(v_cmp_273_);
return v_res_275_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableMem___redArg(lean_object* v_cmp_276_, lean_object* v_m_277_, lean_object* v_a_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_276_, v_a_278_, v_m_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_280_, lean_object* v_m_281_, lean_object* v_a_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l_Std_ExtTreeMap_instDecidableMem___redArg(v_cmp_280_, v_m_281_, v_a_282_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableMem(lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_, lean_object* v_cmp_287_, lean_object* v_inst_288_, lean_object* v_m_289_, lean_object* v_a_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_287_, v_a_290_, v_m_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_292_, lean_object* v_00_u03b2_293_, lean_object* v_cmp_294_, lean_object* v_inst_295_, lean_object* v_m_296_, lean_object* v_a_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Std_ExtTreeMap_instDecidableMem(v_00_u03b1_292_, v_00_u03b2_293_, v_cmp_294_, v_inst_295_, v_m_296_, v_a_297_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___redArg(lean_object* v_t_300_){
_start:
{
if (lean_obj_tag(v_t_300_) == 0)
{
lean_object* v_size_301_; 
v_size_301_ = lean_ctor_get(v_t_300_, 0);
lean_inc(v_size_301_);
return v_size_301_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = lean_unsigned_to_nat(0u);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___redArg___boxed(lean_object* v_t_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_ExtTreeMap_size___redArg(v_t_303_);
lean_dec(v_t_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size(lean_object* v_00_u03b1_305_, lean_object* v_00_u03b2_306_, lean_object* v_cmp_307_, lean_object* v_t_308_){
_start:
{
if (lean_obj_tag(v_t_308_) == 0)
{
lean_object* v_size_309_; 
v_size_309_ = lean_ctor_get(v_t_308_, 0);
lean_inc(v_size_309_);
return v_size_309_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_unsigned_to_nat(0u);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___boxed(lean_object* v_00_u03b1_311_, lean_object* v_00_u03b2_312_, lean_object* v_cmp_313_, lean_object* v_t_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_ExtTreeMap_size(v_00_u03b1_311_, v_00_u03b2_312_, v_cmp_313_, v_t_314_);
lean_dec(v_t_314_);
lean_dec_ref(v_cmp_313_);
return v_res_315_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_isEmpty___redArg(lean_object* v_t_316_){
_start:
{
if (lean_obj_tag(v_t_316_) == 0)
{
uint8_t v___x_317_; 
v___x_317_ = 0;
return v___x_317_;
}
else
{
uint8_t v___x_318_; 
v___x_318_ = 1;
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_isEmpty___redArg___boxed(lean_object* v_t_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Std_ExtTreeMap_isEmpty___redArg(v_t_319_);
lean_dec(v_t_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_isEmpty(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_cmp_324_, lean_object* v_t_325_){
_start:
{
if (lean_obj_tag(v_t_325_) == 0)
{
uint8_t v___x_326_; 
v___x_326_ = 0;
return v___x_326_;
}
else
{
uint8_t v___x_327_; 
v___x_327_ = 1;
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_328_, lean_object* v_00_u03b2_329_, lean_object* v_cmp_330_, lean_object* v_t_331_){
_start:
{
uint8_t v_res_332_; lean_object* v_r_333_; 
v_res_332_ = l_Std_ExtTreeMap_isEmpty(v_00_u03b1_328_, v_00_u03b2_329_, v_cmp_330_, v_t_331_);
lean_dec(v_t_331_);
lean_dec_ref(v_cmp_330_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_erase___redArg(lean_object* v_cmp_334_, lean_object* v_t_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_334_, v_a_336_, v_t_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_erase(lean_object* v_00_u03b1_338_, lean_object* v_00_u03b2_339_, lean_object* v_cmp_340_, lean_object* v_inst_341_, lean_object* v_t_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_340_, v_a_343_, v_t_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x3f___redArg(lean_object* v_cmp_345_, lean_object* v_t_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_345_, v_t_346_, v_a_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x3f(lean_object* v_00_u03b1_349_, lean_object* v_00_u03b2_350_, lean_object* v_cmp_351_, lean_object* v_inst_352_, lean_object* v_t_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_351_, v_t_353_, v_a_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get___redArg(lean_object* v_cmp_356_, lean_object* v_t_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_356_, v_t_357_, v_a_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get(lean_object* v_00_u03b1_360_, lean_object* v_00_u03b2_361_, lean_object* v_cmp_362_, lean_object* v_inst_363_, lean_object* v_t_364_, lean_object* v_a_365_, lean_object* v_h_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_362_, v_t_364_, v_a_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___redArg(lean_object* v_cmp_368_, lean_object* v_inst_369_, lean_object* v_t_370_, lean_object* v_a_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_368_, v_inst_369_, v_t_370_, v_a_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___redArg___boxed(lean_object* v_cmp_373_, lean_object* v_inst_374_, lean_object* v_t_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Std_ExtTreeMap_get_x21___redArg(v_cmp_373_, v_inst_374_, v_t_375_, v_a_376_);
lean_dec(v_inst_374_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21(lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_, lean_object* v_cmp_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_t_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_380_, v_inst_382_, v_t_383_, v_a_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___boxed(lean_object* v_00_u03b1_386_, lean_object* v_00_u03b2_387_, lean_object* v_cmp_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_t_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_ExtTreeMap_get_x21(v_00_u03b1_386_, v_00_u03b2_387_, v_cmp_388_, v_inst_389_, v_inst_390_, v_t_391_, v_a_392_);
lean_dec(v_inst_390_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg(lean_object* v_cmp_394_, lean_object* v_t_395_, lean_object* v_a_396_, lean_object* v_fallback_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_394_, v_t_395_, v_a_396_, v_fallback_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg___boxed(lean_object* v_cmp_399_, lean_object* v_t_400_, lean_object* v_a_401_, lean_object* v_fallback_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_ExtTreeMap_getD___redArg(v_cmp_399_, v_t_400_, v_a_401_, v_fallback_402_);
lean_dec(v_fallback_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD(lean_object* v_00_u03b1_404_, lean_object* v_00_u03b2_405_, lean_object* v_cmp_406_, lean_object* v_inst_407_, lean_object* v_t_408_, lean_object* v_a_409_, lean_object* v_fallback_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_406_, v_t_408_, v_a_409_, v_fallback_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___boxed(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_cmp_414_, lean_object* v_inst_415_, lean_object* v_t_416_, lean_object* v_a_417_, lean_object* v_fallback_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_ExtTreeMap_getD(v_00_u03b1_412_, v_00_u03b2_413_, v_cmp_414_, v_inst_415_, v_t_416_, v_a_417_, v_fallback_418_);
lean_dec(v_fallback_418_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_cmp_420_, lean_object* v_m_421_, lean_object* v_a_422_, lean_object* v_h_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_420_, v_m_421_, v_a_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_cmp_425_, lean_object* v_m_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_425_, v_m_426_, v_a_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_cmp_429_, lean_object* v_inst_430_, lean_object* v_m_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_429_, v_inst_430_, v_m_431_, v_a_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_cmp_434_, lean_object* v_inst_435_, lean_object* v_m_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(v_cmp_434_, v_inst_435_, v_m_436_, v_a_437_);
lean_dec(v_inst_435_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(lean_object* v_cmp_439_){
_start:
{
lean_object* v___f_440_; lean_object* v___f_441_; lean_object* v___f_442_; lean_object* v___x_443_; 
lean_inc_ref_n(v_cmp_439_, 2);
v___f_440_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0), 4, 1);
lean_closure_set(v___f_440_, 0, v_cmp_439_);
v___f_441_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1), 3, 1);
lean_closure_set(v___f_441_, 0, v_cmp_439_);
v___f_442_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_442_, 0, v_cmp_439_);
v___x_443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_443_, 0, v___f_440_);
lean_ctor_set(v___x_443_, 1, v___f_441_);
lean_ctor_set(v___x_443_, 2, v___f_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem(lean_object* v_00_u03b1_444_, lean_object* v_00_u03b2_445_, lean_object* v_cmp_446_, lean_object* v_inst_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(v_cmp_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f___redArg(lean_object* v_cmp_449_, lean_object* v_t_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_449_, v_t_450_, v_a_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f(lean_object* v_00_u03b1_453_, lean_object* v_00_u03b2_454_, lean_object* v_cmp_455_, lean_object* v_inst_456_, lean_object* v_t_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_455_, v_t_457_, v_a_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey___redArg(lean_object* v_cmp_460_, lean_object* v_t_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_460_, v_t_461_, v_a_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_cmp_466_, lean_object* v_inst_467_, lean_object* v_t_468_, lean_object* v_a_469_, lean_object* v_h_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_466_, v_t_468_, v_a_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___redArg(lean_object* v_cmp_472_, lean_object* v_inst_473_, lean_object* v_t_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_472_, v_t_474_, v_a_475_, v_inst_473_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___redArg___boxed(lean_object* v_cmp_477_, lean_object* v_inst_478_, lean_object* v_t_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Std_ExtTreeMap_getKey_x21___redArg(v_cmp_477_, v_inst_478_, v_t_479_, v_a_480_);
lean_dec(v_inst_478_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21(lean_object* v_00_u03b1_482_, lean_object* v_00_u03b2_483_, lean_object* v_cmp_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_t_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_484_, v_t_487_, v_a_488_, v_inst_486_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___boxed(lean_object* v_00_u03b1_490_, lean_object* v_00_u03b2_491_, lean_object* v_cmp_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_t_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_ExtTreeMap_getKey_x21(v_00_u03b1_490_, v_00_u03b2_491_, v_cmp_492_, v_inst_493_, v_inst_494_, v_t_495_, v_a_496_);
lean_dec(v_inst_494_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___redArg(lean_object* v_cmp_498_, lean_object* v_t_499_, lean_object* v_a_500_, lean_object* v_fallback_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_498_, v_t_499_, v_a_500_, v_fallback_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_503_, lean_object* v_t_504_, lean_object* v_a_505_, lean_object* v_fallback_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_ExtTreeMap_getKeyD___redArg(v_cmp_503_, v_t_504_, v_a_505_, v_fallback_506_);
lean_dec(v_fallback_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_, lean_object* v_cmp_510_, lean_object* v_inst_511_, lean_object* v_t_512_, lean_object* v_a_513_, lean_object* v_fallback_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_510_, v_t_512_, v_a_513_, v_fallback_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_516_, lean_object* v_00_u03b2_517_, lean_object* v_cmp_518_, lean_object* v_inst_519_, lean_object* v_t_520_, lean_object* v_a_521_, lean_object* v_fallback_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_ExtTreeMap_getKeyD(v_00_u03b1_516_, v_00_u03b2_517_, v_cmp_518_, v_inst_519_, v_t_520_, v_a_521_, v_fallback_522_);
lean_dec(v_fallback_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___redArg(lean_object* v_t_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_ExtTreeMap_minEntry_x3f___redArg(v_t_526_);
lean_dec(v_t_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f(lean_object* v_00_u03b1_528_, lean_object* v_00_u03b2_529_, lean_object* v_cmp_530_, lean_object* v_inst_531_, lean_object* v_t_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_534_, lean_object* v_00_u03b2_535_, lean_object* v_cmp_536_, lean_object* v_inst_537_, lean_object* v_t_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Std_ExtTreeMap_minEntry_x3f(v_00_u03b1_534_, v_00_u03b2_535_, v_cmp_536_, v_inst_537_, v_t_538_);
lean_dec(v_t_538_);
lean_dec_ref(v_cmp_536_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___redArg(lean_object* v_t_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___redArg___boxed(lean_object* v_t_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_ExtTreeMap_minEntry___redArg(v_t_542_);
lean_dec(v_t_542_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry(lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_, lean_object* v_cmp_546_, lean_object* v_inst_547_, lean_object* v_t_548_, lean_object* v_h_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___boxed(lean_object* v_00_u03b1_551_, lean_object* v_00_u03b2_552_, lean_object* v_cmp_553_, lean_object* v_inst_554_, lean_object* v_t_555_, lean_object* v_h_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_ExtTreeMap_minEntry(v_00_u03b1_551_, v_00_u03b2_552_, v_cmp_553_, v_inst_554_, v_t_555_, v_h_556_);
lean_dec(v_t_555_);
lean_dec_ref(v_cmp_553_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___redArg(lean_object* v_inst_558_, lean_object* v_t_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_558_, v_t_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_561_, lean_object* v_t_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_ExtTreeMap_minEntry_x21___redArg(v_inst_561_, v_t_562_);
lean_dec(v_t_562_);
lean_dec_ref(v_inst_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21(lean_object* v_00_u03b1_564_, lean_object* v_00_u03b2_565_, lean_object* v_cmp_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_t_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_568_, v_t_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_cmp_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_t_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_ExtTreeMap_minEntry_x21(v_00_u03b1_571_, v_00_u03b2_572_, v_cmp_573_, v_inst_574_, v_inst_575_, v_t_576_);
lean_dec(v_t_576_);
lean_dec_ref(v_inst_575_);
lean_dec_ref(v_cmp_573_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___redArg(lean_object* v_t_578_, lean_object* v_fallback_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_578_, v_fallback_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___redArg___boxed(lean_object* v_t_581_, lean_object* v_fallback_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_ExtTreeMap_minEntryD___redArg(v_t_581_, v_fallback_582_);
lean_dec_ref(v_fallback_582_);
lean_dec(v_t_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_cmp_586_, lean_object* v_inst_587_, lean_object* v_t_588_, lean_object* v_fallback_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_588_, v_fallback_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_591_, lean_object* v_00_u03b2_592_, lean_object* v_cmp_593_, lean_object* v_inst_594_, lean_object* v_t_595_, lean_object* v_fallback_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_ExtTreeMap_minEntryD(v_00_u03b1_591_, v_00_u03b2_592_, v_cmp_593_, v_inst_594_, v_t_595_, v_fallback_596_);
lean_dec_ref(v_fallback_596_);
lean_dec(v_t_595_);
lean_dec_ref(v_cmp_593_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___redArg(lean_object* v_t_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_ExtTreeMap_maxEntry_x3f___redArg(v_t_600_);
lean_dec(v_t_600_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_602_, lean_object* v_00_u03b2_603_, lean_object* v_cmp_604_, lean_object* v_inst_605_, lean_object* v_t_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_cmp_610_, lean_object* v_inst_611_, lean_object* v_t_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_ExtTreeMap_maxEntry_x3f(v_00_u03b1_608_, v_00_u03b2_609_, v_cmp_610_, v_inst_611_, v_t_612_);
lean_dec(v_t_612_);
lean_dec_ref(v_cmp_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___redArg(lean_object* v_t_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___redArg___boxed(lean_object* v_t_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_ExtTreeMap_maxEntry___redArg(v_t_616_);
lean_dec(v_t_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry(lean_object* v_00_u03b1_618_, lean_object* v_00_u03b2_619_, lean_object* v_cmp_620_, lean_object* v_inst_621_, lean_object* v_t_622_, lean_object* v_h_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_625_, lean_object* v_00_u03b2_626_, lean_object* v_cmp_627_, lean_object* v_inst_628_, lean_object* v_t_629_, lean_object* v_h_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std_ExtTreeMap_maxEntry(v_00_u03b1_625_, v_00_u03b2_626_, v_cmp_627_, v_inst_628_, v_t_629_, v_h_630_);
lean_dec(v_t_629_);
lean_dec_ref(v_cmp_627_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___redArg(lean_object* v_inst_632_, lean_object* v_t_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_632_, v_t_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_635_, lean_object* v_t_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Std_ExtTreeMap_maxEntry_x21___redArg(v_inst_635_, v_t_636_);
lean_dec(v_t_636_);
lean_dec_ref(v_inst_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21(lean_object* v_00_u03b1_638_, lean_object* v_00_u03b2_639_, lean_object* v_cmp_640_, lean_object* v_inst_641_, lean_object* v_inst_642_, lean_object* v_t_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_642_, v_t_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_645_, lean_object* v_00_u03b2_646_, lean_object* v_cmp_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_t_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_ExtTreeMap_maxEntry_x21(v_00_u03b1_645_, v_00_u03b2_646_, v_cmp_647_, v_inst_648_, v_inst_649_, v_t_650_);
lean_dec(v_t_650_);
lean_dec_ref(v_inst_649_);
lean_dec_ref(v_cmp_647_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___redArg(lean_object* v_t_652_, lean_object* v_fallback_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_652_, v_fallback_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_655_, lean_object* v_fallback_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_ExtTreeMap_maxEntryD___redArg(v_t_655_, v_fallback_656_);
lean_dec_ref(v_fallback_656_);
lean_dec(v_t_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD(lean_object* v_00_u03b1_658_, lean_object* v_00_u03b2_659_, lean_object* v_cmp_660_, lean_object* v_inst_661_, lean_object* v_t_662_, lean_object* v_fallback_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_662_, v_fallback_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_665_, lean_object* v_00_u03b2_666_, lean_object* v_cmp_667_, lean_object* v_inst_668_, lean_object* v_t_669_, lean_object* v_fallback_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Std_ExtTreeMap_maxEntryD(v_00_u03b1_665_, v_00_u03b2_666_, v_cmp_667_, v_inst_668_, v_t_669_, v_fallback_670_);
lean_dec_ref(v_fallback_670_);
lean_dec(v_t_669_);
lean_dec_ref(v_cmp_667_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___redArg(lean_object* v_t_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_ExtTreeMap_minKey_x3f___redArg(v_t_674_);
lean_dec(v_t_674_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f(lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_cmp_678_, lean_object* v_inst_679_, lean_object* v_t_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_cmp_684_, lean_object* v_inst_685_, lean_object* v_t_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_ExtTreeMap_minKey_x3f(v_00_u03b1_682_, v_00_u03b2_683_, v_cmp_684_, v_inst_685_, v_t_686_);
lean_dec(v_t_686_);
lean_dec_ref(v_cmp_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___redArg(lean_object* v_t_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___redArg___boxed(lean_object* v_t_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_ExtTreeMap_minKey___redArg(v_t_690_);
lean_dec(v_t_690_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey(lean_object* v_00_u03b1_692_, lean_object* v_00_u03b2_693_, lean_object* v_cmp_694_, lean_object* v_inst_695_, lean_object* v_t_696_, lean_object* v_h_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_696_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___boxed(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_cmp_701_, lean_object* v_inst_702_, lean_object* v_t_703_, lean_object* v_h_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Std_ExtTreeMap_minKey(v_00_u03b1_699_, v_00_u03b2_700_, v_cmp_701_, v_inst_702_, v_t_703_, v_h_704_);
lean_dec(v_t_703_);
lean_dec_ref(v_cmp_701_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___redArg(lean_object* v_inst_706_, lean_object* v_t_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_706_, v_t_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_709_, lean_object* v_t_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_ExtTreeMap_minKey_x21___redArg(v_inst_709_, v_t_710_);
lean_dec(v_t_710_);
lean_dec(v_inst_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21(lean_object* v_00_u03b1_712_, lean_object* v_00_u03b2_713_, lean_object* v_cmp_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_t_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_716_, v_t_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_719_, lean_object* v_00_u03b2_720_, lean_object* v_cmp_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_t_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_ExtTreeMap_minKey_x21(v_00_u03b1_719_, v_00_u03b2_720_, v_cmp_721_, v_inst_722_, v_inst_723_, v_t_724_);
lean_dec(v_t_724_);
lean_dec(v_inst_723_);
lean_dec_ref(v_cmp_721_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___redArg(lean_object* v_t_726_, lean_object* v_fallback_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_726_, v_fallback_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___redArg___boxed(lean_object* v_t_729_, lean_object* v_fallback_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_ExtTreeMap_minKeyD___redArg(v_t_729_, v_fallback_730_);
lean_dec(v_fallback_730_);
lean_dec(v_t_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD(lean_object* v_00_u03b1_732_, lean_object* v_00_u03b2_733_, lean_object* v_cmp_734_, lean_object* v_inst_735_, lean_object* v_t_736_, lean_object* v_fallback_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_736_, v_fallback_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_739_, lean_object* v_00_u03b2_740_, lean_object* v_cmp_741_, lean_object* v_inst_742_, lean_object* v_t_743_, lean_object* v_fallback_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Std_ExtTreeMap_minKeyD(v_00_u03b1_739_, v_00_u03b2_740_, v_cmp_741_, v_inst_742_, v_t_743_, v_fallback_744_);
lean_dec(v_fallback_744_);
lean_dec(v_t_743_);
lean_dec_ref(v_cmp_741_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___redArg(lean_object* v_t_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_ExtTreeMap_maxKey_x3f___redArg(v_t_748_);
lean_dec(v_t_748_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f(lean_object* v_00_u03b1_750_, lean_object* v_00_u03b2_751_, lean_object* v_cmp_752_, lean_object* v_inst_753_, lean_object* v_t_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b2_757_, lean_object* v_cmp_758_, lean_object* v_inst_759_, lean_object* v_t_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Std_ExtTreeMap_maxKey_x3f(v_00_u03b1_756_, v_00_u03b2_757_, v_cmp_758_, v_inst_759_, v_t_760_);
lean_dec(v_t_760_);
lean_dec_ref(v_cmp_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___redArg(lean_object* v_t_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___redArg___boxed(lean_object* v_t_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_ExtTreeMap_maxKey___redArg(v_t_764_);
lean_dec(v_t_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey(lean_object* v_00_u03b1_766_, lean_object* v_00_u03b2_767_, lean_object* v_cmp_768_, lean_object* v_inst_769_, lean_object* v_t_770_, lean_object* v_h_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___boxed(lean_object* v_00_u03b1_773_, lean_object* v_00_u03b2_774_, lean_object* v_cmp_775_, lean_object* v_inst_776_, lean_object* v_t_777_, lean_object* v_h_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_ExtTreeMap_maxKey(v_00_u03b1_773_, v_00_u03b2_774_, v_cmp_775_, v_inst_776_, v_t_777_, v_h_778_);
lean_dec(v_t_777_);
lean_dec_ref(v_cmp_775_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___redArg(lean_object* v_inst_780_, lean_object* v_t_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_780_, v_t_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_783_, lean_object* v_t_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_ExtTreeMap_maxKey_x21___redArg(v_inst_783_, v_t_784_);
lean_dec(v_t_784_);
lean_dec(v_inst_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21(lean_object* v_00_u03b1_786_, lean_object* v_00_u03b2_787_, lean_object* v_cmp_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_t_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_790_, v_t_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_793_, lean_object* v_00_u03b2_794_, lean_object* v_cmp_795_, lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_t_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Std_ExtTreeMap_maxKey_x21(v_00_u03b1_793_, v_00_u03b2_794_, v_cmp_795_, v_inst_796_, v_inst_797_, v_t_798_);
lean_dec(v_t_798_);
lean_dec(v_inst_797_);
lean_dec_ref(v_cmp_795_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___redArg(lean_object* v_t_800_, lean_object* v_fallback_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_800_, v_fallback_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_803_, lean_object* v_fallback_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_ExtTreeMap_maxKeyD___redArg(v_t_803_, v_fallback_804_);
lean_dec(v_fallback_804_);
lean_dec(v_t_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD(lean_object* v_00_u03b1_806_, lean_object* v_00_u03b2_807_, lean_object* v_cmp_808_, lean_object* v_inst_809_, lean_object* v_t_810_, lean_object* v_fallback_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_810_, v_fallback_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_813_, lean_object* v_00_u03b2_814_, lean_object* v_cmp_815_, lean_object* v_inst_816_, lean_object* v_t_817_, lean_object* v_fallback_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_ExtTreeMap_maxKeyD(v_00_u03b1_813_, v_00_u03b2_814_, v_cmp_815_, v_inst_816_, v_t_817_, v_fallback_818_);
lean_dec(v_fallback_818_);
lean_dec(v_t_817_);
lean_dec_ref(v_cmp_815_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_820_, lean_object* v_n_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_820_, v_n_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_823_, lean_object* v_n_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(v_t_823_, v_n_824_);
lean_dec(v_t_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_cmp_828_, lean_object* v_inst_829_, lean_object* v_t_830_, lean_object* v_n_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_830_, v_n_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_833_, lean_object* v_00_u03b2_834_, lean_object* v_cmp_835_, lean_object* v_inst_836_, lean_object* v_t_837_, lean_object* v_n_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_ExtTreeMap_entryAtIdx_x3f(v_00_u03b1_833_, v_00_u03b2_834_, v_cmp_835_, v_inst_836_, v_t_837_, v_n_838_);
lean_dec(v_t_837_);
lean_dec_ref(v_cmp_835_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___redArg(lean_object* v_t_840_, lean_object* v_n_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_840_, v_n_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_843_, lean_object* v_n_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_ExtTreeMap_entryAtIdx___redArg(v_t_843_, v_n_844_);
lean_dec(v_t_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx(lean_object* v_00_u03b1_846_, lean_object* v_00_u03b2_847_, lean_object* v_cmp_848_, lean_object* v_inst_849_, lean_object* v_t_850_, lean_object* v_n_851_, lean_object* v_h_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_850_, v_n_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_854_, lean_object* v_00_u03b2_855_, lean_object* v_cmp_856_, lean_object* v_inst_857_, lean_object* v_t_858_, lean_object* v_n_859_, lean_object* v_h_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_ExtTreeMap_entryAtIdx(v_00_u03b1_854_, v_00_u03b2_855_, v_cmp_856_, v_inst_857_, v_t_858_, v_n_859_, v_h_860_);
lean_dec(v_t_858_);
lean_dec_ref(v_cmp_856_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_862_, lean_object* v_t_863_, lean_object* v_n_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_862_, v_t_863_, v_n_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_866_, lean_object* v_t_867_, lean_object* v_n_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_ExtTreeMap_entryAtIdx_x21___redArg(v_inst_866_, v_t_867_, v_n_868_);
lean_dec(v_t_867_);
lean_dec_ref(v_inst_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_cmp_872_, lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_t_875_, lean_object* v_n_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_874_, v_t_875_, v_n_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_878_, lean_object* v_00_u03b2_879_, lean_object* v_cmp_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_t_883_, lean_object* v_n_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_ExtTreeMap_entryAtIdx_x21(v_00_u03b1_878_, v_00_u03b2_879_, v_cmp_880_, v_inst_881_, v_inst_882_, v_t_883_, v_n_884_);
lean_dec(v_t_883_);
lean_dec_ref(v_inst_882_);
lean_dec_ref(v_cmp_880_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___redArg(lean_object* v_t_886_, lean_object* v_n_887_, lean_object* v_fallback_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_886_, v_n_887_, v_fallback_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_890_, lean_object* v_n_891_, lean_object* v_fallback_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_ExtTreeMap_entryAtIdxD___redArg(v_t_890_, v_n_891_, v_fallback_892_);
lean_dec_ref(v_fallback_892_);
lean_dec(v_t_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD(lean_object* v_00_u03b1_894_, lean_object* v_00_u03b2_895_, lean_object* v_cmp_896_, lean_object* v_inst_897_, lean_object* v_t_898_, lean_object* v_n_899_, lean_object* v_fallback_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_898_, v_n_899_, v_fallback_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_cmp_904_, lean_object* v_inst_905_, lean_object* v_t_906_, lean_object* v_n_907_, lean_object* v_fallback_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_ExtTreeMap_entryAtIdxD(v_00_u03b1_902_, v_00_u03b2_903_, v_cmp_904_, v_inst_905_, v_t_906_, v_n_907_, v_fallback_908_);
lean_dec_ref(v_fallback_908_);
lean_dec(v_t_906_);
lean_dec_ref(v_cmp_904_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_910_, lean_object* v_n_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_910_, v_n_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_913_, lean_object* v_n_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(v_t_913_, v_n_914_);
lean_dec(v_t_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_916_, lean_object* v_00_u03b2_917_, lean_object* v_cmp_918_, lean_object* v_inst_919_, lean_object* v_t_920_, lean_object* v_n_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_920_, v_n_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_923_, lean_object* v_00_u03b2_924_, lean_object* v_cmp_925_, lean_object* v_inst_926_, lean_object* v_t_927_, lean_object* v_n_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_ExtTreeMap_keyAtIdx_x3f(v_00_u03b1_923_, v_00_u03b2_924_, v_cmp_925_, v_inst_926_, v_t_927_, v_n_928_);
lean_dec(v_t_927_);
lean_dec_ref(v_cmp_925_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___redArg(lean_object* v_t_930_, lean_object* v_n_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_930_, v_n_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_933_, lean_object* v_n_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_ExtTreeMap_keyAtIdx___redArg(v_t_933_, v_n_934_);
lean_dec(v_t_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx(lean_object* v_00_u03b1_936_, lean_object* v_00_u03b2_937_, lean_object* v_cmp_938_, lean_object* v_inst_939_, lean_object* v_t_940_, lean_object* v_n_941_, lean_object* v_h_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_940_, v_n_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_944_, lean_object* v_00_u03b2_945_, lean_object* v_cmp_946_, lean_object* v_inst_947_, lean_object* v_t_948_, lean_object* v_n_949_, lean_object* v_h_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_ExtTreeMap_keyAtIdx(v_00_u03b1_944_, v_00_u03b2_945_, v_cmp_946_, v_inst_947_, v_t_948_, v_n_949_, v_h_950_);
lean_dec(v_t_948_);
lean_dec_ref(v_cmp_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_952_, lean_object* v_t_953_, lean_object* v_n_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_952_, v_t_953_, v_n_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_956_, lean_object* v_t_957_, lean_object* v_n_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Std_ExtTreeMap_keyAtIdx_x21___redArg(v_inst_956_, v_t_957_, v_n_958_);
lean_dec(v_t_957_);
lean_dec(v_inst_956_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_960_, lean_object* v_00_u03b2_961_, lean_object* v_cmp_962_, lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_t_965_, lean_object* v_n_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_964_, v_t_965_, v_n_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_968_, lean_object* v_00_u03b2_969_, lean_object* v_cmp_970_, lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_t_973_, lean_object* v_n_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_ExtTreeMap_keyAtIdx_x21(v_00_u03b1_968_, v_00_u03b2_969_, v_cmp_970_, v_inst_971_, v_inst_972_, v_t_973_, v_n_974_);
lean_dec(v_t_973_);
lean_dec(v_inst_972_);
lean_dec_ref(v_cmp_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___redArg(lean_object* v_t_976_, lean_object* v_n_977_, lean_object* v_fallback_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_976_, v_n_977_, v_fallback_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_980_, lean_object* v_n_981_, lean_object* v_fallback_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Std_ExtTreeMap_keyAtIdxD___redArg(v_t_980_, v_n_981_, v_fallback_982_);
lean_dec(v_fallback_982_);
lean_dec(v_t_980_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD(lean_object* v_00_u03b1_984_, lean_object* v_00_u03b2_985_, lean_object* v_cmp_986_, lean_object* v_inst_987_, lean_object* v_t_988_, lean_object* v_n_989_, lean_object* v_fallback_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_988_, v_n_989_, v_fallback_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_992_, lean_object* v_00_u03b2_993_, lean_object* v_cmp_994_, lean_object* v_inst_995_, lean_object* v_t_996_, lean_object* v_n_997_, lean_object* v_fallback_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Std_ExtTreeMap_keyAtIdxD(v_00_u03b1_992_, v_00_u03b2_993_, v_cmp_994_, v_inst_995_, v_t_996_, v_n_997_, v_fallback_998_);
lean_dec(v_fallback_998_);
lean_dec(v_t_996_);
lean_dec_ref(v_cmp_994_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1000_, lean_object* v_t_1001_, lean_object* v_k_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_box(0);
v___x_1004_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1000_, v_k_1002_, v___x_1003_, v_t_1001_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1005_, lean_object* v_00_u03b2_1006_, lean_object* v_cmp_1007_, lean_object* v_inst_1008_, lean_object* v_t_1009_, lean_object* v_k_1010_){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = lean_box(0);
v___x_1012_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1007_, v_k_1010_, v___x_1011_, v_t_1009_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1013_, lean_object* v_t_1014_, lean_object* v_k_1015_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_box(0);
v___x_1017_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1013_, v_k_1015_, v___x_1016_, v_t_1014_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1018_, lean_object* v_00_u03b2_1019_, lean_object* v_cmp_1020_, lean_object* v_inst_1021_, lean_object* v_t_1022_, lean_object* v_k_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1020_, v_k_1023_, v___x_1024_, v_t_1022_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1026_, lean_object* v_t_1027_, lean_object* v_k_1028_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1026_, v_k_1028_, v___x_1029_, v_t_1027_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1031_, lean_object* v_00_u03b2_1032_, lean_object* v_cmp_1033_, lean_object* v_inst_1034_, lean_object* v_t_1035_, lean_object* v_k_1036_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1033_, v_k_1036_, v___x_1037_, v_t_1035_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1039_, lean_object* v_t_1040_, lean_object* v_k_1041_){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1039_, v_k_1041_, v___x_1042_, v_t_1040_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1044_, lean_object* v_00_u03b2_1045_, lean_object* v_cmp_1046_, lean_object* v_inst_1047_, lean_object* v_t_1048_, lean_object* v_k_1049_){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_box(0);
v___x_1051_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1046_, v_k_1049_, v___x_1050_, v_t_1048_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE___redArg(lean_object* v_cmp_1052_, lean_object* v_t_1053_, lean_object* v_k_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_1052_, v_k_1054_, v_t_1053_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE(lean_object* v_00_u03b1_1056_, lean_object* v_00_u03b2_1057_, lean_object* v_cmp_1058_, lean_object* v_inst_1059_, lean_object* v_t_1060_, lean_object* v_k_1061_, lean_object* v_h_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_1058_, v_k_1061_, v_t_1060_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT___redArg(lean_object* v_cmp_1064_, lean_object* v_t_1065_, lean_object* v_k_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_1064_, v_k_1066_, v_t_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT(lean_object* v_00_u03b1_1068_, lean_object* v_00_u03b2_1069_, lean_object* v_cmp_1070_, lean_object* v_inst_1071_, lean_object* v_t_1072_, lean_object* v_k_1073_, lean_object* v_h_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_1070_, v_k_1073_, v_t_1072_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE___redArg(lean_object* v_cmp_1076_, lean_object* v_t_1077_, lean_object* v_k_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_1076_, v_k_1078_, v_t_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE(lean_object* v_00_u03b1_1080_, lean_object* v_00_u03b2_1081_, lean_object* v_cmp_1082_, lean_object* v_inst_1083_, lean_object* v_t_1084_, lean_object* v_k_1085_, lean_object* v_h_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_1082_, v_k_1085_, v_t_1084_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT___redArg(lean_object* v_cmp_1088_, lean_object* v_t_1089_, lean_object* v_k_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_1088_, v_k_1090_, v_t_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT(lean_object* v_00_u03b1_1092_, lean_object* v_00_u03b2_1093_, lean_object* v_cmp_1094_, lean_object* v_inst_1095_, lean_object* v_t_1096_, lean_object* v_k_1097_, lean_object* v_h_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_1094_, v_k_1097_, v_t_1096_);
return v___x_1099_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1103_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1104_ = lean_unsigned_to_nat(14u);
v___x_1105_ = lean_unsigned_to_nat(22u);
v___x_1106_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1107_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1108_ = l_mkPanicMessageWithDecl(v___x_1107_, v___x_1106_, v___x_1105_, v___x_1104_, v___x_1103_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1109_, lean_object* v_inst_1110_, lean_object* v_t_1111_, lean_object* v_k_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1109_, v_k_1112_, v___x_1113_, v_t_1111_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1116_ = l_panic___redArg(v_inst_1110_, v___x_1115_);
return v___x_1116_;
}
else
{
lean_object* v_val_1117_; 
v_val_1117_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_val_1117_);
lean_dec_ref_known(v___x_1114_, 1);
return v_val_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1118_, lean_object* v_inst_1119_, lean_object* v_t_1120_, lean_object* v_k_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Std_ExtTreeMap_getEntryGE_x21___redArg(v_cmp_1118_, v_inst_1119_, v_t_1120_, v_k_1121_);
lean_dec_ref(v_inst_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1123_, lean_object* v_00_u03b2_1124_, lean_object* v_cmp_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_t_1128_, lean_object* v_k_1129_){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_box(0);
v___x_1131_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1125_, v_k_1129_, v___x_1130_, v_t_1128_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1133_ = l_panic___redArg(v_inst_1127_, v___x_1132_);
return v___x_1133_;
}
else
{
lean_object* v_val_1134_; 
v_val_1134_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_val_1134_);
lean_dec_ref_known(v___x_1131_, 1);
return v_val_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_cmp_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_t_1140_, lean_object* v_k_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_ExtTreeMap_getEntryGE_x21(v_00_u03b1_1135_, v_00_u03b2_1136_, v_cmp_1137_, v_inst_1138_, v_inst_1139_, v_t_1140_, v_k_1141_);
lean_dec_ref(v_inst_1139_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1143_, lean_object* v_inst_1144_, lean_object* v_t_1145_, lean_object* v_k_1146_){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_box(0);
v___x_1148_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1143_, v_k_1146_, v___x_1147_, v_t_1145_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1150_ = l_panic___redArg(v_inst_1144_, v___x_1149_);
return v___x_1150_;
}
else
{
lean_object* v_val_1151_; 
v_val_1151_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_val_1151_);
lean_dec_ref_known(v___x_1148_, 1);
return v_val_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1152_, lean_object* v_inst_1153_, lean_object* v_t_1154_, lean_object* v_k_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_ExtTreeMap_getEntryGT_x21___redArg(v_cmp_1152_, v_inst_1153_, v_t_1154_, v_k_1155_);
lean_dec_ref(v_inst_1153_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_cmp_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_t_1162_, lean_object* v_k_1163_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_box(0);
v___x_1165_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1159_, v_k_1163_, v___x_1164_, v_t_1162_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1167_ = l_panic___redArg(v_inst_1161_, v___x_1166_);
return v___x_1167_;
}
else
{
lean_object* v_val_1168_; 
v_val_1168_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v___x_1165_, 1);
return v_val_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_00_u03b2_1170_, lean_object* v_cmp_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_t_1174_, lean_object* v_k_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Std_ExtTreeMap_getEntryGT_x21(v_00_u03b1_1169_, v_00_u03b2_1170_, v_cmp_1171_, v_inst_1172_, v_inst_1173_, v_t_1174_, v_k_1175_);
lean_dec_ref(v_inst_1173_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1177_, lean_object* v_inst_1178_, lean_object* v_t_1179_, lean_object* v_k_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_box(0);
v___x_1182_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1177_, v_k_1180_, v___x_1181_, v_t_1179_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1184_ = l_panic___redArg(v_inst_1178_, v___x_1183_);
return v___x_1184_;
}
else
{
lean_object* v_val_1185_; 
v_val_1185_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v___x_1182_, 1);
return v_val_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1186_, lean_object* v_inst_1187_, lean_object* v_t_1188_, lean_object* v_k_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Std_ExtTreeMap_getEntryLE_x21___redArg(v_cmp_1186_, v_inst_1187_, v_t_1188_, v_k_1189_);
lean_dec_ref(v_inst_1187_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1191_, lean_object* v_00_u03b2_1192_, lean_object* v_cmp_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_t_1196_, lean_object* v_k_1197_){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_box(0);
v___x_1199_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1193_, v_k_1197_, v___x_1198_, v_t_1196_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1201_ = l_panic___redArg(v_inst_1195_, v___x_1200_);
return v___x_1201_;
}
else
{
lean_object* v_val_1202_; 
v_val_1202_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_val_1202_);
lean_dec_ref_known(v___x_1199_, 1);
return v_val_1202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1203_, lean_object* v_00_u03b2_1204_, lean_object* v_cmp_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_t_1208_, lean_object* v_k_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Std_ExtTreeMap_getEntryLE_x21(v_00_u03b1_1203_, v_00_u03b2_1204_, v_cmp_1205_, v_inst_1206_, v_inst_1207_, v_t_1208_, v_k_1209_);
lean_dec_ref(v_inst_1207_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1211_, lean_object* v_inst_1212_, lean_object* v_t_1213_, lean_object* v_k_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_box(0);
v___x_1216_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1211_, v_k_1214_, v___x_1215_, v_t_1213_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1218_ = l_panic___redArg(v_inst_1212_, v___x_1217_);
return v___x_1218_;
}
else
{
lean_object* v_val_1219_; 
v_val_1219_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_val_1219_);
lean_dec_ref_known(v___x_1216_, 1);
return v_val_1219_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1220_, lean_object* v_inst_1221_, lean_object* v_t_1222_, lean_object* v_k_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Std_ExtTreeMap_getEntryLT_x21___redArg(v_cmp_1220_, v_inst_1221_, v_t_1222_, v_k_1223_);
lean_dec_ref(v_inst_1221_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1225_, lean_object* v_00_u03b2_1226_, lean_object* v_cmp_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_t_1230_, lean_object* v_k_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_box(0);
v___x_1233_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1227_, v_k_1231_, v___x_1232_, v_t_1230_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1235_ = l_panic___redArg(v_inst_1229_, v___x_1234_);
return v___x_1235_;
}
else
{
lean_object* v_val_1236_; 
v_val_1236_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_val_1236_);
lean_dec_ref_known(v___x_1233_, 1);
return v_val_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1237_, lean_object* v_00_u03b2_1238_, lean_object* v_cmp_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_t_1242_, lean_object* v_k_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Std_ExtTreeMap_getEntryLT_x21(v_00_u03b1_1237_, v_00_u03b2_1238_, v_cmp_1239_, v_inst_1240_, v_inst_1241_, v_t_1242_, v_k_1243_);
lean_dec_ref(v_inst_1241_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___redArg(lean_object* v_cmp_1245_, lean_object* v_t_1246_, lean_object* v_k_1247_, lean_object* v_fallback_1248_){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1245_, v_k_1247_, v___x_1249_, v_t_1246_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_inc_ref(v_fallback_1248_);
return v_fallback_1248_;
}
else
{
lean_object* v_val_1251_; 
v_val_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_val_1251_);
lean_dec_ref_known(v___x_1250_, 1);
return v_val_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1252_, lean_object* v_t_1253_, lean_object* v_k_1254_, lean_object* v_fallback_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_ExtTreeMap_getEntryGED___redArg(v_cmp_1252_, v_t_1253_, v_k_1254_, v_fallback_1255_);
lean_dec_ref(v_fallback_1255_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED(lean_object* v_00_u03b1_1257_, lean_object* v_00_u03b2_1258_, lean_object* v_cmp_1259_, lean_object* v_inst_1260_, lean_object* v_t_1261_, lean_object* v_k_1262_, lean_object* v_fallback_1263_){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_box(0);
v___x_1265_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1259_, v_k_1262_, v___x_1264_, v_t_1261_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_inc_ref(v_fallback_1263_);
return v_fallback_1263_;
}
else
{
lean_object* v_val_1266_; 
v_val_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_val_1266_);
lean_dec_ref_known(v___x_1265_, 1);
return v_val_1266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1267_, lean_object* v_00_u03b2_1268_, lean_object* v_cmp_1269_, lean_object* v_inst_1270_, lean_object* v_t_1271_, lean_object* v_k_1272_, lean_object* v_fallback_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Std_ExtTreeMap_getEntryGED(v_00_u03b1_1267_, v_00_u03b2_1268_, v_cmp_1269_, v_inst_1270_, v_t_1271_, v_k_1272_, v_fallback_1273_);
lean_dec_ref(v_fallback_1273_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1275_, lean_object* v_t_1276_, lean_object* v_k_1277_, lean_object* v_fallback_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_box(0);
v___x_1280_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1275_, v_k_1277_, v___x_1279_, v_t_1276_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_inc_ref(v_fallback_1278_);
return v_fallback_1278_;
}
else
{
lean_object* v_val_1281_; 
v_val_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1280_, 1);
return v_val_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1282_, lean_object* v_t_1283_, lean_object* v_k_1284_, lean_object* v_fallback_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_ExtTreeMap_getEntryGTD___redArg(v_cmp_1282_, v_t_1283_, v_k_1284_, v_fallback_1285_);
lean_dec_ref(v_fallback_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD(lean_object* v_00_u03b1_1287_, lean_object* v_00_u03b2_1288_, lean_object* v_cmp_1289_, lean_object* v_inst_1290_, lean_object* v_t_1291_, lean_object* v_k_1292_, lean_object* v_fallback_1293_){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_box(0);
v___x_1295_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1289_, v_k_1292_, v___x_1294_, v_t_1291_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_inc_ref(v_fallback_1293_);
return v_fallback_1293_;
}
else
{
lean_object* v_val_1296_; 
v_val_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v___x_1295_, 1);
return v_val_1296_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1297_, lean_object* v_00_u03b2_1298_, lean_object* v_cmp_1299_, lean_object* v_inst_1300_, lean_object* v_t_1301_, lean_object* v_k_1302_, lean_object* v_fallback_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Std_ExtTreeMap_getEntryGTD(v_00_u03b1_1297_, v_00_u03b2_1298_, v_cmp_1299_, v_inst_1300_, v_t_1301_, v_k_1302_, v_fallback_1303_);
lean_dec_ref(v_fallback_1303_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___redArg(lean_object* v_cmp_1305_, lean_object* v_t_1306_, lean_object* v_k_1307_, lean_object* v_fallback_1308_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1305_, v_k_1307_, v___x_1309_, v_t_1306_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_inc_ref(v_fallback_1308_);
return v_fallback_1308_;
}
else
{
lean_object* v_val_1311_; 
v_val_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_val_1311_);
lean_dec_ref_known(v___x_1310_, 1);
return v_val_1311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1312_, lean_object* v_t_1313_, lean_object* v_k_1314_, lean_object* v_fallback_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Std_ExtTreeMap_getEntryLED___redArg(v_cmp_1312_, v_t_1313_, v_k_1314_, v_fallback_1315_);
lean_dec_ref(v_fallback_1315_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED(lean_object* v_00_u03b1_1317_, lean_object* v_00_u03b2_1318_, lean_object* v_cmp_1319_, lean_object* v_inst_1320_, lean_object* v_t_1321_, lean_object* v_k_1322_, lean_object* v_fallback_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1319_, v_k_1322_, v___x_1324_, v_t_1321_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_inc_ref(v_fallback_1323_);
return v_fallback_1323_;
}
else
{
lean_object* v_val_1326_; 
v_val_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_val_1326_);
lean_dec_ref_known(v___x_1325_, 1);
return v_val_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_00_u03b2_1328_, lean_object* v_cmp_1329_, lean_object* v_inst_1330_, lean_object* v_t_1331_, lean_object* v_k_1332_, lean_object* v_fallback_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Std_ExtTreeMap_getEntryLED(v_00_u03b1_1327_, v_00_u03b2_1328_, v_cmp_1329_, v_inst_1330_, v_t_1331_, v_k_1332_, v_fallback_1333_);
lean_dec_ref(v_fallback_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1335_, lean_object* v_t_1336_, lean_object* v_k_1337_, lean_object* v_fallback_1338_){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1335_, v_k_1337_, v___x_1339_, v_t_1336_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_inc_ref(v_fallback_1338_);
return v_fallback_1338_;
}
else
{
lean_object* v_val_1341_; 
v_val_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_val_1341_);
lean_dec_ref_known(v___x_1340_, 1);
return v_val_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1342_, lean_object* v_t_1343_, lean_object* v_k_1344_, lean_object* v_fallback_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_ExtTreeMap_getEntryLTD___redArg(v_cmp_1342_, v_t_1343_, v_k_1344_, v_fallback_1345_);
lean_dec_ref(v_fallback_1345_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD(lean_object* v_00_u03b1_1347_, lean_object* v_00_u03b2_1348_, lean_object* v_cmp_1349_, lean_object* v_inst_1350_, lean_object* v_t_1351_, lean_object* v_k_1352_, lean_object* v_fallback_1353_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1349_, v_k_1352_, v___x_1354_, v_t_1351_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_inc_ref(v_fallback_1353_);
return v_fallback_1353_;
}
else
{
lean_object* v_val_1356_; 
v_val_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v___x_1355_, 1);
return v_val_1356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1357_, lean_object* v_00_u03b2_1358_, lean_object* v_cmp_1359_, lean_object* v_inst_1360_, lean_object* v_t_1361_, lean_object* v_k_1362_, lean_object* v_fallback_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Std_ExtTreeMap_getEntryLTD(v_00_u03b1_1357_, v_00_u03b2_1358_, v_cmp_1359_, v_inst_1360_, v_t_1361_, v_k_1362_, v_fallback_1363_);
lean_dec_ref(v_fallback_1363_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1365_, lean_object* v_t_1366_, lean_object* v_k_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1365_, v_k_1367_, v___x_1368_, v_t_1366_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1370_, lean_object* v_00_u03b2_1371_, lean_object* v_cmp_1372_, lean_object* v_inst_1373_, lean_object* v_t_1374_, lean_object* v_k_1375_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_box(0);
v___x_1377_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1372_, v_k_1375_, v___x_1376_, v_t_1374_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1378_, lean_object* v_t_1379_, lean_object* v_k_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_box(0);
v___x_1382_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1378_, v_k_1380_, v___x_1381_, v_t_1379_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1383_, lean_object* v_00_u03b2_1384_, lean_object* v_cmp_1385_, lean_object* v_inst_1386_, lean_object* v_t_1387_, lean_object* v_k_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1385_, v_k_1388_, v___x_1389_, v_t_1387_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1391_, lean_object* v_t_1392_, lean_object* v_k_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1391_, v_k_1393_, v___x_1394_, v_t_1392_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1396_, lean_object* v_00_u03b2_1397_, lean_object* v_cmp_1398_, lean_object* v_inst_1399_, lean_object* v_t_1400_, lean_object* v_k_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1398_, v_k_1401_, v___x_1402_, v_t_1400_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1404_, lean_object* v_t_1405_, lean_object* v_k_1406_){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_box(0);
v___x_1408_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1404_, v_k_1406_, v___x_1407_, v_t_1405_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1409_, lean_object* v_00_u03b2_1410_, lean_object* v_cmp_1411_, lean_object* v_inst_1412_, lean_object* v_t_1413_, lean_object* v_k_1414_){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_box(0);
v___x_1416_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1411_, v_k_1414_, v___x_1415_, v_t_1413_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE___redArg(lean_object* v_cmp_1417_, lean_object* v_t_1418_, lean_object* v_k_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1417_, v_k_1419_, v_t_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE(lean_object* v_00_u03b1_1421_, lean_object* v_00_u03b2_1422_, lean_object* v_cmp_1423_, lean_object* v_inst_1424_, lean_object* v_t_1425_, lean_object* v_k_1426_, lean_object* v_h_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1423_, v_k_1426_, v_t_1425_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT___redArg(lean_object* v_cmp_1429_, lean_object* v_t_1430_, lean_object* v_k_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1429_, v_k_1431_, v_t_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT(lean_object* v_00_u03b1_1433_, lean_object* v_00_u03b2_1434_, lean_object* v_cmp_1435_, lean_object* v_inst_1436_, lean_object* v_t_1437_, lean_object* v_k_1438_, lean_object* v_h_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1435_, v_k_1438_, v_t_1437_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE___redArg(lean_object* v_cmp_1441_, lean_object* v_t_1442_, lean_object* v_k_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1441_, v_k_1443_, v_t_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE(lean_object* v_00_u03b1_1445_, lean_object* v_00_u03b2_1446_, lean_object* v_cmp_1447_, lean_object* v_inst_1448_, lean_object* v_t_1449_, lean_object* v_k_1450_, lean_object* v_h_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1447_, v_k_1450_, v_t_1449_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT___redArg(lean_object* v_cmp_1453_, lean_object* v_t_1454_, lean_object* v_k_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1453_, v_k_1455_, v_t_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT(lean_object* v_00_u03b1_1457_, lean_object* v_00_u03b2_1458_, lean_object* v_cmp_1459_, lean_object* v_inst_1460_, lean_object* v_t_1461_, lean_object* v_k_1462_, lean_object* v_h_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1459_, v_k_1462_, v_t_1461_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1465_, lean_object* v_inst_1466_, lean_object* v_t_1467_, lean_object* v_k_1468_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_box(0);
v___x_1470_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1465_, v_k_1468_, v___x_1469_, v_t_1467_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1472_ = l_panic___redArg(v_inst_1466_, v___x_1471_);
return v___x_1472_;
}
else
{
lean_object* v_val_1473_; 
v_val_1473_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_val_1473_);
lean_dec_ref_known(v___x_1470_, 1);
return v_val_1473_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1474_, lean_object* v_inst_1475_, lean_object* v_t_1476_, lean_object* v_k_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Std_ExtTreeMap_getKeyGE_x21___redArg(v_cmp_1474_, v_inst_1475_, v_t_1476_, v_k_1477_);
lean_dec(v_inst_1475_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1479_, lean_object* v_00_u03b2_1480_, lean_object* v_cmp_1481_, lean_object* v_inst_1482_, lean_object* v_inst_1483_, lean_object* v_t_1484_, lean_object* v_k_1485_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_box(0);
v___x_1487_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1481_, v_k_1485_, v___x_1486_, v_t_1484_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1489_ = l_panic___redArg(v_inst_1483_, v___x_1488_);
return v___x_1489_;
}
else
{
lean_object* v_val_1490_; 
v_val_1490_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_val_1490_);
lean_dec_ref_known(v___x_1487_, 1);
return v_val_1490_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1491_, lean_object* v_00_u03b2_1492_, lean_object* v_cmp_1493_, lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_t_1496_, lean_object* v_k_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Std_ExtTreeMap_getKeyGE_x21(v_00_u03b1_1491_, v_00_u03b2_1492_, v_cmp_1493_, v_inst_1494_, v_inst_1495_, v_t_1496_, v_k_1497_);
lean_dec(v_inst_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1499_, lean_object* v_inst_1500_, lean_object* v_t_1501_, lean_object* v_k_1502_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_box(0);
v___x_1504_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1499_, v_k_1502_, v___x_1503_, v_t_1501_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1506_ = l_panic___redArg(v_inst_1500_, v___x_1505_);
return v___x_1506_;
}
else
{
lean_object* v_val_1507_; 
v_val_1507_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_val_1507_);
lean_dec_ref_known(v___x_1504_, 1);
return v_val_1507_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1508_, lean_object* v_inst_1509_, lean_object* v_t_1510_, lean_object* v_k_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Std_ExtTreeMap_getKeyGT_x21___redArg(v_cmp_1508_, v_inst_1509_, v_t_1510_, v_k_1511_);
lean_dec(v_inst_1509_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1513_, lean_object* v_00_u03b2_1514_, lean_object* v_cmp_1515_, lean_object* v_inst_1516_, lean_object* v_inst_1517_, lean_object* v_t_1518_, lean_object* v_k_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_box(0);
v___x_1521_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1515_, v_k_1519_, v___x_1520_, v_t_1518_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1523_ = l_panic___redArg(v_inst_1517_, v___x_1522_);
return v___x_1523_;
}
else
{
lean_object* v_val_1524_; 
v_val_1524_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_val_1524_);
lean_dec_ref_known(v___x_1521_, 1);
return v_val_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1525_, lean_object* v_00_u03b2_1526_, lean_object* v_cmp_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_t_1530_, lean_object* v_k_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Std_ExtTreeMap_getKeyGT_x21(v_00_u03b1_1525_, v_00_u03b2_1526_, v_cmp_1527_, v_inst_1528_, v_inst_1529_, v_t_1530_, v_k_1531_);
lean_dec(v_inst_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1533_, lean_object* v_inst_1534_, lean_object* v_t_1535_, lean_object* v_k_1536_){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_box(0);
v___x_1538_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1533_, v_k_1536_, v___x_1537_, v_t_1535_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1540_ = l_panic___redArg(v_inst_1534_, v___x_1539_);
return v___x_1540_;
}
else
{
lean_object* v_val_1541_; 
v_val_1541_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_val_1541_);
lean_dec_ref_known(v___x_1538_, 1);
return v_val_1541_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1542_, lean_object* v_inst_1543_, lean_object* v_t_1544_, lean_object* v_k_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Std_ExtTreeMap_getKeyLE_x21___redArg(v_cmp_1542_, v_inst_1543_, v_t_1544_, v_k_1545_);
lean_dec(v_inst_1543_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1547_, lean_object* v_00_u03b2_1548_, lean_object* v_cmp_1549_, lean_object* v_inst_1550_, lean_object* v_inst_1551_, lean_object* v_t_1552_, lean_object* v_k_1553_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1549_, v_k_1553_, v___x_1554_, v_t_1552_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1557_ = l_panic___redArg(v_inst_1551_, v___x_1556_);
return v___x_1557_;
}
else
{
lean_object* v_val_1558_; 
v_val_1558_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_val_1558_);
lean_dec_ref_known(v___x_1555_, 1);
return v_val_1558_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1559_, lean_object* v_00_u03b2_1560_, lean_object* v_cmp_1561_, lean_object* v_inst_1562_, lean_object* v_inst_1563_, lean_object* v_t_1564_, lean_object* v_k_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Std_ExtTreeMap_getKeyLE_x21(v_00_u03b1_1559_, v_00_u03b2_1560_, v_cmp_1561_, v_inst_1562_, v_inst_1563_, v_t_1564_, v_k_1565_);
lean_dec(v_inst_1563_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1567_, lean_object* v_inst_1568_, lean_object* v_t_1569_, lean_object* v_k_1570_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_box(0);
v___x_1572_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1567_, v_k_1570_, v___x_1571_, v_t_1569_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1574_ = l_panic___redArg(v_inst_1568_, v___x_1573_);
return v___x_1574_;
}
else
{
lean_object* v_val_1575_; 
v_val_1575_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_val_1575_);
lean_dec_ref_known(v___x_1572_, 1);
return v_val_1575_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1576_, lean_object* v_inst_1577_, lean_object* v_t_1578_, lean_object* v_k_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Std_ExtTreeMap_getKeyLT_x21___redArg(v_cmp_1576_, v_inst_1577_, v_t_1578_, v_k_1579_);
lean_dec(v_inst_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1581_, lean_object* v_00_u03b2_1582_, lean_object* v_cmp_1583_, lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_t_1586_, lean_object* v_k_1587_){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_box(0);
v___x_1589_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1583_, v_k_1587_, v___x_1588_, v_t_1586_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1591_ = l_panic___redArg(v_inst_1585_, v___x_1590_);
return v___x_1591_;
}
else
{
lean_object* v_val_1592_; 
v_val_1592_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v___x_1589_, 1);
return v_val_1592_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1593_, lean_object* v_00_u03b2_1594_, lean_object* v_cmp_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_t_1598_, lean_object* v_k_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Std_ExtTreeMap_getKeyLT_x21(v_00_u03b1_1593_, v_00_u03b2_1594_, v_cmp_1595_, v_inst_1596_, v_inst_1597_, v_t_1598_, v_k_1599_);
lean_dec(v_inst_1597_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___redArg(lean_object* v_cmp_1601_, lean_object* v_t_1602_, lean_object* v_k_1603_, lean_object* v_fallback_1604_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_box(0);
v___x_1606_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1601_, v_k_1603_, v___x_1605_, v_t_1602_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_inc(v_fallback_1604_);
return v_fallback_1604_;
}
else
{
lean_object* v_val_1607_; 
v_val_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_val_1607_);
lean_dec_ref_known(v___x_1606_, 1);
return v_val_1607_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1608_, lean_object* v_t_1609_, lean_object* v_k_1610_, lean_object* v_fallback_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Std_ExtTreeMap_getKeyGED___redArg(v_cmp_1608_, v_t_1609_, v_k_1610_, v_fallback_1611_);
lean_dec(v_fallback_1611_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED(lean_object* v_00_u03b1_1613_, lean_object* v_00_u03b2_1614_, lean_object* v_cmp_1615_, lean_object* v_inst_1616_, lean_object* v_t_1617_, lean_object* v_k_1618_, lean_object* v_fallback_1619_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_box(0);
v___x_1621_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1615_, v_k_1618_, v___x_1620_, v_t_1617_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_inc(v_fallback_1619_);
return v_fallback_1619_;
}
else
{
lean_object* v_val_1622_; 
v_val_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_val_1622_);
lean_dec_ref_known(v___x_1621_, 1);
return v_val_1622_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1623_, lean_object* v_00_u03b2_1624_, lean_object* v_cmp_1625_, lean_object* v_inst_1626_, lean_object* v_t_1627_, lean_object* v_k_1628_, lean_object* v_fallback_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Std_ExtTreeMap_getKeyGED(v_00_u03b1_1623_, v_00_u03b2_1624_, v_cmp_1625_, v_inst_1626_, v_t_1627_, v_k_1628_, v_fallback_1629_);
lean_dec(v_fallback_1629_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1631_, lean_object* v_t_1632_, lean_object* v_k_1633_, lean_object* v_fallback_1634_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_box(0);
v___x_1636_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1631_, v_k_1633_, v___x_1635_, v_t_1632_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_inc(v_fallback_1634_);
return v_fallback_1634_;
}
else
{
lean_object* v_val_1637_; 
v_val_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_val_1637_);
lean_dec_ref_known(v___x_1636_, 1);
return v_val_1637_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1638_, lean_object* v_t_1639_, lean_object* v_k_1640_, lean_object* v_fallback_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Std_ExtTreeMap_getKeyGTD___redArg(v_cmp_1638_, v_t_1639_, v_k_1640_, v_fallback_1641_);
lean_dec(v_fallback_1641_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD(lean_object* v_00_u03b1_1643_, lean_object* v_00_u03b2_1644_, lean_object* v_cmp_1645_, lean_object* v_inst_1646_, lean_object* v_t_1647_, lean_object* v_k_1648_, lean_object* v_fallback_1649_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_box(0);
v___x_1651_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1645_, v_k_1648_, v___x_1650_, v_t_1647_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_inc(v_fallback_1649_);
return v_fallback_1649_;
}
else
{
lean_object* v_val_1652_; 
v_val_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_val_1652_);
lean_dec_ref_known(v___x_1651_, 1);
return v_val_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1653_, lean_object* v_00_u03b2_1654_, lean_object* v_cmp_1655_, lean_object* v_inst_1656_, lean_object* v_t_1657_, lean_object* v_k_1658_, lean_object* v_fallback_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Std_ExtTreeMap_getKeyGTD(v_00_u03b1_1653_, v_00_u03b2_1654_, v_cmp_1655_, v_inst_1656_, v_t_1657_, v_k_1658_, v_fallback_1659_);
lean_dec(v_fallback_1659_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___redArg(lean_object* v_cmp_1661_, lean_object* v_t_1662_, lean_object* v_k_1663_, lean_object* v_fallback_1664_){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_box(0);
v___x_1666_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1661_, v_k_1663_, v___x_1665_, v_t_1662_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_inc(v_fallback_1664_);
return v_fallback_1664_;
}
else
{
lean_object* v_val_1667_; 
v_val_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_val_1667_);
lean_dec_ref_known(v___x_1666_, 1);
return v_val_1667_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1668_, lean_object* v_t_1669_, lean_object* v_k_1670_, lean_object* v_fallback_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Std_ExtTreeMap_getKeyLED___redArg(v_cmp_1668_, v_t_1669_, v_k_1670_, v_fallback_1671_);
lean_dec(v_fallback_1671_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED(lean_object* v_00_u03b1_1673_, lean_object* v_00_u03b2_1674_, lean_object* v_cmp_1675_, lean_object* v_inst_1676_, lean_object* v_t_1677_, lean_object* v_k_1678_, lean_object* v_fallback_1679_){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_box(0);
v___x_1681_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1675_, v_k_1678_, v___x_1680_, v_t_1677_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_inc(v_fallback_1679_);
return v_fallback_1679_;
}
else
{
lean_object* v_val_1682_; 
v_val_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_val_1682_);
lean_dec_ref_known(v___x_1681_, 1);
return v_val_1682_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1683_, lean_object* v_00_u03b2_1684_, lean_object* v_cmp_1685_, lean_object* v_inst_1686_, lean_object* v_t_1687_, lean_object* v_k_1688_, lean_object* v_fallback_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_ExtTreeMap_getKeyLED(v_00_u03b1_1683_, v_00_u03b2_1684_, v_cmp_1685_, v_inst_1686_, v_t_1687_, v_k_1688_, v_fallback_1689_);
lean_dec(v_fallback_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1691_, lean_object* v_t_1692_, lean_object* v_k_1693_, lean_object* v_fallback_1694_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = lean_box(0);
v___x_1696_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1691_, v_k_1693_, v___x_1695_, v_t_1692_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_inc(v_fallback_1694_);
return v_fallback_1694_;
}
else
{
lean_object* v_val_1697_; 
v_val_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_val_1697_);
lean_dec_ref_known(v___x_1696_, 1);
return v_val_1697_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1698_, lean_object* v_t_1699_, lean_object* v_k_1700_, lean_object* v_fallback_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Std_ExtTreeMap_getKeyLTD___redArg(v_cmp_1698_, v_t_1699_, v_k_1700_, v_fallback_1701_);
lean_dec(v_fallback_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD(lean_object* v_00_u03b1_1703_, lean_object* v_00_u03b2_1704_, lean_object* v_cmp_1705_, lean_object* v_inst_1706_, lean_object* v_t_1707_, lean_object* v_k_1708_, lean_object* v_fallback_1709_){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_box(0);
v___x_1711_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1705_, v_k_1708_, v___x_1710_, v_t_1707_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_inc(v_fallback_1709_);
return v_fallback_1709_;
}
else
{
lean_object* v_val_1712_; 
v_val_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_val_1712_);
lean_dec_ref_known(v___x_1711_, 1);
return v_val_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_cmp_1715_, lean_object* v_inst_1716_, lean_object* v_t_1717_, lean_object* v_k_1718_, lean_object* v_fallback_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Std_ExtTreeMap_getKeyLTD(v_00_u03b1_1713_, v_00_u03b2_1714_, v_cmp_1715_, v_inst_1716_, v_t_1717_, v_k_1718_, v_fallback_1719_);
lean_dec(v_fallback_1719_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter___redArg(lean_object* v_f_1721_, lean_object* v_m_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_1721_, v_m_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter(lean_object* v_00_u03b1_1724_, lean_object* v_00_u03b2_1725_, lean_object* v_cmp_1726_, lean_object* v_f_1727_, lean_object* v_m_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_1727_, v_m_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter___boxed(lean_object* v_00_u03b1_1730_, lean_object* v_00_u03b2_1731_, lean_object* v_cmp_1732_, lean_object* v_f_1733_, lean_object* v_m_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Std_ExtTreeMap_filter(v_00_u03b1_1730_, v_00_u03b2_1731_, v_cmp_1732_, v_f_1733_, v_m_1734_);
lean_dec_ref(v_cmp_1732_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap___redArg(lean_object* v_f_1736_, lean_object* v_m_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_1736_, v_m_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap(lean_object* v_00_u03b1_1739_, lean_object* v_00_u03b2_1740_, lean_object* v_00_u03b3_1741_, lean_object* v_cmp_1742_, lean_object* v_f_1743_, lean_object* v_m_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_1743_, v_m_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_00_u03b2_1747_, lean_object* v_00_u03b3_1748_, lean_object* v_cmp_1749_, lean_object* v_f_1750_, lean_object* v_m_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Std_ExtTreeMap_filterMap(v_00_u03b1_1746_, v_00_u03b2_1747_, v_00_u03b3_1748_, v_cmp_1749_, v_f_1750_, v_m_1751_);
lean_dec_ref(v_cmp_1749_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map___redArg(lean_object* v_f_1753_, lean_object* v_t_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_1753_, v_t_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map(lean_object* v_00_u03b1_1756_, lean_object* v_00_u03b2_1757_, lean_object* v_00_u03b3_1758_, lean_object* v_cmp_1759_, lean_object* v_f_1760_, lean_object* v_t_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_1760_, v_t_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map___boxed(lean_object* v_00_u03b1_1763_, lean_object* v_00_u03b2_1764_, lean_object* v_00_u03b3_1765_, lean_object* v_cmp_1766_, lean_object* v_f_1767_, lean_object* v_t_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Std_ExtTreeMap_map(v_00_u03b1_1763_, v_00_u03b2_1764_, v_00_u03b3_1765_, v_cmp_1766_, v_f_1767_, v_t_1768_);
lean_dec_ref(v_cmp_1766_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM___redArg(lean_object* v_inst_1770_, lean_object* v_f_1771_, lean_object* v_init_1772_, lean_object* v_t_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1770_, v_f_1771_, v_init_1772_, v_t_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM(lean_object* v_00_u03b1_1775_, lean_object* v_00_u03b2_1776_, lean_object* v_cmp_1777_, lean_object* v_00_u03b4_1778_, lean_object* v_m_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_f_1783_, lean_object* v_init_1784_, lean_object* v_t_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1780_, v_f_1783_, v_init_1784_, v_t_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM___boxed(lean_object* v_00_u03b1_1787_, lean_object* v_00_u03b2_1788_, lean_object* v_cmp_1789_, lean_object* v_00_u03b4_1790_, lean_object* v_m_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_f_1795_, lean_object* v_init_1796_, lean_object* v_t_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Std_ExtTreeMap_foldlM(v_00_u03b1_1787_, v_00_u03b2_1788_, v_cmp_1789_, v_00_u03b4_1790_, v_m_1791_, v_inst_1792_, v_inst_1793_, v_inst_1794_, v_f_1795_, v_init_1796_, v_t_1797_);
lean_dec_ref(v_cmp_1789_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl___redArg(lean_object* v_f_1799_, lean_object* v_init_1800_, lean_object* v_t_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1799_, v_init_1800_, v_t_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl(lean_object* v_00_u03b1_1803_, lean_object* v_00_u03b2_1804_, lean_object* v_cmp_1805_, lean_object* v_00_u03b4_1806_, lean_object* v_inst_1807_, lean_object* v_f_1808_, lean_object* v_init_1809_, lean_object* v_t_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1808_, v_init_1809_, v_t_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl___boxed(lean_object* v_00_u03b1_1812_, lean_object* v_00_u03b2_1813_, lean_object* v_cmp_1814_, lean_object* v_00_u03b4_1815_, lean_object* v_inst_1816_, lean_object* v_f_1817_, lean_object* v_init_1818_, lean_object* v_t_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Std_ExtTreeMap_foldl(v_00_u03b1_1812_, v_00_u03b2_1813_, v_cmp_1814_, v_00_u03b4_1815_, v_inst_1816_, v_f_1817_, v_init_1818_, v_t_1819_);
lean_dec_ref(v_cmp_1814_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM___redArg(lean_object* v_inst_1821_, lean_object* v_f_1822_, lean_object* v_init_1823_, lean_object* v_t_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1821_, v_f_1822_, v_init_1823_, v_t_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM(lean_object* v_00_u03b1_1826_, lean_object* v_00_u03b2_1827_, lean_object* v_cmp_1828_, lean_object* v_00_u03b4_1829_, lean_object* v_m_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_f_1834_, lean_object* v_init_1835_, lean_object* v_t_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1831_, v_f_1834_, v_init_1835_, v_t_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM___boxed(lean_object* v_00_u03b1_1838_, lean_object* v_00_u03b2_1839_, lean_object* v_cmp_1840_, lean_object* v_00_u03b4_1841_, lean_object* v_m_1842_, lean_object* v_inst_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_f_1846_, lean_object* v_init_1847_, lean_object* v_t_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Std_ExtTreeMap_foldrM(v_00_u03b1_1838_, v_00_u03b2_1839_, v_cmp_1840_, v_00_u03b4_1841_, v_m_1842_, v_inst_1843_, v_inst_1844_, v_inst_1845_, v_f_1846_, v_init_1847_, v_t_1848_);
lean_dec_ref(v_cmp_1840_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___redArg___lam__0(lean_object* v_f_1850_, lean_object* v_x1_1851_, lean_object* v_x2_1852_, lean_object* v_x3_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_apply_3(v_f_1850_, v_x1_1851_, v_x2_1852_, v_x3_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___redArg(lean_object* v_f_1874_, lean_object* v_init_1875_, lean_object* v_t_1876_){
_start:
{
lean_object* v___f_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___f_1877_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1877_, 0, v_f_1874_);
v___x_1878_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_1879_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1878_, v___f_1877_, v_init_1875_, v_t_1876_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr(lean_object* v_00_u03b1_1880_, lean_object* v_00_u03b2_1881_, lean_object* v_cmp_1882_, lean_object* v_00_u03b4_1883_, lean_object* v_inst_1884_, lean_object* v_f_1885_, lean_object* v_init_1886_, lean_object* v_t_1887_){
_start:
{
lean_object* v___f_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___f_1888_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1888_, 0, v_f_1885_);
v___x_1889_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_1890_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1889_, v___f_1888_, v_init_1886_, v_t_1887_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___boxed(lean_object* v_00_u03b1_1891_, lean_object* v_00_u03b2_1892_, lean_object* v_cmp_1893_, lean_object* v_00_u03b4_1894_, lean_object* v_inst_1895_, lean_object* v_f_1896_, lean_object* v_init_1897_, lean_object* v_t_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Std_ExtTreeMap_foldr(v_00_u03b1_1891_, v_00_u03b2_1892_, v_cmp_1893_, v_00_u03b4_1894_, v_inst_1895_, v_f_1896_, v_init_1897_, v_t_1898_);
lean_dec_ref(v_cmp_1893_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition___redArg___lam__0(lean_object* v_f_1900_, lean_object* v_cmp_1901_, lean_object* v_x_1902_, lean_object* v_a_1903_, lean_object* v_b_1904_){
_start:
{
lean_object* v_fst_1905_; lean_object* v_snd_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1920_; 
v_fst_1905_ = lean_ctor_get(v_x_1902_, 0);
v_snd_1906_ = lean_ctor_get(v_x_1902_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_x_1902_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1908_ = v_x_1902_;
v_isShared_1909_ = v_isSharedCheck_1920_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_snd_1906_);
lean_inc(v_fst_1905_);
lean_dec(v_x_1902_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1920_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; uint8_t v___x_1911_; 
lean_inc(v_b_1904_);
lean_inc(v_a_1903_);
v___x_1910_ = lean_apply_2(v_f_1900_, v_a_1903_, v_b_1904_);
v___x_1911_ = lean_unbox(v___x_1910_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1912_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1901_, v_a_1903_, v_b_1904_, v_snd_1906_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 1, v___x_1912_);
v___x_1914_ = v___x_1908_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_fst_1905_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1916_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1901_, v_a_1903_, v_b_1904_, v_fst_1905_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1916_);
v___x_1918_ = v___x_1908_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_snd_1906_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition___redArg(lean_object* v_cmp_1923_, lean_object* v_f_1924_, lean_object* v_t_1925_){
_start:
{
lean_object* v___f_1926_; lean_object* v___x_1927_; lean_object* v_p_1928_; lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v___f_1926_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1926_, 0, v_f_1924_);
lean_closure_set(v___f_1926_, 1, v_cmp_1923_);
v___x_1927_ = ((lean_object*)(l_Std_ExtTreeMap_partition___redArg___closed__0));
v_p_1928_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1926_, v___x_1927_, v_t_1925_);
v_fst_1929_ = lean_ctor_get(v_p_1928_, 0);
v_snd_1930_ = lean_ctor_get(v_p_1928_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_p_1928_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v_p_1928_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_snd_1930_);
lean_inc(v_fst_1929_);
lean_dec(v_p_1928_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_fst_1929_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_snd_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition(lean_object* v_00_u03b1_1938_, lean_object* v_00_u03b2_1939_, lean_object* v_cmp_1940_, lean_object* v_inst_1941_, lean_object* v_f_1942_, lean_object* v_t_1943_){
_start:
{
lean_object* v___f_1944_; lean_object* v___x_1945_; lean_object* v_p_1946_; lean_object* v_fst_1947_; lean_object* v_snd_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v___f_1944_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1944_, 0, v_f_1942_);
lean_closure_set(v___f_1944_, 1, v_cmp_1940_);
v___x_1945_ = ((lean_object*)(l_Std_ExtTreeMap_partition___redArg___closed__0));
v_p_1946_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1944_, v___x_1945_, v_t_1943_);
v_fst_1947_ = lean_ctor_get(v_p_1946_, 0);
v_snd_1948_ = lean_ctor_get(v_p_1946_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_p_1946_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v_p_1946_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_snd_1948_);
lean_inc(v_fst_1947_);
lean_dec(v_p_1946_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_fst_1947_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_snd_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___redArg___lam__0(lean_object* v_f_1956_, lean_object* v_x_1957_, lean_object* v_k_1958_, lean_object* v_v_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = lean_apply_2(v_f_1956_, v_k_1958_, v_v_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___redArg(lean_object* v_inst_1961_, lean_object* v_f_1962_, lean_object* v_t_1963_){
_start:
{
lean_object* v___f_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___f_1964_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1964_, 0, v_f_1962_);
v___x_1965_ = lean_box(0);
v___x_1966_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1961_, v___f_1964_, v___x_1965_, v_t_1963_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM(lean_object* v_00_u03b1_1967_, lean_object* v_00_u03b2_1968_, lean_object* v_cmp_1969_, lean_object* v_m_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_f_1974_, lean_object* v_t_1975_){
_start:
{
lean_object* v___f_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___f_1976_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1976_, 0, v_f_1974_);
v___x_1977_ = lean_box(0);
v___x_1978_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1971_, v___f_1976_, v___x_1977_, v_t_1975_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___boxed(lean_object* v_00_u03b1_1979_, lean_object* v_00_u03b2_1980_, lean_object* v_cmp_1981_, lean_object* v_m_1982_, lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_inst_1985_, lean_object* v_f_1986_, lean_object* v_t_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Std_ExtTreeMap_forM(v_00_u03b1_1979_, v_00_u03b2_1980_, v_cmp_1981_, v_m_1982_, v_inst_1983_, v_inst_1984_, v_inst_1985_, v_f_1986_, v_t_1987_);
lean_dec_ref(v_cmp_1981_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg___lam__0(lean_object* v_f_1989_, lean_object* v_a_1990_, lean_object* v_b_1991_, lean_object* v_c_1992_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_apply_3(v_f_1989_, v_a_1990_, v_b_1991_, v_c_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg___lam__1(lean_object* v_toPure_1994_, lean_object* v_____do__lift_1995_){
_start:
{
lean_object* v_a_1996_; lean_object* v___x_1997_; 
v_a_1996_ = lean_ctor_get(v_____do__lift_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref(v_____do__lift_1995_);
v___x_1997_ = lean_apply_2(v_toPure_1994_, lean_box(0), v_a_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg(lean_object* v_inst_1998_, lean_object* v_f_1999_, lean_object* v_init_2000_, lean_object* v_t_2001_){
_start:
{
lean_object* v_toApplicative_2002_; lean_object* v_toBind_2003_; lean_object* v_toPure_2004_; lean_object* v___f_2005_; lean_object* v___x_2006_; lean_object* v___f_2007_; lean_object* v___x_2008_; 
v_toApplicative_2002_ = lean_ctor_get(v_inst_1998_, 0);
v_toBind_2003_ = lean_ctor_get(v_inst_1998_, 1);
lean_inc(v_toBind_2003_);
v_toPure_2004_ = lean_ctor_get(v_toApplicative_2002_, 1);
lean_inc(v_toPure_2004_);
v___f_2005_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2005_, 0, v_f_1999_);
v___x_2006_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1998_, v___f_2005_, v_init_2000_, v_t_2001_);
v___f_2007_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2007_, 0, v_toPure_2004_);
v___x_2008_ = lean_apply_4(v_toBind_2003_, lean_box(0), lean_box(0), v___x_2006_, v___f_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn(lean_object* v_00_u03b1_2009_, lean_object* v_00_u03b2_2010_, lean_object* v_cmp_2011_, lean_object* v_00_u03b4_2012_, lean_object* v_m_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_f_2017_, lean_object* v_init_2018_, lean_object* v_t_2019_){
_start:
{
lean_object* v_toApplicative_2020_; lean_object* v_toBind_2021_; lean_object* v_toPure_2022_; lean_object* v___f_2023_; lean_object* v___x_2024_; lean_object* v___f_2025_; lean_object* v___x_2026_; 
v_toApplicative_2020_ = lean_ctor_get(v_inst_2014_, 0);
v_toBind_2021_ = lean_ctor_get(v_inst_2014_, 1);
lean_inc(v_toBind_2021_);
v_toPure_2022_ = lean_ctor_get(v_toApplicative_2020_, 1);
lean_inc(v_toPure_2022_);
v___f_2023_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2023_, 0, v_f_2017_);
v___x_2024_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2014_, v___f_2023_, v_init_2018_, v_t_2019_);
v___f_2025_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2025_, 0, v_toPure_2022_);
v___x_2026_ = lean_apply_4(v_toBind_2021_, lean_box(0), lean_box(0), v___x_2024_, v___f_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___boxed(lean_object* v_00_u03b1_2027_, lean_object* v_00_u03b2_2028_, lean_object* v_cmp_2029_, lean_object* v_00_u03b4_2030_, lean_object* v_m_2031_, lean_object* v_inst_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_f_2035_, lean_object* v_init_2036_, lean_object* v_t_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Std_ExtTreeMap_forIn(v_00_u03b1_2027_, v_00_u03b2_2028_, v_cmp_2029_, v_00_u03b4_2030_, v_m_2031_, v_inst_2032_, v_inst_2033_, v_inst_2034_, v_f_2035_, v_init_2036_, v_t_2037_);
lean_dec_ref(v_cmp_2029_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2039_, lean_object* v_x_2040_, lean_object* v_k_2041_, lean_object* v_v_2042_){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v_k_2041_);
lean_ctor_set(v___x_2043_, 1, v_v_2042_);
v___x_2044_ = lean_apply_1(v_f_2039_, v___x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_2045_, lean_object* v_t_2046_, lean_object* v_f_2047_){
_start:
{
lean_object* v___f_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___f_2048_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2048_, 0, v_f_2047_);
v___x_2049_ = lean_box(0);
v___x_2050_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2045_, v___f_2048_, v___x_2049_, v_t_2046_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2051_){
_start:
{
lean_object* v___f_2052_; 
v___f_2052_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2052_, 0, v_inst_2051_);
return v___f_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2053_, lean_object* v_00_u03b2_2054_, lean_object* v_cmp_2055_, lean_object* v_m_2056_, lean_object* v_inst_2057_, lean_object* v_inst_2058_, lean_object* v_inst_2059_){
_start:
{
lean_object* v___f_2060_; 
v___f_2060_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2060_, 0, v_inst_2058_);
return v___f_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2061_, lean_object* v_00_u03b2_2062_, lean_object* v_cmp_2063_, lean_object* v_m_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_inst_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(v_00_u03b1_2061_, v_00_u03b2_2062_, v_cmp_2063_, v_m_2064_, v_inst_2065_, v_inst_2066_, v_inst_2067_);
lean_dec_ref(v_cmp_2063_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2069_, lean_object* v_a_2070_, lean_object* v_b_2071_, lean_object* v_c_2072_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2073_, 0, v_a_2070_);
lean_ctor_set(v___x_2073_, 1, v_b_2071_);
v___x_2074_ = lean_apply_2(v_f_2069_, v___x_2073_, v_c_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_2075_, lean_object* v_00_u03b2_2076_, lean_object* v_m_2077_, lean_object* v_init_2078_, lean_object* v_f_2079_){
_start:
{
lean_object* v_toApplicative_2080_; lean_object* v_toBind_2081_; lean_object* v_toPure_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___f_2085_; lean_object* v___x_2086_; 
v_toApplicative_2080_ = lean_ctor_get(v_inst_2075_, 0);
v_toBind_2081_ = lean_ctor_get(v_inst_2075_, 1);
lean_inc(v_toBind_2081_);
v_toPure_2082_ = lean_ctor_get(v_toApplicative_2080_, 1);
lean_inc(v_toPure_2082_);
v___f_2083_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2083_, 0, v_f_2079_);
v___x_2084_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2075_, v___f_2083_, v_init_2078_, v_m_2077_);
v___f_2085_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2085_, 0, v_toPure_2082_);
v___x_2086_ = lean_apply_4(v_toBind_2081_, lean_box(0), lean_box(0), v___x_2084_, v___f_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2087_){
_start:
{
lean_object* v___f_2088_; 
v___f_2088_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2088_, 0, v_inst_2087_);
return v___f_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2089_, lean_object* v_00_u03b2_2090_, lean_object* v_cmp_2091_, lean_object* v_m_2092_, lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_inst_2095_){
_start:
{
lean_object* v___f_2096_; 
v___f_2096_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2096_, 0, v_inst_2094_);
return v___f_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2097_, lean_object* v_00_u03b2_2098_, lean_object* v_cmp_2099_, lean_object* v_m_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(v_00_u03b1_2097_, v_00_u03b2_2098_, v_cmp_2099_, v_m_2100_, v_inst_2101_, v_inst_2102_, v_inst_2103_);
lean_dec_ref(v_cmp_2099_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___lam__0(lean_object* v_p_2105_, lean_object* v___x_2106_, lean_object* v___x_2107_, lean_object* v_a_2108_, lean_object* v_b_2109_, lean_object* v_acc_2110_){
_start:
{
lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2111_ = lean_apply_2(v_p_2105_, v_a_2108_, v_b_2109_);
v___x_2112_ = lean_unbox(v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2106_);
return v___x_2113_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref(v___x_2106_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2111_);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v___x_2107_);
v___x_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
return v___x_2116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2117_, lean_object* v___x_2118_, lean_object* v___x_2119_, lean_object* v_a_2120_, lean_object* v_b_2121_, lean_object* v_acc_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Std_ExtTreeMap_any___redArg___lam__0(v_p_2117_, v___x_2118_, v___x_2119_, v_a_2120_, v_b_2121_, v_acc_2122_);
lean_dec_ref(v_acc_2122_);
return v_res_2123_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_any___redArg(lean_object* v_t_2127_, lean_object* v_p_2128_){
_start:
{
lean_object* v___y_2130_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___f_2138_; lean_object* v___x_2139_; lean_object* v_a_2140_; 
v___x_2135_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2136_ = lean_box(0);
v___x_2137_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2138_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2138_, 0, v_p_2128_);
lean_closure_set(v___f_2138_, 1, v___x_2137_);
lean_closure_set(v___f_2138_, 2, v___x_2136_);
v___x_2139_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2135_, v___f_2138_, v___x_2137_, v_t_2127_);
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___y_2130_ = v_a_2140_;
goto v___jp_2129_;
v___jp_2129_:
{
lean_object* v_fst_2131_; 
v_fst_2131_ = lean_ctor_get(v___y_2130_, 0);
lean_inc(v_fst_2131_);
lean_dec_ref(v___y_2130_);
if (lean_obj_tag(v_fst_2131_) == 0)
{
uint8_t v___x_2132_; 
v___x_2132_ = 0;
return v___x_2132_;
}
else
{
lean_object* v_val_2133_; uint8_t v___x_2134_; 
v_val_2133_ = lean_ctor_get(v_fst_2131_, 0);
lean_inc(v_val_2133_);
lean_dec_ref_known(v_fst_2131_, 1);
v___x_2134_ = lean_unbox(v_val_2133_);
lean_dec(v_val_2133_);
return v___x_2134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___boxed(lean_object* v_t_2141_, lean_object* v_p_2142_){
_start:
{
uint8_t v_res_2143_; lean_object* v_r_2144_; 
v_res_2143_ = l_Std_ExtTreeMap_any___redArg(v_t_2141_, v_p_2142_);
v_r_2144_ = lean_box(v_res_2143_);
return v_r_2144_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_any(lean_object* v_00_u03b1_2145_, lean_object* v_00_u03b2_2146_, lean_object* v_cmp_2147_, lean_object* v_inst_2148_, lean_object* v_t_2149_, lean_object* v_p_2150_){
_start:
{
lean_object* v___y_2152_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___f_2160_; lean_object* v___x_2161_; lean_object* v_a_2162_; 
v___x_2157_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2158_ = lean_box(0);
v___x_2159_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2160_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2160_, 0, v_p_2150_);
lean_closure_set(v___f_2160_, 1, v___x_2159_);
lean_closure_set(v___f_2160_, 2, v___x_2158_);
v___x_2161_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2157_, v___f_2160_, v___x_2159_, v_t_2149_);
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
v___y_2152_ = v_a_2162_;
goto v___jp_2151_;
v___jp_2151_:
{
lean_object* v_fst_2153_; 
v_fst_2153_ = lean_ctor_get(v___y_2152_, 0);
lean_inc(v_fst_2153_);
lean_dec_ref(v___y_2152_);
if (lean_obj_tag(v_fst_2153_) == 0)
{
uint8_t v___x_2154_; 
v___x_2154_ = 0;
return v___x_2154_;
}
else
{
lean_object* v_val_2155_; uint8_t v___x_2156_; 
v_val_2155_ = lean_ctor_get(v_fst_2153_, 0);
lean_inc(v_val_2155_);
lean_dec_ref_known(v_fst_2153_, 1);
v___x_2156_ = lean_unbox(v_val_2155_);
lean_dec(v_val_2155_);
return v___x_2156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_00_u03b2_2164_, lean_object* v_cmp_2165_, lean_object* v_inst_2166_, lean_object* v_t_2167_, lean_object* v_p_2168_){
_start:
{
uint8_t v_res_2169_; lean_object* v_r_2170_; 
v_res_2169_ = l_Std_ExtTreeMap_any(v_00_u03b1_2163_, v_00_u03b2_2164_, v_cmp_2165_, v_inst_2166_, v_t_2167_, v_p_2168_);
lean_dec_ref(v_cmp_2165_);
v_r_2170_ = lean_box(v_res_2169_);
return v_r_2170_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___lam__0(lean_object* v_p_2171_, lean_object* v___x_2172_, lean_object* v___x_2173_, lean_object* v_a_2174_, lean_object* v_b_2175_, lean_object* v_acc_2176_){
_start:
{
lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2177_ = lean_apply_2(v_p_2171_, v_a_2174_, v_b_2175_);
v___x_2178_ = lean_unbox(v___x_2177_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
lean_dec_ref(v___x_2173_);
v___x_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
v___x_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set(v___x_2180_, 1, v___x_2172_);
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
return v___x_2181_;
}
else
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2173_);
return v___x_2182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_2183_, lean_object* v___x_2184_, lean_object* v___x_2185_, lean_object* v_a_2186_, lean_object* v_b_2187_, lean_object* v_acc_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Std_ExtTreeMap_all___redArg___lam__0(v_p_2183_, v___x_2184_, v___x_2185_, v_a_2186_, v_b_2187_, v_acc_2188_);
lean_dec_ref(v_acc_2188_);
return v_res_2189_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_all___redArg(lean_object* v_t_2190_, lean_object* v_p_2191_){
_start:
{
lean_object* v___y_2193_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___f_2201_; lean_object* v___x_2202_; lean_object* v_a_2203_; 
v___x_2198_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2199_ = lean_box(0);
v___x_2200_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2201_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2201_, 0, v_p_2191_);
lean_closure_set(v___f_2201_, 1, v___x_2199_);
lean_closure_set(v___f_2201_, 2, v___x_2200_);
v___x_2202_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2198_, v___f_2201_, v___x_2200_, v_t_2190_);
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___y_2193_ = v_a_2203_;
goto v___jp_2192_;
v___jp_2192_:
{
lean_object* v_fst_2194_; 
v_fst_2194_ = lean_ctor_get(v___y_2193_, 0);
lean_inc(v_fst_2194_);
lean_dec_ref(v___y_2193_);
if (lean_obj_tag(v_fst_2194_) == 0)
{
uint8_t v___x_2195_; 
v___x_2195_ = 1;
return v___x_2195_;
}
else
{
lean_object* v_val_2196_; uint8_t v___x_2197_; 
v_val_2196_ = lean_ctor_get(v_fst_2194_, 0);
lean_inc(v_val_2196_);
lean_dec_ref_known(v_fst_2194_, 1);
v___x_2197_ = lean_unbox(v_val_2196_);
lean_dec(v_val_2196_);
return v___x_2197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___boxed(lean_object* v_t_2204_, lean_object* v_p_2205_){
_start:
{
uint8_t v_res_2206_; lean_object* v_r_2207_; 
v_res_2206_ = l_Std_ExtTreeMap_all___redArg(v_t_2204_, v_p_2205_);
v_r_2207_ = lean_box(v_res_2206_);
return v_r_2207_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_all(lean_object* v_00_u03b1_2208_, lean_object* v_00_u03b2_2209_, lean_object* v_cmp_2210_, lean_object* v_inst_2211_, lean_object* v_t_2212_, lean_object* v_p_2213_){
_start:
{
lean_object* v___y_2215_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___f_2223_; lean_object* v___x_2224_; lean_object* v_a_2225_; 
v___x_2220_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2221_ = lean_box(0);
v___x_2222_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2223_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2223_, 0, v_p_2213_);
lean_closure_set(v___f_2223_, 1, v___x_2221_);
lean_closure_set(v___f_2223_, 2, v___x_2222_);
v___x_2224_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2220_, v___f_2223_, v___x_2222_, v_t_2212_);
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___y_2215_ = v_a_2225_;
goto v___jp_2214_;
v___jp_2214_:
{
lean_object* v_fst_2216_; 
v_fst_2216_ = lean_ctor_get(v___y_2215_, 0);
lean_inc(v_fst_2216_);
lean_dec_ref(v___y_2215_);
if (lean_obj_tag(v_fst_2216_) == 0)
{
uint8_t v___x_2217_; 
v___x_2217_ = 1;
return v___x_2217_;
}
else
{
lean_object* v_val_2218_; uint8_t v___x_2219_; 
v_val_2218_ = lean_ctor_get(v_fst_2216_, 0);
lean_inc(v_val_2218_);
lean_dec_ref_known(v_fst_2216_, 1);
v___x_2219_ = lean_unbox(v_val_2218_);
lean_dec(v_val_2218_);
return v___x_2219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___boxed(lean_object* v_00_u03b1_2226_, lean_object* v_00_u03b2_2227_, lean_object* v_cmp_2228_, lean_object* v_inst_2229_, lean_object* v_t_2230_, lean_object* v_p_2231_){
_start:
{
uint8_t v_res_2232_; lean_object* v_r_2233_; 
v_res_2232_ = l_Std_ExtTreeMap_all(v_00_u03b1_2226_, v_00_u03b2_2227_, v_cmp_2228_, v_inst_2229_, v_t_2230_, v_p_2231_);
lean_dec_ref(v_cmp_2228_);
v_r_2233_ = lean_box(v_res_2232_);
return v_r_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg___lam__0(lean_object* v_x1_2234_, lean_object* v_x2_2235_, lean_object* v_x3_2236_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2237_, 0, v_x1_2234_);
lean_ctor_set(v___x_2237_, 1, v_x3_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_2238_, lean_object* v_x2_2239_, lean_object* v_x3_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Std_ExtTreeMap_keys___redArg___lam__0(v_x1_2238_, v_x2_2239_, v_x3_2240_);
lean_dec(v_x2_2239_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg(lean_object* v_t_2243_){
_start:
{
lean_object* v___f_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___f_2244_ = ((lean_object*)(l_Std_ExtTreeMap_keys___redArg___closed__0));
v___x_2245_ = lean_box(0);
v___x_2246_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2247_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2246_, v___f_2244_, v___x_2245_, v_t_2243_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys(lean_object* v_00_u03b1_2248_, lean_object* v_00_u03b2_2249_, lean_object* v_cmp_2250_, lean_object* v_inst_2251_, lean_object* v_t_2252_){
_start:
{
lean_object* v___f_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___f_2253_ = ((lean_object*)(l_Std_ExtTreeMap_keys___redArg___closed__0));
v___x_2254_ = lean_box(0);
v___x_2255_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2256_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2255_, v___f_2253_, v___x_2254_, v_t_2252_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___boxed(lean_object* v_00_u03b1_2257_, lean_object* v_00_u03b2_2258_, lean_object* v_cmp_2259_, lean_object* v_inst_2260_, lean_object* v_t_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Std_ExtTreeMap_keys(v_00_u03b1_2257_, v_00_u03b2_2258_, v_cmp_2259_, v_inst_2260_, v_t_2261_);
lean_dec_ref(v_cmp_2259_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg___lam__0(lean_object* v_l_2263_, lean_object* v_k_2264_, lean_object* v_x_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_array_push(v_l_2263_, v_k_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_2267_, lean_object* v_k_2268_, lean_object* v_x_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Std_ExtTreeMap_keysArray___redArg___lam__0(v_l_2267_, v_k_2268_, v_x_2269_);
lean_dec(v_x_2269_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg(lean_object* v_t_2272_){
_start:
{
lean_object* v___f_2273_; lean_object* v___y_2275_; 
v___f_2273_ = ((lean_object*)(l_Std_ExtTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2272_) == 0)
{
lean_object* v_size_2278_; 
v_size_2278_ = lean_ctor_get(v_t_2272_, 0);
lean_inc(v_size_2278_);
v___y_2275_ = v_size_2278_;
goto v___jp_2274_;
}
else
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_unsigned_to_nat(0u);
v___y_2275_ = v___x_2279_;
goto v___jp_2274_;
}
v___jp_2274_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_mk_empty_array_with_capacity(v___y_2275_);
lean_dec(v___y_2275_);
v___x_2277_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2273_, v___x_2276_, v_t_2272_);
return v___x_2277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray(lean_object* v_00_u03b1_2280_, lean_object* v_00_u03b2_2281_, lean_object* v_cmp_2282_, lean_object* v_inst_2283_, lean_object* v_t_2284_){
_start:
{
lean_object* v___f_2285_; lean_object* v___y_2287_; 
v___f_2285_ = ((lean_object*)(l_Std_ExtTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2284_) == 0)
{
lean_object* v_size_2290_; 
v_size_2290_ = lean_ctor_get(v_t_2284_, 0);
lean_inc(v_size_2290_);
v___y_2287_ = v_size_2290_;
goto v___jp_2286_;
}
else
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_unsigned_to_nat(0u);
v___y_2287_ = v___x_2291_;
goto v___jp_2286_;
}
v___jp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_mk_empty_array_with_capacity(v___y_2287_);
lean_dec(v___y_2287_);
v___x_2289_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2285_, v___x_2288_, v_t_2284_);
return v___x_2289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___boxed(lean_object* v_00_u03b1_2292_, lean_object* v_00_u03b2_2293_, lean_object* v_cmp_2294_, lean_object* v_inst_2295_, lean_object* v_t_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Std_ExtTreeMap_keysArray(v_00_u03b1_2292_, v_00_u03b2_2293_, v_cmp_2294_, v_inst_2295_, v_t_2296_);
lean_dec_ref(v_cmp_2294_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg___lam__0(lean_object* v_x1_2298_, lean_object* v_x2_2299_, lean_object* v_x3_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2301_, 0, v_x2_2299_);
lean_ctor_set(v___x_2301_, 1, v_x3_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_2302_, lean_object* v_x2_2303_, lean_object* v_x3_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Std_ExtTreeMap_values___redArg___lam__0(v_x1_2302_, v_x2_2303_, v_x3_2304_);
lean_dec(v_x1_2302_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg(lean_object* v_t_2307_){
_start:
{
lean_object* v___f_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___f_2308_ = ((lean_object*)(l_Std_ExtTreeMap_values___redArg___closed__0));
v___x_2309_ = lean_box(0);
v___x_2310_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2311_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2310_, v___f_2308_, v___x_2309_, v_t_2307_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values(lean_object* v_00_u03b1_2312_, lean_object* v_00_u03b2_2313_, lean_object* v_cmp_2314_, lean_object* v_inst_2315_, lean_object* v_t_2316_){
_start:
{
lean_object* v___f_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___f_2317_ = ((lean_object*)(l_Std_ExtTreeMap_values___redArg___closed__0));
v___x_2318_ = lean_box(0);
v___x_2319_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2320_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2319_, v___f_2317_, v___x_2318_, v_t_2316_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___boxed(lean_object* v_00_u03b1_2321_, lean_object* v_00_u03b2_2322_, lean_object* v_cmp_2323_, lean_object* v_inst_2324_, lean_object* v_t_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Std_ExtTreeMap_values(v_00_u03b1_2321_, v_00_u03b2_2322_, v_cmp_2323_, v_inst_2324_, v_t_2325_);
lean_dec_ref(v_cmp_2323_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_2327_, lean_object* v_x_2328_, lean_object* v_v_2329_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = lean_array_push(v_l_2327_, v_v_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2331_, lean_object* v_x_2332_, lean_object* v_v_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Std_ExtTreeMap_valuesArray___redArg___lam__0(v_l_2331_, v_x_2332_, v_v_2333_);
lean_dec(v_x_2332_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg(lean_object* v_t_2336_){
_start:
{
lean_object* v___f_2337_; lean_object* v___y_2339_; 
v___f_2337_ = ((lean_object*)(l_Std_ExtTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2336_) == 0)
{
lean_object* v_size_2342_; 
v_size_2342_ = lean_ctor_get(v_t_2336_, 0);
lean_inc(v_size_2342_);
v___y_2339_ = v_size_2342_;
goto v___jp_2338_;
}
else
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_unsigned_to_nat(0u);
v___y_2339_ = v___x_2343_;
goto v___jp_2338_;
}
v___jp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_mk_empty_array_with_capacity(v___y_2339_);
lean_dec(v___y_2339_);
v___x_2341_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2337_, v___x_2340_, v_t_2336_);
return v___x_2341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray(lean_object* v_00_u03b1_2344_, lean_object* v_00_u03b2_2345_, lean_object* v_cmp_2346_, lean_object* v_inst_2347_, lean_object* v_t_2348_){
_start:
{
lean_object* v___f_2349_; lean_object* v___y_2351_; 
v___f_2349_ = ((lean_object*)(l_Std_ExtTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2348_) == 0)
{
lean_object* v_size_2354_; 
v_size_2354_ = lean_ctor_get(v_t_2348_, 0);
lean_inc(v_size_2354_);
v___y_2351_ = v_size_2354_;
goto v___jp_2350_;
}
else
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_unsigned_to_nat(0u);
v___y_2351_ = v___x_2355_;
goto v___jp_2350_;
}
v___jp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_mk_empty_array_with_capacity(v___y_2351_);
lean_dec(v___y_2351_);
v___x_2353_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2349_, v___x_2352_, v_t_2348_);
return v___x_2353_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_2356_, lean_object* v_00_u03b2_2357_, lean_object* v_cmp_2358_, lean_object* v_inst_2359_, lean_object* v_t_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Std_ExtTreeMap_valuesArray(v_00_u03b1_2356_, v_00_u03b2_2357_, v_cmp_2358_, v_inst_2359_, v_t_2360_);
lean_dec_ref(v_cmp_2358_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___redArg___lam__0(lean_object* v_x1_2362_, lean_object* v_x2_2363_, lean_object* v_x3_2364_){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2365_, 0, v_x1_2362_);
lean_ctor_set(v___x_2365_, 1, v_x2_2363_);
v___x_2366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
lean_ctor_set(v___x_2366_, 1, v_x3_2364_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___redArg(lean_object* v_t_2368_){
_start:
{
lean_object* v___f_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___f_2369_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___x_2370_ = lean_box(0);
v___x_2371_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2372_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2371_, v___f_2369_, v___x_2370_, v_t_2368_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList(lean_object* v_00_u03b1_2373_, lean_object* v_00_u03b2_2374_, lean_object* v_cmp_2375_, lean_object* v_inst_2376_, lean_object* v_t_2377_){
_start:
{
lean_object* v___f_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___f_2378_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___x_2379_ = lean_box(0);
v___x_2380_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2381_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2380_, v___f_2378_, v___x_2379_, v_t_2377_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___boxed(lean_object* v_00_u03b1_2382_, lean_object* v_00_u03b2_2383_, lean_object* v_cmp_2384_, lean_object* v_inst_2385_, lean_object* v_t_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Std_ExtTreeMap_toList(v_00_u03b1_2382_, v_00_u03b2_2383_, v_cmp_2384_, v_inst_2385_, v_t_2386_);
lean_dec_ref(v_cmp_2384_);
return v_res_2387_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__25, &l_Std_ExtTreeMap___auto__1___closed__25_once, _init_l_Std_ExtTreeMap___auto__1___closed__25);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_2389_, lean_object* v_a_2390_, lean_object* v_x_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_fst_2393_; lean_object* v_snd_2394_; lean_object* v_r_2395_; lean_object* v___x_2396_; 
v_fst_2393_ = lean_ctor_get(v_a_2390_, 0);
lean_inc(v_fst_2393_);
v_snd_2394_ = lean_ctor_get(v_a_2390_, 1);
lean_inc(v_snd_2394_);
lean_dec_ref(v_a_2390_);
v_r_2395_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2389_, v_fst_2393_, v_snd_2394_, v___y_2392_);
v___x_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2396_, 0, v_r_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg(lean_object* v_l_2397_, lean_object* v_cmp_2398_){
_start:
{
lean_object* v___f_2399_; lean_object* v___x_2400_; lean_object* v_r_2401_; lean_object* v___x_2402_; 
v___f_2399_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2399_, 0, v_cmp_2398_);
v___x_2400_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2401_ = lean_box(1);
v___x_2402_ = l_List_forIn_x27_loop___redArg(v___x_2400_, v___f_2399_, v_l_2397_, v_r_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg___boxed(lean_object* v_l_2403_, lean_object* v_cmp_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Std_ExtTreeMap_ofList___redArg(v_l_2403_, v_cmp_2404_);
lean_dec(v_l_2403_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList(lean_object* v_00_u03b1_2406_, lean_object* v_00_u03b2_2407_, lean_object* v_l_2408_, lean_object* v_cmp_2409_){
_start:
{
lean_object* v___f_2410_; lean_object* v___x_2411_; lean_object* v_r_2412_; lean_object* v___x_2413_; 
v___f_2410_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2410_, 0, v_cmp_2409_);
v___x_2411_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2412_ = lean_box(1);
v___x_2413_ = l_List_forIn_x27_loop___redArg(v___x_2411_, v___f_2410_, v_l_2408_, v_r_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___boxed(lean_object* v_00_u03b1_2414_, lean_object* v_00_u03b2_2415_, lean_object* v_l_2416_, lean_object* v_cmp_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Std_ExtTreeMap_ofList(v_00_u03b1_2414_, v_00_u03b2_2415_, v_l_2416_, v_cmp_2417_);
lean_dec(v_l_2416_);
return v_res_2418_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__25, &l_Std_ExtTreeMap___auto__1___closed__25_once, _init_l_Std_ExtTreeMap___auto__1___closed__25);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg___lam__0(lean_object* v_cmp_2420_, lean_object* v_a_2421_, lean_object* v_x_2422_, lean_object* v___y_2423_){
_start:
{
uint8_t v___x_2424_; 
lean_inc(v___y_2423_);
lean_inc(v_a_2421_);
lean_inc_ref(v_cmp_2420_);
v___x_2424_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2420_, v_a_2421_, v___y_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2425_ = lean_box(0);
v___x_2426_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2420_, v_a_2421_, v___x_2425_, v___y_2423_);
v___x_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
return v___x_2427_;
}
else
{
lean_object* v___x_2428_; 
lean_dec(v_a_2421_);
lean_dec_ref(v_cmp_2420_);
v___x_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___y_2423_);
return v___x_2428_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg(lean_object* v_l_2429_, lean_object* v_cmp_2430_){
_start:
{
lean_object* v___f_2431_; lean_object* v___x_2432_; lean_object* v_r_2433_; lean_object* v___x_2434_; 
v___f_2431_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2431_, 0, v_cmp_2430_);
v___x_2432_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2433_ = lean_box(1);
v___x_2434_ = l_List_forIn_x27_loop___redArg(v___x_2432_, v___f_2431_, v_l_2429_, v_r_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg___boxed(lean_object* v_l_2435_, lean_object* v_cmp_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Std_ExtTreeMap_unitOfList___redArg(v_l_2435_, v_cmp_2436_);
lean_dec(v_l_2435_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList(lean_object* v_00_u03b1_2438_, lean_object* v_l_2439_, lean_object* v_cmp_2440_){
_start:
{
lean_object* v___f_2441_; lean_object* v___x_2442_; lean_object* v_r_2443_; lean_object* v___x_2444_; 
v___f_2441_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2441_, 0, v_cmp_2440_);
v___x_2442_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2443_ = lean_box(1);
v___x_2444_ = l_List_forIn_x27_loop___redArg(v___x_2442_, v___f_2441_, v_l_2439_, v_r_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___boxed(lean_object* v_00_u03b1_2445_, lean_object* v_l_2446_, lean_object* v_cmp_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Std_ExtTreeMap_unitOfList(v_00_u03b1_2445_, v_l_2446_, v_cmp_2447_);
lean_dec(v_l_2446_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___redArg___lam__0(lean_object* v_acc_2449_, lean_object* v_k_2450_, lean_object* v_v_2451_){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v_k_2450_);
lean_ctor_set(v___x_2452_, 1, v_v_2451_);
v___x_2453_ = lean_array_push(v_acc_2449_, v___x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___redArg(lean_object* v_t_2457_){
_start:
{
lean_object* v___f_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___f_2458_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__0));
v___x_2459_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__1));
v___x_2460_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2458_, v___x_2459_, v_t_2457_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray(lean_object* v_00_u03b1_2461_, lean_object* v_00_u03b2_2462_, lean_object* v_cmp_2463_, lean_object* v_inst_2464_, lean_object* v_t_2465_){
_start:
{
lean_object* v___f_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___f_2466_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__0));
v___x_2467_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__1));
v___x_2468_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2466_, v___x_2467_, v_t_2465_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___boxed(lean_object* v_00_u03b1_2469_, lean_object* v_00_u03b2_2470_, lean_object* v_cmp_2471_, lean_object* v_inst_2472_, lean_object* v_t_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Std_ExtTreeMap_toArray(v_00_u03b1_2469_, v_00_u03b2_2470_, v_cmp_2471_, v_inst_2472_, v_t_2473_);
lean_dec_ref(v_cmp_2471_);
return v_res_2474_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__25, &l_Std_ExtTreeMap___auto__1___closed__25_once, _init_l_Std_ExtTreeMap___auto__1___closed__25);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray___redArg(lean_object* v_a_2476_, lean_object* v_cmp_2477_){
_start:
{
lean_object* v___f_2478_; lean_object* v___x_2479_; lean_object* v_r_2480_; size_t v_sz_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
v___f_2478_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2478_, 0, v_cmp_2477_);
v___x_2479_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2480_ = lean_box(1);
v_sz_2481_ = lean_array_size(v_a_2476_);
v___x_2482_ = ((size_t)0ULL);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2479_, v_a_2476_, v___f_2478_, v_sz_2481_, v___x_2482_, v_r_2480_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray(lean_object* v_00_u03b1_2484_, lean_object* v_00_u03b2_2485_, lean_object* v_a_2486_, lean_object* v_cmp_2487_){
_start:
{
lean_object* v___f_2488_; lean_object* v___x_2489_; lean_object* v_r_2490_; size_t v_sz_2491_; size_t v___x_2492_; lean_object* v___x_2493_; 
v___f_2488_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2488_, 0, v_cmp_2487_);
v___x_2489_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2490_ = lean_box(1);
v_sz_2491_ = lean_array_size(v_a_2486_);
v___x_2492_ = ((size_t)0ULL);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2489_, v_a_2486_, v___f_2488_, v_sz_2491_, v___x_2492_, v_r_2490_);
return v___x_2493_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__25, &l_Std_ExtTreeMap___auto__1___closed__25_once, _init_l_Std_ExtTreeMap___auto__1___closed__25);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray___redArg(lean_object* v_a_2495_, lean_object* v_cmp_2496_){
_start:
{
lean_object* v___f_2497_; lean_object* v___x_2498_; lean_object* v_r_2499_; size_t v_sz_2500_; size_t v___x_2501_; lean_object* v___x_2502_; 
v___f_2497_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2497_, 0, v_cmp_2496_);
v___x_2498_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2499_ = lean_box(1);
v_sz_2500_ = lean_array_size(v_a_2495_);
v___x_2501_ = ((size_t)0ULL);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2498_, v_a_2495_, v___f_2497_, v_sz_2500_, v___x_2501_, v_r_2499_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray(lean_object* v_00_u03b1_2503_, lean_object* v_a_2504_, lean_object* v_cmp_2505_){
_start:
{
lean_object* v___f_2506_; lean_object* v___x_2507_; lean_object* v_r_2508_; size_t v_sz_2509_; size_t v___x_2510_; lean_object* v___x_2511_; 
v___f_2506_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2506_, 0, v_cmp_2505_);
v___x_2507_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2508_ = lean_box(1);
v_sz_2509_ = lean_array_size(v_a_2504_);
v___x_2510_ = ((size_t)0ULL);
v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2507_, v_a_2504_, v___f_2506_, v_sz_2509_, v___x_2510_, v_r_2508_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_modify___redArg(lean_object* v_cmp_2512_, lean_object* v_t_2513_, lean_object* v_a_2514_, lean_object* v_f_2515_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2512_, v_a_2514_, v_f_2515_, v_t_2513_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_modify(lean_object* v_00_u03b1_2517_, lean_object* v_00_u03b2_2518_, lean_object* v_cmp_2519_, lean_object* v_inst_2520_, lean_object* v_t_2521_, lean_object* v_a_2522_, lean_object* v_f_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2519_, v_a_2522_, v_f_2523_, v_t_2521_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_alter___redArg(lean_object* v_cmp_2525_, lean_object* v_t_2526_, lean_object* v_a_2527_, lean_object* v_f_2528_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2525_, v_a_2527_, v_f_2528_, v_t_2526_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_alter(lean_object* v_00_u03b1_2530_, lean_object* v_00_u03b2_2531_, lean_object* v_cmp_2532_, lean_object* v_inst_2533_, lean_object* v_t_2534_, lean_object* v_a_2535_, lean_object* v_f_2536_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2532_, v_a_2535_, v_f_2536_, v_t_2534_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2538_, lean_object* v_mergeFn_2539_, lean_object* v_a_2540_, lean_object* v_x_2541_){
_start:
{
if (lean_obj_tag(v_x_2541_) == 0)
{
lean_object* v___x_2542_; 
lean_dec(v_a_2540_);
lean_dec(v_mergeFn_2539_);
v___x_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2542_, 0, v_b_u2082_2538_);
return v___x_2542_;
}
else
{
lean_object* v_val_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2551_; 
v_val_2543_ = lean_ctor_get(v_x_2541_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_x_2541_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2545_ = v_x_2541_;
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_val_2543_);
lean_dec(v_x_2541_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
v___x_2547_ = lean_apply_3(v_mergeFn_2539_, v_a_2540_, v_val_2543_, v_b_u2082_2538_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2547_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2552_, lean_object* v_cmp_2553_, lean_object* v_t_2554_, lean_object* v_a_2555_, lean_object* v_b_u2082_2556_){
_start:
{
lean_object* v___f_2557_; lean_object* v___x_2558_; 
lean_inc(v_a_2555_);
v___f_2557_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2557_, 0, v_b_u2082_2556_);
lean_closure_set(v___f_2557_, 1, v_mergeFn_2552_);
lean_closure_set(v___f_2557_, 2, v_a_2555_);
v___x_2558_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2553_, v_a_2555_, v___f_2557_, v_t_2554_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg(lean_object* v_cmp_2559_, lean_object* v_mergeFn_2560_, lean_object* v_t_u2081_2561_, lean_object* v_t_u2082_2562_){
_start:
{
lean_object* v___f_2563_; lean_object* v___x_2564_; 
v___f_2563_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2563_, 0, v_mergeFn_2560_);
lean_closure_set(v___f_2563_, 1, v_cmp_2559_);
v___x_2564_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2563_, v_t_u2081_2561_, v_t_u2082_2562_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith(lean_object* v_00_u03b1_2565_, lean_object* v_00_u03b2_2566_, lean_object* v_cmp_2567_, lean_object* v_inst_2568_, lean_object* v_mergeFn_2569_, lean_object* v_t_u2081_2570_, lean_object* v_t_u2082_2571_){
_start:
{
lean_object* v___f_2572_; lean_object* v___x_2573_; 
v___f_2572_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2572_, 0, v_mergeFn_2569_);
lean_closure_set(v___f_2572_, 1, v_cmp_2567_);
v___x_2573_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2572_, v_t_u2081_2570_, v_t_u2082_2571_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_2574_, lean_object* v_x_2575_, lean_object* v_____s_2576_){
_start:
{
lean_object* v_fst_2577_; lean_object* v_snd_2578_; lean_object* v_acc_2579_; lean_object* v___x_2580_; 
v_fst_2577_ = lean_ctor_get(v_x_2575_, 0);
lean_inc(v_fst_2577_);
v_snd_2578_ = lean_ctor_get(v_x_2575_, 1);
lean_inc(v_snd_2578_);
lean_dec_ref(v_x_2575_);
v_acc_2579_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2574_, v_fst_2577_, v_snd_2578_, v_____s_2576_);
v___x_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_acc_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany___redArg(lean_object* v_cmp_2581_, lean_object* v_inst_2582_, lean_object* v_t_2583_, lean_object* v_l_2584_){
_start:
{
lean_object* v___f_2585_; lean_object* v___x_2586_; 
v___f_2585_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2585_, 0, v_cmp_2581_);
v___x_2586_ = lean_apply_4(v_inst_2582_, lean_box(0), v_l_2584_, v_t_2583_, v___f_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany(lean_object* v_00_u03b1_2587_, lean_object* v_00_u03b2_2588_, lean_object* v_cmp_2589_, lean_object* v_inst_2590_, lean_object* v_00_u03c1_2591_, lean_object* v_inst_2592_, lean_object* v_t_2593_, lean_object* v_l_2594_){
_start:
{
lean_object* v___f_2595_; lean_object* v___x_2596_; 
v___f_2595_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2595_, 0, v_cmp_2589_);
v___x_2596_ = lean_apply_4(v_inst_2592_, lean_box(0), v_l_2594_, v_t_2593_, v___f_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_2597_, lean_object* v_a_2598_, lean_object* v_____s_2599_){
_start:
{
uint8_t v___x_2600_; 
lean_inc(v_____s_2599_);
lean_inc(v_a_2598_);
lean_inc_ref(v_cmp_2597_);
v___x_2600_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2597_, v_a_2598_, v_____s_2599_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = lean_box(0);
v___x_2602_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2597_, v_a_2598_, v___x_2601_, v_____s_2599_);
v___x_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
return v___x_2603_;
}
else
{
lean_object* v___x_2604_; 
lean_dec(v_a_2598_);
lean_dec_ref(v_cmp_2597_);
v___x_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2604_, 0, v_____s_2599_);
return v___x_2604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit___redArg(lean_object* v_cmp_2605_, lean_object* v_inst_2606_, lean_object* v_t_2607_, lean_object* v_l_2608_){
_start:
{
lean_object* v___f_2609_; lean_object* v___x_2610_; 
v___f_2609_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2609_, 0, v_cmp_2605_);
v___x_2610_ = lean_apply_4(v_inst_2606_, lean_box(0), v_l_2608_, v_t_2607_, v___f_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit(lean_object* v_00_u03b1_2611_, lean_object* v_cmp_2612_, lean_object* v_inst_2613_, lean_object* v_00_u03c1_2614_, lean_object* v_inst_2615_, lean_object* v_t_2616_, lean_object* v_l_2617_){
_start:
{
lean_object* v___f_2618_; lean_object* v___x_2619_; 
v___f_2618_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2618_, 0, v_cmp_2612_);
v___x_2619_ = lean_apply_4(v_inst_2615_, lean_box(0), v_l_2617_, v_t_2616_, v___f_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_union___redArg(lean_object* v_cmp_2620_, lean_object* v_t_u2081_2621_, lean_object* v_t_u2082_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_2620_, v_t_u2081_2621_, v_t_u2082_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_union(lean_object* v_00_u03b1_2624_, lean_object* v_00_u03b2_2625_, lean_object* v_cmp_2626_, lean_object* v_inst_2627_, lean_object* v_t_u2081_2628_, lean_object* v_t_u2082_2629_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_2626_, v_t_u2081_2628_, v_t_u2082_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instUnionOfTransCmp___redArg(lean_object* v_cmp_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_union), 6, 4);
lean_closure_set(v___x_2632_, 0, lean_box(0));
lean_closure_set(v___x_2632_, 1, lean_box(0));
lean_closure_set(v___x_2632_, 2, v_cmp_2631_);
lean_closure_set(v___x_2632_, 3, lean_box(0));
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instUnionOfTransCmp(lean_object* v_00_u03b1_2633_, lean_object* v_00_u03b2_2634_, lean_object* v_cmp_2635_, lean_object* v_inst_2636_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_union), 6, 4);
lean_closure_set(v___x_2637_, 0, lean_box(0));
lean_closure_set(v___x_2637_, 1, lean_box(0));
lean_closure_set(v___x_2637_, 2, v_cmp_2635_);
lean_closure_set(v___x_2637_, 3, lean_box(0));
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_inter___redArg(lean_object* v_cmp_2638_, lean_object* v_t_u2081_2639_, lean_object* v_t_u2082_2640_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_2638_, v_t_u2081_2639_, v_t_u2082_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_inter(lean_object* v_00_u03b1_2642_, lean_object* v_00_u03b2_2643_, lean_object* v_cmp_2644_, lean_object* v_inst_2645_, lean_object* v_t_u2081_2646_, lean_object* v_t_u2082_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_2644_, v_t_u2081_2646_, v_t_u2082_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInterOfTransCmp___redArg(lean_object* v_cmp_2649_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_inter), 6, 4);
lean_closure_set(v___x_2650_, 0, lean_box(0));
lean_closure_set(v___x_2650_, 1, lean_box(0));
lean_closure_set(v___x_2650_, 2, v_cmp_2649_);
lean_closure_set(v___x_2650_, 3, lean_box(0));
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInterOfTransCmp(lean_object* v_00_u03b1_2651_, lean_object* v_00_u03b2_2652_, lean_object* v_cmp_2653_, lean_object* v_inst_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_inter), 6, 4);
lean_closure_set(v___x_2655_, 0, lean_box(0));
lean_closure_set(v___x_2655_, 1, lean_box(0));
lean_closure_set(v___x_2655_, 2, v_cmp_2653_);
lean_closure_set(v___x_2655_, 3, lean_box(0));
return v___x_2655_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(lean_object* v_cmp_2656_, lean_object* v_inst_2657_, lean_object* v_m_u2081_2658_, lean_object* v_m_u2082_2659_){
_start:
{
uint8_t v___x_2660_; 
v___x_2660_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2656_, v_inst_2657_, v_m_u2081_2658_, v_m_u2082_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_2661_, lean_object* v_inst_2662_, lean_object* v_m_u2081_2663_, lean_object* v_m_u2082_2664_){
_start:
{
uint8_t v_res_2665_; lean_object* v_r_2666_; 
v_res_2665_ = l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(v_cmp_2661_, v_inst_2662_, v_m_u2081_2663_, v_m_u2082_2664_);
v_r_2666_ = lean_box(v_res_2665_);
return v_r_2666_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp___redArg(lean_object* v_cmp_2667_, lean_object* v_inst_2668_){
_start:
{
lean_object* v___f_2669_; 
v___f_2669_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2669_, 0, v_cmp_2667_);
lean_closure_set(v___f_2669_, 1, v_inst_2668_);
return v___f_2669_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp(lean_object* v_00_u03b1_2670_, lean_object* v_00_u03b2_2671_, lean_object* v_cmp_2672_, lean_object* v_inst_2673_, lean_object* v_inst_2674_){
_start:
{
lean_object* v___f_2675_; 
v___f_2675_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2675_, 0, v_cmp_2672_);
lean_closure_set(v___f_2675_, 1, v_inst_2674_);
return v___f_2675_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_diff___redArg(lean_object* v_cmp_2676_, lean_object* v_t_u2081_2677_, lean_object* v_t_u2082_2678_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2676_, v_t_u2081_2677_, v_t_u2082_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_diff(lean_object* v_00_u03b1_2680_, lean_object* v_00_u03b2_2681_, lean_object* v_cmp_2682_, lean_object* v_inst_2683_, lean_object* v_t_u2081_2684_, lean_object* v_t_u2082_2685_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2682_, v_t_u2081_2684_, v_t_u2082_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSDiffOfTransCmp___redArg(lean_object* v_cmp_2687_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_diff), 6, 4);
lean_closure_set(v___x_2688_, 0, lean_box(0));
lean_closure_set(v___x_2688_, 1, lean_box(0));
lean_closure_set(v___x_2688_, 2, v_cmp_2687_);
lean_closure_set(v___x_2688_, 3, lean_box(0));
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSDiffOfTransCmp(lean_object* v_00_u03b1_2689_, lean_object* v_00_u03b2_2690_, lean_object* v_cmp_2691_, lean_object* v_inst_2692_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_diff), 6, 4);
lean_closure_set(v___x_2693_, 0, lean_box(0));
lean_closure_set(v___x_2693_, 1, lean_box(0));
lean_closure_set(v___x_2693_, 2, v_cmp_2691_);
lean_closure_set(v___x_2693_, 3, lean_box(0));
return v___x_2693_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(lean_object* v_cmp_2694_, lean_object* v_inst_2695_, lean_object* v_x_2696_, lean_object* v_x_2697_){
_start:
{
uint8_t v___x_2698_; 
v___x_2698_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2694_, v_inst_2695_, v_x_2696_, v_x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_2699_, lean_object* v_inst_2700_, lean_object* v_x_2701_, lean_object* v_x_2702_){
_start:
{
uint8_t v_res_2703_; lean_object* v_r_2704_; 
v_res_2703_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(v_cmp_2699_, v_inst_2700_, v_x_2701_, v_x_2702_);
v_r_2704_ = lean_box(v_res_2703_);
return v_r_2704_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(lean_object* v_00_u03b1_2705_, lean_object* v_00_u03b2_2706_, lean_object* v_cmp_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_x_2712_, lean_object* v_x_2713_){
_start:
{
uint8_t v___x_2714_; 
v___x_2714_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2707_, v_inst_2710_, v_x_2712_, v_x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_2715_, lean_object* v_00_u03b2_2716_, lean_object* v_cmp_2717_, lean_object* v_inst_2718_, lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_x_2722_, lean_object* v_x_2723_){
_start:
{
uint8_t v_res_2724_; lean_object* v_r_2725_; 
v_res_2724_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(v_00_u03b1_2715_, v_00_u03b2_2716_, v_cmp_2717_, v_inst_2718_, v_inst_2719_, v_inst_2720_, v_inst_2721_, v_x_2722_, v_x_2723_);
v_r_2725_ = lean_box(v_res_2724_);
return v_r_2725_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_2726_, lean_object* v_a_2727_, lean_object* v_____s_2728_){
_start:
{
lean_object* v_acc_2729_; lean_object* v___x_2730_; 
v_acc_2729_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2726_, v_a_2727_, v_____s_2728_);
v___x_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_acc_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany___redArg(lean_object* v_cmp_2731_, lean_object* v_inst_2732_, lean_object* v_t_2733_, lean_object* v_l_2734_){
_start:
{
lean_object* v___f_2735_; lean_object* v___x_2736_; 
v___f_2735_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2735_, 0, v_cmp_2731_);
v___x_2736_ = lean_apply_4(v_inst_2732_, lean_box(0), v_l_2734_, v_t_2733_, v___f_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany(lean_object* v_00_u03b1_2737_, lean_object* v_00_u03b2_2738_, lean_object* v_cmp_2739_, lean_object* v_inst_2740_, lean_object* v_00_u03c1_2741_, lean_object* v_inst_2742_, lean_object* v_t_2743_, lean_object* v_l_2744_){
_start:
{
lean_object* v___f_2745_; lean_object* v___x_2746_; 
v___f_2745_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2745_, 0, v_cmp_2739_);
v___x_2746_ = lean_apply_4(v_inst_2742_, lean_box(0), v_l_2744_, v_t_2743_, v___f_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_2750_, lean_object* v___x_2751_, lean_object* v_m_2752_, lean_object* v_prec_2753_){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2754_ = ((lean_object*)(l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_2755_ = lean_box(0);
v___x_2756_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2757_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2756_, v___f_2750_, v___x_2755_, v_m_2752_);
v___x_2758_ = l_List_repr___redArg(v___x_2751_, v___x_2757_);
v___x_2759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2754_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = l_Repr_addAppParen(v___x_2759_, v_prec_2753_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_2761_, lean_object* v___x_2762_, lean_object* v_m_2763_, lean_object* v_prec_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(v___f_2761_, v___x_2762_, v_m_2763_, v_prec_2764_);
lean_dec(v_prec_2764_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg(lean_object* v_inst_2766_, lean_object* v_inst_2767_){
_start:
{
lean_object* v___f_2768_; lean_object* v___f_2769_; lean_object* v___x_2770_; lean_object* v___f_2771_; 
v___f_2768_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___f_2769_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2769_, 0, v_inst_2767_);
v___x_2770_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2770_, 0, lean_box(0));
lean_closure_set(v___x_2770_, 1, lean_box(0));
lean_closure_set(v___x_2770_, 2, v_inst_2766_);
lean_closure_set(v___x_2770_, 3, v___f_2769_);
v___f_2771_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2771_, 0, v___f_2768_);
lean_closure_set(v___f_2771_, 1, v___x_2770_);
return v___f_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp(lean_object* v_00_u03b1_2772_, lean_object* v_00_u03b2_2773_, lean_object* v_cmp_2774_, lean_object* v_inst_2775_, lean_object* v_inst_2776_, lean_object* v_inst_2777_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg(v_inst_2776_, v_inst_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_2779_, lean_object* v_00_u03b2_2780_, lean_object* v_cmp_2781_, lean_object* v_inst_2782_, lean_object* v_inst_2783_, lean_object* v_inst_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Std_ExtTreeMap_instReprOfTransCmp(v_00_u03b1_2779_, v_00_u03b2_2780_, v_cmp_2781_, v_inst_2782_, v_inst_2783_, v_inst_2784_);
lean_dec_ref(v_cmp_2781_);
return v_res_2785_;
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
