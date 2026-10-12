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
lean_object* l_Std_ExtTreeMap_empty___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(1);
return v___x_74_;
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_75_;
v_res_75_ = l_Std_ExtTreeMap_empty___redArg();
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___redArg___boxed(lean_object* v___dummy_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_ExtTreeMap_empty___redArg();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty(lean_object* v_00_u03b1_78_, lean_object* v_00_u03b2_79_, lean_object* v_cmp_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(1);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___boxed(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_cmp_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Std_ExtTreeMap_empty(v_00_u03b1_82_, v_00_u03b2_83_, v_cmp_84_);
lean_dec_ref(v_cmp_84_);
return v_res_85_;
}
}
lean_object* l_Std_ExtTreeMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_box(1);
return v___x_87_;
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_88_;
v_res_88_ = l_Std_ExtTreeMap_instEmptyCollection___redArg();
stack->m_obj
 = v_res_88_;
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
lean_object* l_Std_ExtTreeMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_box(1);
return v___x_100_;
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_101_;
v_res_101_ = l_Std_ExtTreeMap_instInhabited___redArg();
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited___redArg___boxed(lean_object* v___dummy_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Std_ExtTreeMap_instInhabited___redArg();
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited(lean_object* v_00_u03b1_104_, lean_object* v_00_u03b2_105_, lean_object* v_cmp_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_box(1);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited___boxed(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_cmp_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Std_ExtTreeMap_instInhabited(v_00_u03b1_108_, v_00_u03b2_109_, v_cmp_110_);
lean_dec_ref(v_cmp_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insert___redArg(lean_object* v_cmp_112_, lean_object* v_l_113_, lean_object* v_a_114_, lean_object* v_b_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_112_, v_a_114_, v_b_115_, v_l_113_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insert(lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_, lean_object* v_cmp_119_, lean_object* v_inst_120_, lean_object* v_l_121_, lean_object* v_a_122_, lean_object* v_b_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_119_, v_a_122_, v_b_123_, v_l_121_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0(lean_object* v_cmp_125_, lean_object* v_e_126_){
_start:
{
lean_object* v_fst_127_; lean_object* v_snd_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_fst_127_ = lean_ctor_get(v_e_126_, 0);
lean_inc(v_fst_127_);
v_snd_128_ = lean_ctor_get(v_e_126_, 1);
lean_inc(v_snd_128_);
lean_dec_ref(v_e_126_);
v___x_129_ = lean_box(1);
v___x_130_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_125_, v_fst_127_, v_snd_128_, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg(lean_object* v_cmp_131_){
_start:
{
lean_object* v___f_132_; 
v___f_132_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_132_, 0, v_cmp_131_);
return v___f_132_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_cmp_135_, lean_object* v_inst_136_){
_start:
{
lean_object* v___f_137_; 
v___f_137_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_137_, 0, v_cmp_135_);
return v___f_137_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0(lean_object* v_cmp_138_, lean_object* v_e_139_, lean_object* v_s_140_){
_start:
{
lean_object* v_fst_141_; lean_object* v_snd_142_; lean_object* v___x_143_; 
v_fst_141_ = lean_ctor_get(v_e_139_, 0);
lean_inc(v_fst_141_);
v_snd_142_ = lean_ctor_get(v_e_139_, 1);
lean_inc(v_snd_142_);
lean_dec_ref(v_e_139_);
v___x_143_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_138_, v_fst_141_, v_snd_142_, v_s_140_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg(lean_object* v_cmp_144_){
_start:
{
lean_object* v___f_145_; 
v___f_145_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_145_, 0, v_cmp_144_);
return v___f_145_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp(lean_object* v_00_u03b1_146_, lean_object* v_00_u03b2_147_, lean_object* v_cmp_148_, lean_object* v_inst_149_){
_start:
{
lean_object* v___f_150_; 
v___f_150_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_150_, 0, v_cmp_148_);
return v___f_150_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertIfNew___redArg(lean_object* v_cmp_151_, lean_object* v_t_152_, lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
uint8_t v___x_155_; 
lean_inc(v_t_152_);
lean_inc(v_a_153_);
lean_inc_ref(v_cmp_151_);
v___x_155_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_151_, v_a_153_, v_t_152_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_151_, v_a_153_, v_b_154_, v_t_152_);
return v___x_156_;
}
else
{
lean_dec(v_b_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_cmp_151_);
return v_t_152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertIfNew(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_cmp_159_, lean_object* v_inst_160_, lean_object* v_t_161_, lean_object* v_a_162_, lean_object* v_b_163_){
_start:
{
uint8_t v___x_164_; 
lean_inc(v_t_161_);
lean_inc(v_a_162_);
lean_inc_ref(v_cmp_159_);
v___x_164_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_159_, v_a_162_, v_t_161_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
v___x_165_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_159_, v_a_162_, v_b_163_, v_t_161_);
return v___x_165_;
}
else
{
lean_dec(v_b_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_cmp_159_);
return v_t_161_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsert___redArg(lean_object* v_cmp_166_, lean_object* v_t_167_, lean_object* v_a_168_, lean_object* v_b_169_){
_start:
{
lean_object* v_sz_170_; lean_object* v_m_171_; lean_object* v___y_173_; 
v_sz_170_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_167_);
v_m_171_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_166_, v_a_168_, v_b_169_, v_t_167_);
if (lean_obj_tag(v_m_171_) == 0)
{
lean_object* v_size_177_; 
v_size_177_ = lean_ctor_get(v_m_171_, 0);
lean_inc(v_size_177_);
v___y_173_ = v_size_177_;
goto v___jp_172_;
}
else
{
lean_object* v___x_178_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___y_173_ = v___x_178_;
goto v___jp_172_;
}
v___jp_172_:
{
uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_nat_dec_eq(v_sz_170_, v___y_173_);
lean_dec(v___y_173_);
lean_dec(v_sz_170_);
v___x_175_ = lean_box(v___x_174_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_m_171_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsert(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_cmp_181_, lean_object* v_inst_182_, lean_object* v_t_183_, lean_object* v_a_184_, lean_object* v_b_185_){
_start:
{
lean_object* v_sz_186_; lean_object* v_m_187_; lean_object* v___y_189_; 
v_sz_186_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_183_);
v_m_187_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_181_, v_a_184_, v_b_185_, v_t_183_);
if (lean_obj_tag(v_m_187_) == 0)
{
lean_object* v_size_193_; 
v_size_193_ = lean_ctor_get(v_m_187_, 0);
lean_inc(v_size_193_);
v___y_189_ = v_size_193_;
goto v___jp_188_;
}
else
{
lean_object* v___x_194_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___y_189_ = v___x_194_;
goto v___jp_188_;
}
v___jp_188_:
{
uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_nat_dec_eq(v_sz_186_, v___y_189_);
lean_dec(v___y_189_);
lean_dec(v_sz_186_);
v___x_191_ = lean_box(v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_m_187_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_195_, lean_object* v_t_196_, lean_object* v_a_197_, lean_object* v_b_198_){
_start:
{
uint8_t v___x_199_; 
lean_inc(v_t_196_);
lean_inc(v_a_197_);
lean_inc_ref(v_cmp_195_);
v___x_199_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_195_, v_a_197_, v_t_196_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_195_, v_a_197_, v_b_198_, v_t_196_);
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
lean_dec_ref(v_cmp_195_);
v___x_203_ = lean_box(v___x_199_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_t_196_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_cmp_207_, lean_object* v_inst_208_, lean_object* v_t_209_, lean_object* v_a_210_, lean_object* v_b_211_){
_start:
{
uint8_t v___x_212_; 
lean_inc(v_t_209_);
lean_inc(v_a_210_);
lean_inc_ref(v_cmp_207_);
v___x_212_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_207_, v_a_210_, v_t_209_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_207_, v_a_210_, v_b_211_, v_t_209_);
v___x_214_ = lean_box(v___x_212_);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec(v_b_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_cmp_207_);
v___x_216_ = lean_box(v___x_212_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v_t_209_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_218_, lean_object* v_t_219_, lean_object* v_a_220_, lean_object* v_b_221_){
_start:
{
lean_object* v___x_222_; 
lean_inc(v_a_220_);
lean_inc(v_t_219_);
lean_inc_ref(v_cmp_218_);
v___x_222_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_218_, v_t_219_, v_a_220_);
if (lean_obj_tag(v___x_222_) == 0)
{
uint8_t v___x_223_; 
lean_inc(v_t_219_);
lean_inc(v_a_220_);
lean_inc_ref(v_cmp_218_);
v___x_223_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_218_, v_a_220_, v_t_219_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_218_, v_a_220_, v_b_221_, v_t_219_);
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
lean_dec_ref(v_cmp_218_);
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
lean_dec_ref(v_cmp_218_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_222_);
lean_ctor_set(v___x_227_, 1, v_t_219_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_228_, lean_object* v_00_u03b2_229_, lean_object* v_cmp_230_, lean_object* v_inst_231_, lean_object* v_t_232_, lean_object* v_a_233_, lean_object* v_b_234_){
_start:
{
lean_object* v___x_235_; 
lean_inc(v_a_233_);
lean_inc(v_t_232_);
lean_inc_ref(v_cmp_230_);
v___x_235_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_230_, v_t_232_, v_a_233_);
if (lean_obj_tag(v___x_235_) == 0)
{
uint8_t v___x_236_; 
lean_inc(v_t_232_);
lean_inc(v_a_233_);
lean_inc_ref(v_cmp_230_);
v___x_236_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_230_, v_a_233_, v_t_232_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_230_, v_a_233_, v_b_234_, v_t_232_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_235_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; 
lean_dec(v_b_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_cmp_230_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_235_);
lean_ctor_set(v___x_239_, 1, v_t_232_);
return v___x_239_;
}
}
else
{
lean_object* v___x_240_; 
lean_dec(v_b_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_cmp_230_);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_235_);
lean_ctor_set(v___x_240_, 1, v_t_232_);
return v___x_240_;
}
}
}
uint8_t l_Std_ExtTreeMap_contains___redArg(lean_object* v_cmp_241_, lean_object* v_l_242_, lean_object* v_a_243_){
_start:
{
uint8_t v___x_244_; 
v___x_244_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_241_, v_a_243_, v_l_242_);
return v___x_244_;
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_241_ = stack[0].m_obj;
lean_object* v_l_242_ = stack[1].m_obj;
lean_object* v_a_243_ = stack[2].m_obj;
uint8_t v_res_245_;
v_res_245_ = l_Std_ExtTreeMap_contains___redArg(v_cmp_241_, v_l_242_, v_a_243_);
stack->m_num = v_res_245_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_contains___redArg___boxed(lean_object* v_cmp_246_, lean_object* v_l_247_, lean_object* v_a_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Std_ExtTreeMap_contains___redArg(v_cmp_246_, v_l_247_, v_a_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
uint8_t l_Std_ExtTreeMap_contains(lean_object* v_00_u03b1_251_, lean_object* v_00_u03b2_252_, lean_object* v_cmp_253_, lean_object* v_inst_254_, lean_object* v_l_255_, lean_object* v_a_256_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_253_, v_a_256_, v_l_255_);
return v___x_257_;
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_253_ = stack[2].m_obj;
lean_object* v_l_255_ = stack[4].m_obj;
lean_object* v_a_256_ = stack[5].m_obj;
uint8_t v_res_258_;
v_res_258_ = l_Std_ExtTreeMap_contains(lean_box(0), lean_box(0), v_cmp_253_, lean_box(0), v_l_255_, v_a_256_);
stack->m_num = v_res_258_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_contains___boxed(lean_object* v_00_u03b1_259_, lean_object* v_00_u03b2_260_, lean_object* v_cmp_261_, lean_object* v_inst_262_, lean_object* v_l_263_, lean_object* v_a_264_){
_start:
{
uint8_t v_res_265_; lean_object* v_r_266_; 
v_res_265_ = l_Std_ExtTreeMap_contains(v_00_u03b1_259_, v_00_u03b2_260_, v_cmp_261_, v_inst_262_, v_l_263_, v_a_264_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg(){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_269_;
v_res_269_ = l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg();
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg___boxed(lean_object* v___dummy_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_ExtTreeMap_instMembershipOfTransCmp___redArg();
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp(lean_object* v_00_u03b1_272_, lean_object* v_00_u03b2_273_, lean_object* v_cmp_274_, lean_object* v_inst_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_box(0);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___boxed(lean_object* v_00_u03b1_277_, lean_object* v_00_u03b2_278_, lean_object* v_cmp_279_, lean_object* v_inst_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Std_ExtTreeMap_instMembershipOfTransCmp(v_00_u03b1_277_, v_00_u03b2_278_, v_cmp_279_, v_inst_280_);
lean_dec_ref(v_cmp_279_);
return v_res_281_;
}
}
uint8_t l_Std_ExtTreeMap_instDecidableMem___redArg(lean_object* v_cmp_282_, lean_object* v_m_283_, lean_object* v_a_284_){
_start:
{
uint8_t v___x_285_; 
v___x_285_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_282_, v_a_284_, v_m_283_);
return v___x_285_;
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_282_ = stack[0].m_obj;
lean_object* v_m_283_ = stack[1].m_obj;
lean_object* v_a_284_ = stack[2].m_obj;
uint8_t v_res_286_;
v_res_286_ = l_Std_ExtTreeMap_instDecidableMem___redArg(v_cmp_282_, v_m_283_, v_a_284_);
stack->m_num = v_res_286_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_287_, lean_object* v_m_288_, lean_object* v_a_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Std_ExtTreeMap_instDecidableMem___redArg(v_cmp_287_, v_m_288_, v_a_289_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
uint8_t l_Std_ExtTreeMap_instDecidableMem(lean_object* v_00_u03b1_292_, lean_object* v_00_u03b2_293_, lean_object* v_cmp_294_, lean_object* v_inst_295_, lean_object* v_m_296_, lean_object* v_a_297_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_294_, v_a_297_, v_m_296_);
return v___x_298_;
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_294_ = stack[2].m_obj;
lean_object* v_m_296_ = stack[4].m_obj;
lean_object* v_a_297_ = stack[5].m_obj;
uint8_t v_res_299_;
v_res_299_ = l_Std_ExtTreeMap_instDecidableMem(lean_box(0), lean_box(0), v_cmp_294_, lean_box(0), v_m_296_, v_a_297_);
stack->m_num = v_res_299_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_300_, lean_object* v_00_u03b2_301_, lean_object* v_cmp_302_, lean_object* v_inst_303_, lean_object* v_m_304_, lean_object* v_a_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Std_ExtTreeMap_instDecidableMem(v_00_u03b1_300_, v_00_u03b2_301_, v_cmp_302_, v_inst_303_, v_m_304_, v_a_305_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___redArg(lean_object* v_t_308_){
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
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___redArg___boxed(lean_object* v_t_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_ExtTreeMap_size___redArg(v_t_311_);
lean_dec(v_t_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size(lean_object* v_00_u03b1_313_, lean_object* v_00_u03b2_314_, lean_object* v_cmp_315_, lean_object* v_t_316_){
_start:
{
if (lean_obj_tag(v_t_316_) == 0)
{
lean_object* v_size_317_; 
v_size_317_ = lean_ctor_get(v_t_316_, 0);
lean_inc(v_size_317_);
return v_size_317_;
}
else
{
lean_object* v___x_318_; 
v___x_318_ = lean_unsigned_to_nat(0u);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___boxed(lean_object* v_00_u03b1_319_, lean_object* v_00_u03b2_320_, lean_object* v_cmp_321_, lean_object* v_t_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_ExtTreeMap_size(v_00_u03b1_319_, v_00_u03b2_320_, v_cmp_321_, v_t_322_);
lean_dec(v_t_322_);
lean_dec_ref(v_cmp_321_);
return v_res_323_;
}
}
uint8_t l_Std_ExtTreeMap_isEmpty___redArg(lean_object* v_t_324_){
_start:
{
if (lean_obj_tag(v_t_324_) == 0)
{
uint8_t v___x_325_; 
v___x_325_ = 0;
return v___x_325_;
}
else
{
uint8_t v___x_326_; 
v___x_326_ = 1;
return v___x_326_;
}
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_324_ = stack[0].m_obj;
uint8_t v_res_327_;
v_res_327_ = l_Std_ExtTreeMap_isEmpty___redArg(v_t_324_);
stack->m_num = v_res_327_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_isEmpty___redArg___boxed(lean_object* v_t_328_){
_start:
{
uint8_t v_res_329_; lean_object* v_r_330_; 
v_res_329_ = l_Std_ExtTreeMap_isEmpty___redArg(v_t_328_);
lean_dec(v_t_328_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
uint8_t l_Std_ExtTreeMap_isEmpty(lean_object* v_00_u03b1_331_, lean_object* v_00_u03b2_332_, lean_object* v_cmp_333_, lean_object* v_t_334_){
_start:
{
if (lean_obj_tag(v_t_334_) == 0)
{
uint8_t v___x_335_; 
v___x_335_ = 0;
return v___x_335_;
}
else
{
uint8_t v___x_336_; 
v___x_336_ = 1;
return v___x_336_;
}
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_333_ = stack[2].m_obj;
lean_object* v_t_334_ = stack[3].m_obj;
uint8_t v_res_337_;
v_res_337_ = l_Std_ExtTreeMap_isEmpty(lean_box(0), lean_box(0), v_cmp_333_, v_t_334_);
stack->m_num = v_res_337_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_338_, lean_object* v_00_u03b2_339_, lean_object* v_cmp_340_, lean_object* v_t_341_){
_start:
{
uint8_t v_res_342_; lean_object* v_r_343_; 
v_res_342_ = l_Std_ExtTreeMap_isEmpty(v_00_u03b1_338_, v_00_u03b2_339_, v_cmp_340_, v_t_341_);
lean_dec(v_t_341_);
lean_dec_ref(v_cmp_340_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_erase___redArg(lean_object* v_cmp_344_, lean_object* v_t_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_344_, v_a_346_, v_t_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_erase(lean_object* v_00_u03b1_348_, lean_object* v_00_u03b2_349_, lean_object* v_cmp_350_, lean_object* v_inst_351_, lean_object* v_t_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_350_, v_a_353_, v_t_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x3f___redArg(lean_object* v_cmp_355_, lean_object* v_t_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_355_, v_t_356_, v_a_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x3f(lean_object* v_00_u03b1_359_, lean_object* v_00_u03b2_360_, lean_object* v_cmp_361_, lean_object* v_inst_362_, lean_object* v_t_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_361_, v_t_363_, v_a_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get___redArg(lean_object* v_cmp_366_, lean_object* v_t_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_366_, v_t_367_, v_a_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_cmp_372_, lean_object* v_inst_373_, lean_object* v_t_374_, lean_object* v_a_375_, lean_object* v_h_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_372_, v_t_374_, v_a_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___redArg(lean_object* v_cmp_378_, lean_object* v_inst_379_, lean_object* v_t_380_, lean_object* v_a_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_378_, v_inst_379_, v_t_380_, v_a_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___redArg___boxed(lean_object* v_cmp_383_, lean_object* v_inst_384_, lean_object* v_t_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_ExtTreeMap_get_x21___redArg(v_cmp_383_, v_inst_384_, v_t_385_, v_a_386_);
lean_dec(v_inst_384_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_cmp_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_t_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_390_, v_inst_392_, v_t_393_, v_a_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___boxed(lean_object* v_00_u03b1_396_, lean_object* v_00_u03b2_397_, lean_object* v_cmp_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_t_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_ExtTreeMap_get_x21(v_00_u03b1_396_, v_00_u03b2_397_, v_cmp_398_, v_inst_399_, v_inst_400_, v_t_401_, v_a_402_);
lean_dec(v_inst_400_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg(lean_object* v_cmp_404_, lean_object* v_t_405_, lean_object* v_a_406_, lean_object* v_fallback_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_404_, v_t_405_, v_a_406_, v_fallback_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg___boxed(lean_object* v_cmp_409_, lean_object* v_t_410_, lean_object* v_a_411_, lean_object* v_fallback_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_ExtTreeMap_getD___redArg(v_cmp_409_, v_t_410_, v_a_411_, v_fallback_412_);
lean_dec(v_fallback_412_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD(lean_object* v_00_u03b1_414_, lean_object* v_00_u03b2_415_, lean_object* v_cmp_416_, lean_object* v_inst_417_, lean_object* v_t_418_, lean_object* v_a_419_, lean_object* v_fallback_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_416_, v_t_418_, v_a_419_, v_fallback_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___boxed(lean_object* v_00_u03b1_422_, lean_object* v_00_u03b2_423_, lean_object* v_cmp_424_, lean_object* v_inst_425_, lean_object* v_t_426_, lean_object* v_a_427_, lean_object* v_fallback_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_ExtTreeMap_getD(v_00_u03b1_422_, v_00_u03b2_423_, v_cmp_424_, v_inst_425_, v_t_426_, v_a_427_, v_fallback_428_);
lean_dec(v_fallback_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_cmp_430_, lean_object* v_m_431_, lean_object* v_a_432_, lean_object* v_h_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_430_, v_m_431_, v_a_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_cmp_435_, lean_object* v_m_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_435_, v_m_436_, v_a_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_cmp_439_, lean_object* v_inst_440_, lean_object* v_m_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_439_, v_inst_440_, v_m_441_, v_a_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_cmp_444_, lean_object* v_inst_445_, lean_object* v_m_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(v_cmp_444_, v_inst_445_, v_m_446_, v_a_447_);
lean_dec(v_inst_445_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(lean_object* v_cmp_449_){
_start:
{
lean_object* v___f_450_; lean_object* v___f_451_; lean_object* v___f_452_; lean_object* v___x_453_; 
lean_inc_ref_n(v_cmp_449_, 2);
v___f_450_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0), 4, 1);
lean_closure_set(v___f_450_, 0, v_cmp_449_);
v___f_451_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1), 3, 1);
lean_closure_set(v___f_451_, 0, v_cmp_449_);
v___f_452_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_452_, 0, v_cmp_449_);
v___x_453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_453_, 0, v___f_450_);
lean_ctor_set(v___x_453_, 1, v___f_451_);
lean_ctor_set(v___x_453_, 2, v___f_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem(lean_object* v_00_u03b1_454_, lean_object* v_00_u03b2_455_, lean_object* v_cmp_456_, lean_object* v_inst_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(v_cmp_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f___redArg(lean_object* v_cmp_459_, lean_object* v_t_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_459_, v_t_460_, v_a_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f(lean_object* v_00_u03b1_463_, lean_object* v_00_u03b2_464_, lean_object* v_cmp_465_, lean_object* v_inst_466_, lean_object* v_t_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_465_, v_t_467_, v_a_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey___redArg(lean_object* v_cmp_470_, lean_object* v_t_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_470_, v_t_471_, v_a_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_cmp_476_, lean_object* v_inst_477_, lean_object* v_t_478_, lean_object* v_a_479_, lean_object* v_h_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_476_, v_t_478_, v_a_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___redArg(lean_object* v_cmp_482_, lean_object* v_inst_483_, lean_object* v_t_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_482_, v_t_484_, v_a_485_, v_inst_483_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___redArg___boxed(lean_object* v_cmp_487_, lean_object* v_inst_488_, lean_object* v_t_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_ExtTreeMap_getKey_x21___redArg(v_cmp_487_, v_inst_488_, v_t_489_, v_a_490_);
lean_dec(v_inst_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21(lean_object* v_00_u03b1_492_, lean_object* v_00_u03b2_493_, lean_object* v_cmp_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_t_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_494_, v_t_497_, v_a_498_, v_inst_496_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___boxed(lean_object* v_00_u03b1_500_, lean_object* v_00_u03b2_501_, lean_object* v_cmp_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_t_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_ExtTreeMap_getKey_x21(v_00_u03b1_500_, v_00_u03b2_501_, v_cmp_502_, v_inst_503_, v_inst_504_, v_t_505_, v_a_506_);
lean_dec(v_inst_504_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___redArg(lean_object* v_cmp_508_, lean_object* v_t_509_, lean_object* v_a_510_, lean_object* v_fallback_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_508_, v_t_509_, v_a_510_, v_fallback_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_513_, lean_object* v_t_514_, lean_object* v_a_515_, lean_object* v_fallback_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_ExtTreeMap_getKeyD___redArg(v_cmp_513_, v_t_514_, v_a_515_, v_fallback_516_);
lean_dec(v_fallback_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD(lean_object* v_00_u03b1_518_, lean_object* v_00_u03b2_519_, lean_object* v_cmp_520_, lean_object* v_inst_521_, lean_object* v_t_522_, lean_object* v_a_523_, lean_object* v_fallback_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_520_, v_t_522_, v_a_523_, v_fallback_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_526_, lean_object* v_00_u03b2_527_, lean_object* v_cmp_528_, lean_object* v_inst_529_, lean_object* v_t_530_, lean_object* v_a_531_, lean_object* v_fallback_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_ExtTreeMap_getKeyD(v_00_u03b1_526_, v_00_u03b2_527_, v_cmp_528_, v_inst_529_, v_t_530_, v_a_531_, v_fallback_532_);
lean_dec(v_fallback_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___redArg(lean_object* v_t_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_ExtTreeMap_minEntry_x3f___redArg(v_t_536_);
lean_dec(v_t_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f(lean_object* v_00_u03b1_538_, lean_object* v_00_u03b2_539_, lean_object* v_cmp_540_, lean_object* v_inst_541_, lean_object* v_t_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_, lean_object* v_cmp_546_, lean_object* v_inst_547_, lean_object* v_t_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_ExtTreeMap_minEntry_x3f(v_00_u03b1_544_, v_00_u03b2_545_, v_cmp_546_, v_inst_547_, v_t_548_);
lean_dec(v_t_548_);
lean_dec_ref(v_cmp_546_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___redArg(lean_object* v_t_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___redArg___boxed(lean_object* v_t_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_ExtTreeMap_minEntry___redArg(v_t_552_);
lean_dec(v_t_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry(lean_object* v_00_u03b1_554_, lean_object* v_00_u03b2_555_, lean_object* v_cmp_556_, lean_object* v_inst_557_, lean_object* v_t_558_, lean_object* v_h_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___boxed(lean_object* v_00_u03b1_561_, lean_object* v_00_u03b2_562_, lean_object* v_cmp_563_, lean_object* v_inst_564_, lean_object* v_t_565_, lean_object* v_h_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_ExtTreeMap_minEntry(v_00_u03b1_561_, v_00_u03b2_562_, v_cmp_563_, v_inst_564_, v_t_565_, v_h_566_);
lean_dec(v_t_565_);
lean_dec_ref(v_cmp_563_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___redArg(lean_object* v_inst_568_, lean_object* v_t_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_568_, v_t_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_571_, lean_object* v_t_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_ExtTreeMap_minEntry_x21___redArg(v_inst_571_, v_t_572_);
lean_dec(v_t_572_);
lean_dec_ref(v_inst_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21(lean_object* v_00_u03b1_574_, lean_object* v_00_u03b2_575_, lean_object* v_cmp_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_t_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_578_, v_t_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_581_, lean_object* v_00_u03b2_582_, lean_object* v_cmp_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_t_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_ExtTreeMap_minEntry_x21(v_00_u03b1_581_, v_00_u03b2_582_, v_cmp_583_, v_inst_584_, v_inst_585_, v_t_586_);
lean_dec(v_t_586_);
lean_dec_ref(v_inst_585_);
lean_dec_ref(v_cmp_583_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___redArg(lean_object* v_t_588_, lean_object* v_fallback_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_588_, v_fallback_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___redArg___boxed(lean_object* v_t_591_, lean_object* v_fallback_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Std_ExtTreeMap_minEntryD___redArg(v_t_591_, v_fallback_592_);
lean_dec_ref(v_fallback_592_);
lean_dec(v_t_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD(lean_object* v_00_u03b1_594_, lean_object* v_00_u03b2_595_, lean_object* v_cmp_596_, lean_object* v_inst_597_, lean_object* v_t_598_, lean_object* v_fallback_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_598_, v_fallback_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v_cmp_603_, lean_object* v_inst_604_, lean_object* v_t_605_, lean_object* v_fallback_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_ExtTreeMap_minEntryD(v_00_u03b1_601_, v_00_u03b2_602_, v_cmp_603_, v_inst_604_, v_t_605_, v_fallback_606_);
lean_dec_ref(v_fallback_606_);
lean_dec(v_t_605_);
lean_dec_ref(v_cmp_603_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___redArg(lean_object* v_t_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_ExtTreeMap_maxEntry_x3f___redArg(v_t_610_);
lean_dec(v_t_610_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_612_, lean_object* v_00_u03b2_613_, lean_object* v_cmp_614_, lean_object* v_inst_615_, lean_object* v_t_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_618_, lean_object* v_00_u03b2_619_, lean_object* v_cmp_620_, lean_object* v_inst_621_, lean_object* v_t_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_ExtTreeMap_maxEntry_x3f(v_00_u03b1_618_, v_00_u03b2_619_, v_cmp_620_, v_inst_621_, v_t_622_);
lean_dec(v_t_622_);
lean_dec_ref(v_cmp_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___redArg(lean_object* v_t_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___redArg___boxed(lean_object* v_t_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_ExtTreeMap_maxEntry___redArg(v_t_626_);
lean_dec(v_t_626_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry(lean_object* v_00_u03b1_628_, lean_object* v_00_u03b2_629_, lean_object* v_cmp_630_, lean_object* v_inst_631_, lean_object* v_t_632_, lean_object* v_h_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_632_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_635_, lean_object* v_00_u03b2_636_, lean_object* v_cmp_637_, lean_object* v_inst_638_, lean_object* v_t_639_, lean_object* v_h_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_ExtTreeMap_maxEntry(v_00_u03b1_635_, v_00_u03b2_636_, v_cmp_637_, v_inst_638_, v_t_639_, v_h_640_);
lean_dec(v_t_639_);
lean_dec_ref(v_cmp_637_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___redArg(lean_object* v_inst_642_, lean_object* v_t_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_642_, v_t_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_645_, lean_object* v_t_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_ExtTreeMap_maxEntry_x21___redArg(v_inst_645_, v_t_646_);
lean_dec(v_t_646_);
lean_dec_ref(v_inst_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21(lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_cmp_650_, lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_t_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_652_, v_t_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_655_, lean_object* v_00_u03b2_656_, lean_object* v_cmp_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_t_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_ExtTreeMap_maxEntry_x21(v_00_u03b1_655_, v_00_u03b2_656_, v_cmp_657_, v_inst_658_, v_inst_659_, v_t_660_);
lean_dec(v_t_660_);
lean_dec_ref(v_inst_659_);
lean_dec_ref(v_cmp_657_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___redArg(lean_object* v_t_662_, lean_object* v_fallback_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_662_, v_fallback_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_665_, lean_object* v_fallback_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Std_ExtTreeMap_maxEntryD___redArg(v_t_665_, v_fallback_666_);
lean_dec_ref(v_fallback_666_);
lean_dec(v_t_665_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD(lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_cmp_670_, lean_object* v_inst_671_, lean_object* v_t_672_, lean_object* v_fallback_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_672_, v_fallback_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_675_, lean_object* v_00_u03b2_676_, lean_object* v_cmp_677_, lean_object* v_inst_678_, lean_object* v_t_679_, lean_object* v_fallback_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_ExtTreeMap_maxEntryD(v_00_u03b1_675_, v_00_u03b2_676_, v_cmp_677_, v_inst_678_, v_t_679_, v_fallback_680_);
lean_dec_ref(v_fallback_680_);
lean_dec(v_t_679_);
lean_dec_ref(v_cmp_677_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___redArg(lean_object* v_t_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Std_ExtTreeMap_minKey_x3f___redArg(v_t_684_);
lean_dec(v_t_684_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f(lean_object* v_00_u03b1_686_, lean_object* v_00_u03b2_687_, lean_object* v_cmp_688_, lean_object* v_inst_689_, lean_object* v_t_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_692_, lean_object* v_00_u03b2_693_, lean_object* v_cmp_694_, lean_object* v_inst_695_, lean_object* v_t_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_ExtTreeMap_minKey_x3f(v_00_u03b1_692_, v_00_u03b2_693_, v_cmp_694_, v_inst_695_, v_t_696_);
lean_dec(v_t_696_);
lean_dec_ref(v_cmp_694_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___redArg(lean_object* v_t_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___redArg___boxed(lean_object* v_t_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Std_ExtTreeMap_minKey___redArg(v_t_700_);
lean_dec(v_t_700_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey(lean_object* v_00_u03b1_702_, lean_object* v_00_u03b2_703_, lean_object* v_cmp_704_, lean_object* v_inst_705_, lean_object* v_t_706_, lean_object* v_h_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___boxed(lean_object* v_00_u03b1_709_, lean_object* v_00_u03b2_710_, lean_object* v_cmp_711_, lean_object* v_inst_712_, lean_object* v_t_713_, lean_object* v_h_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_ExtTreeMap_minKey(v_00_u03b1_709_, v_00_u03b2_710_, v_cmp_711_, v_inst_712_, v_t_713_, v_h_714_);
lean_dec(v_t_713_);
lean_dec_ref(v_cmp_711_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___redArg(lean_object* v_inst_716_, lean_object* v_t_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_716_, v_t_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_719_, lean_object* v_t_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_ExtTreeMap_minKey_x21___redArg(v_inst_719_, v_t_720_);
lean_dec(v_t_720_);
lean_dec(v_inst_719_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21(lean_object* v_00_u03b1_722_, lean_object* v_00_u03b2_723_, lean_object* v_cmp_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_t_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_726_, v_t_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_729_, lean_object* v_00_u03b2_730_, lean_object* v_cmp_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_t_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_ExtTreeMap_minKey_x21(v_00_u03b1_729_, v_00_u03b2_730_, v_cmp_731_, v_inst_732_, v_inst_733_, v_t_734_);
lean_dec(v_t_734_);
lean_dec(v_inst_733_);
lean_dec_ref(v_cmp_731_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___redArg(lean_object* v_t_736_, lean_object* v_fallback_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_736_, v_fallback_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___redArg___boxed(lean_object* v_t_739_, lean_object* v_fallback_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Std_ExtTreeMap_minKeyD___redArg(v_t_739_, v_fallback_740_);
lean_dec(v_fallback_740_);
lean_dec(v_t_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD(lean_object* v_00_u03b1_742_, lean_object* v_00_u03b2_743_, lean_object* v_cmp_744_, lean_object* v_inst_745_, lean_object* v_t_746_, lean_object* v_fallback_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_746_, v_fallback_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_749_, lean_object* v_00_u03b2_750_, lean_object* v_cmp_751_, lean_object* v_inst_752_, lean_object* v_t_753_, lean_object* v_fallback_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Std_ExtTreeMap_minKeyD(v_00_u03b1_749_, v_00_u03b2_750_, v_cmp_751_, v_inst_752_, v_t_753_, v_fallback_754_);
lean_dec(v_fallback_754_);
lean_dec(v_t_753_);
lean_dec_ref(v_cmp_751_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___redArg(lean_object* v_t_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_ExtTreeMap_maxKey_x3f___redArg(v_t_758_);
lean_dec(v_t_758_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f(lean_object* v_00_u03b1_760_, lean_object* v_00_u03b2_761_, lean_object* v_cmp_762_, lean_object* v_inst_763_, lean_object* v_t_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_766_, lean_object* v_00_u03b2_767_, lean_object* v_cmp_768_, lean_object* v_inst_769_, lean_object* v_t_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_ExtTreeMap_maxKey_x3f(v_00_u03b1_766_, v_00_u03b2_767_, v_cmp_768_, v_inst_769_, v_t_770_);
lean_dec(v_t_770_);
lean_dec_ref(v_cmp_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___redArg(lean_object* v_t_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___redArg___boxed(lean_object* v_t_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_ExtTreeMap_maxKey___redArg(v_t_774_);
lean_dec(v_t_774_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey(lean_object* v_00_u03b1_776_, lean_object* v_00_u03b2_777_, lean_object* v_cmp_778_, lean_object* v_inst_779_, lean_object* v_t_780_, lean_object* v_h_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___boxed(lean_object* v_00_u03b1_783_, lean_object* v_00_u03b2_784_, lean_object* v_cmp_785_, lean_object* v_inst_786_, lean_object* v_t_787_, lean_object* v_h_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_ExtTreeMap_maxKey(v_00_u03b1_783_, v_00_u03b2_784_, v_cmp_785_, v_inst_786_, v_t_787_, v_h_788_);
lean_dec(v_t_787_);
lean_dec_ref(v_cmp_785_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___redArg(lean_object* v_inst_790_, lean_object* v_t_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_790_, v_t_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_793_, lean_object* v_t_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_ExtTreeMap_maxKey_x21___redArg(v_inst_793_, v_t_794_);
lean_dec(v_t_794_);
lean_dec(v_inst_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21(lean_object* v_00_u03b1_796_, lean_object* v_00_u03b2_797_, lean_object* v_cmp_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_t_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_800_, v_t_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_803_, lean_object* v_00_u03b2_804_, lean_object* v_cmp_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_t_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_ExtTreeMap_maxKey_x21(v_00_u03b1_803_, v_00_u03b2_804_, v_cmp_805_, v_inst_806_, v_inst_807_, v_t_808_);
lean_dec(v_t_808_);
lean_dec(v_inst_807_);
lean_dec_ref(v_cmp_805_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___redArg(lean_object* v_t_810_, lean_object* v_fallback_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_810_, v_fallback_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_813_, lean_object* v_fallback_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_ExtTreeMap_maxKeyD___redArg(v_t_813_, v_fallback_814_);
lean_dec(v_fallback_814_);
lean_dec(v_t_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_cmp_818_, lean_object* v_inst_819_, lean_object* v_t_820_, lean_object* v_fallback_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_820_, v_fallback_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_cmp_825_, lean_object* v_inst_826_, lean_object* v_t_827_, lean_object* v_fallback_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_ExtTreeMap_maxKeyD(v_00_u03b1_823_, v_00_u03b2_824_, v_cmp_825_, v_inst_826_, v_t_827_, v_fallback_828_);
lean_dec(v_fallback_828_);
lean_dec(v_t_827_);
lean_dec_ref(v_cmp_825_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_830_, lean_object* v_n_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_830_, v_n_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_833_, lean_object* v_n_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(v_t_833_, v_n_834_);
lean_dec(v_t_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_836_, lean_object* v_00_u03b2_837_, lean_object* v_cmp_838_, lean_object* v_inst_839_, lean_object* v_t_840_, lean_object* v_n_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_840_, v_n_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_cmp_845_, lean_object* v_inst_846_, lean_object* v_t_847_, lean_object* v_n_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_ExtTreeMap_entryAtIdx_x3f(v_00_u03b1_843_, v_00_u03b2_844_, v_cmp_845_, v_inst_846_, v_t_847_, v_n_848_);
lean_dec(v_t_847_);
lean_dec_ref(v_cmp_845_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___redArg(lean_object* v_t_850_, lean_object* v_n_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_850_, v_n_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_853_, lean_object* v_n_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Std_ExtTreeMap_entryAtIdx___redArg(v_t_853_, v_n_854_);
lean_dec(v_t_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx(lean_object* v_00_u03b1_856_, lean_object* v_00_u03b2_857_, lean_object* v_cmp_858_, lean_object* v_inst_859_, lean_object* v_t_860_, lean_object* v_n_861_, lean_object* v_h_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_860_, v_n_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_864_, lean_object* v_00_u03b2_865_, lean_object* v_cmp_866_, lean_object* v_inst_867_, lean_object* v_t_868_, lean_object* v_n_869_, lean_object* v_h_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_ExtTreeMap_entryAtIdx(v_00_u03b1_864_, v_00_u03b2_865_, v_cmp_866_, v_inst_867_, v_t_868_, v_n_869_, v_h_870_);
lean_dec(v_t_868_);
lean_dec_ref(v_cmp_866_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_872_, lean_object* v_t_873_, lean_object* v_n_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_872_, v_t_873_, v_n_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_876_, lean_object* v_t_877_, lean_object* v_n_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_ExtTreeMap_entryAtIdx_x21___redArg(v_inst_876_, v_t_877_, v_n_878_);
lean_dec(v_t_877_);
lean_dec_ref(v_inst_876_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_880_, lean_object* v_00_u03b2_881_, lean_object* v_cmp_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_t_885_, lean_object* v_n_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_884_, v_t_885_, v_n_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_888_, lean_object* v_00_u03b2_889_, lean_object* v_cmp_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_t_893_, lean_object* v_n_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_ExtTreeMap_entryAtIdx_x21(v_00_u03b1_888_, v_00_u03b2_889_, v_cmp_890_, v_inst_891_, v_inst_892_, v_t_893_, v_n_894_);
lean_dec(v_t_893_);
lean_dec_ref(v_inst_892_);
lean_dec_ref(v_cmp_890_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___redArg(lean_object* v_t_896_, lean_object* v_n_897_, lean_object* v_fallback_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_896_, v_n_897_, v_fallback_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_900_, lean_object* v_n_901_, lean_object* v_fallback_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Std_ExtTreeMap_entryAtIdxD___redArg(v_t_900_, v_n_901_, v_fallback_902_);
lean_dec_ref(v_fallback_902_);
lean_dec(v_t_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD(lean_object* v_00_u03b1_904_, lean_object* v_00_u03b2_905_, lean_object* v_cmp_906_, lean_object* v_inst_907_, lean_object* v_t_908_, lean_object* v_n_909_, lean_object* v_fallback_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_908_, v_n_909_, v_fallback_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_912_, lean_object* v_00_u03b2_913_, lean_object* v_cmp_914_, lean_object* v_inst_915_, lean_object* v_t_916_, lean_object* v_n_917_, lean_object* v_fallback_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_ExtTreeMap_entryAtIdxD(v_00_u03b1_912_, v_00_u03b2_913_, v_cmp_914_, v_inst_915_, v_t_916_, v_n_917_, v_fallback_918_);
lean_dec_ref(v_fallback_918_);
lean_dec(v_t_916_);
lean_dec_ref(v_cmp_914_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_920_, lean_object* v_n_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_920_, v_n_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_923_, lean_object* v_n_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(v_t_923_, v_n_924_);
lean_dec(v_t_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_926_, lean_object* v_00_u03b2_927_, lean_object* v_cmp_928_, lean_object* v_inst_929_, lean_object* v_t_930_, lean_object* v_n_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_930_, v_n_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_933_, lean_object* v_00_u03b2_934_, lean_object* v_cmp_935_, lean_object* v_inst_936_, lean_object* v_t_937_, lean_object* v_n_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_ExtTreeMap_keyAtIdx_x3f(v_00_u03b1_933_, v_00_u03b2_934_, v_cmp_935_, v_inst_936_, v_t_937_, v_n_938_);
lean_dec(v_t_937_);
lean_dec_ref(v_cmp_935_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___redArg(lean_object* v_t_940_, lean_object* v_n_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_940_, v_n_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_943_, lean_object* v_n_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_ExtTreeMap_keyAtIdx___redArg(v_t_943_, v_n_944_);
lean_dec(v_t_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_cmp_948_, lean_object* v_inst_949_, lean_object* v_t_950_, lean_object* v_n_951_, lean_object* v_h_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_950_, v_n_951_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_954_, lean_object* v_00_u03b2_955_, lean_object* v_cmp_956_, lean_object* v_inst_957_, lean_object* v_t_958_, lean_object* v_n_959_, lean_object* v_h_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std_ExtTreeMap_keyAtIdx(v_00_u03b1_954_, v_00_u03b2_955_, v_cmp_956_, v_inst_957_, v_t_958_, v_n_959_, v_h_960_);
lean_dec(v_t_958_);
lean_dec_ref(v_cmp_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_962_, lean_object* v_t_963_, lean_object* v_n_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_962_, v_t_963_, v_n_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_966_, lean_object* v_t_967_, lean_object* v_n_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Std_ExtTreeMap_keyAtIdx_x21___redArg(v_inst_966_, v_t_967_, v_n_968_);
lean_dec(v_t_967_);
lean_dec(v_inst_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_970_, lean_object* v_00_u03b2_971_, lean_object* v_cmp_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_t_975_, lean_object* v_n_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_974_, v_t_975_, v_n_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_978_, lean_object* v_00_u03b2_979_, lean_object* v_cmp_980_, lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_t_983_, lean_object* v_n_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_ExtTreeMap_keyAtIdx_x21(v_00_u03b1_978_, v_00_u03b2_979_, v_cmp_980_, v_inst_981_, v_inst_982_, v_t_983_, v_n_984_);
lean_dec(v_t_983_);
lean_dec(v_inst_982_);
lean_dec_ref(v_cmp_980_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___redArg(lean_object* v_t_986_, lean_object* v_n_987_, lean_object* v_fallback_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_986_, v_n_987_, v_fallback_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_990_, lean_object* v_n_991_, lean_object* v_fallback_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_ExtTreeMap_keyAtIdxD___redArg(v_t_990_, v_n_991_, v_fallback_992_);
lean_dec(v_fallback_992_);
lean_dec(v_t_990_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD(lean_object* v_00_u03b1_994_, lean_object* v_00_u03b2_995_, lean_object* v_cmp_996_, lean_object* v_inst_997_, lean_object* v_t_998_, lean_object* v_n_999_, lean_object* v_fallback_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_998_, v_n_999_, v_fallback_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_1002_, lean_object* v_00_u03b2_1003_, lean_object* v_cmp_1004_, lean_object* v_inst_1005_, lean_object* v_t_1006_, lean_object* v_n_1007_, lean_object* v_fallback_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Std_ExtTreeMap_keyAtIdxD(v_00_u03b1_1002_, v_00_u03b2_1003_, v_cmp_1004_, v_inst_1005_, v_t_1006_, v_n_1007_, v_fallback_1008_);
lean_dec(v_fallback_1008_);
lean_dec(v_t_1006_);
lean_dec_ref(v_cmp_1004_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1010_, lean_object* v_t_1011_, lean_object* v_k_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1010_, v_k_1012_, v___x_1013_, v_t_1011_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1015_, lean_object* v_00_u03b2_1016_, lean_object* v_cmp_1017_, lean_object* v_inst_1018_, lean_object* v_t_1019_, lean_object* v_k_1020_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_box(0);
v___x_1022_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1017_, v_k_1020_, v___x_1021_, v_t_1019_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1023_, lean_object* v_t_1024_, lean_object* v_k_1025_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1023_, v_k_1025_, v___x_1026_, v_t_1024_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1028_, lean_object* v_00_u03b2_1029_, lean_object* v_cmp_1030_, lean_object* v_inst_1031_, lean_object* v_t_1032_, lean_object* v_k_1033_){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_box(0);
v___x_1035_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1030_, v_k_1033_, v___x_1034_, v_t_1032_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1036_, lean_object* v_t_1037_, lean_object* v_k_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1036_, v_k_1038_, v___x_1039_, v_t_1037_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1041_, lean_object* v_00_u03b2_1042_, lean_object* v_cmp_1043_, lean_object* v_inst_1044_, lean_object* v_t_1045_, lean_object* v_k_1046_){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_box(0);
v___x_1048_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1043_, v_k_1046_, v___x_1047_, v_t_1045_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1049_, lean_object* v_t_1050_, lean_object* v_k_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1049_, v_k_1051_, v___x_1052_, v_t_1050_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1054_, lean_object* v_00_u03b2_1055_, lean_object* v_cmp_1056_, lean_object* v_inst_1057_, lean_object* v_t_1058_, lean_object* v_k_1059_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1056_, v_k_1059_, v___x_1060_, v_t_1058_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE___redArg(lean_object* v_cmp_1062_, lean_object* v_t_1063_, lean_object* v_k_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_1062_, v_k_1064_, v_t_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE(lean_object* v_00_u03b1_1066_, lean_object* v_00_u03b2_1067_, lean_object* v_cmp_1068_, lean_object* v_inst_1069_, lean_object* v_t_1070_, lean_object* v_k_1071_, lean_object* v_h_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_1068_, v_k_1071_, v_t_1070_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT___redArg(lean_object* v_cmp_1074_, lean_object* v_t_1075_, lean_object* v_k_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_1074_, v_k_1076_, v_t_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_cmp_1080_, lean_object* v_inst_1081_, lean_object* v_t_1082_, lean_object* v_k_1083_, lean_object* v_h_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_1080_, v_k_1083_, v_t_1082_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE___redArg(lean_object* v_cmp_1086_, lean_object* v_t_1087_, lean_object* v_k_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_1086_, v_k_1088_, v_t_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE(lean_object* v_00_u03b1_1090_, lean_object* v_00_u03b2_1091_, lean_object* v_cmp_1092_, lean_object* v_inst_1093_, lean_object* v_t_1094_, lean_object* v_k_1095_, lean_object* v_h_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_1092_, v_k_1095_, v_t_1094_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT___redArg(lean_object* v_cmp_1098_, lean_object* v_t_1099_, lean_object* v_k_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_1098_, v_k_1100_, v_t_1099_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT(lean_object* v_00_u03b1_1102_, lean_object* v_00_u03b2_1103_, lean_object* v_cmp_1104_, lean_object* v_inst_1105_, lean_object* v_t_1106_, lean_object* v_k_1107_, lean_object* v_h_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_1104_, v_k_1107_, v_t_1106_);
return v___x_1109_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1113_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1114_ = lean_unsigned_to_nat(14u);
v___x_1115_ = lean_unsigned_to_nat(22u);
v___x_1116_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1117_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1118_ = l_mkPanicMessageWithDecl(v___x_1117_, v___x_1116_, v___x_1115_, v___x_1114_, v___x_1113_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1119_, lean_object* v_inst_1120_, lean_object* v_t_1121_, lean_object* v_k_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_box(0);
v___x_1124_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1119_, v_k_1122_, v___x_1123_, v_t_1121_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1126_ = l_panic___redArg(v_inst_1120_, v___x_1125_);
return v___x_1126_;
}
else
{
lean_object* v_val_1127_; 
v_val_1127_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_val_1127_);
lean_dec_ref_known(v___x_1124_, 1);
return v_val_1127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1128_, lean_object* v_inst_1129_, lean_object* v_t_1130_, lean_object* v_k_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Std_ExtTreeMap_getEntryGE_x21___redArg(v_cmp_1128_, v_inst_1129_, v_t_1130_, v_k_1131_);
lean_dec_ref(v_inst_1129_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1133_, lean_object* v_00_u03b2_1134_, lean_object* v_cmp_1135_, lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_t_1138_, lean_object* v_k_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_box(0);
v___x_1141_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1135_, v_k_1139_, v___x_1140_, v_t_1138_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1143_ = l_panic___redArg(v_inst_1137_, v___x_1142_);
return v___x_1143_;
}
else
{
lean_object* v_val_1144_; 
v_val_1144_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_val_1144_);
lean_dec_ref_known(v___x_1141_, 1);
return v_val_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1145_, lean_object* v_00_u03b2_1146_, lean_object* v_cmp_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_t_1150_, lean_object* v_k_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Std_ExtTreeMap_getEntryGE_x21(v_00_u03b1_1145_, v_00_u03b2_1146_, v_cmp_1147_, v_inst_1148_, v_inst_1149_, v_t_1150_, v_k_1151_);
lean_dec_ref(v_inst_1149_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1153_, lean_object* v_inst_1154_, lean_object* v_t_1155_, lean_object* v_k_1156_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_box(0);
v___x_1158_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1153_, v_k_1156_, v___x_1157_, v_t_1155_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1160_ = l_panic___redArg(v_inst_1154_, v___x_1159_);
return v___x_1160_;
}
else
{
lean_object* v_val_1161_; 
v_val_1161_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_val_1161_);
lean_dec_ref_known(v___x_1158_, 1);
return v_val_1161_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1162_, lean_object* v_inst_1163_, lean_object* v_t_1164_, lean_object* v_k_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Std_ExtTreeMap_getEntryGT_x21___redArg(v_cmp_1162_, v_inst_1163_, v_t_1164_, v_k_1165_);
lean_dec_ref(v_inst_1163_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1167_, lean_object* v_00_u03b2_1168_, lean_object* v_cmp_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_t_1172_, lean_object* v_k_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_box(0);
v___x_1175_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1169_, v_k_1173_, v___x_1174_, v_t_1172_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1177_ = l_panic___redArg(v_inst_1171_, v___x_1176_);
return v___x_1177_;
}
else
{
lean_object* v_val_1178_; 
v_val_1178_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_val_1178_);
lean_dec_ref_known(v___x_1175_, 1);
return v_val_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1179_, lean_object* v_00_u03b2_1180_, lean_object* v_cmp_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_t_1184_, lean_object* v_k_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Std_ExtTreeMap_getEntryGT_x21(v_00_u03b1_1179_, v_00_u03b2_1180_, v_cmp_1181_, v_inst_1182_, v_inst_1183_, v_t_1184_, v_k_1185_);
lean_dec_ref(v_inst_1183_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1187_, lean_object* v_inst_1188_, lean_object* v_t_1189_, lean_object* v_k_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1187_, v_k_1190_, v___x_1191_, v_t_1189_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1194_ = l_panic___redArg(v_inst_1188_, v___x_1193_);
return v___x_1194_;
}
else
{
lean_object* v_val_1195_; 
v_val_1195_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_val_1195_);
lean_dec_ref_known(v___x_1192_, 1);
return v_val_1195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1196_, lean_object* v_inst_1197_, lean_object* v_t_1198_, lean_object* v_k_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_ExtTreeMap_getEntryLE_x21___redArg(v_cmp_1196_, v_inst_1197_, v_t_1198_, v_k_1199_);
lean_dec_ref(v_inst_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_cmp_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_t_1206_, lean_object* v_k_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1203_, v_k_1207_, v___x_1208_, v_t_1206_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1211_ = l_panic___redArg(v_inst_1205_, v___x_1210_);
return v___x_1211_;
}
else
{
lean_object* v_val_1212_; 
v_val_1212_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_val_1212_);
lean_dec_ref_known(v___x_1209_, 1);
return v_val_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1213_, lean_object* v_00_u03b2_1214_, lean_object* v_cmp_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_t_1218_, lean_object* v_k_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_ExtTreeMap_getEntryLE_x21(v_00_u03b1_1213_, v_00_u03b2_1214_, v_cmp_1215_, v_inst_1216_, v_inst_1217_, v_t_1218_, v_k_1219_);
lean_dec_ref(v_inst_1217_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1221_, lean_object* v_inst_1222_, lean_object* v_t_1223_, lean_object* v_k_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1221_, v_k_1224_, v___x_1225_, v_t_1223_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1228_ = l_panic___redArg(v_inst_1222_, v___x_1227_);
return v___x_1228_;
}
else
{
lean_object* v_val_1229_; 
v_val_1229_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v___x_1226_, 1);
return v_val_1229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1230_, lean_object* v_inst_1231_, lean_object* v_t_1232_, lean_object* v_k_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Std_ExtTreeMap_getEntryLT_x21___redArg(v_cmp_1230_, v_inst_1231_, v_t_1232_, v_k_1233_);
lean_dec_ref(v_inst_1231_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1235_, lean_object* v_00_u03b2_1236_, lean_object* v_cmp_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_t_1240_, lean_object* v_k_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_box(0);
v___x_1243_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1237_, v_k_1241_, v___x_1242_, v_t_1240_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1245_ = l_panic___redArg(v_inst_1239_, v___x_1244_);
return v___x_1245_;
}
else
{
lean_object* v_val_1246_; 
v_val_1246_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1246_);
lean_dec_ref_known(v___x_1243_, 1);
return v_val_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1247_, lean_object* v_00_u03b2_1248_, lean_object* v_cmp_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_t_1252_, lean_object* v_k_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Std_ExtTreeMap_getEntryLT_x21(v_00_u03b1_1247_, v_00_u03b2_1248_, v_cmp_1249_, v_inst_1250_, v_inst_1251_, v_t_1252_, v_k_1253_);
lean_dec_ref(v_inst_1251_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___redArg(lean_object* v_cmp_1255_, lean_object* v_t_1256_, lean_object* v_k_1257_, lean_object* v_fallback_1258_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_box(0);
v___x_1260_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1255_, v_k_1257_, v___x_1259_, v_t_1256_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_inc_ref(v_fallback_1258_);
return v_fallback_1258_;
}
else
{
lean_object* v_val_1261_; 
v_val_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_val_1261_);
lean_dec_ref_known(v___x_1260_, 1);
return v_val_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1262_, lean_object* v_t_1263_, lean_object* v_k_1264_, lean_object* v_fallback_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Std_ExtTreeMap_getEntryGED___redArg(v_cmp_1262_, v_t_1263_, v_k_1264_, v_fallback_1265_);
lean_dec_ref(v_fallback_1265_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED(lean_object* v_00_u03b1_1267_, lean_object* v_00_u03b2_1268_, lean_object* v_cmp_1269_, lean_object* v_inst_1270_, lean_object* v_t_1271_, lean_object* v_k_1272_, lean_object* v_fallback_1273_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_box(0);
v___x_1275_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1269_, v_k_1272_, v___x_1274_, v_t_1271_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_inc_ref(v_fallback_1273_);
return v_fallback_1273_;
}
else
{
lean_object* v_val_1276_; 
v_val_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_val_1276_);
lean_dec_ref_known(v___x_1275_, 1);
return v_val_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1277_, lean_object* v_00_u03b2_1278_, lean_object* v_cmp_1279_, lean_object* v_inst_1280_, lean_object* v_t_1281_, lean_object* v_k_1282_, lean_object* v_fallback_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Std_ExtTreeMap_getEntryGED(v_00_u03b1_1277_, v_00_u03b2_1278_, v_cmp_1279_, v_inst_1280_, v_t_1281_, v_k_1282_, v_fallback_1283_);
lean_dec_ref(v_fallback_1283_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1285_, lean_object* v_t_1286_, lean_object* v_k_1287_, lean_object* v_fallback_1288_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_box(0);
v___x_1290_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1285_, v_k_1287_, v___x_1289_, v_t_1286_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_inc_ref(v_fallback_1288_);
return v_fallback_1288_;
}
else
{
lean_object* v_val_1291_; 
v_val_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_val_1291_);
lean_dec_ref_known(v___x_1290_, 1);
return v_val_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1292_, lean_object* v_t_1293_, lean_object* v_k_1294_, lean_object* v_fallback_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Std_ExtTreeMap_getEntryGTD___redArg(v_cmp_1292_, v_t_1293_, v_k_1294_, v_fallback_1295_);
lean_dec_ref(v_fallback_1295_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD(lean_object* v_00_u03b1_1297_, lean_object* v_00_u03b2_1298_, lean_object* v_cmp_1299_, lean_object* v_inst_1300_, lean_object* v_t_1301_, lean_object* v_k_1302_, lean_object* v_fallback_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1299_, v_k_1302_, v___x_1304_, v_t_1301_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_inc_ref(v_fallback_1303_);
return v_fallback_1303_;
}
else
{
lean_object* v_val_1306_; 
v_val_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_val_1306_);
lean_dec_ref_known(v___x_1305_, 1);
return v_val_1306_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_00_u03b2_1308_, lean_object* v_cmp_1309_, lean_object* v_inst_1310_, lean_object* v_t_1311_, lean_object* v_k_1312_, lean_object* v_fallback_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Std_ExtTreeMap_getEntryGTD(v_00_u03b1_1307_, v_00_u03b2_1308_, v_cmp_1309_, v_inst_1310_, v_t_1311_, v_k_1312_, v_fallback_1313_);
lean_dec_ref(v_fallback_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___redArg(lean_object* v_cmp_1315_, lean_object* v_t_1316_, lean_object* v_k_1317_, lean_object* v_fallback_1318_){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_box(0);
v___x_1320_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1315_, v_k_1317_, v___x_1319_, v_t_1316_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_inc_ref(v_fallback_1318_);
return v_fallback_1318_;
}
else
{
lean_object* v_val_1321_; 
v_val_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_val_1321_);
lean_dec_ref_known(v___x_1320_, 1);
return v_val_1321_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1322_, lean_object* v_t_1323_, lean_object* v_k_1324_, lean_object* v_fallback_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Std_ExtTreeMap_getEntryLED___redArg(v_cmp_1322_, v_t_1323_, v_k_1324_, v_fallback_1325_);
lean_dec_ref(v_fallback_1325_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED(lean_object* v_00_u03b1_1327_, lean_object* v_00_u03b2_1328_, lean_object* v_cmp_1329_, lean_object* v_inst_1330_, lean_object* v_t_1331_, lean_object* v_k_1332_, lean_object* v_fallback_1333_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_box(0);
v___x_1335_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1329_, v_k_1332_, v___x_1334_, v_t_1331_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_inc_ref(v_fallback_1333_);
return v_fallback_1333_;
}
else
{
lean_object* v_val_1336_; 
v_val_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_val_1336_);
lean_dec_ref_known(v___x_1335_, 1);
return v_val_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_cmp_1339_, lean_object* v_inst_1340_, lean_object* v_t_1341_, lean_object* v_k_1342_, lean_object* v_fallback_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Std_ExtTreeMap_getEntryLED(v_00_u03b1_1337_, v_00_u03b2_1338_, v_cmp_1339_, v_inst_1340_, v_t_1341_, v_k_1342_, v_fallback_1343_);
lean_dec_ref(v_fallback_1343_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1345_, lean_object* v_t_1346_, lean_object* v_k_1347_, lean_object* v_fallback_1348_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_box(0);
v___x_1350_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1345_, v_k_1347_, v___x_1349_, v_t_1346_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_inc_ref(v_fallback_1348_);
return v_fallback_1348_;
}
else
{
lean_object* v_val_1351_; 
v_val_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v___x_1350_, 1);
return v_val_1351_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1352_, lean_object* v_t_1353_, lean_object* v_k_1354_, lean_object* v_fallback_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Std_ExtTreeMap_getEntryLTD___redArg(v_cmp_1352_, v_t_1353_, v_k_1354_, v_fallback_1355_);
lean_dec_ref(v_fallback_1355_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD(lean_object* v_00_u03b1_1357_, lean_object* v_00_u03b2_1358_, lean_object* v_cmp_1359_, lean_object* v_inst_1360_, lean_object* v_t_1361_, lean_object* v_k_1362_, lean_object* v_fallback_1363_){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_box(0);
v___x_1365_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1359_, v_k_1362_, v___x_1364_, v_t_1361_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_inc_ref(v_fallback_1363_);
return v_fallback_1363_;
}
else
{
lean_object* v_val_1366_; 
v_val_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_val_1366_);
lean_dec_ref_known(v___x_1365_, 1);
return v_val_1366_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1367_, lean_object* v_00_u03b2_1368_, lean_object* v_cmp_1369_, lean_object* v_inst_1370_, lean_object* v_t_1371_, lean_object* v_k_1372_, lean_object* v_fallback_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Std_ExtTreeMap_getEntryLTD(v_00_u03b1_1367_, v_00_u03b2_1368_, v_cmp_1369_, v_inst_1370_, v_t_1371_, v_k_1372_, v_fallback_1373_);
lean_dec_ref(v_fallback_1373_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1375_, lean_object* v_t_1376_, lean_object* v_k_1377_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1375_, v_k_1377_, v___x_1378_, v_t_1376_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1380_, lean_object* v_00_u03b2_1381_, lean_object* v_cmp_1382_, lean_object* v_inst_1383_, lean_object* v_t_1384_, lean_object* v_k_1385_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1382_, v_k_1385_, v___x_1386_, v_t_1384_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1388_, lean_object* v_t_1389_, lean_object* v_k_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_box(0);
v___x_1392_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1388_, v_k_1390_, v___x_1391_, v_t_1389_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1393_, lean_object* v_00_u03b2_1394_, lean_object* v_cmp_1395_, lean_object* v_inst_1396_, lean_object* v_t_1397_, lean_object* v_k_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_box(0);
v___x_1400_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1395_, v_k_1398_, v___x_1399_, v_t_1397_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1401_, lean_object* v_t_1402_, lean_object* v_k_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_box(0);
v___x_1405_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1401_, v_k_1403_, v___x_1404_, v_t_1402_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_cmp_1408_, lean_object* v_inst_1409_, lean_object* v_t_1410_, lean_object* v_k_1411_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_box(0);
v___x_1413_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1408_, v_k_1411_, v___x_1412_, v_t_1410_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1414_, lean_object* v_t_1415_, lean_object* v_k_1416_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_box(0);
v___x_1418_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1414_, v_k_1416_, v___x_1417_, v_t_1415_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1419_, lean_object* v_00_u03b2_1420_, lean_object* v_cmp_1421_, lean_object* v_inst_1422_, lean_object* v_t_1423_, lean_object* v_k_1424_){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_box(0);
v___x_1426_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1421_, v_k_1424_, v___x_1425_, v_t_1423_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE___redArg(lean_object* v_cmp_1427_, lean_object* v_t_1428_, lean_object* v_k_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1427_, v_k_1429_, v_t_1428_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE(lean_object* v_00_u03b1_1431_, lean_object* v_00_u03b2_1432_, lean_object* v_cmp_1433_, lean_object* v_inst_1434_, lean_object* v_t_1435_, lean_object* v_k_1436_, lean_object* v_h_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1433_, v_k_1436_, v_t_1435_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT___redArg(lean_object* v_cmp_1439_, lean_object* v_t_1440_, lean_object* v_k_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1439_, v_k_1441_, v_t_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT(lean_object* v_00_u03b1_1443_, lean_object* v_00_u03b2_1444_, lean_object* v_cmp_1445_, lean_object* v_inst_1446_, lean_object* v_t_1447_, lean_object* v_k_1448_, lean_object* v_h_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1445_, v_k_1448_, v_t_1447_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE___redArg(lean_object* v_cmp_1451_, lean_object* v_t_1452_, lean_object* v_k_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1451_, v_k_1453_, v_t_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE(lean_object* v_00_u03b1_1455_, lean_object* v_00_u03b2_1456_, lean_object* v_cmp_1457_, lean_object* v_inst_1458_, lean_object* v_t_1459_, lean_object* v_k_1460_, lean_object* v_h_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1457_, v_k_1460_, v_t_1459_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT___redArg(lean_object* v_cmp_1463_, lean_object* v_t_1464_, lean_object* v_k_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1463_, v_k_1465_, v_t_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT(lean_object* v_00_u03b1_1467_, lean_object* v_00_u03b2_1468_, lean_object* v_cmp_1469_, lean_object* v_inst_1470_, lean_object* v_t_1471_, lean_object* v_k_1472_, lean_object* v_h_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1469_, v_k_1472_, v_t_1471_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1475_, lean_object* v_inst_1476_, lean_object* v_t_1477_, lean_object* v_k_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_box(0);
v___x_1480_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1475_, v_k_1478_, v___x_1479_, v_t_1477_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1482_ = l_panic___redArg(v_inst_1476_, v___x_1481_);
return v___x_1482_;
}
else
{
lean_object* v_val_1483_; 
v_val_1483_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_val_1483_);
lean_dec_ref_known(v___x_1480_, 1);
return v_val_1483_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1484_, lean_object* v_inst_1485_, lean_object* v_t_1486_, lean_object* v_k_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Std_ExtTreeMap_getKeyGE_x21___redArg(v_cmp_1484_, v_inst_1485_, v_t_1486_, v_k_1487_);
lean_dec(v_inst_1485_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1489_, lean_object* v_00_u03b2_1490_, lean_object* v_cmp_1491_, lean_object* v_inst_1492_, lean_object* v_inst_1493_, lean_object* v_t_1494_, lean_object* v_k_1495_){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_box(0);
v___x_1497_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1491_, v_k_1495_, v___x_1496_, v_t_1494_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1499_ = l_panic___redArg(v_inst_1493_, v___x_1498_);
return v___x_1499_;
}
else
{
lean_object* v_val_1500_; 
v_val_1500_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v___x_1497_, 1);
return v_val_1500_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1501_, lean_object* v_00_u03b2_1502_, lean_object* v_cmp_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_t_1506_, lean_object* v_k_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Std_ExtTreeMap_getKeyGE_x21(v_00_u03b1_1501_, v_00_u03b2_1502_, v_cmp_1503_, v_inst_1504_, v_inst_1505_, v_t_1506_, v_k_1507_);
lean_dec(v_inst_1505_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1509_, lean_object* v_inst_1510_, lean_object* v_t_1511_, lean_object* v_k_1512_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_box(0);
v___x_1514_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1509_, v_k_1512_, v___x_1513_, v_t_1511_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1516_ = l_panic___redArg(v_inst_1510_, v___x_1515_);
return v___x_1516_;
}
else
{
lean_object* v_val_1517_; 
v_val_1517_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v___x_1514_, 1);
return v_val_1517_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1518_, lean_object* v_inst_1519_, lean_object* v_t_1520_, lean_object* v_k_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Std_ExtTreeMap_getKeyGT_x21___redArg(v_cmp_1518_, v_inst_1519_, v_t_1520_, v_k_1521_);
lean_dec(v_inst_1519_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1523_, lean_object* v_00_u03b2_1524_, lean_object* v_cmp_1525_, lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_t_1528_, lean_object* v_k_1529_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1525_, v_k_1529_, v___x_1530_, v_t_1528_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1533_ = l_panic___redArg(v_inst_1527_, v___x_1532_);
return v___x_1533_;
}
else
{
lean_object* v_val_1534_; 
v_val_1534_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___x_1531_, 1);
return v_val_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1535_, lean_object* v_00_u03b2_1536_, lean_object* v_cmp_1537_, lean_object* v_inst_1538_, lean_object* v_inst_1539_, lean_object* v_t_1540_, lean_object* v_k_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Std_ExtTreeMap_getKeyGT_x21(v_00_u03b1_1535_, v_00_u03b2_1536_, v_cmp_1537_, v_inst_1538_, v_inst_1539_, v_t_1540_, v_k_1541_);
lean_dec(v_inst_1539_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1543_, lean_object* v_inst_1544_, lean_object* v_t_1545_, lean_object* v_k_1546_){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_box(0);
v___x_1548_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1543_, v_k_1546_, v___x_1547_, v_t_1545_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1550_ = l_panic___redArg(v_inst_1544_, v___x_1549_);
return v___x_1550_;
}
else
{
lean_object* v_val_1551_; 
v_val_1551_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_val_1551_);
lean_dec_ref_known(v___x_1548_, 1);
return v_val_1551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1552_, lean_object* v_inst_1553_, lean_object* v_t_1554_, lean_object* v_k_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Std_ExtTreeMap_getKeyLE_x21___redArg(v_cmp_1552_, v_inst_1553_, v_t_1554_, v_k_1555_);
lean_dec(v_inst_1553_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1557_, lean_object* v_00_u03b2_1558_, lean_object* v_cmp_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v_t_1562_, lean_object* v_k_1563_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_box(0);
v___x_1565_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1559_, v_k_1563_, v___x_1564_, v_t_1562_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1567_ = l_panic___redArg(v_inst_1561_, v___x_1566_);
return v___x_1567_;
}
else
{
lean_object* v_val_1568_; 
v_val_1568_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_val_1568_);
lean_dec_ref_known(v___x_1565_, 1);
return v_val_1568_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1569_, lean_object* v_00_u03b2_1570_, lean_object* v_cmp_1571_, lean_object* v_inst_1572_, lean_object* v_inst_1573_, lean_object* v_t_1574_, lean_object* v_k_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Std_ExtTreeMap_getKeyLE_x21(v_00_u03b1_1569_, v_00_u03b2_1570_, v_cmp_1571_, v_inst_1572_, v_inst_1573_, v_t_1574_, v_k_1575_);
lean_dec(v_inst_1573_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1577_, lean_object* v_inst_1578_, lean_object* v_t_1579_, lean_object* v_k_1580_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = lean_box(0);
v___x_1582_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1577_, v_k_1580_, v___x_1581_, v_t_1579_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1584_ = l_panic___redArg(v_inst_1578_, v___x_1583_);
return v___x_1584_;
}
else
{
lean_object* v_val_1585_; 
v_val_1585_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v___x_1582_, 1);
return v_val_1585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1586_, lean_object* v_inst_1587_, lean_object* v_t_1588_, lean_object* v_k_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Std_ExtTreeMap_getKeyLT_x21___redArg(v_cmp_1586_, v_inst_1587_, v_t_1588_, v_k_1589_);
lean_dec(v_inst_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1591_, lean_object* v_00_u03b2_1592_, lean_object* v_cmp_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_t_1596_, lean_object* v_k_1597_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_box(0);
v___x_1599_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1593_, v_k_1597_, v___x_1598_, v_t_1596_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1601_ = l_panic___redArg(v_inst_1595_, v___x_1600_);
return v___x_1601_;
}
else
{
lean_object* v_val_1602_; 
v_val_1602_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_val_1602_);
lean_dec_ref_known(v___x_1599_, 1);
return v_val_1602_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1603_, lean_object* v_00_u03b2_1604_, lean_object* v_cmp_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_t_1608_, lean_object* v_k_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Std_ExtTreeMap_getKeyLT_x21(v_00_u03b1_1603_, v_00_u03b2_1604_, v_cmp_1605_, v_inst_1606_, v_inst_1607_, v_t_1608_, v_k_1609_);
lean_dec(v_inst_1607_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___redArg(lean_object* v_cmp_1611_, lean_object* v_t_1612_, lean_object* v_k_1613_, lean_object* v_fallback_1614_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_box(0);
v___x_1616_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1611_, v_k_1613_, v___x_1615_, v_t_1612_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_inc(v_fallback_1614_);
return v_fallback_1614_;
}
else
{
lean_object* v_val_1617_; 
v_val_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v___x_1616_, 1);
return v_val_1617_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1618_, lean_object* v_t_1619_, lean_object* v_k_1620_, lean_object* v_fallback_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Std_ExtTreeMap_getKeyGED___redArg(v_cmp_1618_, v_t_1619_, v_k_1620_, v_fallback_1621_);
lean_dec(v_fallback_1621_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED(lean_object* v_00_u03b1_1623_, lean_object* v_00_u03b2_1624_, lean_object* v_cmp_1625_, lean_object* v_inst_1626_, lean_object* v_t_1627_, lean_object* v_k_1628_, lean_object* v_fallback_1629_){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_box(0);
v___x_1631_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1625_, v_k_1628_, v___x_1630_, v_t_1627_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_inc(v_fallback_1629_);
return v_fallback_1629_;
}
else
{
lean_object* v_val_1632_; 
v_val_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_val_1632_);
lean_dec_ref_known(v___x_1631_, 1);
return v_val_1632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1633_, lean_object* v_00_u03b2_1634_, lean_object* v_cmp_1635_, lean_object* v_inst_1636_, lean_object* v_t_1637_, lean_object* v_k_1638_, lean_object* v_fallback_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Std_ExtTreeMap_getKeyGED(v_00_u03b1_1633_, v_00_u03b2_1634_, v_cmp_1635_, v_inst_1636_, v_t_1637_, v_k_1638_, v_fallback_1639_);
lean_dec(v_fallback_1639_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1641_, lean_object* v_t_1642_, lean_object* v_k_1643_, lean_object* v_fallback_1644_){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_box(0);
v___x_1646_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1641_, v_k_1643_, v___x_1645_, v_t_1642_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_inc(v_fallback_1644_);
return v_fallback_1644_;
}
else
{
lean_object* v_val_1647_; 
v_val_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_val_1647_);
lean_dec_ref_known(v___x_1646_, 1);
return v_val_1647_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1648_, lean_object* v_t_1649_, lean_object* v_k_1650_, lean_object* v_fallback_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Std_ExtTreeMap_getKeyGTD___redArg(v_cmp_1648_, v_t_1649_, v_k_1650_, v_fallback_1651_);
lean_dec(v_fallback_1651_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD(lean_object* v_00_u03b1_1653_, lean_object* v_00_u03b2_1654_, lean_object* v_cmp_1655_, lean_object* v_inst_1656_, lean_object* v_t_1657_, lean_object* v_k_1658_, lean_object* v_fallback_1659_){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_box(0);
v___x_1661_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1655_, v_k_1658_, v___x_1660_, v_t_1657_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_inc(v_fallback_1659_);
return v_fallback_1659_;
}
else
{
lean_object* v_val_1662_; 
v_val_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_val_1662_);
lean_dec_ref_known(v___x_1661_, 1);
return v_val_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1663_, lean_object* v_00_u03b2_1664_, lean_object* v_cmp_1665_, lean_object* v_inst_1666_, lean_object* v_t_1667_, lean_object* v_k_1668_, lean_object* v_fallback_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Std_ExtTreeMap_getKeyGTD(v_00_u03b1_1663_, v_00_u03b2_1664_, v_cmp_1665_, v_inst_1666_, v_t_1667_, v_k_1668_, v_fallback_1669_);
lean_dec(v_fallback_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___redArg(lean_object* v_cmp_1671_, lean_object* v_t_1672_, lean_object* v_k_1673_, lean_object* v_fallback_1674_){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_box(0);
v___x_1676_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1671_, v_k_1673_, v___x_1675_, v_t_1672_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_inc(v_fallback_1674_);
return v_fallback_1674_;
}
else
{
lean_object* v_val_1677_; 
v_val_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_val_1677_);
lean_dec_ref_known(v___x_1676_, 1);
return v_val_1677_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1678_, lean_object* v_t_1679_, lean_object* v_k_1680_, lean_object* v_fallback_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Std_ExtTreeMap_getKeyLED___redArg(v_cmp_1678_, v_t_1679_, v_k_1680_, v_fallback_1681_);
lean_dec(v_fallback_1681_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED(lean_object* v_00_u03b1_1683_, lean_object* v_00_u03b2_1684_, lean_object* v_cmp_1685_, lean_object* v_inst_1686_, lean_object* v_t_1687_, lean_object* v_k_1688_, lean_object* v_fallback_1689_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = lean_box(0);
v___x_1691_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1685_, v_k_1688_, v___x_1690_, v_t_1687_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_inc(v_fallback_1689_);
return v_fallback_1689_;
}
else
{
lean_object* v_val_1692_; 
v_val_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_val_1692_);
lean_dec_ref_known(v___x_1691_, 1);
return v_val_1692_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1693_, lean_object* v_00_u03b2_1694_, lean_object* v_cmp_1695_, lean_object* v_inst_1696_, lean_object* v_t_1697_, lean_object* v_k_1698_, lean_object* v_fallback_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_ExtTreeMap_getKeyLED(v_00_u03b1_1693_, v_00_u03b2_1694_, v_cmp_1695_, v_inst_1696_, v_t_1697_, v_k_1698_, v_fallback_1699_);
lean_dec(v_fallback_1699_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1701_, lean_object* v_t_1702_, lean_object* v_k_1703_, lean_object* v_fallback_1704_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_box(0);
v___x_1706_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1701_, v_k_1703_, v___x_1705_, v_t_1702_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_inc(v_fallback_1704_);
return v_fallback_1704_;
}
else
{
lean_object* v_val_1707_; 
v_val_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_val_1707_);
lean_dec_ref_known(v___x_1706_, 1);
return v_val_1707_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1708_, lean_object* v_t_1709_, lean_object* v_k_1710_, lean_object* v_fallback_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Std_ExtTreeMap_getKeyLTD___redArg(v_cmp_1708_, v_t_1709_, v_k_1710_, v_fallback_1711_);
lean_dec(v_fallback_1711_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD(lean_object* v_00_u03b1_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_cmp_1715_, lean_object* v_inst_1716_, lean_object* v_t_1717_, lean_object* v_k_1718_, lean_object* v_fallback_1719_){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_box(0);
v___x_1721_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1715_, v_k_1718_, v___x_1720_, v_t_1717_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_inc(v_fallback_1719_);
return v_fallback_1719_;
}
else
{
lean_object* v_val_1722_; 
v_val_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_val_1722_);
lean_dec_ref_known(v___x_1721_, 1);
return v_val_1722_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1723_, lean_object* v_00_u03b2_1724_, lean_object* v_cmp_1725_, lean_object* v_inst_1726_, lean_object* v_t_1727_, lean_object* v_k_1728_, lean_object* v_fallback_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Std_ExtTreeMap_getKeyLTD(v_00_u03b1_1723_, v_00_u03b2_1724_, v_cmp_1725_, v_inst_1726_, v_t_1727_, v_k_1728_, v_fallback_1729_);
lean_dec(v_fallback_1729_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter___redArg(lean_object* v_f_1731_, lean_object* v_m_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_1731_, v_m_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter(lean_object* v_00_u03b1_1734_, lean_object* v_00_u03b2_1735_, lean_object* v_cmp_1736_, lean_object* v_f_1737_, lean_object* v_m_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_1737_, v_m_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter___boxed(lean_object* v_00_u03b1_1740_, lean_object* v_00_u03b2_1741_, lean_object* v_cmp_1742_, lean_object* v_f_1743_, lean_object* v_m_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Std_ExtTreeMap_filter(v_00_u03b1_1740_, v_00_u03b2_1741_, v_cmp_1742_, v_f_1743_, v_m_1744_);
lean_dec_ref(v_cmp_1742_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap___redArg(lean_object* v_f_1746_, lean_object* v_m_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_1746_, v_m_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap(lean_object* v_00_u03b1_1749_, lean_object* v_00_u03b2_1750_, lean_object* v_00_u03b3_1751_, lean_object* v_cmp_1752_, lean_object* v_f_1753_, lean_object* v_m_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_1753_, v_m_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap___boxed(lean_object* v_00_u03b1_1756_, lean_object* v_00_u03b2_1757_, lean_object* v_00_u03b3_1758_, lean_object* v_cmp_1759_, lean_object* v_f_1760_, lean_object* v_m_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Std_ExtTreeMap_filterMap(v_00_u03b1_1756_, v_00_u03b2_1757_, v_00_u03b3_1758_, v_cmp_1759_, v_f_1760_, v_m_1761_);
lean_dec_ref(v_cmp_1759_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map___redArg(lean_object* v_f_1763_, lean_object* v_t_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_1763_, v_t_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map(lean_object* v_00_u03b1_1766_, lean_object* v_00_u03b2_1767_, lean_object* v_00_u03b3_1768_, lean_object* v_cmp_1769_, lean_object* v_f_1770_, lean_object* v_t_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_1770_, v_t_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map___boxed(lean_object* v_00_u03b1_1773_, lean_object* v_00_u03b2_1774_, lean_object* v_00_u03b3_1775_, lean_object* v_cmp_1776_, lean_object* v_f_1777_, lean_object* v_t_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Std_ExtTreeMap_map(v_00_u03b1_1773_, v_00_u03b2_1774_, v_00_u03b3_1775_, v_cmp_1776_, v_f_1777_, v_t_1778_);
lean_dec_ref(v_cmp_1776_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM___redArg(lean_object* v_inst_1780_, lean_object* v_f_1781_, lean_object* v_init_1782_, lean_object* v_t_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1780_, v_f_1781_, v_init_1782_, v_t_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM(lean_object* v_00_u03b1_1785_, lean_object* v_00_u03b2_1786_, lean_object* v_cmp_1787_, lean_object* v_00_u03b4_1788_, lean_object* v_m_1789_, lean_object* v_inst_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_f_1793_, lean_object* v_init_1794_, lean_object* v_t_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1790_, v_f_1793_, v_init_1794_, v_t_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM___boxed(lean_object* v_00_u03b1_1797_, lean_object* v_00_u03b2_1798_, lean_object* v_cmp_1799_, lean_object* v_00_u03b4_1800_, lean_object* v_m_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_inst_1804_, lean_object* v_f_1805_, lean_object* v_init_1806_, lean_object* v_t_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_ExtTreeMap_foldlM(v_00_u03b1_1797_, v_00_u03b2_1798_, v_cmp_1799_, v_00_u03b4_1800_, v_m_1801_, v_inst_1802_, v_inst_1803_, v_inst_1804_, v_f_1805_, v_init_1806_, v_t_1807_);
lean_dec_ref(v_cmp_1799_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl___redArg(lean_object* v_f_1809_, lean_object* v_init_1810_, lean_object* v_t_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1809_, v_init_1810_, v_t_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl(lean_object* v_00_u03b1_1813_, lean_object* v_00_u03b2_1814_, lean_object* v_cmp_1815_, lean_object* v_00_u03b4_1816_, lean_object* v_inst_1817_, lean_object* v_f_1818_, lean_object* v_init_1819_, lean_object* v_t_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1818_, v_init_1819_, v_t_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl___boxed(lean_object* v_00_u03b1_1822_, lean_object* v_00_u03b2_1823_, lean_object* v_cmp_1824_, lean_object* v_00_u03b4_1825_, lean_object* v_inst_1826_, lean_object* v_f_1827_, lean_object* v_init_1828_, lean_object* v_t_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Std_ExtTreeMap_foldl(v_00_u03b1_1822_, v_00_u03b2_1823_, v_cmp_1824_, v_00_u03b4_1825_, v_inst_1826_, v_f_1827_, v_init_1828_, v_t_1829_);
lean_dec_ref(v_cmp_1824_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM___redArg(lean_object* v_inst_1831_, lean_object* v_f_1832_, lean_object* v_init_1833_, lean_object* v_t_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1831_, v_f_1832_, v_init_1833_, v_t_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM(lean_object* v_00_u03b1_1836_, lean_object* v_00_u03b2_1837_, lean_object* v_cmp_1838_, lean_object* v_00_u03b4_1839_, lean_object* v_m_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_inst_1843_, lean_object* v_f_1844_, lean_object* v_init_1845_, lean_object* v_t_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1841_, v_f_1844_, v_init_1845_, v_t_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_00_u03b2_1849_, lean_object* v_cmp_1850_, lean_object* v_00_u03b4_1851_, lean_object* v_m_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_f_1856_, lean_object* v_init_1857_, lean_object* v_t_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Std_ExtTreeMap_foldrM(v_00_u03b1_1848_, v_00_u03b2_1849_, v_cmp_1850_, v_00_u03b4_1851_, v_m_1852_, v_inst_1853_, v_inst_1854_, v_inst_1855_, v_f_1856_, v_init_1857_, v_t_1858_);
lean_dec_ref(v_cmp_1850_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___redArg___lam__0(lean_object* v_f_1860_, lean_object* v_x1_1861_, lean_object* v_x2_1862_, lean_object* v_x3_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_apply_3(v_f_1860_, v_x1_1861_, v_x2_1862_, v_x3_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___redArg(lean_object* v_f_1884_, lean_object* v_init_1885_, lean_object* v_t_1886_){
_start:
{
lean_object* v___f_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___f_1887_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1887_, 0, v_f_1884_);
v___x_1888_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_1889_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1888_, v___f_1887_, v_init_1885_, v_t_1886_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr(lean_object* v_00_u03b1_1890_, lean_object* v_00_u03b2_1891_, lean_object* v_cmp_1892_, lean_object* v_00_u03b4_1893_, lean_object* v_inst_1894_, lean_object* v_f_1895_, lean_object* v_init_1896_, lean_object* v_t_1897_){
_start:
{
lean_object* v___f_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___f_1898_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1898_, 0, v_f_1895_);
v___x_1899_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_1900_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1899_, v___f_1898_, v_init_1896_, v_t_1897_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___boxed(lean_object* v_00_u03b1_1901_, lean_object* v_00_u03b2_1902_, lean_object* v_cmp_1903_, lean_object* v_00_u03b4_1904_, lean_object* v_inst_1905_, lean_object* v_f_1906_, lean_object* v_init_1907_, lean_object* v_t_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Std_ExtTreeMap_foldr(v_00_u03b1_1901_, v_00_u03b2_1902_, v_cmp_1903_, v_00_u03b4_1904_, v_inst_1905_, v_f_1906_, v_init_1907_, v_t_1908_);
lean_dec_ref(v_cmp_1903_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition___redArg___lam__0(lean_object* v_f_1910_, lean_object* v_cmp_1911_, lean_object* v_x_1912_, lean_object* v_a_1913_, lean_object* v_b_1914_){
_start:
{
lean_object* v_fst_1915_; lean_object* v_snd_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1930_; 
v_fst_1915_ = lean_ctor_get(v_x_1912_, 0);
v_snd_1916_ = lean_ctor_get(v_x_1912_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_x_1912_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1918_ = v_x_1912_;
v_isShared_1919_ = v_isSharedCheck_1930_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_snd_1916_);
lean_inc(v_fst_1915_);
lean_dec(v_x_1912_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1930_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; uint8_t v___x_1921_; 
lean_inc(v_b_1914_);
lean_inc(v_a_1913_);
v___x_1920_ = lean_apply_2(v_f_1910_, v_a_1913_, v_b_1914_);
v___x_1921_ = lean_unbox(v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1922_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1911_, v_a_1913_, v_b_1914_, v_snd_1916_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1922_);
v___x_1924_ = v___x_1918_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_fst_1915_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1926_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1911_, v_a_1913_, v_b_1914_, v_fst_1915_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1926_);
v___x_1928_ = v___x_1918_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_snd_1916_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition___redArg(lean_object* v_cmp_1933_, lean_object* v_f_1934_, lean_object* v_t_1935_){
_start:
{
lean_object* v___f_1936_; lean_object* v___x_1937_; lean_object* v_p_1938_; lean_object* v_fst_1939_; lean_object* v_snd_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
v___f_1936_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1936_, 0, v_f_1934_);
lean_closure_set(v___f_1936_, 1, v_cmp_1933_);
v___x_1937_ = ((lean_object*)(l_Std_ExtTreeMap_partition___redArg___closed__0));
v_p_1938_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1936_, v___x_1937_, v_t_1935_);
v_fst_1939_ = lean_ctor_get(v_p_1938_, 0);
v_snd_1940_ = lean_ctor_get(v_p_1938_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_p_1938_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v_p_1938_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_snd_1940_);
lean_inc(v_fst_1939_);
lean_dec(v_p_1938_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_fst_1939_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_snd_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition(lean_object* v_00_u03b1_1948_, lean_object* v_00_u03b2_1949_, lean_object* v_cmp_1950_, lean_object* v_inst_1951_, lean_object* v_f_1952_, lean_object* v_t_1953_){
_start:
{
lean_object* v___f_1954_; lean_object* v___x_1955_; lean_object* v_p_1956_; lean_object* v_fst_1957_; lean_object* v_snd_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v___f_1954_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1954_, 0, v_f_1952_);
lean_closure_set(v___f_1954_, 1, v_cmp_1950_);
v___x_1955_ = ((lean_object*)(l_Std_ExtTreeMap_partition___redArg___closed__0));
v_p_1956_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1954_, v___x_1955_, v_t_1953_);
v_fst_1957_ = lean_ctor_get(v_p_1956_, 0);
v_snd_1958_ = lean_ctor_get(v_p_1956_, 1);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_p_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v_p_1956_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_snd_1958_);
lean_inc(v_fst_1957_);
lean_dec(v_p_1956_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_fst_1957_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_snd_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___redArg___lam__0(lean_object* v_f_1966_, lean_object* v_x_1967_, lean_object* v_k_1968_, lean_object* v_v_1969_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_apply_2(v_f_1966_, v_k_1968_, v_v_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___redArg(lean_object* v_inst_1971_, lean_object* v_f_1972_, lean_object* v_t_1973_){
_start:
{
lean_object* v___f_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___f_1974_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1974_, 0, v_f_1972_);
v___x_1975_ = lean_box(0);
v___x_1976_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1971_, v___f_1974_, v___x_1975_, v_t_1973_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM(lean_object* v_00_u03b1_1977_, lean_object* v_00_u03b2_1978_, lean_object* v_cmp_1979_, lean_object* v_m_1980_, lean_object* v_inst_1981_, lean_object* v_inst_1982_, lean_object* v_inst_1983_, lean_object* v_f_1984_, lean_object* v_t_1985_){
_start:
{
lean_object* v___f_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___f_1986_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1986_, 0, v_f_1984_);
v___x_1987_ = lean_box(0);
v___x_1988_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1981_, v___f_1986_, v___x_1987_, v_t_1985_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___boxed(lean_object* v_00_u03b1_1989_, lean_object* v_00_u03b2_1990_, lean_object* v_cmp_1991_, lean_object* v_m_1992_, lean_object* v_inst_1993_, lean_object* v_inst_1994_, lean_object* v_inst_1995_, lean_object* v_f_1996_, lean_object* v_t_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Std_ExtTreeMap_forM(v_00_u03b1_1989_, v_00_u03b2_1990_, v_cmp_1991_, v_m_1992_, v_inst_1993_, v_inst_1994_, v_inst_1995_, v_f_1996_, v_t_1997_);
lean_dec_ref(v_cmp_1991_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg___lam__0(lean_object* v_f_1999_, lean_object* v_a_2000_, lean_object* v_b_2001_, lean_object* v_c_2002_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_apply_3(v_f_1999_, v_a_2000_, v_b_2001_, v_c_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg___lam__1(lean_object* v_toPure_2004_, lean_object* v_____do__lift_2005_){
_start:
{
lean_object* v_a_2006_; lean_object* v___x_2007_; 
v_a_2006_ = lean_ctor_get(v_____do__lift_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref(v_____do__lift_2005_);
v___x_2007_ = lean_apply_2(v_toPure_2004_, lean_box(0), v_a_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg(lean_object* v_inst_2008_, lean_object* v_f_2009_, lean_object* v_init_2010_, lean_object* v_t_2011_){
_start:
{
lean_object* v_toApplicative_2012_; lean_object* v_toBind_2013_; lean_object* v_toPure_2014_; lean_object* v___f_2015_; lean_object* v___x_2016_; lean_object* v___f_2017_; lean_object* v___x_2018_; 
v_toApplicative_2012_ = lean_ctor_get(v_inst_2008_, 0);
v_toBind_2013_ = lean_ctor_get(v_inst_2008_, 1);
lean_inc(v_toBind_2013_);
v_toPure_2014_ = lean_ctor_get(v_toApplicative_2012_, 1);
lean_inc(v_toPure_2014_);
v___f_2015_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2015_, 0, v_f_2009_);
v___x_2016_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2008_, v___f_2015_, v_init_2010_, v_t_2011_);
v___f_2017_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2017_, 0, v_toPure_2014_);
v___x_2018_ = lean_apply_4(v_toBind_2013_, lean_box(0), lean_box(0), v___x_2016_, v___f_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn(lean_object* v_00_u03b1_2019_, lean_object* v_00_u03b2_2020_, lean_object* v_cmp_2021_, lean_object* v_00_u03b4_2022_, lean_object* v_m_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_f_2027_, lean_object* v_init_2028_, lean_object* v_t_2029_){
_start:
{
lean_object* v_toApplicative_2030_; lean_object* v_toBind_2031_; lean_object* v_toPure_2032_; lean_object* v___f_2033_; lean_object* v___x_2034_; lean_object* v___f_2035_; lean_object* v___x_2036_; 
v_toApplicative_2030_ = lean_ctor_get(v_inst_2024_, 0);
v_toBind_2031_ = lean_ctor_get(v_inst_2024_, 1);
lean_inc(v_toBind_2031_);
v_toPure_2032_ = lean_ctor_get(v_toApplicative_2030_, 1);
lean_inc(v_toPure_2032_);
v___f_2033_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2033_, 0, v_f_2027_);
v___x_2034_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2024_, v___f_2033_, v_init_2028_, v_t_2029_);
v___f_2035_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2035_, 0, v_toPure_2032_);
v___x_2036_ = lean_apply_4(v_toBind_2031_, lean_box(0), lean_box(0), v___x_2034_, v___f_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___boxed(lean_object* v_00_u03b1_2037_, lean_object* v_00_u03b2_2038_, lean_object* v_cmp_2039_, lean_object* v_00_u03b4_2040_, lean_object* v_m_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_, lean_object* v_inst_2044_, lean_object* v_f_2045_, lean_object* v_init_2046_, lean_object* v_t_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Std_ExtTreeMap_forIn(v_00_u03b1_2037_, v_00_u03b2_2038_, v_cmp_2039_, v_00_u03b4_2040_, v_m_2041_, v_inst_2042_, v_inst_2043_, v_inst_2044_, v_f_2045_, v_init_2046_, v_t_2047_);
lean_dec_ref(v_cmp_2039_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2049_, lean_object* v_x_2050_, lean_object* v_k_2051_, lean_object* v_v_2052_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2053_, 0, v_k_2051_);
lean_ctor_set(v___x_2053_, 1, v_v_2052_);
v___x_2054_ = lean_apply_1(v_f_2049_, v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_2055_, lean_object* v_t_2056_, lean_object* v_f_2057_){
_start:
{
lean_object* v___f_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___f_2058_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2058_, 0, v_f_2057_);
v___x_2059_ = lean_box(0);
v___x_2060_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2055_, v___f_2058_, v___x_2059_, v_t_2056_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2061_){
_start:
{
lean_object* v___f_2062_; 
v___f_2062_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2062_, 0, v_inst_2061_);
return v___f_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2063_, lean_object* v_00_u03b2_2064_, lean_object* v_cmp_2065_, lean_object* v_m_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_inst_2069_){
_start:
{
lean_object* v___f_2070_; 
v___f_2070_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2070_, 0, v_inst_2068_);
return v___f_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2071_, lean_object* v_00_u03b2_2072_, lean_object* v_cmp_2073_, lean_object* v_m_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_inst_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(v_00_u03b1_2071_, v_00_u03b2_2072_, v_cmp_2073_, v_m_2074_, v_inst_2075_, v_inst_2076_, v_inst_2077_);
lean_dec_ref(v_cmp_2073_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2079_, lean_object* v_a_2080_, lean_object* v_b_2081_, lean_object* v_c_2082_){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v_a_2080_);
lean_ctor_set(v___x_2083_, 1, v_b_2081_);
v___x_2084_ = lean_apply_2(v_f_2079_, v___x_2083_, v_c_2082_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_2085_, lean_object* v_00_u03b2_2086_, lean_object* v_m_2087_, lean_object* v_init_2088_, lean_object* v_f_2089_){
_start:
{
lean_object* v_toApplicative_2090_; lean_object* v_toBind_2091_; lean_object* v_toPure_2092_; lean_object* v___f_2093_; lean_object* v___x_2094_; lean_object* v___f_2095_; lean_object* v___x_2096_; 
v_toApplicative_2090_ = lean_ctor_get(v_inst_2085_, 0);
v_toBind_2091_ = lean_ctor_get(v_inst_2085_, 1);
lean_inc(v_toBind_2091_);
v_toPure_2092_ = lean_ctor_get(v_toApplicative_2090_, 1);
lean_inc(v_toPure_2092_);
v___f_2093_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2093_, 0, v_f_2089_);
v___x_2094_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2085_, v___f_2093_, v_init_2088_, v_m_2087_);
v___f_2095_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2095_, 0, v_toPure_2092_);
v___x_2096_ = lean_apply_4(v_toBind_2091_, lean_box(0), lean_box(0), v___x_2094_, v___f_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2097_){
_start:
{
lean_object* v___f_2098_; 
v___f_2098_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2098_, 0, v_inst_2097_);
return v___f_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_cmp_2101_, lean_object* v_m_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_inst_2105_){
_start:
{
lean_object* v___f_2106_; 
v___f_2106_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2106_, 0, v_inst_2104_);
return v___f_2106_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2107_, lean_object* v_00_u03b2_2108_, lean_object* v_cmp_2109_, lean_object* v_m_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(v_00_u03b1_2107_, v_00_u03b2_2108_, v_cmp_2109_, v_m_2110_, v_inst_2111_, v_inst_2112_, v_inst_2113_);
lean_dec_ref(v_cmp_2109_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___lam__0(lean_object* v_p_2115_, lean_object* v___x_2116_, lean_object* v___x_2117_, lean_object* v_a_2118_, lean_object* v_b_2119_, lean_object* v_acc_2120_){
_start:
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = lean_apply_2(v_p_2115_, v_a_2118_, v_b_2119_);
v___x_2122_ = lean_unbox(v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2116_);
return v___x_2123_;
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_dec_ref(v___x_2116_);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2121_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v___x_2117_);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2127_, lean_object* v___x_2128_, lean_object* v___x_2129_, lean_object* v_a_2130_, lean_object* v_b_2131_, lean_object* v_acc_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Std_ExtTreeMap_any___redArg___lam__0(v_p_2127_, v___x_2128_, v___x_2129_, v_a_2130_, v_b_2131_, v_acc_2132_);
lean_dec_ref(v_acc_2132_);
return v_res_2133_;
}
}
uint8_t l_Std_ExtTreeMap_any___redArg(lean_object* v_t_2137_, lean_object* v_p_2138_){
_start:
{
lean_object* v___y_2140_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; lean_object* v_a_2150_; 
v___x_2145_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2146_ = lean_box(0);
v___x_2147_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2148_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2148_, 0, v_p_2138_);
lean_closure_set(v___f_2148_, 1, v___x_2147_);
lean_closure_set(v___f_2148_, 2, v___x_2146_);
v___x_2149_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2145_, v___f_2148_, v___x_2147_, v_t_2137_);
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___y_2140_ = v_a_2150_;
goto v___jp_2139_;
v___jp_2139_:
{
lean_object* v_fst_2141_; 
v_fst_2141_ = lean_ctor_get(v___y_2140_, 0);
lean_inc(v_fst_2141_);
lean_dec_ref(v___y_2140_);
if (lean_obj_tag(v_fst_2141_) == 0)
{
uint8_t v___x_2142_; 
v___x_2142_ = 0;
return v___x_2142_;
}
else
{
lean_object* v_val_2143_; uint8_t v___x_2144_; 
v_val_2143_ = lean_ctor_get(v_fst_2141_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v_fst_2141_, 1);
v___x_2144_ = lean_unbox(v_val_2143_);
lean_dec(v_val_2143_);
return v___x_2144_;
}
}
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2137_ = stack[0].m_obj;
lean_object* v_p_2138_ = stack[1].m_obj;
uint8_t v_res_2151_;
v_res_2151_ = l_Std_ExtTreeMap_any___redArg(v_t_2137_, v_p_2138_);
stack->m_num = v_res_2151_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___boxed(lean_object* v_t_2152_, lean_object* v_p_2153_){
_start:
{
uint8_t v_res_2154_; lean_object* v_r_2155_; 
v_res_2154_ = l_Std_ExtTreeMap_any___redArg(v_t_2152_, v_p_2153_);
v_r_2155_ = lean_box(v_res_2154_);
return v_r_2155_;
}
}
uint8_t l_Std_ExtTreeMap_any(lean_object* v_00_u03b1_2156_, lean_object* v_00_u03b2_2157_, lean_object* v_cmp_2158_, lean_object* v_inst_2159_, lean_object* v_t_2160_, lean_object* v_p_2161_){
_start:
{
lean_object* v___y_2163_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___f_2171_; lean_object* v___x_2172_; lean_object* v_a_2173_; 
v___x_2168_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2169_ = lean_box(0);
v___x_2170_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2171_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2171_, 0, v_p_2161_);
lean_closure_set(v___f_2171_, 1, v___x_2170_);
lean_closure_set(v___f_2171_, 2, v___x_2169_);
v___x_2172_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2168_, v___f_2171_, v___x_2170_, v_t_2160_);
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___y_2163_ = v_a_2173_;
goto v___jp_2162_;
v___jp_2162_:
{
lean_object* v_fst_2164_; 
v_fst_2164_ = lean_ctor_get(v___y_2163_, 0);
lean_inc(v_fst_2164_);
lean_dec_ref(v___y_2163_);
if (lean_obj_tag(v_fst_2164_) == 0)
{
uint8_t v___x_2165_; 
v___x_2165_ = 0;
return v___x_2165_;
}
else
{
lean_object* v_val_2166_; uint8_t v___x_2167_; 
v_val_2166_ = lean_ctor_get(v_fst_2164_, 0);
lean_inc(v_val_2166_);
lean_dec_ref_known(v_fst_2164_, 1);
v___x_2167_ = lean_unbox(v_val_2166_);
lean_dec(v_val_2166_);
return v___x_2167_;
}
}
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2158_ = stack[2].m_obj;
lean_object* v_t_2160_ = stack[4].m_obj;
lean_object* v_p_2161_ = stack[5].m_obj;
uint8_t v_res_2174_;
v_res_2174_ = l_Std_ExtTreeMap_any(lean_box(0), lean_box(0), v_cmp_2158_, lean_box(0), v_t_2160_, v_p_2161_);
stack->m_num = v_res_2174_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___boxed(lean_object* v_00_u03b1_2175_, lean_object* v_00_u03b2_2176_, lean_object* v_cmp_2177_, lean_object* v_inst_2178_, lean_object* v_t_2179_, lean_object* v_p_2180_){
_start:
{
uint8_t v_res_2181_; lean_object* v_r_2182_; 
v_res_2181_ = l_Std_ExtTreeMap_any(v_00_u03b1_2175_, v_00_u03b2_2176_, v_cmp_2177_, v_inst_2178_, v_t_2179_, v_p_2180_);
lean_dec_ref(v_cmp_2177_);
v_r_2182_ = lean_box(v_res_2181_);
return v_r_2182_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___lam__0(lean_object* v_p_2183_, lean_object* v___x_2184_, lean_object* v___x_2185_, lean_object* v_a_2186_, lean_object* v_b_2187_, lean_object* v_acc_2188_){
_start:
{
lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2189_ = lean_apply_2(v_p_2183_, v_a_2186_, v_b_2187_);
v___x_2190_ = lean_unbox(v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_dec_ref(v___x_2185_);
v___x_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v___x_2184_);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2185_);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_2195_, lean_object* v___x_2196_, lean_object* v___x_2197_, lean_object* v_a_2198_, lean_object* v_b_2199_, lean_object* v_acc_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Std_ExtTreeMap_all___redArg___lam__0(v_p_2195_, v___x_2196_, v___x_2197_, v_a_2198_, v_b_2199_, v_acc_2200_);
lean_dec_ref(v_acc_2200_);
return v_res_2201_;
}
}
uint8_t l_Std_ExtTreeMap_all___redArg(lean_object* v_t_2202_, lean_object* v_p_2203_){
_start:
{
lean_object* v___y_2205_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___f_2213_; lean_object* v___x_2214_; lean_object* v_a_2215_; 
v___x_2210_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2211_ = lean_box(0);
v___x_2212_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2213_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2213_, 0, v_p_2203_);
lean_closure_set(v___f_2213_, 1, v___x_2211_);
lean_closure_set(v___f_2213_, 2, v___x_2212_);
v___x_2214_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2210_, v___f_2213_, v___x_2212_, v_t_2202_);
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec(v___x_2214_);
v___y_2205_ = v_a_2215_;
goto v___jp_2204_;
v___jp_2204_:
{
lean_object* v_fst_2206_; 
v_fst_2206_ = lean_ctor_get(v___y_2205_, 0);
lean_inc(v_fst_2206_);
lean_dec_ref(v___y_2205_);
if (lean_obj_tag(v_fst_2206_) == 0)
{
uint8_t v___x_2207_; 
v___x_2207_ = 1;
return v___x_2207_;
}
else
{
lean_object* v_val_2208_; uint8_t v___x_2209_; 
v_val_2208_ = lean_ctor_get(v_fst_2206_, 0);
lean_inc(v_val_2208_);
lean_dec_ref_known(v_fst_2206_, 1);
v___x_2209_ = lean_unbox(v_val_2208_);
lean_dec(v_val_2208_);
return v___x_2209_;
}
}
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2202_ = stack[0].m_obj;
lean_object* v_p_2203_ = stack[1].m_obj;
uint8_t v_res_2216_;
v_res_2216_ = l_Std_ExtTreeMap_all___redArg(v_t_2202_, v_p_2203_);
stack->m_num = v_res_2216_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___boxed(lean_object* v_t_2217_, lean_object* v_p_2218_){
_start:
{
uint8_t v_res_2219_; lean_object* v_r_2220_; 
v_res_2219_ = l_Std_ExtTreeMap_all___redArg(v_t_2217_, v_p_2218_);
v_r_2220_ = lean_box(v_res_2219_);
return v_r_2220_;
}
}
uint8_t l_Std_ExtTreeMap_all(lean_object* v_00_u03b1_2221_, lean_object* v_00_u03b2_2222_, lean_object* v_cmp_2223_, lean_object* v_inst_2224_, lean_object* v_t_2225_, lean_object* v_p_2226_){
_start:
{
lean_object* v___y_2228_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___f_2236_; lean_object* v___x_2237_; lean_object* v_a_2238_; 
v___x_2233_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2234_ = lean_box(0);
v___x_2235_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2236_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2236_, 0, v_p_2226_);
lean_closure_set(v___f_2236_, 1, v___x_2234_);
lean_closure_set(v___f_2236_, 2, v___x_2235_);
v___x_2237_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2233_, v___f_2236_, v___x_2235_, v_t_2225_);
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___y_2228_ = v_a_2238_;
goto v___jp_2227_;
v___jp_2227_:
{
lean_object* v_fst_2229_; 
v_fst_2229_ = lean_ctor_get(v___y_2228_, 0);
lean_inc(v_fst_2229_);
lean_dec_ref(v___y_2228_);
if (lean_obj_tag(v_fst_2229_) == 0)
{
uint8_t v___x_2230_; 
v___x_2230_ = 1;
return v___x_2230_;
}
else
{
lean_object* v_val_2231_; uint8_t v___x_2232_; 
v_val_2231_ = lean_ctor_get(v_fst_2229_, 0);
lean_inc(v_val_2231_);
lean_dec_ref_known(v_fst_2229_, 1);
v___x_2232_ = lean_unbox(v_val_2231_);
lean_dec(v_val_2231_);
return v___x_2232_;
}
}
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2223_ = stack[2].m_obj;
lean_object* v_t_2225_ = stack[4].m_obj;
lean_object* v_p_2226_ = stack[5].m_obj;
uint8_t v_res_2239_;
v_res_2239_ = l_Std_ExtTreeMap_all(lean_box(0), lean_box(0), v_cmp_2223_, lean_box(0), v_t_2225_, v_p_2226_);
stack->m_num = v_res_2239_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___boxed(lean_object* v_00_u03b1_2240_, lean_object* v_00_u03b2_2241_, lean_object* v_cmp_2242_, lean_object* v_inst_2243_, lean_object* v_t_2244_, lean_object* v_p_2245_){
_start:
{
uint8_t v_res_2246_; lean_object* v_r_2247_; 
v_res_2246_ = l_Std_ExtTreeMap_all(v_00_u03b1_2240_, v_00_u03b2_2241_, v_cmp_2242_, v_inst_2243_, v_t_2244_, v_p_2245_);
lean_dec_ref(v_cmp_2242_);
v_r_2247_ = lean_box(v_res_2246_);
return v_r_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg___lam__0(lean_object* v_x1_2248_, lean_object* v_x2_2249_, lean_object* v_x3_2250_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2251_, 0, v_x1_2248_);
lean_ctor_set(v___x_2251_, 1, v_x3_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_2252_, lean_object* v_x2_2253_, lean_object* v_x3_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Std_ExtTreeMap_keys___redArg___lam__0(v_x1_2252_, v_x2_2253_, v_x3_2254_);
lean_dec(v_x2_2253_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg(lean_object* v_t_2257_){
_start:
{
lean_object* v___f_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___f_2258_ = ((lean_object*)(l_Std_ExtTreeMap_keys___redArg___closed__0));
v___x_2259_ = lean_box(0);
v___x_2260_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2261_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2260_, v___f_2258_, v___x_2259_, v_t_2257_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys(lean_object* v_00_u03b1_2262_, lean_object* v_00_u03b2_2263_, lean_object* v_cmp_2264_, lean_object* v_inst_2265_, lean_object* v_t_2266_){
_start:
{
lean_object* v___f_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___f_2267_ = ((lean_object*)(l_Std_ExtTreeMap_keys___redArg___closed__0));
v___x_2268_ = lean_box(0);
v___x_2269_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2270_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2269_, v___f_2267_, v___x_2268_, v_t_2266_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___boxed(lean_object* v_00_u03b1_2271_, lean_object* v_00_u03b2_2272_, lean_object* v_cmp_2273_, lean_object* v_inst_2274_, lean_object* v_t_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Std_ExtTreeMap_keys(v_00_u03b1_2271_, v_00_u03b2_2272_, v_cmp_2273_, v_inst_2274_, v_t_2275_);
lean_dec_ref(v_cmp_2273_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg___lam__0(lean_object* v_l_2277_, lean_object* v_k_2278_, lean_object* v_x_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_array_push(v_l_2277_, v_k_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_2281_, lean_object* v_k_2282_, lean_object* v_x_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Std_ExtTreeMap_keysArray___redArg___lam__0(v_l_2281_, v_k_2282_, v_x_2283_);
lean_dec(v_x_2283_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg(lean_object* v_t_2286_){
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
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray(lean_object* v_00_u03b1_2294_, lean_object* v_00_u03b2_2295_, lean_object* v_cmp_2296_, lean_object* v_inst_2297_, lean_object* v_t_2298_){
_start:
{
lean_object* v___f_2299_; lean_object* v___y_2301_; 
v___f_2299_ = ((lean_object*)(l_Std_ExtTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2298_) == 0)
{
lean_object* v_size_2304_; 
v_size_2304_ = lean_ctor_get(v_t_2298_, 0);
lean_inc(v_size_2304_);
v___y_2301_ = v_size_2304_;
goto v___jp_2300_;
}
else
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_unsigned_to_nat(0u);
v___y_2301_ = v___x_2305_;
goto v___jp_2300_;
}
v___jp_2300_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = lean_mk_empty_array_with_capacity(v___y_2301_);
lean_dec(v___y_2301_);
v___x_2303_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2299_, v___x_2302_, v_t_2298_);
return v___x_2303_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___boxed(lean_object* v_00_u03b1_2306_, lean_object* v_00_u03b2_2307_, lean_object* v_cmp_2308_, lean_object* v_inst_2309_, lean_object* v_t_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Std_ExtTreeMap_keysArray(v_00_u03b1_2306_, v_00_u03b2_2307_, v_cmp_2308_, v_inst_2309_, v_t_2310_);
lean_dec_ref(v_cmp_2308_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg___lam__0(lean_object* v_x1_2312_, lean_object* v_x2_2313_, lean_object* v_x3_2314_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2315_, 0, v_x2_2313_);
lean_ctor_set(v___x_2315_, 1, v_x3_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_2316_, lean_object* v_x2_2317_, lean_object* v_x3_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Std_ExtTreeMap_values___redArg___lam__0(v_x1_2316_, v_x2_2317_, v_x3_2318_);
lean_dec(v_x1_2316_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg(lean_object* v_t_2321_){
_start:
{
lean_object* v___f_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___f_2322_ = ((lean_object*)(l_Std_ExtTreeMap_values___redArg___closed__0));
v___x_2323_ = lean_box(0);
v___x_2324_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2325_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2324_, v___f_2322_, v___x_2323_, v_t_2321_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values(lean_object* v_00_u03b1_2326_, lean_object* v_00_u03b2_2327_, lean_object* v_cmp_2328_, lean_object* v_inst_2329_, lean_object* v_t_2330_){
_start:
{
lean_object* v___f_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___f_2331_ = ((lean_object*)(l_Std_ExtTreeMap_values___redArg___closed__0));
v___x_2332_ = lean_box(0);
v___x_2333_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2334_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2333_, v___f_2331_, v___x_2332_, v_t_2330_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___boxed(lean_object* v_00_u03b1_2335_, lean_object* v_00_u03b2_2336_, lean_object* v_cmp_2337_, lean_object* v_inst_2338_, lean_object* v_t_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Std_ExtTreeMap_values(v_00_u03b1_2335_, v_00_u03b2_2336_, v_cmp_2337_, v_inst_2338_, v_t_2339_);
lean_dec_ref(v_cmp_2337_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_2341_, lean_object* v_x_2342_, lean_object* v_v_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_array_push(v_l_2341_, v_v_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2345_, lean_object* v_x_2346_, lean_object* v_v_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Std_ExtTreeMap_valuesArray___redArg___lam__0(v_l_2345_, v_x_2346_, v_v_2347_);
lean_dec(v_x_2346_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg(lean_object* v_t_2350_){
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
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray(lean_object* v_00_u03b1_2358_, lean_object* v_00_u03b2_2359_, lean_object* v_cmp_2360_, lean_object* v_inst_2361_, lean_object* v_t_2362_){
_start:
{
lean_object* v___f_2363_; lean_object* v___y_2365_; 
v___f_2363_ = ((lean_object*)(l_Std_ExtTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2362_) == 0)
{
lean_object* v_size_2368_; 
v_size_2368_ = lean_ctor_get(v_t_2362_, 0);
lean_inc(v_size_2368_);
v___y_2365_ = v_size_2368_;
goto v___jp_2364_;
}
else
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_unsigned_to_nat(0u);
v___y_2365_ = v___x_2369_;
goto v___jp_2364_;
}
v___jp_2364_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_mk_empty_array_with_capacity(v___y_2365_);
lean_dec(v___y_2365_);
v___x_2367_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2363_, v___x_2366_, v_t_2362_);
return v___x_2367_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_2370_, lean_object* v_00_u03b2_2371_, lean_object* v_cmp_2372_, lean_object* v_inst_2373_, lean_object* v_t_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Std_ExtTreeMap_valuesArray(v_00_u03b1_2370_, v_00_u03b2_2371_, v_cmp_2372_, v_inst_2373_, v_t_2374_);
lean_dec_ref(v_cmp_2372_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___redArg___lam__0(lean_object* v_x1_2376_, lean_object* v_x2_2377_, lean_object* v_x3_2378_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v_x1_2376_);
lean_ctor_set(v___x_2379_, 1, v_x2_2377_);
v___x_2380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v_x3_2378_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___redArg(lean_object* v_t_2382_){
_start:
{
lean_object* v___f_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___f_2383_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___x_2384_ = lean_box(0);
v___x_2385_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2386_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2385_, v___f_2383_, v___x_2384_, v_t_2382_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList(lean_object* v_00_u03b1_2387_, lean_object* v_00_u03b2_2388_, lean_object* v_cmp_2389_, lean_object* v_inst_2390_, lean_object* v_t_2391_){
_start:
{
lean_object* v___f_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___f_2392_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___x_2393_ = lean_box(0);
v___x_2394_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2395_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2394_, v___f_2392_, v___x_2393_, v_t_2391_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___boxed(lean_object* v_00_u03b1_2396_, lean_object* v_00_u03b2_2397_, lean_object* v_cmp_2398_, lean_object* v_inst_2399_, lean_object* v_t_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Std_ExtTreeMap_toList(v_00_u03b1_2396_, v_00_u03b2_2397_, v_cmp_2398_, v_inst_2399_, v_t_2400_);
lean_dec_ref(v_cmp_2398_);
return v_res_2401_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__25, &l_Std_ExtTreeMap___auto__1___closed__25_once, _init_l_Std_ExtTreeMap___auto__1___closed__25);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_2403_, lean_object* v_a_2404_, lean_object* v_x_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_fst_2407_; lean_object* v_snd_2408_; lean_object* v_r_2409_; lean_object* v___x_2410_; 
v_fst_2407_ = lean_ctor_get(v_a_2404_, 0);
lean_inc(v_fst_2407_);
v_snd_2408_ = lean_ctor_get(v_a_2404_, 1);
lean_inc(v_snd_2408_);
lean_dec_ref(v_a_2404_);
v_r_2409_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2403_, v_fst_2407_, v_snd_2408_, v___y_2406_);
v___x_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2410_, 0, v_r_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg(lean_object* v_l_2411_, lean_object* v_cmp_2412_){
_start:
{
lean_object* v___f_2413_; lean_object* v___x_2414_; lean_object* v_r_2415_; lean_object* v___x_2416_; 
v___f_2413_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2413_, 0, v_cmp_2412_);
v___x_2414_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2415_ = lean_box(1);
v___x_2416_ = l_List_forIn_x27_loop___redArg(v___x_2414_, v___f_2413_, v_l_2411_, v_r_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg___boxed(lean_object* v_l_2417_, lean_object* v_cmp_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Std_ExtTreeMap_ofList___redArg(v_l_2417_, v_cmp_2418_);
lean_dec(v_l_2417_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList(lean_object* v_00_u03b1_2420_, lean_object* v_00_u03b2_2421_, lean_object* v_l_2422_, lean_object* v_cmp_2423_){
_start:
{
lean_object* v___f_2424_; lean_object* v___x_2425_; lean_object* v_r_2426_; lean_object* v___x_2427_; 
v___f_2424_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2424_, 0, v_cmp_2423_);
v___x_2425_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2426_ = lean_box(1);
v___x_2427_ = l_List_forIn_x27_loop___redArg(v___x_2425_, v___f_2424_, v_l_2422_, v_r_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___boxed(lean_object* v_00_u03b1_2428_, lean_object* v_00_u03b2_2429_, lean_object* v_l_2430_, lean_object* v_cmp_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Std_ExtTreeMap_ofList(v_00_u03b1_2428_, v_00_u03b2_2429_, v_l_2430_, v_cmp_2431_);
lean_dec(v_l_2430_);
return v_res_2432_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__25, &l_Std_ExtTreeMap___auto__1___closed__25_once, _init_l_Std_ExtTreeMap___auto__1___closed__25);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg___lam__0(lean_object* v_cmp_2434_, lean_object* v_a_2435_, lean_object* v_x_2436_, lean_object* v___y_2437_){
_start:
{
uint8_t v___x_2438_; 
lean_inc(v___y_2437_);
lean_inc(v_a_2435_);
lean_inc_ref(v_cmp_2434_);
v___x_2438_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2434_, v_a_2435_, v___y_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = lean_box(0);
v___x_2440_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2434_, v_a_2435_, v___x_2439_, v___y_2437_);
v___x_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
return v___x_2441_;
}
else
{
lean_object* v___x_2442_; 
lean_dec(v_a_2435_);
lean_dec_ref(v_cmp_2434_);
v___x_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___y_2437_);
return v___x_2442_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg(lean_object* v_l_2443_, lean_object* v_cmp_2444_){
_start:
{
lean_object* v___f_2445_; lean_object* v___x_2446_; lean_object* v_r_2447_; lean_object* v___x_2448_; 
v___f_2445_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2445_, 0, v_cmp_2444_);
v___x_2446_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2447_ = lean_box(1);
v___x_2448_ = l_List_forIn_x27_loop___redArg(v___x_2446_, v___f_2445_, v_l_2443_, v_r_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg___boxed(lean_object* v_l_2449_, lean_object* v_cmp_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Std_ExtTreeMap_unitOfList___redArg(v_l_2449_, v_cmp_2450_);
lean_dec(v_l_2449_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList(lean_object* v_00_u03b1_2452_, lean_object* v_l_2453_, lean_object* v_cmp_2454_){
_start:
{
lean_object* v___f_2455_; lean_object* v___x_2456_; lean_object* v_r_2457_; lean_object* v___x_2458_; 
v___f_2455_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2455_, 0, v_cmp_2454_);
v___x_2456_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2457_ = lean_box(1);
v___x_2458_ = l_List_forIn_x27_loop___redArg(v___x_2456_, v___f_2455_, v_l_2453_, v_r_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___boxed(lean_object* v_00_u03b1_2459_, lean_object* v_l_2460_, lean_object* v_cmp_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Std_ExtTreeMap_unitOfList(v_00_u03b1_2459_, v_l_2460_, v_cmp_2461_);
lean_dec(v_l_2460_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___redArg___lam__0(lean_object* v_acc_2463_, lean_object* v_k_2464_, lean_object* v_v_2465_){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v_k_2464_);
lean_ctor_set(v___x_2466_, 1, v_v_2465_);
v___x_2467_ = lean_array_push(v_acc_2463_, v___x_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___redArg(lean_object* v_t_2471_){
_start:
{
lean_object* v___f_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___f_2472_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__0));
v___x_2473_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__1));
v___x_2474_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2472_, v___x_2473_, v_t_2471_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray(lean_object* v_00_u03b1_2475_, lean_object* v_00_u03b2_2476_, lean_object* v_cmp_2477_, lean_object* v_inst_2478_, lean_object* v_t_2479_){
_start:
{
lean_object* v___f_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___f_2480_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__0));
v___x_2481_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__1));
v___x_2482_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2480_, v___x_2481_, v_t_2479_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___boxed(lean_object* v_00_u03b1_2483_, lean_object* v_00_u03b2_2484_, lean_object* v_cmp_2485_, lean_object* v_inst_2486_, lean_object* v_t_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Std_ExtTreeMap_toArray(v_00_u03b1_2483_, v_00_u03b2_2484_, v_cmp_2485_, v_inst_2486_, v_t_2487_);
lean_dec_ref(v_cmp_2485_);
return v_res_2488_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__25, &l_Std_ExtTreeMap___auto__1___closed__25_once, _init_l_Std_ExtTreeMap___auto__1___closed__25);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray___redArg(lean_object* v_a_2490_, lean_object* v_cmp_2491_){
_start:
{
lean_object* v___f_2492_; lean_object* v___x_2493_; lean_object* v_r_2494_; size_t v_sz_2495_; size_t v___x_2496_; lean_object* v___x_2497_; 
v___f_2492_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2492_, 0, v_cmp_2491_);
v___x_2493_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2494_ = lean_box(1);
v_sz_2495_ = lean_array_size(v_a_2490_);
v___x_2496_ = ((size_t)0ULL);
v___x_2497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2493_, v_a_2490_, v___f_2492_, v_sz_2495_, v___x_2496_, v_r_2494_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray(lean_object* v_00_u03b1_2498_, lean_object* v_00_u03b2_2499_, lean_object* v_a_2500_, lean_object* v_cmp_2501_){
_start:
{
lean_object* v___f_2502_; lean_object* v___x_2503_; lean_object* v_r_2504_; size_t v_sz_2505_; size_t v___x_2506_; lean_object* v___x_2507_; 
v___f_2502_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2502_, 0, v_cmp_2501_);
v___x_2503_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2504_ = lean_box(1);
v_sz_2505_ = lean_array_size(v_a_2500_);
v___x_2506_ = ((size_t)0ULL);
v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2503_, v_a_2500_, v___f_2502_, v_sz_2505_, v___x_2506_, v_r_2504_);
return v___x_2507_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__25, &l_Std_ExtTreeMap___auto__1___closed__25_once, _init_l_Std_ExtTreeMap___auto__1___closed__25);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray___redArg(lean_object* v_a_2509_, lean_object* v_cmp_2510_){
_start:
{
lean_object* v___f_2511_; lean_object* v___x_2512_; lean_object* v_r_2513_; size_t v_sz_2514_; size_t v___x_2515_; lean_object* v___x_2516_; 
v___f_2511_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2511_, 0, v_cmp_2510_);
v___x_2512_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2513_ = lean_box(1);
v_sz_2514_ = lean_array_size(v_a_2509_);
v___x_2515_ = ((size_t)0ULL);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2512_, v_a_2509_, v___f_2511_, v_sz_2514_, v___x_2515_, v_r_2513_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray(lean_object* v_00_u03b1_2517_, lean_object* v_a_2518_, lean_object* v_cmp_2519_){
_start:
{
lean_object* v___f_2520_; lean_object* v___x_2521_; lean_object* v_r_2522_; size_t v_sz_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
v___f_2520_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2520_, 0, v_cmp_2519_);
v___x_2521_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2522_ = lean_box(1);
v_sz_2523_ = lean_array_size(v_a_2518_);
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2521_, v_a_2518_, v___f_2520_, v_sz_2523_, v___x_2524_, v_r_2522_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_modify___redArg(lean_object* v_cmp_2526_, lean_object* v_t_2527_, lean_object* v_a_2528_, lean_object* v_f_2529_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2526_, v_a_2528_, v_f_2529_, v_t_2527_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_modify(lean_object* v_00_u03b1_2531_, lean_object* v_00_u03b2_2532_, lean_object* v_cmp_2533_, lean_object* v_inst_2534_, lean_object* v_t_2535_, lean_object* v_a_2536_, lean_object* v_f_2537_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2533_, v_a_2536_, v_f_2537_, v_t_2535_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_alter___redArg(lean_object* v_cmp_2539_, lean_object* v_t_2540_, lean_object* v_a_2541_, lean_object* v_f_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2539_, v_a_2541_, v_f_2542_, v_t_2540_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_alter(lean_object* v_00_u03b1_2544_, lean_object* v_00_u03b2_2545_, lean_object* v_cmp_2546_, lean_object* v_inst_2547_, lean_object* v_t_2548_, lean_object* v_a_2549_, lean_object* v_f_2550_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2546_, v_a_2549_, v_f_2550_, v_t_2548_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2552_, lean_object* v_mergeFn_2553_, lean_object* v_a_2554_, lean_object* v_x_2555_){
_start:
{
if (lean_obj_tag(v_x_2555_) == 0)
{
lean_object* v___x_2556_; 
lean_dec(v_a_2554_);
lean_dec(v_mergeFn_2553_);
v___x_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_b_u2082_2552_);
return v___x_2556_;
}
else
{
lean_object* v_val_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2565_; 
v_val_2557_ = lean_ctor_get(v_x_2555_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_x_2555_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2559_ = v_x_2555_;
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_val_2557_);
lean_dec(v_x_2555_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2561_ = lean_apply_3(v_mergeFn_2553_, v_a_2554_, v_val_2557_, v_b_u2082_2552_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2561_);
v___x_2563_ = v___x_2559_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2566_, lean_object* v_cmp_2567_, lean_object* v_t_2568_, lean_object* v_a_2569_, lean_object* v_b_u2082_2570_){
_start:
{
lean_object* v___f_2571_; lean_object* v___x_2572_; 
lean_inc(v_a_2569_);
v___f_2571_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2571_, 0, v_b_u2082_2570_);
lean_closure_set(v___f_2571_, 1, v_mergeFn_2566_);
lean_closure_set(v___f_2571_, 2, v_a_2569_);
v___x_2572_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2567_, v_a_2569_, v___f_2571_, v_t_2568_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg(lean_object* v_cmp_2573_, lean_object* v_mergeFn_2574_, lean_object* v_t_u2081_2575_, lean_object* v_t_u2082_2576_){
_start:
{
lean_object* v___f_2577_; lean_object* v___x_2578_; 
v___f_2577_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2577_, 0, v_mergeFn_2574_);
lean_closure_set(v___f_2577_, 1, v_cmp_2573_);
v___x_2578_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2577_, v_t_u2081_2575_, v_t_u2082_2576_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith(lean_object* v_00_u03b1_2579_, lean_object* v_00_u03b2_2580_, lean_object* v_cmp_2581_, lean_object* v_inst_2582_, lean_object* v_mergeFn_2583_, lean_object* v_t_u2081_2584_, lean_object* v_t_u2082_2585_){
_start:
{
lean_object* v___f_2586_; lean_object* v___x_2587_; 
v___f_2586_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2586_, 0, v_mergeFn_2583_);
lean_closure_set(v___f_2586_, 1, v_cmp_2581_);
v___x_2587_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2586_, v_t_u2081_2584_, v_t_u2082_2585_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_2588_, lean_object* v_x_2589_, lean_object* v_____s_2590_){
_start:
{
lean_object* v_fst_2591_; lean_object* v_snd_2592_; lean_object* v_acc_2593_; lean_object* v___x_2594_; 
v_fst_2591_ = lean_ctor_get(v_x_2589_, 0);
lean_inc(v_fst_2591_);
v_snd_2592_ = lean_ctor_get(v_x_2589_, 1);
lean_inc(v_snd_2592_);
lean_dec_ref(v_x_2589_);
v_acc_2593_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2588_, v_fst_2591_, v_snd_2592_, v_____s_2590_);
v___x_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2594_, 0, v_acc_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany___redArg(lean_object* v_cmp_2595_, lean_object* v_inst_2596_, lean_object* v_t_2597_, lean_object* v_l_2598_){
_start:
{
lean_object* v___f_2599_; lean_object* v___x_2600_; 
v___f_2599_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2599_, 0, v_cmp_2595_);
v___x_2600_ = lean_apply_4(v_inst_2596_, lean_box(0), v_l_2598_, v_t_2597_, v___f_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany(lean_object* v_00_u03b1_2601_, lean_object* v_00_u03b2_2602_, lean_object* v_cmp_2603_, lean_object* v_inst_2604_, lean_object* v_00_u03c1_2605_, lean_object* v_inst_2606_, lean_object* v_t_2607_, lean_object* v_l_2608_){
_start:
{
lean_object* v___f_2609_; lean_object* v___x_2610_; 
v___f_2609_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2609_, 0, v_cmp_2603_);
v___x_2610_ = lean_apply_4(v_inst_2606_, lean_box(0), v_l_2608_, v_t_2607_, v___f_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_2611_, lean_object* v_a_2612_, lean_object* v_____s_2613_){
_start:
{
uint8_t v___x_2614_; 
lean_inc(v_____s_2613_);
lean_inc(v_a_2612_);
lean_inc_ref(v_cmp_2611_);
v___x_2614_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2611_, v_a_2612_, v_____s_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_box(0);
v___x_2616_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2611_, v_a_2612_, v___x_2615_, v_____s_2613_);
v___x_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
return v___x_2617_;
}
else
{
lean_object* v___x_2618_; 
lean_dec(v_a_2612_);
lean_dec_ref(v_cmp_2611_);
v___x_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2618_, 0, v_____s_2613_);
return v___x_2618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit___redArg(lean_object* v_cmp_2619_, lean_object* v_inst_2620_, lean_object* v_t_2621_, lean_object* v_l_2622_){
_start:
{
lean_object* v___f_2623_; lean_object* v___x_2624_; 
v___f_2623_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2623_, 0, v_cmp_2619_);
v___x_2624_ = lean_apply_4(v_inst_2620_, lean_box(0), v_l_2622_, v_t_2621_, v___f_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit(lean_object* v_00_u03b1_2625_, lean_object* v_cmp_2626_, lean_object* v_inst_2627_, lean_object* v_00_u03c1_2628_, lean_object* v_inst_2629_, lean_object* v_t_2630_, lean_object* v_l_2631_){
_start:
{
lean_object* v___f_2632_; lean_object* v___x_2633_; 
v___f_2632_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2632_, 0, v_cmp_2626_);
v___x_2633_ = lean_apply_4(v_inst_2629_, lean_box(0), v_l_2631_, v_t_2630_, v___f_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_union___redArg(lean_object* v_cmp_2634_, lean_object* v_t_u2081_2635_, lean_object* v_t_u2082_2636_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_2634_, v_t_u2081_2635_, v_t_u2082_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_union(lean_object* v_00_u03b1_2638_, lean_object* v_00_u03b2_2639_, lean_object* v_cmp_2640_, lean_object* v_inst_2641_, lean_object* v_t_u2081_2642_, lean_object* v_t_u2082_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_2640_, v_t_u2081_2642_, v_t_u2082_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instUnionOfTransCmp___redArg(lean_object* v_cmp_2645_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_union), 6, 4);
lean_closure_set(v___x_2646_, 0, lean_box(0));
lean_closure_set(v___x_2646_, 1, lean_box(0));
lean_closure_set(v___x_2646_, 2, v_cmp_2645_);
lean_closure_set(v___x_2646_, 3, lean_box(0));
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instUnionOfTransCmp(lean_object* v_00_u03b1_2647_, lean_object* v_00_u03b2_2648_, lean_object* v_cmp_2649_, lean_object* v_inst_2650_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_union), 6, 4);
lean_closure_set(v___x_2651_, 0, lean_box(0));
lean_closure_set(v___x_2651_, 1, lean_box(0));
lean_closure_set(v___x_2651_, 2, v_cmp_2649_);
lean_closure_set(v___x_2651_, 3, lean_box(0));
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_inter___redArg(lean_object* v_cmp_2652_, lean_object* v_t_u2081_2653_, lean_object* v_t_u2082_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_2652_, v_t_u2081_2653_, v_t_u2082_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_inter(lean_object* v_00_u03b1_2656_, lean_object* v_00_u03b2_2657_, lean_object* v_cmp_2658_, lean_object* v_inst_2659_, lean_object* v_t_u2081_2660_, lean_object* v_t_u2082_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_2658_, v_t_u2081_2660_, v_t_u2082_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInterOfTransCmp___redArg(lean_object* v_cmp_2663_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_inter), 6, 4);
lean_closure_set(v___x_2664_, 0, lean_box(0));
lean_closure_set(v___x_2664_, 1, lean_box(0));
lean_closure_set(v___x_2664_, 2, v_cmp_2663_);
lean_closure_set(v___x_2664_, 3, lean_box(0));
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInterOfTransCmp(lean_object* v_00_u03b1_2665_, lean_object* v_00_u03b2_2666_, lean_object* v_cmp_2667_, lean_object* v_inst_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_inter), 6, 4);
lean_closure_set(v___x_2669_, 0, lean_box(0));
lean_closure_set(v___x_2669_, 1, lean_box(0));
lean_closure_set(v___x_2669_, 2, v_cmp_2667_);
lean_closure_set(v___x_2669_, 3, lean_box(0));
return v___x_2669_;
}
}
uint8_t l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(lean_object* v_cmp_2670_, lean_object* v_inst_2671_, lean_object* v_m_u2081_2672_, lean_object* v_m_u2082_2673_){
_start:
{
uint8_t v___x_2674_; 
v___x_2674_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2670_, v_inst_2671_, v_m_u2081_2672_, v_m_u2082_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2670_ = stack[0].m_obj;
lean_object* v_inst_2671_ = stack[1].m_obj;
lean_object* v_m_u2081_2672_ = stack[2].m_obj;
lean_object* v_m_u2082_2673_ = stack[3].m_obj;
uint8_t v_res_2675_;
v_res_2675_ = l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(v_cmp_2670_, v_inst_2671_, v_m_u2081_2672_, v_m_u2082_2673_);
stack->m_num = v_res_2675_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_2676_, lean_object* v_inst_2677_, lean_object* v_m_u2081_2678_, lean_object* v_m_u2082_2679_){
_start:
{
uint8_t v_res_2680_; lean_object* v_r_2681_; 
v_res_2680_ = l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(v_cmp_2676_, v_inst_2677_, v_m_u2081_2678_, v_m_u2082_2679_);
v_r_2681_ = lean_box(v_res_2680_);
return v_r_2681_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp___redArg(lean_object* v_cmp_2682_, lean_object* v_inst_2683_){
_start:
{
lean_object* v___f_2684_; 
v___f_2684_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2684_, 0, v_cmp_2682_);
lean_closure_set(v___f_2684_, 1, v_inst_2683_);
return v___f_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp(lean_object* v_00_u03b1_2685_, lean_object* v_00_u03b2_2686_, lean_object* v_cmp_2687_, lean_object* v_inst_2688_, lean_object* v_inst_2689_){
_start:
{
lean_object* v___f_2690_; 
v___f_2690_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2690_, 0, v_cmp_2687_);
lean_closure_set(v___f_2690_, 1, v_inst_2689_);
return v___f_2690_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_diff___redArg(lean_object* v_cmp_2691_, lean_object* v_t_u2081_2692_, lean_object* v_t_u2082_2693_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2691_, v_t_u2081_2692_, v_t_u2082_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_diff(lean_object* v_00_u03b1_2695_, lean_object* v_00_u03b2_2696_, lean_object* v_cmp_2697_, lean_object* v_inst_2698_, lean_object* v_t_u2081_2699_, lean_object* v_t_u2082_2700_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2697_, v_t_u2081_2699_, v_t_u2082_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSDiffOfTransCmp___redArg(lean_object* v_cmp_2702_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_diff), 6, 4);
lean_closure_set(v___x_2703_, 0, lean_box(0));
lean_closure_set(v___x_2703_, 1, lean_box(0));
lean_closure_set(v___x_2703_, 2, v_cmp_2702_);
lean_closure_set(v___x_2703_, 3, lean_box(0));
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSDiffOfTransCmp(lean_object* v_00_u03b1_2704_, lean_object* v_00_u03b2_2705_, lean_object* v_cmp_2706_, lean_object* v_inst_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_diff), 6, 4);
lean_closure_set(v___x_2708_, 0, lean_box(0));
lean_closure_set(v___x_2708_, 1, lean_box(0));
lean_closure_set(v___x_2708_, 2, v_cmp_2706_);
lean_closure_set(v___x_2708_, 3, lean_box(0));
return v___x_2708_;
}
}
uint8_t l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(lean_object* v_cmp_2709_, lean_object* v_inst_2710_, lean_object* v_x_2711_, lean_object* v_x_2712_){
_start:
{
uint8_t v___x_2713_; 
v___x_2713_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2709_, v_inst_2710_, v_x_2711_, v_x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2709_ = stack[0].m_obj;
lean_object* v_inst_2710_ = stack[1].m_obj;
lean_object* v_x_2711_ = stack[2].m_obj;
lean_object* v_x_2712_ = stack[3].m_obj;
uint8_t v_res_2714_;
v_res_2714_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(v_cmp_2709_, v_inst_2710_, v_x_2711_, v_x_2712_);
stack->m_num = v_res_2714_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_2715_, lean_object* v_inst_2716_, lean_object* v_x_2717_, lean_object* v_x_2718_){
_start:
{
uint8_t v_res_2719_; lean_object* v_r_2720_; 
v_res_2719_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(v_cmp_2715_, v_inst_2716_, v_x_2717_, v_x_2718_);
v_r_2720_ = lean_box(v_res_2719_);
return v_r_2720_;
}
}
uint8_t l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(lean_object* v_00_u03b1_2721_, lean_object* v_00_u03b2_2722_, lean_object* v_cmp_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_){
_start:
{
uint8_t v___x_2730_; 
v___x_2730_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2723_, v_inst_2726_, v_x_2728_, v_x_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT void l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2723_ = stack[2].m_obj;
lean_object* v_inst_2726_ = stack[5].m_obj;
lean_object* v_x_2728_ = stack[7].m_obj;
lean_object* v_x_2729_ = stack[8].m_obj;
uint8_t v_res_2731_;
v_res_2731_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(lean_box(0), lean_box(0), v_cmp_2723_, lean_box(0), lean_box(0), v_inst_2726_, lean_box(0), v_x_2728_, v_x_2729_);
stack->m_num = v_res_2731_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_2732_, lean_object* v_00_u03b2_2733_, lean_object* v_cmp_2734_, lean_object* v_inst_2735_, lean_object* v_inst_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v_x_2739_, lean_object* v_x_2740_){
_start:
{
uint8_t v_res_2741_; lean_object* v_r_2742_; 
v_res_2741_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(v_00_u03b1_2732_, v_00_u03b2_2733_, v_cmp_2734_, v_inst_2735_, v_inst_2736_, v_inst_2737_, v_inst_2738_, v_x_2739_, v_x_2740_);
v_r_2742_ = lean_box(v_res_2741_);
return v_r_2742_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_2743_, lean_object* v_a_2744_, lean_object* v_____s_2745_){
_start:
{
lean_object* v_acc_2746_; lean_object* v___x_2747_; 
v_acc_2746_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2743_, v_a_2744_, v_____s_2745_);
v___x_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2747_, 0, v_acc_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany___redArg(lean_object* v_cmp_2748_, lean_object* v_inst_2749_, lean_object* v_t_2750_, lean_object* v_l_2751_){
_start:
{
lean_object* v___f_2752_; lean_object* v___x_2753_; 
v___f_2752_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2752_, 0, v_cmp_2748_);
v___x_2753_ = lean_apply_4(v_inst_2749_, lean_box(0), v_l_2751_, v_t_2750_, v___f_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany(lean_object* v_00_u03b1_2754_, lean_object* v_00_u03b2_2755_, lean_object* v_cmp_2756_, lean_object* v_inst_2757_, lean_object* v_00_u03c1_2758_, lean_object* v_inst_2759_, lean_object* v_t_2760_, lean_object* v_l_2761_){
_start:
{
lean_object* v___f_2762_; lean_object* v___x_2763_; 
v___f_2762_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2762_, 0, v_cmp_2756_);
v___x_2763_ = lean_apply_4(v_inst_2759_, lean_box(0), v_l_2761_, v_t_2760_, v___f_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_2767_, lean_object* v___x_2768_, lean_object* v_m_2769_, lean_object* v_prec_2770_){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2771_ = ((lean_object*)(l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_2772_ = lean_box(0);
v___x_2773_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2774_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2773_, v___f_2767_, v___x_2772_, v_m_2769_);
v___x_2775_ = l_List_repr___redArg(v___x_2768_, v___x_2774_);
v___x_2776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2771_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = l_Repr_addAppParen(v___x_2776_, v_prec_2770_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_2778_, lean_object* v___x_2779_, lean_object* v_m_2780_, lean_object* v_prec_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(v___f_2778_, v___x_2779_, v_m_2780_, v_prec_2781_);
lean_dec(v_prec_2781_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg(lean_object* v_inst_2783_, lean_object* v_inst_2784_){
_start:
{
lean_object* v___f_2785_; lean_object* v___f_2786_; lean_object* v___x_2787_; lean_object* v___f_2788_; 
v___f_2785_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___f_2786_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2786_, 0, v_inst_2784_);
v___x_2787_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2787_, 0, lean_box(0));
lean_closure_set(v___x_2787_, 1, lean_box(0));
lean_closure_set(v___x_2787_, 2, v_inst_2783_);
lean_closure_set(v___x_2787_, 3, v___f_2786_);
v___f_2788_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2788_, 0, v___f_2785_);
lean_closure_set(v___f_2788_, 1, v___x_2787_);
return v___f_2788_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp(lean_object* v_00_u03b1_2789_, lean_object* v_00_u03b2_2790_, lean_object* v_cmp_2791_, lean_object* v_inst_2792_, lean_object* v_inst_2793_, lean_object* v_inst_2794_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg(v_inst_2793_, v_inst_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_2796_, lean_object* v_00_u03b2_2797_, lean_object* v_cmp_2798_, lean_object* v_inst_2799_, lean_object* v_inst_2800_, lean_object* v_inst_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Std_ExtTreeMap_instReprOfTransCmp(v_00_u03b1_2796_, v_00_u03b2_2797_, v_cmp_2798_, v_inst_2799_, v_inst_2800_, v_inst_2801_);
lean_dec_ref(v_cmp_2798_);
return v_res_2802_;
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
