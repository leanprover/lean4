// Lean compiler output
// Module: Std.Data.ExtDTreeMap.Basic
// Imports: public import Std.Data.DTreeMap.Lemmas
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
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Sigma_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_map___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_ExtDTreeMap___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__0_value;
static const lean_string_object l_Std_ExtDTreeMap___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__1 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__1_value;
static const lean_string_object l_Std_ExtDTreeMap___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__2 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__2_value;
static const lean_string_object l_Std_ExtDTreeMap___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__3 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__3_value;
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__4 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__4_value;
static const lean_array_object l_Std_ExtDTreeMap___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__5 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__5_value;
static const lean_string_object l_Std_ExtDTreeMap___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__6 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__6_value;
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__7 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__7_value;
static const lean_string_object l_Std_ExtDTreeMap___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__8 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__8_value;
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__9 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__9_value;
static const lean_string_object l_Std_ExtDTreeMap___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__10 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__10_value;
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__11 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__11_value;
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__12;
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__13;
static const lean_string_object l_Std_ExtDTreeMap___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__14 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__14_value;
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__15 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__15_value;
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__16 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__16_value;
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__15_value),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_ExtDTreeMap___auto__1___closed__17 = (const lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__17_value;
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__18;
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__19;
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__20;
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__21;
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__22;
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__23;
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__24;
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__25;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mk(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift_u2082___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_liftOn_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_liftOn_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_liftOn_u2082___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_pliftOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_pliftOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_pliftOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall___redArg();
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty___redArg();
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg();
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__0_value;
static const lean_string_object l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__1 = (const lean_object*)&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__1_value;
static const lean_string_object l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__2 = (const lean_object*)&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtDTreeMap_foldr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_foldr___redArg___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__0_value;
static const lean_closure_object l_Std_ExtDTreeMap_foldr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_foldr___redArg___closed__1 = (const lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__1_value;
static const lean_closure_object l_Std_ExtDTreeMap_foldr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_foldr___redArg___closed__2 = (const lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__2_value;
static const lean_closure_object l_Std_ExtDTreeMap_foldr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_foldr___redArg___closed__3 = (const lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__3_value;
static const lean_closure_object l_Std_ExtDTreeMap_foldr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_foldr___redArg___closed__4 = (const lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__4_value;
static const lean_closure_object l_Std_ExtDTreeMap_foldr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_foldr___redArg___closed__5 = (const lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__5_value;
static const lean_closure_object l_Std_ExtDTreeMap_foldr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_foldr___redArg___closed__6 = (const lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__6_value;
static const lean_ctor_object l_Std_ExtDTreeMap_foldr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__0_value),((lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__1_value)}};
static const lean_object* l_Std_ExtDTreeMap_foldr___redArg___closed__7 = (const lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__7_value;
static const lean_ctor_object l_Std_ExtDTreeMap_foldr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__7_value),((lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__2_value),((lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__3_value),((lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__4_value),((lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__5_value)}};
static const lean_object* l_Std_ExtDTreeMap_foldr___redArg___closed__8 = (const lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__8_value;
static const lean_ctor_object l_Std_ExtDTreeMap_foldr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__8_value),((lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__6_value)}};
static const lean_object* l_Std_ExtDTreeMap_foldr___redArg___closed__9 = (const lean_object*)&l_Std_ExtDTreeMap_foldr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_ExtDTreeMap_partition___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_ExtDTreeMap_partition___redArg___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_partition___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_ExtDTreeMap_any___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_ExtDTreeMap_any___redArg___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_any___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtDTreeMap_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtDTreeMap_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_keys___redArg___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_keys___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtDTreeMap_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtDTreeMap_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_keysArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtDTreeMap_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtDTreeMap_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_values___redArg___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_values___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtDTreeMap_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtDTreeMap_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_valuesArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtDTreeMap_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtDTreeMap_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_toList___redArg___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtDTreeMap_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtDTreeMap_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_toArray___redArg___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtDTreeMap_Const_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtDTreeMap_Const_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_Const_toList___redArg___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_Const_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtDTreeMap_Const_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0_value;
static const lean_array_object l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1 = (const lean_object*)&l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instUnionOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instUnionOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_inter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInterOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInterOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_Const_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSDiffOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSDiffOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.ExtDTreeMap.ofList "};
static const lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__12, &l_Std_ExtDTreeMap___auto__1___closed__12_once, _init_l_Std_ExtDTreeMap___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__17));
v___x_45_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__13, &l_Std_ExtDTreeMap___auto__1___closed__13_once, _init_l_Std_ExtDTreeMap___auto__1___closed__13);
v___x_46_ = lean_array_push(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__18, &l_Std_ExtDTreeMap___auto__1___closed__18_once, _init_l_Std_ExtDTreeMap___auto__1___closed__18);
v___x_48_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__11));
v___x_49_ = lean_box(2);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__19, &l_Std_ExtDTreeMap___auto__1___closed__19_once, _init_l_Std_ExtDTreeMap___auto__1___closed__19);
v___x_52_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__5));
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__21(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__20, &l_Std_ExtDTreeMap___auto__1___closed__20_once, _init_l_Std_ExtDTreeMap___auto__1___closed__20);
v___x_55_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__9));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__22(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__21, &l_Std_ExtDTreeMap___auto__1___closed__21_once, _init_l_Std_ExtDTreeMap___auto__1___closed__21);
v___x_59_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__5));
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__23(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__22, &l_Std_ExtDTreeMap___auto__1___closed__22_once, _init_l_Std_ExtDTreeMap___auto__1___closed__22);
v___x_62_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__7));
v___x_63_ = lean_box(2);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__24(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__23, &l_Std_ExtDTreeMap___auto__1___closed__23_once, _init_l_Std_ExtDTreeMap___auto__1___closed__23);
v___x_66_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__25(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__24, &l_Std_ExtDTreeMap___auto__1___closed__24_once, _init_l_Std_ExtDTreeMap___auto__1___closed__24);
v___x_69_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__4));
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mk___redArg(lean_object* v_t_73_){
_start:
{
lean_inc(v_t_73_);
return v_t_73_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mk___redArg___boxed(lean_object* v_t_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_ExtDTreeMap_mk___redArg(v_t_74_);
lean_dec(v_t_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mk(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_cmp_78_, lean_object* v_t_79_){
_start:
{
lean_inc(v_t_79_);
return v_t_79_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mk___boxed(lean_object* v_00_u03b1_80_, lean_object* v_00_u03b2_81_, lean_object* v_cmp_82_, lean_object* v_t_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_ExtDTreeMap_mk(v_00_u03b1_80_, v_00_u03b2_81_, v_cmp_82_, v_t_83_);
lean_dec(v_t_83_);
lean_dec_ref(v_cmp_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift___redArg(lean_object* v_f_85_, lean_object* v_t_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_apply_1(v_f_85_, v_t_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift(lean_object* v_00_u03b1_88_, lean_object* v_00_u03b2_89_, lean_object* v_cmp_90_, lean_object* v_00_u03b3_91_, lean_object* v_f_92_, lean_object* v_h_93_, lean_object* v_t_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_apply_1(v_f_92_, v_t_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift___boxed(lean_object* v_00_u03b1_96_, lean_object* v_00_u03b2_97_, lean_object* v_cmp_98_, lean_object* v_00_u03b3_99_, lean_object* v_f_100_, lean_object* v_h_101_, lean_object* v_t_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Std_ExtDTreeMap_lift(v_00_u03b1_96_, v_00_u03b2_97_, v_cmp_98_, v_00_u03b3_99_, v_f_100_, v_h_101_, v_t_102_);
lean_dec_ref(v_cmp_98_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift_u2082___redArg(lean_object* v_f_104_, lean_object* v_m_u2081_105_, lean_object* v_m_u2082_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_apply_2(v_f_104_, v_m_u2081_105_, v_m_u2082_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift_u2082(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_cmp_110_, lean_object* v_00_u03b3_111_, lean_object* v_f_112_, lean_object* v_h_113_, lean_object* v_m_u2081_114_, lean_object* v_m_u2082_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_apply_2(v_f_112_, v_m_u2081_114_, v_m_u2082_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift_u2082___boxed(lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_, lean_object* v_cmp_119_, lean_object* v_00_u03b3_120_, lean_object* v_f_121_, lean_object* v_h_122_, lean_object* v_m_u2081_123_, lean_object* v_m_u2082_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_ExtDTreeMap_lift_u2082(v_00_u03b1_117_, v_00_u03b2_118_, v_cmp_119_, v_00_u03b3_120_, v_f_121_, v_h_122_, v_m_u2081_123_, v_m_u2082_124_);
lean_dec_ref(v_cmp_119_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_liftOn_u2082___redArg(lean_object* v_t_u2081_126_, lean_object* v_t_u2082_127_, lean_object* v_f_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_apply_2(v_f_128_, v_t_u2081_126_, v_t_u2082_127_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_liftOn_u2082(lean_object* v_00_u03b1_130_, lean_object* v_00_u03b2_131_, lean_object* v_cmp_132_, lean_object* v_00_u03b3_133_, lean_object* v_t_u2081_134_, lean_object* v_t_u2082_135_, lean_object* v_f_136_, lean_object* v_h_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_apply_2(v_f_136_, v_t_u2081_134_, v_t_u2082_135_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_liftOn_u2082___boxed(lean_object* v_00_u03b1_139_, lean_object* v_00_u03b2_140_, lean_object* v_cmp_141_, lean_object* v_00_u03b3_142_, lean_object* v_t_u2081_143_, lean_object* v_t_u2082_144_, lean_object* v_f_145_, lean_object* v_h_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Std_ExtDTreeMap_liftOn_u2082(v_00_u03b1_139_, v_00_u03b2_140_, v_cmp_141_, v_00_u03b3_142_, v_t_u2081_143_, v_t_u2082_144_, v_f_145_, v_h_146_);
lean_dec_ref(v_cmp_141_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_pliftOn___redArg(lean_object* v_t_148_, lean_object* v_f_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_apply_2(v_f_149_, v_t_148_, lean_box(0));
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_pliftOn(lean_object* v_00_u03b1_151_, lean_object* v_00_u03b2_152_, lean_object* v_cmp_153_, lean_object* v_00_u03b3_154_, lean_object* v_t_155_, lean_object* v_f_156_, lean_object* v_h_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_apply_2(v_f_156_, v_t_155_, lean_box(0));
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_pliftOn___boxed(lean_object* v_00_u03b1_159_, lean_object* v_00_u03b2_160_, lean_object* v_cmp_161_, lean_object* v_00_u03b3_162_, lean_object* v_t_163_, lean_object* v_f_164_, lean_object* v_h_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_ExtDTreeMap_pliftOn(v_00_u03b1_159_, v_00_u03b2_160_, v_cmp_161_, v_00_u03b3_162_, v_t_163_, v_f_164_, v_h_165_);
lean_dec_ref(v_cmp_161_);
return v_res_166_;
}
}
lean_object* l_Std_ExtDTreeMap_instCoeTypeForall___redArg(){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_instCoeTypeForall___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_169_;
v_res_169_ = l_Std_ExtDTreeMap_instCoeTypeForall___redArg();
stack->m_obj
 = v_res_169_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall___redArg___boxed(lean_object* v___dummy_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_ExtDTreeMap_instCoeTypeForall___redArg();
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall(lean_object* v_00_u03b1_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_box(0);
return v___x_173_;
}
}
lean_object* l_Std_ExtDTreeMap_empty___redArg(){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_box(1);
return v___x_175_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_176_;
v_res_176_ = l_Std_ExtDTreeMap_empty___redArg();
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty___redArg___boxed(lean_object* v___dummy_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_ExtDTreeMap_empty___redArg();
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_cmp_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_box(1);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty___boxed(lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_cmp_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_ExtDTreeMap_empty(v_00_u03b1_183_, v_00_u03b2_184_, v_cmp_185_);
lean_dec_ref(v_cmp_185_);
return v_res_186_;
}
}
lean_object* l_Std_ExtDTreeMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(1);
return v___x_188_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_189_;
v_res_189_ = l_Std_ExtDTreeMap_instEmptyCollection___redArg();
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_ExtDTreeMap_instEmptyCollection___redArg();
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection(lean_object* v_00_u03b1_192_, lean_object* v_00_u03b2_193_, lean_object* v_cmp_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(1);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_cmp_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_ExtDTreeMap_instEmptyCollection(v_00_u03b1_196_, v_00_u03b2_197_, v_cmp_198_);
lean_dec_ref(v_cmp_198_);
return v_res_199_;
}
}
lean_object* l_Std_ExtDTreeMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_box(1);
return v___x_201_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_202_;
v_res_202_ = l_Std_ExtDTreeMap_instInhabited___redArg();
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited___redArg___boxed(lean_object* v___dummy_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_ExtDTreeMap_instInhabited___redArg();
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_cmp_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_box(1);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited___boxed(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_cmp_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Std_ExtDTreeMap_instInhabited(v_00_u03b1_209_, v_00_u03b2_210_, v_cmp_211_);
lean_dec_ref(v_cmp_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insert___redArg(lean_object* v_cmp_213_, lean_object* v_t_214_, lean_object* v_a_215_, lean_object* v_b_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_213_, v_a_215_, v_b_216_, v_t_214_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insert(lean_object* v_00_u03b1_218_, lean_object* v_00_u03b2_219_, lean_object* v_cmp_220_, lean_object* v_inst_221_, lean_object* v_t_222_, lean_object* v_a_223_, lean_object* v_b_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_220_, v_a_223_, v_b_224_, v_t_222_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0(lean_object* v_cmp_226_, lean_object* v_e_227_){
_start:
{
lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_fst_228_ = lean_ctor_get(v_e_227_, 0);
lean_inc(v_fst_228_);
v_snd_229_ = lean_ctor_get(v_e_227_, 1);
lean_inc(v_snd_229_);
lean_dec_ref(v_e_227_);
v___x_230_ = lean_box(1);
v___x_231_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_226_, v_fst_228_, v_snd_229_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg(lean_object* v_cmp_232_){
_start:
{
lean_object* v___f_233_; 
v___f_233_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_233_, 0, v_cmp_232_);
return v___f_233_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_cmp_236_, lean_object* v_inst_237_){
_start:
{
lean_object* v___f_238_; 
v___f_238_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_238_, 0, v_cmp_236_);
return v___f_238_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0(lean_object* v_cmp_239_, lean_object* v_e_240_, lean_object* v_s_241_){
_start:
{
lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_244_; 
v_fst_242_ = lean_ctor_get(v_e_240_, 0);
lean_inc(v_fst_242_);
v_snd_243_ = lean_ctor_get(v_e_240_, 1);
lean_inc(v_snd_243_);
lean_dec_ref(v_e_240_);
v___x_244_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_239_, v_fst_242_, v_snd_243_, v_s_241_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg(lean_object* v_cmp_245_){
_start:
{
lean_object* v___f_246_; 
v___f_246_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_246_, 0, v_cmp_245_);
return v___f_246_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_cmp_249_, lean_object* v_inst_250_){
_start:
{
lean_object* v___f_251_; 
v___f_251_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_251_, 0, v_cmp_249_);
return v___f_251_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertIfNew___redArg(lean_object* v_cmp_252_, lean_object* v_t_253_, lean_object* v_a_254_, lean_object* v_b_255_){
_start:
{
uint8_t v___x_256_; 
lean_inc(v_t_253_);
lean_inc(v_a_254_);
lean_inc_ref(v_cmp_252_);
v___x_256_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_252_, v_a_254_, v_t_253_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
v___x_257_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_252_, v_a_254_, v_b_255_, v_t_253_);
return v___x_257_;
}
else
{
lean_dec(v_b_255_);
lean_dec(v_a_254_);
lean_dec_ref(v_cmp_252_);
return v_t_253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertIfNew(lean_object* v_00_u03b1_258_, lean_object* v_00_u03b2_259_, lean_object* v_cmp_260_, lean_object* v_inst_261_, lean_object* v_t_262_, lean_object* v_a_263_, lean_object* v_b_264_){
_start:
{
uint8_t v___x_265_; 
lean_inc(v_t_262_);
lean_inc(v_a_263_);
lean_inc_ref(v_cmp_260_);
v___x_265_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_260_, v_a_263_, v_t_262_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_260_, v_a_263_, v_b_264_, v_t_262_);
return v___x_266_;
}
else
{
lean_dec(v_b_264_);
lean_dec(v_a_263_);
lean_dec_ref(v_cmp_260_);
return v_t_262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsert___redArg(lean_object* v_cmp_267_, lean_object* v_t_268_, lean_object* v_a_269_, lean_object* v_b_270_){
_start:
{
lean_object* v_sz_271_; lean_object* v_m_272_; lean_object* v___y_274_; 
v_sz_271_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_268_);
v_m_272_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_267_, v_a_269_, v_b_270_, v_t_268_);
if (lean_obj_tag(v_m_272_) == 0)
{
lean_object* v_size_278_; 
v_size_278_ = lean_ctor_get(v_m_272_, 0);
lean_inc(v_size_278_);
v___y_274_ = v_size_278_;
goto v___jp_273_;
}
else
{
lean_object* v___x_279_; 
v___x_279_ = lean_unsigned_to_nat(0u);
v___y_274_ = v___x_279_;
goto v___jp_273_;
}
v___jp_273_:
{
uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_nat_dec_eq(v_sz_271_, v___y_274_);
lean_dec(v___y_274_);
lean_dec(v_sz_271_);
v___x_276_ = lean_box(v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_m_272_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsert(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_cmp_282_, lean_object* v_inst_283_, lean_object* v_t_284_, lean_object* v_a_285_, lean_object* v_b_286_){
_start:
{
lean_object* v_sz_287_; lean_object* v_m_288_; lean_object* v___y_290_; 
v_sz_287_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_284_);
v_m_288_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_282_, v_a_285_, v_b_286_, v_t_284_);
if (lean_obj_tag(v_m_288_) == 0)
{
lean_object* v_size_294_; 
v_size_294_ = lean_ctor_get(v_m_288_, 0);
lean_inc(v_size_294_);
v___y_290_ = v_size_294_;
goto v___jp_289_;
}
else
{
lean_object* v___x_295_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v___y_290_ = v___x_295_;
goto v___jp_289_;
}
v___jp_289_:
{
uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_nat_dec_eq(v_sz_287_, v___y_290_);
lean_dec(v___y_290_);
lean_dec(v_sz_287_);
v___x_292_ = lean_box(v___x_291_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_m_288_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_296_, lean_object* v_t_297_, lean_object* v_a_298_, lean_object* v_b_299_){
_start:
{
uint8_t v___x_300_; 
lean_inc(v_t_297_);
lean_inc(v_a_298_);
lean_inc_ref(v_cmp_296_);
v___x_300_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_296_, v_a_298_, v_t_297_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_296_, v_a_298_, v_b_299_, v_t_297_);
v___x_302_ = lean_box(v___x_300_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_301_);
return v___x_303_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v_b_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_cmp_296_);
v___x_304_ = lean_box(v___x_300_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v_t_297_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_306_, lean_object* v_00_u03b2_307_, lean_object* v_cmp_308_, lean_object* v_inst_309_, lean_object* v_t_310_, lean_object* v_a_311_, lean_object* v_b_312_){
_start:
{
uint8_t v___x_313_; 
lean_inc(v_t_310_);
lean_inc(v_a_311_);
lean_inc_ref(v_cmp_308_);
v___x_313_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_308_, v_a_311_, v_t_310_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_308_, v_a_311_, v_b_312_, v_t_310_);
v___x_315_ = lean_box(v___x_313_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_b_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_cmp_308_);
v___x_317_ = lean_box(v___x_313_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v_t_310_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_319_, lean_object* v_t_320_, lean_object* v_a_321_, lean_object* v_b_322_){
_start:
{
lean_object* v___x_323_; 
lean_inc(v_a_321_);
lean_inc(v_t_320_);
lean_inc_ref(v_cmp_319_);
v___x_323_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_319_, v_t_320_, v_a_321_);
if (lean_obj_tag(v___x_323_) == 0)
{
uint8_t v___x_324_; 
lean_inc(v_t_320_);
lean_inc(v_a_321_);
lean_inc_ref(v_cmp_319_);
v___x_324_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_319_, v_a_321_, v_t_320_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_319_, v_a_321_, v_b_322_, v_t_320_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_323_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
return v___x_326_;
}
else
{
lean_object* v___x_327_; 
lean_dec(v_b_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_cmp_319_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_323_);
lean_ctor_set(v___x_327_, 1, v_t_320_);
return v___x_327_;
}
}
else
{
lean_object* v___x_328_; 
lean_dec(v_b_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_cmp_319_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_323_);
lean_ctor_set(v___x_328_, 1, v_t_320_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_cmp_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_t_334_, lean_object* v_a_335_, lean_object* v_b_336_){
_start:
{
lean_object* v___x_337_; 
lean_inc(v_a_335_);
lean_inc(v_t_334_);
lean_inc_ref(v_cmp_331_);
v___x_337_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_331_, v_t_334_, v_a_335_);
if (lean_obj_tag(v___x_337_) == 0)
{
uint8_t v___x_338_; 
lean_inc(v_t_334_);
lean_inc(v_a_335_);
lean_inc_ref(v_cmp_331_);
v___x_338_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_331_, v_a_335_, v_t_334_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_331_, v_a_335_, v_b_336_, v_t_334_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_337_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
return v___x_340_;
}
else
{
lean_object* v___x_341_; 
lean_dec(v_b_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_cmp_331_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_337_);
lean_ctor_set(v___x_341_, 1, v_t_334_);
return v___x_341_;
}
}
else
{
lean_object* v___x_342_; 
lean_dec(v_b_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_cmp_331_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_337_);
lean_ctor_set(v___x_342_, 1, v_t_334_);
return v___x_342_;
}
}
}
uint8_t l_Std_ExtDTreeMap_contains___redArg(lean_object* v_cmp_343_, lean_object* v_t_344_, lean_object* v_a_345_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_343_, v_a_345_, v_t_344_);
return v___x_346_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_343_ = stack[0].m_obj;
lean_object* v_t_344_ = stack[1].m_obj;
lean_object* v_a_345_ = stack[2].m_obj;
uint8_t v_res_347_;
v_res_347_ = l_Std_ExtDTreeMap_contains___redArg(v_cmp_343_, v_t_344_, v_a_345_);
stack->m_num = v_res_347_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_contains___redArg___boxed(lean_object* v_cmp_348_, lean_object* v_t_349_, lean_object* v_a_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Std_ExtDTreeMap_contains___redArg(v_cmp_348_, v_t_349_, v_a_350_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
uint8_t l_Std_ExtDTreeMap_contains(lean_object* v_00_u03b1_353_, lean_object* v_00_u03b2_354_, lean_object* v_cmp_355_, lean_object* v_inst_356_, lean_object* v_t_357_, lean_object* v_a_358_){
_start:
{
uint8_t v___x_359_; 
v___x_359_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_355_, v_a_358_, v_t_357_);
return v___x_359_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_355_ = stack[2].m_obj;
lean_object* v_t_357_ = stack[4].m_obj;
lean_object* v_a_358_ = stack[5].m_obj;
uint8_t v_res_360_;
v_res_360_ = l_Std_ExtDTreeMap_contains(lean_box(0), lean_box(0), v_cmp_355_, lean_box(0), v_t_357_, v_a_358_);
stack->m_num = v_res_360_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_contains___boxed(lean_object* v_00_u03b1_361_, lean_object* v_00_u03b2_362_, lean_object* v_cmp_363_, lean_object* v_inst_364_, lean_object* v_t_365_, lean_object* v_a_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Std_ExtDTreeMap_contains(v_00_u03b1_361_, v_00_u03b2_362_, v_cmp_363_, v_inst_364_, v_t_365_, v_a_366_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg(){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = lean_box(0);
return v___x_370_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_371_;
v_res_371_ = l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg();
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg___boxed(lean_object* v___dummy_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg();
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_cmp_376_, lean_object* v_inst_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_box(0);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___boxed(lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_cmp_381_, lean_object* v_inst_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_ExtDTreeMap_instMembershipOfTransCmp(v_00_u03b1_379_, v_00_u03b2_380_, v_cmp_381_, v_inst_382_);
lean_dec_ref(v_cmp_381_);
return v_res_383_;
}
}
uint8_t l_Std_ExtDTreeMap_instDecidableMem___redArg(lean_object* v_cmp_384_, lean_object* v_m_385_, lean_object* v_a_386_){
_start:
{
uint8_t v___x_387_; 
v___x_387_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_384_, v_a_386_, v_m_385_);
return v___x_387_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_384_ = stack[0].m_obj;
lean_object* v_m_385_ = stack[1].m_obj;
lean_object* v_a_386_ = stack[2].m_obj;
uint8_t v_res_388_;
v_res_388_ = l_Std_ExtDTreeMap_instDecidableMem___redArg(v_cmp_384_, v_m_385_, v_a_386_);
stack->m_num = v_res_388_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_389_, lean_object* v_m_390_, lean_object* v_a_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Std_ExtDTreeMap_instDecidableMem___redArg(v_cmp_389_, v_m_390_, v_a_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
uint8_t l_Std_ExtDTreeMap_instDecidableMem(lean_object* v_00_u03b1_394_, lean_object* v_00_u03b2_395_, lean_object* v_cmp_396_, lean_object* v_inst_397_, lean_object* v_m_398_, lean_object* v_a_399_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_396_, v_a_399_, v_m_398_);
return v___x_400_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_396_ = stack[2].m_obj;
lean_object* v_m_398_ = stack[4].m_obj;
lean_object* v_a_399_ = stack[5].m_obj;
uint8_t v_res_401_;
v_res_401_ = l_Std_ExtDTreeMap_instDecidableMem(lean_box(0), lean_box(0), v_cmp_396_, lean_box(0), v_m_398_, v_a_399_);
stack->m_num = v_res_401_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_402_, lean_object* v_00_u03b2_403_, lean_object* v_cmp_404_, lean_object* v_inst_405_, lean_object* v_m_406_, lean_object* v_a_407_){
_start:
{
uint8_t v_res_408_; lean_object* v_r_409_; 
v_res_408_ = l_Std_ExtDTreeMap_instDecidableMem(v_00_u03b1_402_, v_00_u03b2_403_, v_cmp_404_, v_inst_405_, v_m_406_, v_a_407_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___redArg(lean_object* v_t_410_){
_start:
{
if (lean_obj_tag(v_t_410_) == 0)
{
lean_object* v_size_411_; 
v_size_411_ = lean_ctor_get(v_t_410_, 0);
lean_inc(v_size_411_);
return v_size_411_;
}
else
{
lean_object* v___x_412_; 
v___x_412_ = lean_unsigned_to_nat(0u);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___redArg___boxed(lean_object* v_t_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_ExtDTreeMap_size___redArg(v_t_413_);
lean_dec(v_t_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size(lean_object* v_00_u03b1_415_, lean_object* v_00_u03b2_416_, lean_object* v_cmp_417_, lean_object* v_t_418_){
_start:
{
if (lean_obj_tag(v_t_418_) == 0)
{
lean_object* v_size_419_; 
v_size_419_ = lean_ctor_get(v_t_418_, 0);
lean_inc(v_size_419_);
return v_size_419_;
}
else
{
lean_object* v___x_420_; 
v___x_420_ = lean_unsigned_to_nat(0u);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___boxed(lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_cmp_423_, lean_object* v_t_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_ExtDTreeMap_size(v_00_u03b1_421_, v_00_u03b2_422_, v_cmp_423_, v_t_424_);
lean_dec(v_t_424_);
lean_dec_ref(v_cmp_423_);
return v_res_425_;
}
}
uint8_t l_Std_ExtDTreeMap_isEmpty___redArg(lean_object* v_t_426_){
_start:
{
if (lean_obj_tag(v_t_426_) == 0)
{
uint8_t v___x_427_; 
v___x_427_ = 0;
return v___x_427_;
}
else
{
uint8_t v___x_428_; 
v___x_428_ = 1;
return v___x_428_;
}
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_426_ = stack[0].m_obj;
uint8_t v_res_429_;
v_res_429_ = l_Std_ExtDTreeMap_isEmpty___redArg(v_t_426_);
stack->m_num = v_res_429_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_isEmpty___redArg___boxed(lean_object* v_t_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_Std_ExtDTreeMap_isEmpty___redArg(v_t_430_);
lean_dec(v_t_430_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
uint8_t l_Std_ExtDTreeMap_isEmpty(lean_object* v_00_u03b1_433_, lean_object* v_00_u03b2_434_, lean_object* v_cmp_435_, lean_object* v_t_436_){
_start:
{
if (lean_obj_tag(v_t_436_) == 0)
{
uint8_t v___x_437_; 
v___x_437_ = 0;
return v___x_437_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = 1;
return v___x_438_;
}
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_435_ = stack[2].m_obj;
lean_object* v_t_436_ = stack[3].m_obj;
uint8_t v_res_439_;
v_res_439_ = l_Std_ExtDTreeMap_isEmpty(lean_box(0), lean_box(0), v_cmp_435_, v_t_436_);
stack->m_num = v_res_439_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_440_, lean_object* v_00_u03b2_441_, lean_object* v_cmp_442_, lean_object* v_t_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Std_ExtDTreeMap_isEmpty(v_00_u03b1_440_, v_00_u03b2_441_, v_cmp_442_, v_t_443_);
lean_dec(v_t_443_);
lean_dec_ref(v_cmp_442_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_erase___redArg(lean_object* v_cmp_446_, lean_object* v_t_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_446_, v_a_448_, v_t_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_erase(lean_object* v_00_u03b1_450_, lean_object* v_00_u03b2_451_, lean_object* v_cmp_452_, lean_object* v_inst_453_, lean_object* v_t_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_452_, v_a_455_, v_t_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x3f___redArg(lean_object* v_cmp_457_, lean_object* v_t_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_457_, v_t_458_, v_a_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x3f(lean_object* v_00_u03b1_461_, lean_object* v_00_u03b2_462_, lean_object* v_cmp_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_t_466_, lean_object* v_a_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_463_, v_t_466_, v_a_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get___redArg(lean_object* v_cmp_469_, lean_object* v_t_470_, lean_object* v_a_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_469_, v_t_470_, v_a_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get(lean_object* v_00_u03b1_473_, lean_object* v_00_u03b2_474_, lean_object* v_cmp_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_t_478_, lean_object* v_a_479_, lean_object* v_h_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_475_, v_t_478_, v_a_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___redArg(lean_object* v_cmp_482_, lean_object* v_t_483_, lean_object* v_a_484_, lean_object* v_inst_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_482_, v_t_483_, v_a_484_, v_inst_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___redArg___boxed(lean_object* v_cmp_487_, lean_object* v_t_488_, lean_object* v_a_489_, lean_object* v_inst_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_ExtDTreeMap_get_x21___redArg(v_cmp_487_, v_t_488_, v_a_489_, v_inst_490_);
lean_dec(v_inst_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21(lean_object* v_00_u03b1_492_, lean_object* v_00_u03b2_493_, lean_object* v_cmp_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_t_497_, lean_object* v_a_498_, lean_object* v_inst_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_494_, v_t_497_, v_a_498_, v_inst_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___boxed(lean_object* v_00_u03b1_501_, lean_object* v_00_u03b2_502_, lean_object* v_cmp_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_t_506_, lean_object* v_a_507_, lean_object* v_inst_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_ExtDTreeMap_get_x21(v_00_u03b1_501_, v_00_u03b2_502_, v_cmp_503_, v_inst_504_, v_inst_505_, v_t_506_, v_a_507_, v_inst_508_);
lean_dec(v_inst_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg(lean_object* v_cmp_510_, lean_object* v_t_511_, lean_object* v_a_512_, lean_object* v_fallback_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_510_, v_t_511_, v_a_512_, v_fallback_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg___boxed(lean_object* v_cmp_515_, lean_object* v_t_516_, lean_object* v_a_517_, lean_object* v_fallback_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_ExtDTreeMap_getD___redArg(v_cmp_515_, v_t_516_, v_a_517_, v_fallback_518_);
lean_dec(v_fallback_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_cmp_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_t_525_, lean_object* v_a_526_, lean_object* v_fallback_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_522_, v_t_525_, v_a_526_, v_fallback_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___boxed(lean_object* v_00_u03b1_529_, lean_object* v_00_u03b2_530_, lean_object* v_cmp_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_t_534_, lean_object* v_a_535_, lean_object* v_fallback_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_ExtDTreeMap_getD(v_00_u03b1_529_, v_00_u03b2_530_, v_cmp_531_, v_inst_532_, v_inst_533_, v_t_534_, v_a_535_, v_fallback_536_);
lean_dec(v_fallback_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f___redArg(lean_object* v_cmp_538_, lean_object* v_t_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_538_, v_t_539_, v_a_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_, lean_object* v_cmp_544_, lean_object* v_inst_545_, lean_object* v_t_546_, lean_object* v_a_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_544_, v_t_546_, v_a_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey___redArg(lean_object* v_cmp_549_, lean_object* v_t_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_549_, v_t_550_, v_a_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey(lean_object* v_00_u03b1_553_, lean_object* v_00_u03b2_554_, lean_object* v_cmp_555_, lean_object* v_inst_556_, lean_object* v_t_557_, lean_object* v_a_558_, lean_object* v_h_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_555_, v_t_557_, v_a_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___redArg(lean_object* v_cmp_561_, lean_object* v_inst_562_, lean_object* v_t_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_561_, v_t_563_, v_a_564_, v_inst_562_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___redArg___boxed(lean_object* v_cmp_566_, lean_object* v_inst_567_, lean_object* v_t_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_ExtDTreeMap_getKey_x21___redArg(v_cmp_566_, v_inst_567_, v_t_568_, v_a_569_);
lean_dec(v_inst_567_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_cmp_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_t_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_573_, v_t_576_, v_a_577_, v_inst_575_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___boxed(lean_object* v_00_u03b1_579_, lean_object* v_00_u03b2_580_, lean_object* v_cmp_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_t_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_ExtDTreeMap_getKey_x21(v_00_u03b1_579_, v_00_u03b2_580_, v_cmp_581_, v_inst_582_, v_inst_583_, v_t_584_, v_a_585_);
lean_dec(v_inst_583_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___redArg(lean_object* v_cmp_587_, lean_object* v_t_588_, lean_object* v_a_589_, lean_object* v_fallback_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_587_, v_t_588_, v_a_589_, v_fallback_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_592_, lean_object* v_t_593_, lean_object* v_a_594_, lean_object* v_fallback_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_ExtDTreeMap_getKeyD___redArg(v_cmp_592_, v_t_593_, v_a_594_, v_fallback_595_);
lean_dec(v_fallback_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD(lean_object* v_00_u03b1_597_, lean_object* v_00_u03b2_598_, lean_object* v_cmp_599_, lean_object* v_inst_600_, lean_object* v_t_601_, lean_object* v_a_602_, lean_object* v_fallback_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_599_, v_t_601_, v_a_602_, v_fallback_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_605_, lean_object* v_00_u03b2_606_, lean_object* v_cmp_607_, lean_object* v_inst_608_, lean_object* v_t_609_, lean_object* v_a_610_, lean_object* v_fallback_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_ExtDTreeMap_getKeyD(v_00_u03b1_605_, v_00_u03b2_606_, v_cmp_607_, v_inst_608_, v_t_609_, v_a_610_, v_fallback_611_);
lean_dec(v_fallback_611_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___redArg(lean_object* v_t_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_ExtDTreeMap_minEntry_x3f___redArg(v_t_615_);
lean_dec(v_t_615_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_cmp_619_, lean_object* v_inst_620_, lean_object* v_t_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_623_, lean_object* v_00_u03b2_624_, lean_object* v_cmp_625_, lean_object* v_inst_626_, lean_object* v_t_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std_ExtDTreeMap_minEntry_x3f(v_00_u03b1_623_, v_00_u03b2_624_, v_cmp_625_, v_inst_626_, v_t_627_);
lean_dec(v_t_627_);
lean_dec_ref(v_cmp_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___redArg(lean_object* v_t_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___redArg___boxed(lean_object* v_t_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_ExtDTreeMap_minEntry___redArg(v_t_631_);
lean_dec(v_t_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry(lean_object* v_00_u03b1_633_, lean_object* v_00_u03b2_634_, lean_object* v_cmp_635_, lean_object* v_inst_636_, lean_object* v_t_637_, lean_object* v_h_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___boxed(lean_object* v_00_u03b1_640_, lean_object* v_00_u03b2_641_, lean_object* v_cmp_642_, lean_object* v_inst_643_, lean_object* v_t_644_, lean_object* v_h_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_ExtDTreeMap_minEntry(v_00_u03b1_640_, v_00_u03b2_641_, v_cmp_642_, v_inst_643_, v_t_644_, v_h_645_);
lean_dec(v_t_644_);
lean_dec_ref(v_cmp_642_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___redArg(lean_object* v_inst_647_, lean_object* v_t_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_647_, v_t_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_650_, lean_object* v_t_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Std_ExtDTreeMap_minEntry_x21___redArg(v_inst_650_, v_t_651_);
lean_dec(v_t_651_);
lean_dec_ref(v_inst_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21(lean_object* v_00_u03b1_653_, lean_object* v_00_u03b2_654_, lean_object* v_cmp_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_t_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_657_, v_t_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_660_, lean_object* v_00_u03b2_661_, lean_object* v_cmp_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_t_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_ExtDTreeMap_minEntry_x21(v_00_u03b1_660_, v_00_u03b2_661_, v_cmp_662_, v_inst_663_, v_inst_664_, v_t_665_);
lean_dec(v_t_665_);
lean_dec_ref(v_inst_664_);
lean_dec_ref(v_cmp_662_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___redArg(lean_object* v_t_667_, lean_object* v_fallback_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_667_, v_fallback_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___redArg___boxed(lean_object* v_t_670_, lean_object* v_fallback_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Std_ExtDTreeMap_minEntryD___redArg(v_t_670_, v_fallback_671_);
lean_dec_ref(v_fallback_671_);
lean_dec(v_t_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD(lean_object* v_00_u03b1_673_, lean_object* v_00_u03b2_674_, lean_object* v_cmp_675_, lean_object* v_inst_676_, lean_object* v_t_677_, lean_object* v_fallback_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_677_, v_fallback_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_cmp_682_, lean_object* v_inst_683_, lean_object* v_t_684_, lean_object* v_fallback_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Std_ExtDTreeMap_minEntryD(v_00_u03b1_680_, v_00_u03b2_681_, v_cmp_682_, v_inst_683_, v_t_684_, v_fallback_685_);
lean_dec_ref(v_fallback_685_);
lean_dec(v_t_684_);
lean_dec_ref(v_cmp_682_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___redArg(lean_object* v_t_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_ExtDTreeMap_maxEntry_x3f___redArg(v_t_689_);
lean_dec(v_t_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_691_, lean_object* v_00_u03b2_692_, lean_object* v_cmp_693_, lean_object* v_inst_694_, lean_object* v_t_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_697_, lean_object* v_00_u03b2_698_, lean_object* v_cmp_699_, lean_object* v_inst_700_, lean_object* v_t_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_ExtDTreeMap_maxEntry_x3f(v_00_u03b1_697_, v_00_u03b2_698_, v_cmp_699_, v_inst_700_, v_t_701_);
lean_dec(v_t_701_);
lean_dec_ref(v_cmp_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___redArg(lean_object* v_t_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___redArg___boxed(lean_object* v_t_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_ExtDTreeMap_maxEntry___redArg(v_t_705_);
lean_dec(v_t_705_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry(lean_object* v_00_u03b1_707_, lean_object* v_00_u03b2_708_, lean_object* v_cmp_709_, lean_object* v_inst_710_, lean_object* v_t_711_, lean_object* v_h_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_714_, lean_object* v_00_u03b2_715_, lean_object* v_cmp_716_, lean_object* v_inst_717_, lean_object* v_t_718_, lean_object* v_h_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_ExtDTreeMap_maxEntry(v_00_u03b1_714_, v_00_u03b2_715_, v_cmp_716_, v_inst_717_, v_t_718_, v_h_719_);
lean_dec(v_t_718_);
lean_dec_ref(v_cmp_716_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___redArg(lean_object* v_inst_721_, lean_object* v_t_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_721_, v_t_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_724_, lean_object* v_t_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Std_ExtDTreeMap_maxEntry_x21___redArg(v_inst_724_, v_t_725_);
lean_dec(v_t_725_);
lean_dec_ref(v_inst_724_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21(lean_object* v_00_u03b1_727_, lean_object* v_00_u03b2_728_, lean_object* v_cmp_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_t_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_731_, v_t_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_734_, lean_object* v_00_u03b2_735_, lean_object* v_cmp_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_t_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_ExtDTreeMap_maxEntry_x21(v_00_u03b1_734_, v_00_u03b2_735_, v_cmp_736_, v_inst_737_, v_inst_738_, v_t_739_);
lean_dec(v_t_739_);
lean_dec_ref(v_inst_738_);
lean_dec_ref(v_cmp_736_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___redArg(lean_object* v_t_741_, lean_object* v_fallback_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_741_, v_fallback_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_744_, lean_object* v_fallback_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Std_ExtDTreeMap_maxEntryD___redArg(v_t_744_, v_fallback_745_);
lean_dec_ref(v_fallback_745_);
lean_dec(v_t_744_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD(lean_object* v_00_u03b1_747_, lean_object* v_00_u03b2_748_, lean_object* v_cmp_749_, lean_object* v_inst_750_, lean_object* v_t_751_, lean_object* v_fallback_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_751_, v_fallback_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_754_, lean_object* v_00_u03b2_755_, lean_object* v_cmp_756_, lean_object* v_inst_757_, lean_object* v_t_758_, lean_object* v_fallback_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_ExtDTreeMap_maxEntryD(v_00_u03b1_754_, v_00_u03b2_755_, v_cmp_756_, v_inst_757_, v_t_758_, v_fallback_759_);
lean_dec_ref(v_fallback_759_);
lean_dec(v_t_758_);
lean_dec_ref(v_cmp_756_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___redArg(lean_object* v_t_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_ExtDTreeMap_minKey_x3f___redArg(v_t_763_);
lean_dec(v_t_763_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f(lean_object* v_00_u03b1_765_, lean_object* v_00_u03b2_766_, lean_object* v_cmp_767_, lean_object* v_inst_768_, lean_object* v_t_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_771_, lean_object* v_00_u03b2_772_, lean_object* v_cmp_773_, lean_object* v_inst_774_, lean_object* v_t_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Std_ExtDTreeMap_minKey_x3f(v_00_u03b1_771_, v_00_u03b2_772_, v_cmp_773_, v_inst_774_, v_t_775_);
lean_dec(v_t_775_);
lean_dec_ref(v_cmp_773_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___redArg(lean_object* v_t_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___redArg___boxed(lean_object* v_t_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_ExtDTreeMap_minKey___redArg(v_t_779_);
lean_dec(v_t_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey(lean_object* v_00_u03b1_781_, lean_object* v_00_u03b2_782_, lean_object* v_cmp_783_, lean_object* v_inst_784_, lean_object* v_t_785_, lean_object* v_h_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___boxed(lean_object* v_00_u03b1_788_, lean_object* v_00_u03b2_789_, lean_object* v_cmp_790_, lean_object* v_inst_791_, lean_object* v_t_792_, lean_object* v_h_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_ExtDTreeMap_minKey(v_00_u03b1_788_, v_00_u03b2_789_, v_cmp_790_, v_inst_791_, v_t_792_, v_h_793_);
lean_dec(v_t_792_);
lean_dec_ref(v_cmp_790_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___redArg(lean_object* v_inst_795_, lean_object* v_t_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_795_, v_t_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_798_, lean_object* v_t_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_ExtDTreeMap_minKey_x21___redArg(v_inst_798_, v_t_799_);
lean_dec(v_t_799_);
lean_dec(v_inst_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_cmp_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_t_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_805_, v_t_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_808_, lean_object* v_00_u03b2_809_, lean_object* v_cmp_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_t_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Std_ExtDTreeMap_minKey_x21(v_00_u03b1_808_, v_00_u03b2_809_, v_cmp_810_, v_inst_811_, v_inst_812_, v_t_813_);
lean_dec(v_t_813_);
lean_dec(v_inst_812_);
lean_dec_ref(v_cmp_810_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___redArg(lean_object* v_t_815_, lean_object* v_fallback_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_815_, v_fallback_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___redArg___boxed(lean_object* v_t_818_, lean_object* v_fallback_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_ExtDTreeMap_minKeyD___redArg(v_t_818_, v_fallback_819_);
lean_dec(v_fallback_819_);
lean_dec(v_t_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD(lean_object* v_00_u03b1_821_, lean_object* v_00_u03b2_822_, lean_object* v_cmp_823_, lean_object* v_inst_824_, lean_object* v_t_825_, lean_object* v_fallback_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_825_, v_fallback_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_cmp_830_, lean_object* v_inst_831_, lean_object* v_t_832_, lean_object* v_fallback_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_ExtDTreeMap_minKeyD(v_00_u03b1_828_, v_00_u03b2_829_, v_cmp_830_, v_inst_831_, v_t_832_, v_fallback_833_);
lean_dec(v_fallback_833_);
lean_dec(v_t_832_);
lean_dec_ref(v_cmp_830_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___redArg(lean_object* v_t_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_ExtDTreeMap_maxKey_x3f___redArg(v_t_837_);
lean_dec(v_t_837_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f(lean_object* v_00_u03b1_839_, lean_object* v_00_u03b2_840_, lean_object* v_cmp_841_, lean_object* v_inst_842_, lean_object* v_t_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_845_, lean_object* v_00_u03b2_846_, lean_object* v_cmp_847_, lean_object* v_inst_848_, lean_object* v_t_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_ExtDTreeMap_maxKey_x3f(v_00_u03b1_845_, v_00_u03b2_846_, v_cmp_847_, v_inst_848_, v_t_849_);
lean_dec(v_t_849_);
lean_dec_ref(v_cmp_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___redArg(lean_object* v_t_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___redArg___boxed(lean_object* v_t_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Std_ExtDTreeMap_maxKey___redArg(v_t_853_);
lean_dec(v_t_853_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey(lean_object* v_00_u03b1_855_, lean_object* v_00_u03b2_856_, lean_object* v_cmp_857_, lean_object* v_inst_858_, lean_object* v_t_859_, lean_object* v_h_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___boxed(lean_object* v_00_u03b1_862_, lean_object* v_00_u03b2_863_, lean_object* v_cmp_864_, lean_object* v_inst_865_, lean_object* v_t_866_, lean_object* v_h_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_ExtDTreeMap_maxKey(v_00_u03b1_862_, v_00_u03b2_863_, v_cmp_864_, v_inst_865_, v_t_866_, v_h_867_);
lean_dec(v_t_866_);
lean_dec_ref(v_cmp_864_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___redArg(lean_object* v_inst_869_, lean_object* v_t_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_869_, v_t_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_872_, lean_object* v_t_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Std_ExtDTreeMap_maxKey_x21___redArg(v_inst_872_, v_t_873_);
lean_dec(v_t_873_);
lean_dec(v_inst_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21(lean_object* v_00_u03b1_875_, lean_object* v_00_u03b2_876_, lean_object* v_cmp_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_t_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_879_, v_t_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_882_, lean_object* v_00_u03b2_883_, lean_object* v_cmp_884_, lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_t_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Std_ExtDTreeMap_maxKey_x21(v_00_u03b1_882_, v_00_u03b2_883_, v_cmp_884_, v_inst_885_, v_inst_886_, v_t_887_);
lean_dec(v_t_887_);
lean_dec(v_inst_886_);
lean_dec_ref(v_cmp_884_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___redArg(lean_object* v_t_889_, lean_object* v_fallback_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_889_, v_fallback_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_892_, lean_object* v_fallback_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Std_ExtDTreeMap_maxKeyD___redArg(v_t_892_, v_fallback_893_);
lean_dec(v_fallback_893_);
lean_dec(v_t_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD(lean_object* v_00_u03b1_895_, lean_object* v_00_u03b2_896_, lean_object* v_cmp_897_, lean_object* v_inst_898_, lean_object* v_t_899_, lean_object* v_fallback_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_899_, v_fallback_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_cmp_904_, lean_object* v_inst_905_, lean_object* v_t_906_, lean_object* v_fallback_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_ExtDTreeMap_maxKeyD(v_00_u03b1_902_, v_00_u03b2_903_, v_cmp_904_, v_inst_905_, v_t_906_, v_fallback_907_);
lean_dec(v_fallback_907_);
lean_dec(v_t_906_);
lean_dec_ref(v_cmp_904_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_909_, lean_object* v_n_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_909_, v_n_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_912_, lean_object* v_n_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(v_t_912_, v_n_913_);
lean_dec(v_t_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_915_, lean_object* v_00_u03b2_916_, lean_object* v_cmp_917_, lean_object* v_inst_918_, lean_object* v_t_919_, lean_object* v_n_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_919_, v_n_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_922_, lean_object* v_00_u03b2_923_, lean_object* v_cmp_924_, lean_object* v_inst_925_, lean_object* v_t_926_, lean_object* v_n_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Std_ExtDTreeMap_entryAtIdx_x3f(v_00_u03b1_922_, v_00_u03b2_923_, v_cmp_924_, v_inst_925_, v_t_926_, v_n_927_);
lean_dec(v_t_926_);
lean_dec_ref(v_cmp_924_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___redArg(lean_object* v_t_929_, lean_object* v_n_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_929_, v_n_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_932_, lean_object* v_n_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_ExtDTreeMap_entryAtIdx___redArg(v_t_932_, v_n_933_);
lean_dec(v_t_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_cmp_937_, lean_object* v_inst_938_, lean_object* v_t_939_, lean_object* v_n_940_, lean_object* v_h_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_939_, v_n_940_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_943_, lean_object* v_00_u03b2_944_, lean_object* v_cmp_945_, lean_object* v_inst_946_, lean_object* v_t_947_, lean_object* v_n_948_, lean_object* v_h_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Std_ExtDTreeMap_entryAtIdx(v_00_u03b1_943_, v_00_u03b2_944_, v_cmp_945_, v_inst_946_, v_t_947_, v_n_948_, v_h_949_);
lean_dec(v_t_947_);
lean_dec_ref(v_cmp_945_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_951_, lean_object* v_t_952_, lean_object* v_n_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_951_, v_t_952_, v_n_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_955_, lean_object* v_t_956_, lean_object* v_n_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(v_inst_955_, v_t_956_, v_n_957_);
lean_dec(v_t_956_);
lean_dec_ref(v_inst_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_959_, lean_object* v_00_u03b2_960_, lean_object* v_cmp_961_, lean_object* v_inst_962_, lean_object* v_inst_963_, lean_object* v_t_964_, lean_object* v_n_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_963_, v_t_964_, v_n_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_967_, lean_object* v_00_u03b2_968_, lean_object* v_cmp_969_, lean_object* v_inst_970_, lean_object* v_inst_971_, lean_object* v_t_972_, lean_object* v_n_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Std_ExtDTreeMap_entryAtIdx_x21(v_00_u03b1_967_, v_00_u03b2_968_, v_cmp_969_, v_inst_970_, v_inst_971_, v_t_972_, v_n_973_);
lean_dec(v_t_972_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_cmp_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___redArg(lean_object* v_t_975_, lean_object* v_n_976_, lean_object* v_fallback_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_975_, v_n_976_, v_fallback_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_979_, lean_object* v_n_980_, lean_object* v_fallback_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Std_ExtDTreeMap_entryAtIdxD___redArg(v_t_979_, v_n_980_, v_fallback_981_);
lean_dec_ref(v_fallback_981_);
lean_dec(v_t_979_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD(lean_object* v_00_u03b1_983_, lean_object* v_00_u03b2_984_, lean_object* v_cmp_985_, lean_object* v_inst_986_, lean_object* v_t_987_, lean_object* v_n_988_, lean_object* v_fallback_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_987_, v_n_988_, v_fallback_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_991_, lean_object* v_00_u03b2_992_, lean_object* v_cmp_993_, lean_object* v_inst_994_, lean_object* v_t_995_, lean_object* v_n_996_, lean_object* v_fallback_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_ExtDTreeMap_entryAtIdxD(v_00_u03b1_991_, v_00_u03b2_992_, v_cmp_993_, v_inst_994_, v_t_995_, v_n_996_, v_fallback_997_);
lean_dec_ref(v_fallback_997_);
lean_dec(v_t_995_);
lean_dec_ref(v_cmp_993_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_999_, lean_object* v_n_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_999_, v_n_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_1002_, lean_object* v_n_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(v_t_1002_, v_n_1003_);
lean_dec(v_t_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_1005_, lean_object* v_00_u03b2_1006_, lean_object* v_cmp_1007_, lean_object* v_inst_1008_, lean_object* v_t_1009_, lean_object* v_n_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_1009_, v_n_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_1012_, lean_object* v_00_u03b2_1013_, lean_object* v_cmp_1014_, lean_object* v_inst_1015_, lean_object* v_t_1016_, lean_object* v_n_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Std_ExtDTreeMap_keyAtIdx_x3f(v_00_u03b1_1012_, v_00_u03b2_1013_, v_cmp_1014_, v_inst_1015_, v_t_1016_, v_n_1017_);
lean_dec(v_t_1016_);
lean_dec_ref(v_cmp_1014_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___redArg(lean_object* v_t_1019_, lean_object* v_n_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1019_, v_n_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_1022_, lean_object* v_n_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_ExtDTreeMap_keyAtIdx___redArg(v_t_1022_, v_n_1023_);
lean_dec(v_t_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx(lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_cmp_1027_, lean_object* v_inst_1028_, lean_object* v_t_1029_, lean_object* v_n_1030_, lean_object* v_h_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1029_, v_n_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_1033_, lean_object* v_00_u03b2_1034_, lean_object* v_cmp_1035_, lean_object* v_inst_1036_, lean_object* v_t_1037_, lean_object* v_n_1038_, lean_object* v_h_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Std_ExtDTreeMap_keyAtIdx(v_00_u03b1_1033_, v_00_u03b2_1034_, v_cmp_1035_, v_inst_1036_, v_t_1037_, v_n_1038_, v_h_1039_);
lean_dec(v_t_1037_);
lean_dec_ref(v_cmp_1035_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_1041_, lean_object* v_t_1042_, lean_object* v_n_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1041_, v_t_1042_, v_n_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_1045_, lean_object* v_t_1046_, lean_object* v_n_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(v_inst_1045_, v_t_1046_, v_n_1047_);
lean_dec(v_t_1046_);
lean_dec(v_inst_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_1049_, lean_object* v_00_u03b2_1050_, lean_object* v_cmp_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_t_1054_, lean_object* v_n_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1053_, v_t_1054_, v_n_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_1057_, lean_object* v_00_u03b2_1058_, lean_object* v_cmp_1059_, lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_t_1062_, lean_object* v_n_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Std_ExtDTreeMap_keyAtIdx_x21(v_00_u03b1_1057_, v_00_u03b2_1058_, v_cmp_1059_, v_inst_1060_, v_inst_1061_, v_t_1062_, v_n_1063_);
lean_dec(v_t_1062_);
lean_dec(v_inst_1061_);
lean_dec_ref(v_cmp_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___redArg(lean_object* v_t_1065_, lean_object* v_n_1066_, lean_object* v_fallback_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1065_, v_n_1066_, v_fallback_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_1069_, lean_object* v_n_1070_, lean_object* v_fallback_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Std_ExtDTreeMap_keyAtIdxD___redArg(v_t_1069_, v_n_1070_, v_fallback_1071_);
lean_dec(v_fallback_1071_);
lean_dec(v_t_1069_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD(lean_object* v_00_u03b1_1073_, lean_object* v_00_u03b2_1074_, lean_object* v_cmp_1075_, lean_object* v_inst_1076_, lean_object* v_t_1077_, lean_object* v_n_1078_, lean_object* v_fallback_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1077_, v_n_1078_, v_fallback_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_1081_, lean_object* v_00_u03b2_1082_, lean_object* v_cmp_1083_, lean_object* v_inst_1084_, lean_object* v_t_1085_, lean_object* v_n_1086_, lean_object* v_fallback_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Std_ExtDTreeMap_keyAtIdxD(v_00_u03b1_1081_, v_00_u03b2_1082_, v_cmp_1083_, v_inst_1084_, v_t_1085_, v_n_1086_, v_fallback_1087_);
lean_dec(v_fallback_1087_);
lean_dec(v_t_1085_);
lean_dec_ref(v_cmp_1083_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1089_, lean_object* v_t_1090_, lean_object* v_k_1091_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1089_, v_k_1091_, v___x_1092_, v_t_1090_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1094_, lean_object* v_00_u03b2_1095_, lean_object* v_cmp_1096_, lean_object* v_inst_1097_, lean_object* v_t_1098_, lean_object* v_k_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_box(0);
v___x_1101_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1096_, v_k_1099_, v___x_1100_, v_t_1098_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1102_, lean_object* v_t_1103_, lean_object* v_k_1104_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_box(0);
v___x_1106_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1102_, v_k_1104_, v___x_1105_, v_t_1103_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1107_, lean_object* v_00_u03b2_1108_, lean_object* v_cmp_1109_, lean_object* v_inst_1110_, lean_object* v_t_1111_, lean_object* v_k_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1109_, v_k_1112_, v___x_1113_, v_t_1111_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1115_, lean_object* v_t_1116_, lean_object* v_k_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_box(0);
v___x_1119_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1115_, v_k_1117_, v___x_1118_, v_t_1116_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1120_, lean_object* v_00_u03b2_1121_, lean_object* v_cmp_1122_, lean_object* v_inst_1123_, lean_object* v_t_1124_, lean_object* v_k_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1122_, v_k_1125_, v___x_1126_, v_t_1124_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1128_, lean_object* v_t_1129_, lean_object* v_k_1130_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_box(0);
v___x_1132_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1128_, v_k_1130_, v___x_1131_, v_t_1129_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1133_, lean_object* v_00_u03b2_1134_, lean_object* v_cmp_1135_, lean_object* v_inst_1136_, lean_object* v_t_1137_, lean_object* v_k_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_box(0);
v___x_1140_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1135_, v_k_1138_, v___x_1139_, v_t_1137_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE___redArg(lean_object* v_cmp_1141_, lean_object* v_t_1142_, lean_object* v_k_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_1141_, v_k_1143_, v_t_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE(lean_object* v_00_u03b1_1145_, lean_object* v_00_u03b2_1146_, lean_object* v_cmp_1147_, lean_object* v_inst_1148_, lean_object* v_t_1149_, lean_object* v_k_1150_, lean_object* v_h_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_1147_, v_k_1150_, v_t_1149_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT___redArg(lean_object* v_cmp_1153_, lean_object* v_t_1154_, lean_object* v_k_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_1153_, v_k_1155_, v_t_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_cmp_1159_, lean_object* v_inst_1160_, lean_object* v_t_1161_, lean_object* v_k_1162_, lean_object* v_h_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_1159_, v_k_1162_, v_t_1161_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE___redArg(lean_object* v_cmp_1165_, lean_object* v_t_1166_, lean_object* v_k_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_1165_, v_k_1167_, v_t_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE(lean_object* v_00_u03b1_1169_, lean_object* v_00_u03b2_1170_, lean_object* v_cmp_1171_, lean_object* v_inst_1172_, lean_object* v_t_1173_, lean_object* v_k_1174_, lean_object* v_h_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_1171_, v_k_1174_, v_t_1173_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT___redArg(lean_object* v_cmp_1177_, lean_object* v_t_1178_, lean_object* v_k_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_1177_, v_k_1179_, v_t_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT(lean_object* v_00_u03b1_1181_, lean_object* v_00_u03b2_1182_, lean_object* v_cmp_1183_, lean_object* v_inst_1184_, lean_object* v_t_1185_, lean_object* v_k_1186_, lean_object* v_h_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_1183_, v_k_1186_, v_t_1185_);
return v___x_1188_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1192_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1193_ = lean_unsigned_to_nat(14u);
v___x_1194_ = lean_unsigned_to_nat(22u);
v___x_1195_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1196_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1197_ = l_mkPanicMessageWithDecl(v___x_1196_, v___x_1195_, v___x_1194_, v___x_1193_, v___x_1192_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1198_, lean_object* v_inst_1199_, lean_object* v_t_1200_, lean_object* v_k_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_box(0);
v___x_1203_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1198_, v_k_1201_, v___x_1202_, v_t_1200_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1205_ = l_panic___redArg(v_inst_1199_, v___x_1204_);
return v___x_1205_;
}
else
{
lean_object* v_val_1206_; 
v_val_1206_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_val_1206_);
lean_dec_ref_known(v___x_1203_, 1);
return v_val_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1207_, lean_object* v_inst_1208_, lean_object* v_t_1209_, lean_object* v_k_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_ExtDTreeMap_getEntryGE_x21___redArg(v_cmp_1207_, v_inst_1208_, v_t_1209_, v_k_1210_);
lean_dec_ref(v_inst_1208_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1212_, lean_object* v_00_u03b2_1213_, lean_object* v_cmp_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_t_1217_, lean_object* v_k_1218_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_box(0);
v___x_1220_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1214_, v_k_1218_, v___x_1219_, v_t_1217_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1222_ = l_panic___redArg(v_inst_1216_, v___x_1221_);
return v___x_1222_;
}
else
{
lean_object* v_val_1223_; 
v_val_1223_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_val_1223_);
lean_dec_ref_known(v___x_1220_, 1);
return v_val_1223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1224_, lean_object* v_00_u03b2_1225_, lean_object* v_cmp_1226_, lean_object* v_inst_1227_, lean_object* v_inst_1228_, lean_object* v_t_1229_, lean_object* v_k_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Std_ExtDTreeMap_getEntryGE_x21(v_00_u03b1_1224_, v_00_u03b2_1225_, v_cmp_1226_, v_inst_1227_, v_inst_1228_, v_t_1229_, v_k_1230_);
lean_dec_ref(v_inst_1228_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1232_, lean_object* v_inst_1233_, lean_object* v_t_1234_, lean_object* v_k_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_box(0);
v___x_1237_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1232_, v_k_1235_, v___x_1236_, v_t_1234_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1239_ = l_panic___redArg(v_inst_1233_, v___x_1238_);
return v___x_1239_;
}
else
{
lean_object* v_val_1240_; 
v_val_1240_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_val_1240_);
lean_dec_ref_known(v___x_1237_, 1);
return v_val_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1241_, lean_object* v_inst_1242_, lean_object* v_t_1243_, lean_object* v_k_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Std_ExtDTreeMap_getEntryGT_x21___redArg(v_cmp_1241_, v_inst_1242_, v_t_1243_, v_k_1244_);
lean_dec_ref(v_inst_1242_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1246_, lean_object* v_00_u03b2_1247_, lean_object* v_cmp_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_t_1251_, lean_object* v_k_1252_){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_box(0);
v___x_1254_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1248_, v_k_1252_, v___x_1253_, v_t_1251_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1256_ = l_panic___redArg(v_inst_1250_, v___x_1255_);
return v___x_1256_;
}
else
{
lean_object* v_val_1257_; 
v_val_1257_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_val_1257_);
lean_dec_ref_known(v___x_1254_, 1);
return v_val_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1258_, lean_object* v_00_u03b2_1259_, lean_object* v_cmp_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_t_1263_, lean_object* v_k_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Std_ExtDTreeMap_getEntryGT_x21(v_00_u03b1_1258_, v_00_u03b2_1259_, v_cmp_1260_, v_inst_1261_, v_inst_1262_, v_t_1263_, v_k_1264_);
lean_dec_ref(v_inst_1262_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1266_, lean_object* v_inst_1267_, lean_object* v_t_1268_, lean_object* v_k_1269_){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_box(0);
v___x_1271_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1266_, v_k_1269_, v___x_1270_, v_t_1268_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1273_ = l_panic___redArg(v_inst_1267_, v___x_1272_);
return v___x_1273_;
}
else
{
lean_object* v_val_1274_; 
v_val_1274_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v___x_1271_, 1);
return v_val_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1275_, lean_object* v_inst_1276_, lean_object* v_t_1277_, lean_object* v_k_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Std_ExtDTreeMap_getEntryLE_x21___redArg(v_cmp_1275_, v_inst_1276_, v_t_1277_, v_k_1278_);
lean_dec_ref(v_inst_1276_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1280_, lean_object* v_00_u03b2_1281_, lean_object* v_cmp_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_t_1285_, lean_object* v_k_1286_){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_box(0);
v___x_1288_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1282_, v_k_1286_, v___x_1287_, v_t_1285_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1290_ = l_panic___redArg(v_inst_1284_, v___x_1289_);
return v___x_1290_;
}
else
{
lean_object* v_val_1291_; 
v_val_1291_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_val_1291_);
lean_dec_ref_known(v___x_1288_, 1);
return v_val_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_00_u03b2_1293_, lean_object* v_cmp_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_t_1297_, lean_object* v_k_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_ExtDTreeMap_getEntryLE_x21(v_00_u03b1_1292_, v_00_u03b2_1293_, v_cmp_1294_, v_inst_1295_, v_inst_1296_, v_t_1297_, v_k_1298_);
lean_dec_ref(v_inst_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1300_, lean_object* v_inst_1301_, lean_object* v_t_1302_, lean_object* v_k_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1300_, v_k_1303_, v___x_1304_, v_t_1302_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1307_ = l_panic___redArg(v_inst_1301_, v___x_1306_);
return v___x_1307_;
}
else
{
lean_object* v_val_1308_; 
v_val_1308_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v___x_1305_, 1);
return v_val_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1309_, lean_object* v_inst_1310_, lean_object* v_t_1311_, lean_object* v_k_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Std_ExtDTreeMap_getEntryLT_x21___redArg(v_cmp_1309_, v_inst_1310_, v_t_1311_, v_k_1312_);
lean_dec_ref(v_inst_1310_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1314_, lean_object* v_00_u03b2_1315_, lean_object* v_cmp_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_t_1319_, lean_object* v_k_1320_){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1316_, v_k_1320_, v___x_1321_, v_t_1319_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1324_ = l_panic___redArg(v_inst_1318_, v___x_1323_);
return v___x_1324_;
}
else
{
lean_object* v_val_1325_; 
v_val_1325_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_val_1325_);
lean_dec_ref_known(v___x_1322_, 1);
return v_val_1325_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_00_u03b2_1327_, lean_object* v_cmp_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_t_1331_, lean_object* v_k_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Std_ExtDTreeMap_getEntryLT_x21(v_00_u03b1_1326_, v_00_u03b2_1327_, v_cmp_1328_, v_inst_1329_, v_inst_1330_, v_t_1331_, v_k_1332_);
lean_dec_ref(v_inst_1330_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___redArg(lean_object* v_cmp_1334_, lean_object* v_t_1335_, lean_object* v_k_1336_, lean_object* v_fallback_1337_){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_box(0);
v___x_1339_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1334_, v_k_1336_, v___x_1338_, v_t_1335_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_inc_ref(v_fallback_1337_);
return v_fallback_1337_;
}
else
{
lean_object* v_val_1340_; 
v_val_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_val_1340_);
lean_dec_ref_known(v___x_1339_, 1);
return v_val_1340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1341_, lean_object* v_t_1342_, lean_object* v_k_1343_, lean_object* v_fallback_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Std_ExtDTreeMap_getEntryGED___redArg(v_cmp_1341_, v_t_1342_, v_k_1343_, v_fallback_1344_);
lean_dec_ref(v_fallback_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED(lean_object* v_00_u03b1_1346_, lean_object* v_00_u03b2_1347_, lean_object* v_cmp_1348_, lean_object* v_inst_1349_, lean_object* v_t_1350_, lean_object* v_k_1351_, lean_object* v_fallback_1352_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_box(0);
v___x_1354_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1348_, v_k_1351_, v___x_1353_, v_t_1350_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_inc_ref(v_fallback_1352_);
return v_fallback_1352_;
}
else
{
lean_object* v_val_1355_; 
v_val_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_val_1355_);
lean_dec_ref_known(v___x_1354_, 1);
return v_val_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_00_u03b2_1357_, lean_object* v_cmp_1358_, lean_object* v_inst_1359_, lean_object* v_t_1360_, lean_object* v_k_1361_, lean_object* v_fallback_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Std_ExtDTreeMap_getEntryGED(v_00_u03b1_1356_, v_00_u03b2_1357_, v_cmp_1358_, v_inst_1359_, v_t_1360_, v_k_1361_, v_fallback_1362_);
lean_dec_ref(v_fallback_1362_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1364_, lean_object* v_t_1365_, lean_object* v_k_1366_, lean_object* v_fallback_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1364_, v_k_1366_, v___x_1368_, v_t_1365_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_inc_ref(v_fallback_1367_);
return v_fallback_1367_;
}
else
{
lean_object* v_val_1370_; 
v_val_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v___x_1369_, 1);
return v_val_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1371_, lean_object* v_t_1372_, lean_object* v_k_1373_, lean_object* v_fallback_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Std_ExtDTreeMap_getEntryGTD___redArg(v_cmp_1371_, v_t_1372_, v_k_1373_, v_fallback_1374_);
lean_dec_ref(v_fallback_1374_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD(lean_object* v_00_u03b1_1376_, lean_object* v_00_u03b2_1377_, lean_object* v_cmp_1378_, lean_object* v_inst_1379_, lean_object* v_t_1380_, lean_object* v_k_1381_, lean_object* v_fallback_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1378_, v_k_1381_, v___x_1383_, v_t_1380_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_inc_ref(v_fallback_1382_);
return v_fallback_1382_;
}
else
{
lean_object* v_val_1385_; 
v_val_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v___x_1384_, 1);
return v_val_1385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1386_, lean_object* v_00_u03b2_1387_, lean_object* v_cmp_1388_, lean_object* v_inst_1389_, lean_object* v_t_1390_, lean_object* v_k_1391_, lean_object* v_fallback_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Std_ExtDTreeMap_getEntryGTD(v_00_u03b1_1386_, v_00_u03b2_1387_, v_cmp_1388_, v_inst_1389_, v_t_1390_, v_k_1391_, v_fallback_1392_);
lean_dec_ref(v_fallback_1392_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___redArg(lean_object* v_cmp_1394_, lean_object* v_t_1395_, lean_object* v_k_1396_, lean_object* v_fallback_1397_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_box(0);
v___x_1399_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1394_, v_k_1396_, v___x_1398_, v_t_1395_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_inc_ref(v_fallback_1397_);
return v_fallback_1397_;
}
else
{
lean_object* v_val_1400_; 
v_val_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v___x_1399_, 1);
return v_val_1400_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1401_, lean_object* v_t_1402_, lean_object* v_k_1403_, lean_object* v_fallback_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Std_ExtDTreeMap_getEntryLED___redArg(v_cmp_1401_, v_t_1402_, v_k_1403_, v_fallback_1404_);
lean_dec_ref(v_fallback_1404_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED(lean_object* v_00_u03b1_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_cmp_1408_, lean_object* v_inst_1409_, lean_object* v_t_1410_, lean_object* v_k_1411_, lean_object* v_fallback_1412_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_box(0);
v___x_1414_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1408_, v_k_1411_, v___x_1413_, v_t_1410_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_inc_ref(v_fallback_1412_);
return v_fallback_1412_;
}
else
{
lean_object* v_val_1415_; 
v_val_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_val_1415_);
lean_dec_ref_known(v___x_1414_, 1);
return v_val_1415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_00_u03b2_1417_, lean_object* v_cmp_1418_, lean_object* v_inst_1419_, lean_object* v_t_1420_, lean_object* v_k_1421_, lean_object* v_fallback_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Std_ExtDTreeMap_getEntryLED(v_00_u03b1_1416_, v_00_u03b2_1417_, v_cmp_1418_, v_inst_1419_, v_t_1420_, v_k_1421_, v_fallback_1422_);
lean_dec_ref(v_fallback_1422_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1424_, lean_object* v_t_1425_, lean_object* v_k_1426_, lean_object* v_fallback_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_box(0);
v___x_1429_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1424_, v_k_1426_, v___x_1428_, v_t_1425_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_inc_ref(v_fallback_1427_);
return v_fallback_1427_;
}
else
{
lean_object* v_val_1430_; 
v_val_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_val_1430_);
lean_dec_ref_known(v___x_1429_, 1);
return v_val_1430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1431_, lean_object* v_t_1432_, lean_object* v_k_1433_, lean_object* v_fallback_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Std_ExtDTreeMap_getEntryLTD___redArg(v_cmp_1431_, v_t_1432_, v_k_1433_, v_fallback_1434_);
lean_dec_ref(v_fallback_1434_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD(lean_object* v_00_u03b1_1436_, lean_object* v_00_u03b2_1437_, lean_object* v_cmp_1438_, lean_object* v_inst_1439_, lean_object* v_t_1440_, lean_object* v_k_1441_, lean_object* v_fallback_1442_){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_box(0);
v___x_1444_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1438_, v_k_1441_, v___x_1443_, v_t_1440_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_inc_ref(v_fallback_1442_);
return v_fallback_1442_;
}
else
{
lean_object* v_val_1445_; 
v_val_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_val_1445_);
lean_dec_ref_known(v___x_1444_, 1);
return v_val_1445_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1446_, lean_object* v_00_u03b2_1447_, lean_object* v_cmp_1448_, lean_object* v_inst_1449_, lean_object* v_t_1450_, lean_object* v_k_1451_, lean_object* v_fallback_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Std_ExtDTreeMap_getEntryLTD(v_00_u03b1_1446_, v_00_u03b2_1447_, v_cmp_1448_, v_inst_1449_, v_t_1450_, v_k_1451_, v_fallback_1452_);
lean_dec_ref(v_fallback_1452_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1454_, lean_object* v_t_1455_, lean_object* v_k_1456_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_box(0);
v___x_1458_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1454_, v_k_1456_, v___x_1457_, v_t_1455_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1459_, lean_object* v_00_u03b2_1460_, lean_object* v_cmp_1461_, lean_object* v_inst_1462_, lean_object* v_t_1463_, lean_object* v_k_1464_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_box(0);
v___x_1466_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1461_, v_k_1464_, v___x_1465_, v_t_1463_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1467_, lean_object* v_t_1468_, lean_object* v_k_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_box(0);
v___x_1471_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1467_, v_k_1469_, v___x_1470_, v_t_1468_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1472_, lean_object* v_00_u03b2_1473_, lean_object* v_cmp_1474_, lean_object* v_inst_1475_, lean_object* v_t_1476_, lean_object* v_k_1477_){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_box(0);
v___x_1479_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1474_, v_k_1477_, v___x_1478_, v_t_1476_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1480_, lean_object* v_t_1481_, lean_object* v_k_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_box(0);
v___x_1484_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1480_, v_k_1482_, v___x_1483_, v_t_1481_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1485_, lean_object* v_00_u03b2_1486_, lean_object* v_cmp_1487_, lean_object* v_inst_1488_, lean_object* v_t_1489_, lean_object* v_k_1490_){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_box(0);
v___x_1492_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1487_, v_k_1490_, v___x_1491_, v_t_1489_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1493_, lean_object* v_t_1494_, lean_object* v_k_1495_){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_box(0);
v___x_1497_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1493_, v_k_1495_, v___x_1496_, v_t_1494_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1498_, lean_object* v_00_u03b2_1499_, lean_object* v_cmp_1500_, lean_object* v_inst_1501_, lean_object* v_t_1502_, lean_object* v_k_1503_){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_box(0);
v___x_1505_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1500_, v_k_1503_, v___x_1504_, v_t_1502_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE___redArg(lean_object* v_cmp_1506_, lean_object* v_t_1507_, lean_object* v_k_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1506_, v_k_1508_, v_t_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE(lean_object* v_00_u03b1_1510_, lean_object* v_00_u03b2_1511_, lean_object* v_cmp_1512_, lean_object* v_inst_1513_, lean_object* v_t_1514_, lean_object* v_k_1515_, lean_object* v_h_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1512_, v_k_1515_, v_t_1514_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT___redArg(lean_object* v_cmp_1518_, lean_object* v_t_1519_, lean_object* v_k_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1518_, v_k_1520_, v_t_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT(lean_object* v_00_u03b1_1522_, lean_object* v_00_u03b2_1523_, lean_object* v_cmp_1524_, lean_object* v_inst_1525_, lean_object* v_t_1526_, lean_object* v_k_1527_, lean_object* v_h_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1524_, v_k_1527_, v_t_1526_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE___redArg(lean_object* v_cmp_1530_, lean_object* v_t_1531_, lean_object* v_k_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1530_, v_k_1532_, v_t_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE(lean_object* v_00_u03b1_1534_, lean_object* v_00_u03b2_1535_, lean_object* v_cmp_1536_, lean_object* v_inst_1537_, lean_object* v_t_1538_, lean_object* v_k_1539_, lean_object* v_h_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1536_, v_k_1539_, v_t_1538_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT___redArg(lean_object* v_cmp_1542_, lean_object* v_t_1543_, lean_object* v_k_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1542_, v_k_1544_, v_t_1543_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT(lean_object* v_00_u03b1_1546_, lean_object* v_00_u03b2_1547_, lean_object* v_cmp_1548_, lean_object* v_inst_1549_, lean_object* v_t_1550_, lean_object* v_k_1551_, lean_object* v_h_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1548_, v_k_1551_, v_t_1550_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1554_, lean_object* v_inst_1555_, lean_object* v_t_1556_, lean_object* v_k_1557_){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_box(0);
v___x_1559_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1554_, v_k_1557_, v___x_1558_, v_t_1556_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1561_ = l_panic___redArg(v_inst_1555_, v___x_1560_);
return v___x_1561_;
}
else
{
lean_object* v_val_1562_; 
v_val_1562_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_val_1562_);
lean_dec_ref_known(v___x_1559_, 1);
return v_val_1562_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1563_, lean_object* v_inst_1564_, lean_object* v_t_1565_, lean_object* v_k_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Std_ExtDTreeMap_getKeyGE_x21___redArg(v_cmp_1563_, v_inst_1564_, v_t_1565_, v_k_1566_);
lean_dec(v_inst_1564_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1568_, lean_object* v_00_u03b2_1569_, lean_object* v_cmp_1570_, lean_object* v_inst_1571_, lean_object* v_inst_1572_, lean_object* v_t_1573_, lean_object* v_k_1574_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_box(0);
v___x_1576_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1570_, v_k_1574_, v___x_1575_, v_t_1573_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1578_ = l_panic___redArg(v_inst_1572_, v___x_1577_);
return v___x_1578_;
}
else
{
lean_object* v_val_1579_; 
v_val_1579_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_val_1579_);
lean_dec_ref_known(v___x_1576_, 1);
return v_val_1579_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_cmp_1582_, lean_object* v_inst_1583_, lean_object* v_inst_1584_, lean_object* v_t_1585_, lean_object* v_k_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Std_ExtDTreeMap_getKeyGE_x21(v_00_u03b1_1580_, v_00_u03b2_1581_, v_cmp_1582_, v_inst_1583_, v_inst_1584_, v_t_1585_, v_k_1586_);
lean_dec(v_inst_1584_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1588_, lean_object* v_inst_1589_, lean_object* v_t_1590_, lean_object* v_k_1591_){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_box(0);
v___x_1593_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1588_, v_k_1591_, v___x_1592_, v_t_1590_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1595_ = l_panic___redArg(v_inst_1589_, v___x_1594_);
return v___x_1595_;
}
else
{
lean_object* v_val_1596_; 
v_val_1596_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v___x_1593_, 1);
return v_val_1596_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1597_, lean_object* v_inst_1598_, lean_object* v_t_1599_, lean_object* v_k_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Std_ExtDTreeMap_getKeyGT_x21___redArg(v_cmp_1597_, v_inst_1598_, v_t_1599_, v_k_1600_);
lean_dec(v_inst_1598_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1602_, lean_object* v_00_u03b2_1603_, lean_object* v_cmp_1604_, lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_t_1607_, lean_object* v_k_1608_){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_box(0);
v___x_1610_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1604_, v_k_1608_, v___x_1609_, v_t_1607_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1612_ = l_panic___redArg(v_inst_1606_, v___x_1611_);
return v___x_1612_;
}
else
{
lean_object* v_val_1613_; 
v_val_1613_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_val_1613_);
lean_dec_ref_known(v___x_1610_, 1);
return v_val_1613_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1614_, lean_object* v_00_u03b2_1615_, lean_object* v_cmp_1616_, lean_object* v_inst_1617_, lean_object* v_inst_1618_, lean_object* v_t_1619_, lean_object* v_k_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Std_ExtDTreeMap_getKeyGT_x21(v_00_u03b1_1614_, v_00_u03b2_1615_, v_cmp_1616_, v_inst_1617_, v_inst_1618_, v_t_1619_, v_k_1620_);
lean_dec(v_inst_1618_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1622_, lean_object* v_inst_1623_, lean_object* v_t_1624_, lean_object* v_k_1625_){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_box(0);
v___x_1627_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1622_, v_k_1625_, v___x_1626_, v_t_1624_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1629_ = l_panic___redArg(v_inst_1623_, v___x_1628_);
return v___x_1629_;
}
else
{
lean_object* v_val_1630_; 
v_val_1630_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_val_1630_);
lean_dec_ref_known(v___x_1627_, 1);
return v_val_1630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1631_, lean_object* v_inst_1632_, lean_object* v_t_1633_, lean_object* v_k_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Std_ExtDTreeMap_getKeyLE_x21___redArg(v_cmp_1631_, v_inst_1632_, v_t_1633_, v_k_1634_);
lean_dec(v_inst_1632_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1636_, lean_object* v_00_u03b2_1637_, lean_object* v_cmp_1638_, lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_t_1641_, lean_object* v_k_1642_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_box(0);
v___x_1644_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1638_, v_k_1642_, v___x_1643_, v_t_1641_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1646_ = l_panic___redArg(v_inst_1640_, v___x_1645_);
return v___x_1646_;
}
else
{
lean_object* v_val_1647_; 
v_val_1647_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_val_1647_);
lean_dec_ref_known(v___x_1644_, 1);
return v_val_1647_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1648_, lean_object* v_00_u03b2_1649_, lean_object* v_cmp_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_t_1653_, lean_object* v_k_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Std_ExtDTreeMap_getKeyLE_x21(v_00_u03b1_1648_, v_00_u03b2_1649_, v_cmp_1650_, v_inst_1651_, v_inst_1652_, v_t_1653_, v_k_1654_);
lean_dec(v_inst_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1656_, lean_object* v_inst_1657_, lean_object* v_t_1658_, lean_object* v_k_1659_){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_box(0);
v___x_1661_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1656_, v_k_1659_, v___x_1660_, v_t_1658_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1663_ = l_panic___redArg(v_inst_1657_, v___x_1662_);
return v___x_1663_;
}
else
{
lean_object* v_val_1664_; 
v_val_1664_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_val_1664_);
lean_dec_ref_known(v___x_1661_, 1);
return v_val_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1665_, lean_object* v_inst_1666_, lean_object* v_t_1667_, lean_object* v_k_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Std_ExtDTreeMap_getKeyLT_x21___redArg(v_cmp_1665_, v_inst_1666_, v_t_1667_, v_k_1668_);
lean_dec(v_inst_1666_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1670_, lean_object* v_00_u03b2_1671_, lean_object* v_cmp_1672_, lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_t_1675_, lean_object* v_k_1676_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_box(0);
v___x_1678_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1672_, v_k_1676_, v___x_1677_, v_t_1675_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1680_ = l_panic___redArg(v_inst_1674_, v___x_1679_);
return v___x_1680_;
}
else
{
lean_object* v_val_1681_; 
v_val_1681_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_val_1681_);
lean_dec_ref_known(v___x_1678_, 1);
return v_val_1681_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1682_, lean_object* v_00_u03b2_1683_, lean_object* v_cmp_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_t_1687_, lean_object* v_k_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Std_ExtDTreeMap_getKeyLT_x21(v_00_u03b1_1682_, v_00_u03b2_1683_, v_cmp_1684_, v_inst_1685_, v_inst_1686_, v_t_1687_, v_k_1688_);
lean_dec(v_inst_1686_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___redArg(lean_object* v_cmp_1690_, lean_object* v_t_1691_, lean_object* v_k_1692_, lean_object* v_fallback_1693_){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_box(0);
v___x_1695_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1690_, v_k_1692_, v___x_1694_, v_t_1691_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_inc(v_fallback_1693_);
return v_fallback_1693_;
}
else
{
lean_object* v_val_1696_; 
v_val_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_val_1696_);
lean_dec_ref_known(v___x_1695_, 1);
return v_val_1696_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1697_, lean_object* v_t_1698_, lean_object* v_k_1699_, lean_object* v_fallback_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Std_ExtDTreeMap_getKeyGED___redArg(v_cmp_1697_, v_t_1698_, v_k_1699_, v_fallback_1700_);
lean_dec(v_fallback_1700_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED(lean_object* v_00_u03b1_1702_, lean_object* v_00_u03b2_1703_, lean_object* v_cmp_1704_, lean_object* v_inst_1705_, lean_object* v_t_1706_, lean_object* v_k_1707_, lean_object* v_fallback_1708_){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_box(0);
v___x_1710_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1704_, v_k_1707_, v___x_1709_, v_t_1706_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_inc(v_fallback_1708_);
return v_fallback_1708_;
}
else
{
lean_object* v_val_1711_; 
v_val_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_val_1711_);
lean_dec_ref_known(v___x_1710_, 1);
return v_val_1711_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1712_, lean_object* v_00_u03b2_1713_, lean_object* v_cmp_1714_, lean_object* v_inst_1715_, lean_object* v_t_1716_, lean_object* v_k_1717_, lean_object* v_fallback_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Std_ExtDTreeMap_getKeyGED(v_00_u03b1_1712_, v_00_u03b2_1713_, v_cmp_1714_, v_inst_1715_, v_t_1716_, v_k_1717_, v_fallback_1718_);
lean_dec(v_fallback_1718_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1720_, lean_object* v_t_1721_, lean_object* v_k_1722_, lean_object* v_fallback_1723_){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_box(0);
v___x_1725_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1720_, v_k_1722_, v___x_1724_, v_t_1721_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_inc(v_fallback_1723_);
return v_fallback_1723_;
}
else
{
lean_object* v_val_1726_; 
v_val_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_val_1726_);
lean_dec_ref_known(v___x_1725_, 1);
return v_val_1726_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1727_, lean_object* v_t_1728_, lean_object* v_k_1729_, lean_object* v_fallback_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Std_ExtDTreeMap_getKeyGTD___redArg(v_cmp_1727_, v_t_1728_, v_k_1729_, v_fallback_1730_);
lean_dec(v_fallback_1730_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD(lean_object* v_00_u03b1_1732_, lean_object* v_00_u03b2_1733_, lean_object* v_cmp_1734_, lean_object* v_inst_1735_, lean_object* v_t_1736_, lean_object* v_k_1737_, lean_object* v_fallback_1738_){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_box(0);
v___x_1740_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1734_, v_k_1737_, v___x_1739_, v_t_1736_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_inc(v_fallback_1738_);
return v_fallback_1738_;
}
else
{
lean_object* v_val_1741_; 
v_val_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_val_1741_);
lean_dec_ref_known(v___x_1740_, 1);
return v_val_1741_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_cmp_1744_, lean_object* v_inst_1745_, lean_object* v_t_1746_, lean_object* v_k_1747_, lean_object* v_fallback_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Std_ExtDTreeMap_getKeyGTD(v_00_u03b1_1742_, v_00_u03b2_1743_, v_cmp_1744_, v_inst_1745_, v_t_1746_, v_k_1747_, v_fallback_1748_);
lean_dec(v_fallback_1748_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___redArg(lean_object* v_cmp_1750_, lean_object* v_t_1751_, lean_object* v_k_1752_, lean_object* v_fallback_1753_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_box(0);
v___x_1755_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1750_, v_k_1752_, v___x_1754_, v_t_1751_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_inc(v_fallback_1753_);
return v_fallback_1753_;
}
else
{
lean_object* v_val_1756_; 
v_val_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_val_1756_);
lean_dec_ref_known(v___x_1755_, 1);
return v_val_1756_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1757_, lean_object* v_t_1758_, lean_object* v_k_1759_, lean_object* v_fallback_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Std_ExtDTreeMap_getKeyLED___redArg(v_cmp_1757_, v_t_1758_, v_k_1759_, v_fallback_1760_);
lean_dec(v_fallback_1760_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED(lean_object* v_00_u03b1_1762_, lean_object* v_00_u03b2_1763_, lean_object* v_cmp_1764_, lean_object* v_inst_1765_, lean_object* v_t_1766_, lean_object* v_k_1767_, lean_object* v_fallback_1768_){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = lean_box(0);
v___x_1770_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1764_, v_k_1767_, v___x_1769_, v_t_1766_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_inc(v_fallback_1768_);
return v_fallback_1768_;
}
else
{
lean_object* v_val_1771_; 
v_val_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_val_1771_);
lean_dec_ref_known(v___x_1770_, 1);
return v_val_1771_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1772_, lean_object* v_00_u03b2_1773_, lean_object* v_cmp_1774_, lean_object* v_inst_1775_, lean_object* v_t_1776_, lean_object* v_k_1777_, lean_object* v_fallback_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Std_ExtDTreeMap_getKeyLED(v_00_u03b1_1772_, v_00_u03b2_1773_, v_cmp_1774_, v_inst_1775_, v_t_1776_, v_k_1777_, v_fallback_1778_);
lean_dec(v_fallback_1778_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1780_, lean_object* v_t_1781_, lean_object* v_k_1782_, lean_object* v_fallback_1783_){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_box(0);
v___x_1785_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1780_, v_k_1782_, v___x_1784_, v_t_1781_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_inc(v_fallback_1783_);
return v_fallback_1783_;
}
else
{
lean_object* v_val_1786_; 
v_val_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_val_1786_);
lean_dec_ref_known(v___x_1785_, 1);
return v_val_1786_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1787_, lean_object* v_t_1788_, lean_object* v_k_1789_, lean_object* v_fallback_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Std_ExtDTreeMap_getKeyLTD___redArg(v_cmp_1787_, v_t_1788_, v_k_1789_, v_fallback_1790_);
lean_dec(v_fallback_1790_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD(lean_object* v_00_u03b1_1792_, lean_object* v_00_u03b2_1793_, lean_object* v_cmp_1794_, lean_object* v_inst_1795_, lean_object* v_t_1796_, lean_object* v_k_1797_, lean_object* v_fallback_1798_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1794_, v_k_1797_, v___x_1799_, v_t_1796_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_inc(v_fallback_1798_);
return v_fallback_1798_;
}
else
{
lean_object* v_val_1801_; 
v_val_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_val_1801_);
lean_dec_ref_known(v___x_1800_, 1);
return v_val_1801_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1802_, lean_object* v_00_u03b2_1803_, lean_object* v_cmp_1804_, lean_object* v_inst_1805_, lean_object* v_t_1806_, lean_object* v_k_1807_, lean_object* v_fallback_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Std_ExtDTreeMap_getKeyLTD(v_00_u03b1_1802_, v_00_u03b2_1803_, v_cmp_1804_, v_inst_1805_, v_t_1806_, v_k_1807_, v_fallback_1808_);
lean_dec(v_fallback_1808_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1810_, lean_object* v_t_1811_, lean_object* v_a_1812_, lean_object* v_b_1813_){
_start:
{
lean_object* v___x_1814_; 
lean_inc(v_a_1812_);
lean_inc(v_t_1811_);
lean_inc_ref(v_cmp_1810_);
v___x_1814_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1810_, v_t_1811_, v_a_1812_);
if (lean_obj_tag(v___x_1814_) == 0)
{
uint8_t v___x_1815_; 
lean_inc(v_t_1811_);
lean_inc(v_a_1812_);
lean_inc_ref(v_cmp_1810_);
v___x_1815_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1810_, v_a_1812_, v_t_1811_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1810_, v_a_1812_, v_b_1813_, v_t_1811_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1814_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; 
lean_dec(v_b_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_cmp_1810_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1814_);
lean_ctor_set(v___x_1818_, 1, v_t_1811_);
return v___x_1818_;
}
}
else
{
lean_object* v___x_1819_; 
lean_dec(v_b_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_cmp_1810_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1814_);
lean_ctor_set(v___x_1819_, 1, v_t_1811_);
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1820_, lean_object* v_cmp_1821_, lean_object* v_00_u03b2_1822_, lean_object* v_inst_1823_, lean_object* v_t_1824_, lean_object* v_a_1825_, lean_object* v_b_1826_){
_start:
{
lean_object* v___x_1827_; 
lean_inc(v_a_1825_);
lean_inc(v_t_1824_);
lean_inc_ref(v_cmp_1821_);
v___x_1827_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1821_, v_t_1824_, v_a_1825_);
if (lean_obj_tag(v___x_1827_) == 0)
{
uint8_t v___x_1828_; 
lean_inc(v_t_1824_);
lean_inc(v_a_1825_);
lean_inc_ref(v_cmp_1821_);
v___x_1828_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1821_, v_a_1825_, v_t_1824_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1821_, v_a_1825_, v_b_1826_, v_t_1824_);
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1827_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
return v___x_1830_;
}
else
{
lean_object* v___x_1831_; 
lean_dec(v_b_1826_);
lean_dec(v_a_1825_);
lean_dec_ref(v_cmp_1821_);
v___x_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1827_);
lean_ctor_set(v___x_1831_, 1, v_t_1824_);
return v___x_1831_;
}
}
else
{
lean_object* v___x_1832_; 
lean_dec(v_b_1826_);
lean_dec(v_a_1825_);
lean_dec_ref(v_cmp_1821_);
v___x_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1827_);
lean_ctor_set(v___x_1832_, 1, v_t_1824_);
return v___x_1832_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x3f___redArg(lean_object* v_cmp_1833_, lean_object* v_t_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1833_, v_t_1834_, v_a_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x3f(lean_object* v_00_u03b1_1837_, lean_object* v_cmp_1838_, lean_object* v_00_u03b2_1839_, lean_object* v_inst_1840_, lean_object* v_t_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1838_, v_t_1841_, v_a_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get___redArg(lean_object* v_cmp_1844_, lean_object* v_t_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1844_, v_t_1845_, v_a_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get(lean_object* v_00_u03b1_1848_, lean_object* v_cmp_1849_, lean_object* v_00_u03b2_1850_, lean_object* v_inst_1851_, lean_object* v_t_1852_, lean_object* v_a_1853_, lean_object* v_h_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1849_, v_t_1852_, v_a_1853_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___redArg(lean_object* v_cmp_1856_, lean_object* v_inst_1857_, lean_object* v_t_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1856_, v_inst_1857_, v_t_1858_, v_a_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___redArg___boxed(lean_object* v_cmp_1861_, lean_object* v_inst_1862_, lean_object* v_t_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Std_ExtDTreeMap_Const_get_x21___redArg(v_cmp_1861_, v_inst_1862_, v_t_1863_, v_a_1864_);
lean_dec(v_inst_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21(lean_object* v_00_u03b1_1866_, lean_object* v_cmp_1867_, lean_object* v_00_u03b2_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_t_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1867_, v_inst_1870_, v_t_1871_, v_a_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___boxed(lean_object* v_00_u03b1_1874_, lean_object* v_cmp_1875_, lean_object* v_00_u03b2_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_, lean_object* v_t_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Std_ExtDTreeMap_Const_get_x21(v_00_u03b1_1874_, v_cmp_1875_, v_00_u03b2_1876_, v_inst_1877_, v_inst_1878_, v_t_1879_, v_a_1880_);
lean_dec(v_inst_1878_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___redArg(lean_object* v_cmp_1882_, lean_object* v_t_1883_, lean_object* v_a_1884_, lean_object* v_fallback_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1882_, v_t_1883_, v_a_1884_, v_fallback_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___redArg___boxed(lean_object* v_cmp_1887_, lean_object* v_t_1888_, lean_object* v_a_1889_, lean_object* v_fallback_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Std_ExtDTreeMap_Const_getD___redArg(v_cmp_1887_, v_t_1888_, v_a_1889_, v_fallback_1890_);
lean_dec(v_fallback_1890_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD(lean_object* v_00_u03b1_1892_, lean_object* v_cmp_1893_, lean_object* v_00_u03b2_1894_, lean_object* v_inst_1895_, lean_object* v_t_1896_, lean_object* v_a_1897_, lean_object* v_fallback_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1893_, v_t_1896_, v_a_1897_, v_fallback_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___boxed(lean_object* v_00_u03b1_1900_, lean_object* v_cmp_1901_, lean_object* v_00_u03b2_1902_, lean_object* v_inst_1903_, lean_object* v_t_1904_, lean_object* v_a_1905_, lean_object* v_fallback_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Std_ExtDTreeMap_Const_getD(v_00_u03b1_1900_, v_cmp_1901_, v_00_u03b2_1902_, v_inst_1903_, v_t_1904_, v_a_1905_, v_fallback_1906_);
lean_dec(v_fallback_1906_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(lean_object* v_t_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(v_t_1910_);
lean_dec(v_t_1910_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f(lean_object* v_00_u03b1_1912_, lean_object* v_cmp_1913_, lean_object* v_00_u03b2_1914_, lean_object* v_inst_1915_, lean_object* v_t_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1918_, lean_object* v_cmp_1919_, lean_object* v_00_u03b2_1920_, lean_object* v_inst_1921_, lean_object* v_t_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Std_ExtDTreeMap_Const_minEntry_x3f(v_00_u03b1_1918_, v_cmp_1919_, v_00_u03b2_1920_, v_inst_1921_, v_t_1922_);
lean_dec(v_t_1922_);
lean_dec_ref(v_cmp_1919_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___redArg(lean_object* v_t_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___redArg___boxed(lean_object* v_t_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Std_ExtDTreeMap_Const_minEntry___redArg(v_t_1926_);
lean_dec(v_t_1926_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry(lean_object* v_00_u03b1_1928_, lean_object* v_cmp_1929_, lean_object* v_00_u03b2_1930_, lean_object* v_inst_1931_, lean_object* v_t_1932_, lean_object* v_h_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1932_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___boxed(lean_object* v_00_u03b1_1935_, lean_object* v_cmp_1936_, lean_object* v_00_u03b2_1937_, lean_object* v_inst_1938_, lean_object* v_t_1939_, lean_object* v_h_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Std_ExtDTreeMap_Const_minEntry(v_00_u03b1_1935_, v_cmp_1936_, v_00_u03b2_1937_, v_inst_1938_, v_t_1939_, v_h_1940_);
lean_dec(v_t_1939_);
lean_dec_ref(v_cmp_1936_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(lean_object* v_inst_1942_, lean_object* v_t_1943_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1942_, v_t_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1945_, lean_object* v_t_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(v_inst_1945_, v_t_1946_);
lean_dec(v_t_1946_);
lean_dec_ref(v_inst_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21(lean_object* v_00_u03b1_1948_, lean_object* v_cmp_1949_, lean_object* v_00_u03b2_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_t_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1952_, v_t_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1955_, lean_object* v_cmp_1956_, lean_object* v_00_u03b2_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_t_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Std_ExtDTreeMap_Const_minEntry_x21(v_00_u03b1_1955_, v_cmp_1956_, v_00_u03b2_1957_, v_inst_1958_, v_inst_1959_, v_t_1960_);
lean_dec(v_t_1960_);
lean_dec_ref(v_inst_1959_);
lean_dec_ref(v_cmp_1956_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___redArg(lean_object* v_t_1962_, lean_object* v_fallback_1963_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1962_, v_fallback_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___redArg___boxed(lean_object* v_t_1965_, lean_object* v_fallback_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Std_ExtDTreeMap_Const_minEntryD___redArg(v_t_1965_, v_fallback_1966_);
lean_dec_ref(v_fallback_1966_);
lean_dec(v_t_1965_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD(lean_object* v_00_u03b1_1968_, lean_object* v_cmp_1969_, lean_object* v_00_u03b2_1970_, lean_object* v_inst_1971_, lean_object* v_t_1972_, lean_object* v_fallback_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1972_, v_fallback_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___boxed(lean_object* v_00_u03b1_1975_, lean_object* v_cmp_1976_, lean_object* v_00_u03b2_1977_, lean_object* v_inst_1978_, lean_object* v_t_1979_, lean_object* v_fallback_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Std_ExtDTreeMap_Const_minEntryD(v_00_u03b1_1975_, v_cmp_1976_, v_00_u03b2_1977_, v_inst_1978_, v_t_1979_, v_fallback_1980_);
lean_dec_ref(v_fallback_1980_);
lean_dec(v_t_1979_);
lean_dec_ref(v_cmp_1976_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(lean_object* v_t_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(v_t_1984_);
lean_dec(v_t_1984_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f(lean_object* v_00_u03b1_1986_, lean_object* v_cmp_1987_, lean_object* v_00_u03b2_1988_, lean_object* v_inst_1989_, lean_object* v_t_1990_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1992_, lean_object* v_cmp_1993_, lean_object* v_00_u03b2_1994_, lean_object* v_inst_1995_, lean_object* v_t_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Std_ExtDTreeMap_Const_maxEntry_x3f(v_00_u03b1_1992_, v_cmp_1993_, v_00_u03b2_1994_, v_inst_1995_, v_t_1996_);
lean_dec(v_t_1996_);
lean_dec_ref(v_cmp_1993_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___redArg(lean_object* v_t_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___redArg___boxed(lean_object* v_t_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Std_ExtDTreeMap_Const_maxEntry___redArg(v_t_2000_);
lean_dec(v_t_2000_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry(lean_object* v_00_u03b1_2002_, lean_object* v_cmp_2003_, lean_object* v_00_u03b2_2004_, lean_object* v_inst_2005_, lean_object* v_t_2006_, lean_object* v_h_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_2006_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___boxed(lean_object* v_00_u03b1_2009_, lean_object* v_cmp_2010_, lean_object* v_00_u03b2_2011_, lean_object* v_inst_2012_, lean_object* v_t_2013_, lean_object* v_h_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Std_ExtDTreeMap_Const_maxEntry(v_00_u03b1_2009_, v_cmp_2010_, v_00_u03b2_2011_, v_inst_2012_, v_t_2013_, v_h_2014_);
lean_dec(v_t_2013_);
lean_dec_ref(v_cmp_2010_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(lean_object* v_inst_2016_, lean_object* v_t_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_2016_, v_t_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_2019_, lean_object* v_t_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(v_inst_2019_, v_t_2020_);
lean_dec(v_t_2020_);
lean_dec_ref(v_inst_2019_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21(lean_object* v_00_u03b1_2022_, lean_object* v_cmp_2023_, lean_object* v_00_u03b2_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_t_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_2026_, v_t_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_2029_, lean_object* v_cmp_2030_, lean_object* v_00_u03b2_2031_, lean_object* v_inst_2032_, lean_object* v_inst_2033_, lean_object* v_t_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Std_ExtDTreeMap_Const_maxEntry_x21(v_00_u03b1_2029_, v_cmp_2030_, v_00_u03b2_2031_, v_inst_2032_, v_inst_2033_, v_t_2034_);
lean_dec(v_t_2034_);
lean_dec_ref(v_inst_2033_);
lean_dec_ref(v_cmp_2030_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___redArg(lean_object* v_t_2036_, lean_object* v_fallback_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_2036_, v_fallback_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___redArg___boxed(lean_object* v_t_2039_, lean_object* v_fallback_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Std_ExtDTreeMap_Const_maxEntryD___redArg(v_t_2039_, v_fallback_2040_);
lean_dec_ref(v_fallback_2040_);
lean_dec(v_t_2039_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD(lean_object* v_00_u03b1_2042_, lean_object* v_cmp_2043_, lean_object* v_00_u03b2_2044_, lean_object* v_inst_2045_, lean_object* v_t_2046_, lean_object* v_fallback_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_2046_, v_fallback_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___boxed(lean_object* v_00_u03b1_2049_, lean_object* v_cmp_2050_, lean_object* v_00_u03b2_2051_, lean_object* v_inst_2052_, lean_object* v_t_2053_, lean_object* v_fallback_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Std_ExtDTreeMap_Const_maxEntryD(v_00_u03b1_2049_, v_cmp_2050_, v_00_u03b2_2051_, v_inst_2052_, v_t_2053_, v_fallback_2054_);
lean_dec_ref(v_fallback_2054_);
lean_dec(v_t_2053_);
lean_dec_ref(v_cmp_2050_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(lean_object* v_t_2056_, lean_object* v_n_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_2056_, v_n_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_2059_, lean_object* v_n_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(v_t_2059_, v_n_2060_);
lean_dec(v_t_2059_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_2062_, lean_object* v_cmp_2063_, lean_object* v_00_u03b2_2064_, lean_object* v_inst_2065_, lean_object* v_t_2066_, lean_object* v_n_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_2066_, v_n_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_cmp_2070_, lean_object* v_00_u03b2_2071_, lean_object* v_inst_2072_, lean_object* v_t_2073_, lean_object* v_n_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(v_00_u03b1_2069_, v_cmp_2070_, v_00_u03b2_2071_, v_inst_2072_, v_t_2073_, v_n_2074_);
lean_dec(v_t_2073_);
lean_dec_ref(v_cmp_2070_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(lean_object* v_t_2076_, lean_object* v_n_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_2076_, v_n_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___redArg___boxed(lean_object* v_t_2079_, lean_object* v_n_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(v_t_2079_, v_n_2080_);
lean_dec(v_t_2079_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx(lean_object* v_00_u03b1_2082_, lean_object* v_cmp_2083_, lean_object* v_00_u03b2_2084_, lean_object* v_inst_2085_, lean_object* v_t_2086_, lean_object* v_n_2087_, lean_object* v_h_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_2086_, v_n_2087_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_2090_, lean_object* v_cmp_2091_, lean_object* v_00_u03b2_2092_, lean_object* v_inst_2093_, lean_object* v_t_2094_, lean_object* v_n_2095_, lean_object* v_h_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Std_ExtDTreeMap_Const_entryAtIdx(v_00_u03b1_2090_, v_cmp_2091_, v_00_u03b2_2092_, v_inst_2093_, v_t_2094_, v_n_2095_, v_h_2096_);
lean_dec(v_t_2094_);
lean_dec_ref(v_cmp_2091_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(lean_object* v_inst_2098_, lean_object* v_t_2099_, lean_object* v_n_2100_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_2098_, v_t_2099_, v_n_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_2102_, lean_object* v_t_2103_, lean_object* v_n_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(v_inst_2102_, v_t_2103_, v_n_2104_);
lean_dec(v_t_2103_);
lean_dec_ref(v_inst_2102_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21(lean_object* v_00_u03b1_2106_, lean_object* v_cmp_2107_, lean_object* v_00_u03b2_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_t_2111_, lean_object* v_n_2112_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_2110_, v_t_2111_, v_n_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_2114_, lean_object* v_cmp_2115_, lean_object* v_00_u03b2_2116_, lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_t_2119_, lean_object* v_n_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x21(v_00_u03b1_2114_, v_cmp_2115_, v_00_u03b2_2116_, v_inst_2117_, v_inst_2118_, v_t_2119_, v_n_2120_);
lean_dec(v_t_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_cmp_2115_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(lean_object* v_t_2122_, lean_object* v_n_2123_, lean_object* v_fallback_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_2122_, v_n_2123_, v_fallback_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_2126_, lean_object* v_n_2127_, lean_object* v_fallback_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(v_t_2126_, v_n_2127_, v_fallback_2128_);
lean_dec_ref(v_fallback_2128_);
lean_dec(v_t_2126_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD(lean_object* v_00_u03b1_2130_, lean_object* v_cmp_2131_, lean_object* v_00_u03b2_2132_, lean_object* v_inst_2133_, lean_object* v_t_2134_, lean_object* v_n_2135_, lean_object* v_fallback_2136_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_2134_, v_n_2135_, v_fallback_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_2138_, lean_object* v_cmp_2139_, lean_object* v_00_u03b2_2140_, lean_object* v_inst_2141_, lean_object* v_t_2142_, lean_object* v_n_2143_, lean_object* v_fallback_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Std_ExtDTreeMap_Const_entryAtIdxD(v_00_u03b1_2138_, v_cmp_2139_, v_00_u03b2_2140_, v_inst_2141_, v_t_2142_, v_n_2143_, v_fallback_2144_);
lean_dec_ref(v_fallback_2144_);
lean_dec(v_t_2142_);
lean_dec_ref(v_cmp_2139_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_2146_, lean_object* v_t_2147_, lean_object* v_k_2148_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_box(0);
v___x_2150_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2146_, v_k_2148_, v___x_2149_, v_t_2147_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x3f(lean_object* v_00_u03b1_2151_, lean_object* v_cmp_2152_, lean_object* v_00_u03b2_2153_, lean_object* v_inst_2154_, lean_object* v_t_2155_, lean_object* v_k_2156_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_box(0);
v___x_2158_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2152_, v_k_2156_, v___x_2157_, v_t_2155_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_2159_, lean_object* v_t_2160_, lean_object* v_k_2161_){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_box(0);
v___x_2163_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2159_, v_k_2161_, v___x_2162_, v_t_2160_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x3f(lean_object* v_00_u03b1_2164_, lean_object* v_cmp_2165_, lean_object* v_00_u03b2_2166_, lean_object* v_inst_2167_, lean_object* v_t_2168_, lean_object* v_k_2169_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_box(0);
v___x_2171_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2165_, v_k_2169_, v___x_2170_, v_t_2168_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_2172_, lean_object* v_t_2173_, lean_object* v_k_2174_){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_box(0);
v___x_2176_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2172_, v_k_2174_, v___x_2175_, v_t_2173_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x3f(lean_object* v_00_u03b1_2177_, lean_object* v_cmp_2178_, lean_object* v_00_u03b2_2179_, lean_object* v_inst_2180_, lean_object* v_t_2181_, lean_object* v_k_2182_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = lean_box(0);
v___x_2184_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2178_, v_k_2182_, v___x_2183_, v_t_2181_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_2185_, lean_object* v_t_2186_, lean_object* v_k_2187_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_box(0);
v___x_2189_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2185_, v_k_2187_, v___x_2188_, v_t_2186_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x3f(lean_object* v_00_u03b1_2190_, lean_object* v_cmp_2191_, lean_object* v_00_u03b2_2192_, lean_object* v_inst_2193_, lean_object* v_t_2194_, lean_object* v_k_2195_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_box(0);
v___x_2197_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2191_, v_k_2195_, v___x_2196_, v_t_2194_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE___redArg(lean_object* v_cmp_2198_, lean_object* v_t_2199_, lean_object* v_k_2200_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_2198_, v_k_2200_, v_t_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE(lean_object* v_00_u03b1_2202_, lean_object* v_cmp_2203_, lean_object* v_00_u03b2_2204_, lean_object* v_inst_2205_, lean_object* v_t_2206_, lean_object* v_k_2207_, lean_object* v_h_2208_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_2203_, v_k_2207_, v_t_2206_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT___redArg(lean_object* v_cmp_2210_, lean_object* v_t_2211_, lean_object* v_k_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_2210_, v_k_2212_, v_t_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT(lean_object* v_00_u03b1_2214_, lean_object* v_cmp_2215_, lean_object* v_00_u03b2_2216_, lean_object* v_inst_2217_, lean_object* v_t_2218_, lean_object* v_k_2219_, lean_object* v_h_2220_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_2215_, v_k_2219_, v_t_2218_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE___redArg(lean_object* v_cmp_2222_, lean_object* v_t_2223_, lean_object* v_k_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_2222_, v_k_2224_, v_t_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE(lean_object* v_00_u03b1_2226_, lean_object* v_cmp_2227_, lean_object* v_00_u03b2_2228_, lean_object* v_inst_2229_, lean_object* v_t_2230_, lean_object* v_k_2231_, lean_object* v_h_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_2227_, v_k_2231_, v_t_2230_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT___redArg(lean_object* v_cmp_2234_, lean_object* v_t_2235_, lean_object* v_k_2236_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_2234_, v_k_2236_, v_t_2235_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT(lean_object* v_00_u03b1_2238_, lean_object* v_cmp_2239_, lean_object* v_00_u03b2_2240_, lean_object* v_inst_2241_, lean_object* v_t_2242_, lean_object* v_k_2243_, lean_object* v_h_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_2239_, v_k_2243_, v_t_2242_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg(lean_object* v_cmp_2246_, lean_object* v_inst_2247_, lean_object* v_t_2248_, lean_object* v_k_2249_){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_box(0);
v___x_2251_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2246_, v_k_2249_, v___x_2250_, v_t_2248_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2253_ = l_panic___redArg(v_inst_2247_, v___x_2252_);
return v___x_2253_;
}
else
{
lean_object* v_val_2254_; 
v_val_2254_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_val_2254_);
lean_dec_ref_known(v___x_2251_, 1);
return v_val_2254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_2255_, lean_object* v_inst_2256_, lean_object* v_t_2257_, lean_object* v_k_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg(v_cmp_2255_, v_inst_2256_, v_t_2257_, v_k_2258_);
lean_dec_ref(v_inst_2256_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21(lean_object* v_00_u03b1_2260_, lean_object* v_cmp_2261_, lean_object* v_00_u03b2_2262_, lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_t_2265_, lean_object* v_k_2266_){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_box(0);
v___x_2268_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2261_, v_k_2266_, v___x_2267_, v_t_2265_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2270_ = l_panic___redArg(v_inst_2264_, v___x_2269_);
return v___x_2270_;
}
else
{
lean_object* v_val_2271_; 
v_val_2271_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_val_2271_);
lean_dec_ref_known(v___x_2268_, 1);
return v_val_2271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_2272_, lean_object* v_cmp_2273_, lean_object* v_00_u03b2_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_t_2277_, lean_object* v_k_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Std_ExtDTreeMap_Const_getEntryGE_x21(v_00_u03b1_2272_, v_cmp_2273_, v_00_u03b2_2274_, v_inst_2275_, v_inst_2276_, v_t_2277_, v_k_2278_);
lean_dec_ref(v_inst_2276_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(lean_object* v_cmp_2280_, lean_object* v_inst_2281_, lean_object* v_t_2282_, lean_object* v_k_2283_){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_box(0);
v___x_2285_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2280_, v_k_2283_, v___x_2284_, v_t_2282_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2287_ = l_panic___redArg(v_inst_2281_, v___x_2286_);
return v___x_2287_;
}
else
{
lean_object* v_val_2288_; 
v_val_2288_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_val_2288_);
lean_dec_ref_known(v___x_2285_, 1);
return v_val_2288_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_2289_, lean_object* v_inst_2290_, lean_object* v_t_2291_, lean_object* v_k_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(v_cmp_2289_, v_inst_2290_, v_t_2291_, v_k_2292_);
lean_dec_ref(v_inst_2290_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21(lean_object* v_00_u03b1_2294_, lean_object* v_cmp_2295_, lean_object* v_00_u03b2_2296_, lean_object* v_inst_2297_, lean_object* v_inst_2298_, lean_object* v_t_2299_, lean_object* v_k_2300_){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = lean_box(0);
v___x_2302_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2295_, v_k_2300_, v___x_2301_, v_t_2299_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2304_ = l_panic___redArg(v_inst_2298_, v___x_2303_);
return v___x_2304_;
}
else
{
lean_object* v_val_2305_; 
v_val_2305_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_val_2305_);
lean_dec_ref_known(v___x_2302_, 1);
return v_val_2305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_2306_, lean_object* v_cmp_2307_, lean_object* v_00_u03b2_2308_, lean_object* v_inst_2309_, lean_object* v_inst_2310_, lean_object* v_t_2311_, lean_object* v_k_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Std_ExtDTreeMap_Const_getEntryGT_x21(v_00_u03b1_2306_, v_cmp_2307_, v_00_u03b2_2308_, v_inst_2309_, v_inst_2310_, v_t_2311_, v_k_2312_);
lean_dec_ref(v_inst_2310_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(lean_object* v_cmp_2314_, lean_object* v_inst_2315_, lean_object* v_t_2316_, lean_object* v_k_2317_){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_box(0);
v___x_2319_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2314_, v_k_2317_, v___x_2318_, v_t_2316_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2321_ = l_panic___redArg(v_inst_2315_, v___x_2320_);
return v___x_2321_;
}
else
{
lean_object* v_val_2322_; 
v_val_2322_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v___x_2319_, 1);
return v_val_2322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_2323_, lean_object* v_inst_2324_, lean_object* v_t_2325_, lean_object* v_k_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(v_cmp_2323_, v_inst_2324_, v_t_2325_, v_k_2326_);
lean_dec_ref(v_inst_2324_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21(lean_object* v_00_u03b1_2328_, lean_object* v_cmp_2329_, lean_object* v_00_u03b2_2330_, lean_object* v_inst_2331_, lean_object* v_inst_2332_, lean_object* v_t_2333_, lean_object* v_k_2334_){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = lean_box(0);
v___x_2336_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2329_, v_k_2334_, v___x_2335_, v_t_2333_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2338_ = l_panic___redArg(v_inst_2332_, v___x_2337_);
return v___x_2338_;
}
else
{
lean_object* v_val_2339_; 
v_val_2339_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_val_2339_);
lean_dec_ref_known(v___x_2336_, 1);
return v_val_2339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2340_, lean_object* v_cmp_2341_, lean_object* v_00_u03b2_2342_, lean_object* v_inst_2343_, lean_object* v_inst_2344_, lean_object* v_t_2345_, lean_object* v_k_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Std_ExtDTreeMap_Const_getEntryLE_x21(v_00_u03b1_2340_, v_cmp_2341_, v_00_u03b2_2342_, v_inst_2343_, v_inst_2344_, v_t_2345_, v_k_2346_);
lean_dec_ref(v_inst_2344_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(lean_object* v_cmp_2348_, lean_object* v_inst_2349_, lean_object* v_t_2350_, lean_object* v_k_2351_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_box(0);
v___x_2353_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2348_, v_k_2351_, v___x_2352_, v_t_2350_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2355_ = l_panic___redArg(v_inst_2349_, v___x_2354_);
return v___x_2355_;
}
else
{
lean_object* v_val_2356_; 
v_val_2356_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_val_2356_);
lean_dec_ref_known(v___x_2353_, 1);
return v_val_2356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_2357_, lean_object* v_inst_2358_, lean_object* v_t_2359_, lean_object* v_k_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(v_cmp_2357_, v_inst_2358_, v_t_2359_, v_k_2360_);
lean_dec_ref(v_inst_2358_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21(lean_object* v_00_u03b1_2362_, lean_object* v_cmp_2363_, lean_object* v_00_u03b2_2364_, lean_object* v_inst_2365_, lean_object* v_inst_2366_, lean_object* v_t_2367_, lean_object* v_k_2368_){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2363_, v_k_2368_, v___x_2369_, v_t_2367_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2372_ = l_panic___redArg(v_inst_2366_, v___x_2371_);
return v___x_2372_;
}
else
{
lean_object* v_val_2373_; 
v_val_2373_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_val_2373_);
lean_dec_ref_known(v___x_2370_, 1);
return v_val_2373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2374_, lean_object* v_cmp_2375_, lean_object* v_00_u03b2_2376_, lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_t_2379_, lean_object* v_k_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Std_ExtDTreeMap_Const_getEntryLT_x21(v_00_u03b1_2374_, v_cmp_2375_, v_00_u03b2_2376_, v_inst_2377_, v_inst_2378_, v_t_2379_, v_k_2380_);
lean_dec_ref(v_inst_2378_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___redArg(lean_object* v_cmp_2382_, lean_object* v_t_2383_, lean_object* v_k_2384_, lean_object* v_fallback_2385_){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = lean_box(0);
v___x_2387_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2382_, v_k_2384_, v___x_2386_, v_t_2383_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_inc_ref(v_fallback_2385_);
return v_fallback_2385_;
}
else
{
lean_object* v_val_2388_; 
v_val_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_val_2388_);
lean_dec_ref_known(v___x_2387_, 1);
return v_val_2388_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2389_, lean_object* v_t_2390_, lean_object* v_k_2391_, lean_object* v_fallback_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Std_ExtDTreeMap_Const_getEntryGED___redArg(v_cmp_2389_, v_t_2390_, v_k_2391_, v_fallback_2392_);
lean_dec_ref(v_fallback_2392_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED(lean_object* v_00_u03b1_2394_, lean_object* v_cmp_2395_, lean_object* v_00_u03b2_2396_, lean_object* v_inst_2397_, lean_object* v_t_2398_, lean_object* v_k_2399_, lean_object* v_fallback_2400_){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = lean_box(0);
v___x_2402_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2395_, v_k_2399_, v___x_2401_, v_t_2398_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_inc_ref(v_fallback_2400_);
return v_fallback_2400_;
}
else
{
lean_object* v_val_2403_; 
v_val_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_val_2403_);
lean_dec_ref_known(v___x_2402_, 1);
return v_val_2403_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2404_, lean_object* v_cmp_2405_, lean_object* v_00_u03b2_2406_, lean_object* v_inst_2407_, lean_object* v_t_2408_, lean_object* v_k_2409_, lean_object* v_fallback_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Std_ExtDTreeMap_Const_getEntryGED(v_00_u03b1_2404_, v_cmp_2405_, v_00_u03b2_2406_, v_inst_2407_, v_t_2408_, v_k_2409_, v_fallback_2410_);
lean_dec_ref(v_fallback_2410_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(lean_object* v_cmp_2412_, lean_object* v_t_2413_, lean_object* v_k_2414_, lean_object* v_fallback_2415_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = lean_box(0);
v___x_2417_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2412_, v_k_2414_, v___x_2416_, v_t_2413_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_inc_ref(v_fallback_2415_);
return v_fallback_2415_;
}
else
{
lean_object* v_val_2418_; 
v_val_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_val_2418_);
lean_dec_ref_known(v___x_2417_, 1);
return v_val_2418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2419_, lean_object* v_t_2420_, lean_object* v_k_2421_, lean_object* v_fallback_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(v_cmp_2419_, v_t_2420_, v_k_2421_, v_fallback_2422_);
lean_dec_ref(v_fallback_2422_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD(lean_object* v_00_u03b1_2424_, lean_object* v_cmp_2425_, lean_object* v_00_u03b2_2426_, lean_object* v_inst_2427_, lean_object* v_t_2428_, lean_object* v_k_2429_, lean_object* v_fallback_2430_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_box(0);
v___x_2432_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2425_, v_k_2429_, v___x_2431_, v_t_2428_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_inc_ref(v_fallback_2430_);
return v_fallback_2430_;
}
else
{
lean_object* v_val_2433_; 
v_val_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_val_2433_);
lean_dec_ref_known(v___x_2432_, 1);
return v_val_2433_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_cmp_2435_, lean_object* v_00_u03b2_2436_, lean_object* v_inst_2437_, lean_object* v_t_2438_, lean_object* v_k_2439_, lean_object* v_fallback_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Std_ExtDTreeMap_Const_getEntryGTD(v_00_u03b1_2434_, v_cmp_2435_, v_00_u03b2_2436_, v_inst_2437_, v_t_2438_, v_k_2439_, v_fallback_2440_);
lean_dec_ref(v_fallback_2440_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___redArg(lean_object* v_cmp_2442_, lean_object* v_t_2443_, lean_object* v_k_2444_, lean_object* v_fallback_2445_){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_box(0);
v___x_2447_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2442_, v_k_2444_, v___x_2446_, v_t_2443_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_inc_ref(v_fallback_2445_);
return v_fallback_2445_;
}
else
{
lean_object* v_val_2448_; 
v_val_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_val_2448_);
lean_dec_ref_known(v___x_2447_, 1);
return v_val_2448_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2449_, lean_object* v_t_2450_, lean_object* v_k_2451_, lean_object* v_fallback_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Std_ExtDTreeMap_Const_getEntryLED___redArg(v_cmp_2449_, v_t_2450_, v_k_2451_, v_fallback_2452_);
lean_dec_ref(v_fallback_2452_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED(lean_object* v_00_u03b1_2454_, lean_object* v_cmp_2455_, lean_object* v_00_u03b2_2456_, lean_object* v_inst_2457_, lean_object* v_t_2458_, lean_object* v_k_2459_, lean_object* v_fallback_2460_){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_box(0);
v___x_2462_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2455_, v_k_2459_, v___x_2461_, v_t_2458_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_inc_ref(v_fallback_2460_);
return v_fallback_2460_;
}
else
{
lean_object* v_val_2463_; 
v_val_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_val_2463_);
lean_dec_ref_known(v___x_2462_, 1);
return v_val_2463_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2464_, lean_object* v_cmp_2465_, lean_object* v_00_u03b2_2466_, lean_object* v_inst_2467_, lean_object* v_t_2468_, lean_object* v_k_2469_, lean_object* v_fallback_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Std_ExtDTreeMap_Const_getEntryLED(v_00_u03b1_2464_, v_cmp_2465_, v_00_u03b2_2466_, v_inst_2467_, v_t_2468_, v_k_2469_, v_fallback_2470_);
lean_dec_ref(v_fallback_2470_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(lean_object* v_cmp_2472_, lean_object* v_t_2473_, lean_object* v_k_2474_, lean_object* v_fallback_2475_){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_box(0);
v___x_2477_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2472_, v_k_2474_, v___x_2476_, v_t_2473_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_inc_ref(v_fallback_2475_);
return v_fallback_2475_;
}
else
{
lean_object* v_val_2478_; 
v_val_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_val_2478_);
lean_dec_ref_known(v___x_2477_, 1);
return v_val_2478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2479_, lean_object* v_t_2480_, lean_object* v_k_2481_, lean_object* v_fallback_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(v_cmp_2479_, v_t_2480_, v_k_2481_, v_fallback_2482_);
lean_dec_ref(v_fallback_2482_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD(lean_object* v_00_u03b1_2484_, lean_object* v_cmp_2485_, lean_object* v_00_u03b2_2486_, lean_object* v_inst_2487_, lean_object* v_t_2488_, lean_object* v_k_2489_, lean_object* v_fallback_2490_){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_box(0);
v___x_2492_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2485_, v_k_2489_, v___x_2491_, v_t_2488_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_inc_ref(v_fallback_2490_);
return v_fallback_2490_;
}
else
{
lean_object* v_val_2493_; 
v_val_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_val_2493_);
lean_dec_ref_known(v___x_2492_, 1);
return v_val_2493_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2494_, lean_object* v_cmp_2495_, lean_object* v_00_u03b2_2496_, lean_object* v_inst_2497_, lean_object* v_t_2498_, lean_object* v_k_2499_, lean_object* v_fallback_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Std_ExtDTreeMap_Const_getEntryLTD(v_00_u03b1_2494_, v_cmp_2495_, v_00_u03b2_2496_, v_inst_2497_, v_t_2498_, v_k_2499_, v_fallback_2500_);
lean_dec_ref(v_fallback_2500_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter___redArg(lean_object* v_f_2502_, lean_object* v_t_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2502_, v_t_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter(lean_object* v_00_u03b1_2505_, lean_object* v_00_u03b2_2506_, lean_object* v_cmp_2507_, lean_object* v_f_2508_, lean_object* v_t_2509_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2508_, v_t_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter___boxed(lean_object* v_00_u03b1_2511_, lean_object* v_00_u03b2_2512_, lean_object* v_cmp_2513_, lean_object* v_f_2514_, lean_object* v_t_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Std_ExtDTreeMap_filter(v_00_u03b1_2511_, v_00_u03b2_2512_, v_cmp_2513_, v_f_2514_, v_t_2515_);
lean_dec_ref(v_cmp_2513_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap___redArg(lean_object* v_f_2517_, lean_object* v_t_2518_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_2517_, v_t_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap(lean_object* v_00_u03b1_2520_, lean_object* v_00_u03b2_2521_, lean_object* v_00_u03b3_2522_, lean_object* v_cmp_2523_, lean_object* v_f_2524_, lean_object* v_t_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_2524_, v_t_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap___boxed(lean_object* v_00_u03b1_2527_, lean_object* v_00_u03b2_2528_, lean_object* v_00_u03b3_2529_, lean_object* v_cmp_2530_, lean_object* v_f_2531_, lean_object* v_t_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Std_ExtDTreeMap_filterMap(v_00_u03b1_2527_, v_00_u03b2_2528_, v_00_u03b3_2529_, v_cmp_2530_, v_f_2531_, v_t_2532_);
lean_dec_ref(v_cmp_2530_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map___redArg(lean_object* v_f_2534_, lean_object* v_t_2535_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_2534_, v_t_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map(lean_object* v_00_u03b1_2537_, lean_object* v_00_u03b2_2538_, lean_object* v_00_u03b3_2539_, lean_object* v_cmp_2540_, lean_object* v_f_2541_, lean_object* v_t_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_2541_, v_t_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map___boxed(lean_object* v_00_u03b1_2544_, lean_object* v_00_u03b2_2545_, lean_object* v_00_u03b3_2546_, lean_object* v_cmp_2547_, lean_object* v_f_2548_, lean_object* v_t_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Std_ExtDTreeMap_map(v_00_u03b1_2544_, v_00_u03b2_2545_, v_00_u03b3_2546_, v_cmp_2547_, v_f_2548_, v_t_2549_);
lean_dec_ref(v_cmp_2547_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM___redArg(lean_object* v_inst_2551_, lean_object* v_f_2552_, lean_object* v_init_2553_, lean_object* v_t_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2551_, v_f_2552_, v_init_2553_, v_t_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM(lean_object* v_00_u03b1_2556_, lean_object* v_00_u03b2_2557_, lean_object* v_cmp_2558_, lean_object* v_00_u03b4_2559_, lean_object* v_m_2560_, lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_f_2564_, lean_object* v_init_2565_, lean_object* v_t_2566_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2561_, v_f_2564_, v_init_2565_, v_t_2566_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM___boxed(lean_object* v_00_u03b1_2568_, lean_object* v_00_u03b2_2569_, lean_object* v_cmp_2570_, lean_object* v_00_u03b4_2571_, lean_object* v_m_2572_, lean_object* v_inst_2573_, lean_object* v_inst_2574_, lean_object* v_inst_2575_, lean_object* v_f_2576_, lean_object* v_init_2577_, lean_object* v_t_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Std_ExtDTreeMap_foldlM(v_00_u03b1_2568_, v_00_u03b2_2569_, v_cmp_2570_, v_00_u03b4_2571_, v_m_2572_, v_inst_2573_, v_inst_2574_, v_inst_2575_, v_f_2576_, v_init_2577_, v_t_2578_);
lean_dec_ref(v_cmp_2570_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl___redArg(lean_object* v_f_2580_, lean_object* v_init_2581_, lean_object* v_t_2582_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2580_, v_init_2581_, v_t_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl(lean_object* v_00_u03b1_2584_, lean_object* v_00_u03b2_2585_, lean_object* v_cmp_2586_, lean_object* v_00_u03b4_2587_, lean_object* v_inst_2588_, lean_object* v_f_2589_, lean_object* v_init_2590_, lean_object* v_t_2591_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2589_, v_init_2590_, v_t_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl___boxed(lean_object* v_00_u03b1_2593_, lean_object* v_00_u03b2_2594_, lean_object* v_cmp_2595_, lean_object* v_00_u03b4_2596_, lean_object* v_inst_2597_, lean_object* v_f_2598_, lean_object* v_init_2599_, lean_object* v_t_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Std_ExtDTreeMap_foldl(v_00_u03b1_2593_, v_00_u03b2_2594_, v_cmp_2595_, v_00_u03b4_2596_, v_inst_2597_, v_f_2598_, v_init_2599_, v_t_2600_);
lean_dec_ref(v_cmp_2595_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM___redArg(lean_object* v_inst_2602_, lean_object* v_f_2603_, lean_object* v_init_2604_, lean_object* v_t_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2602_, v_f_2603_, v_init_2604_, v_t_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM(lean_object* v_00_u03b1_2607_, lean_object* v_00_u03b2_2608_, lean_object* v_cmp_2609_, lean_object* v_00_u03b4_2610_, lean_object* v_m_2611_, lean_object* v_inst_2612_, lean_object* v_inst_2613_, lean_object* v_inst_2614_, lean_object* v_f_2615_, lean_object* v_init_2616_, lean_object* v_t_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2612_, v_f_2615_, v_init_2616_, v_t_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM___boxed(lean_object* v_00_u03b1_2619_, lean_object* v_00_u03b2_2620_, lean_object* v_cmp_2621_, lean_object* v_00_u03b4_2622_, lean_object* v_m_2623_, lean_object* v_inst_2624_, lean_object* v_inst_2625_, lean_object* v_inst_2626_, lean_object* v_f_2627_, lean_object* v_init_2628_, lean_object* v_t_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Std_ExtDTreeMap_foldrM(v_00_u03b1_2619_, v_00_u03b2_2620_, v_cmp_2621_, v_00_u03b4_2622_, v_m_2623_, v_inst_2624_, v_inst_2625_, v_inst_2626_, v_f_2627_, v_init_2628_, v_t_2629_);
lean_dec_ref(v_cmp_2621_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___redArg___lam__0(lean_object* v_f_2631_, lean_object* v_x1_2632_, lean_object* v_x2_2633_, lean_object* v_x3_2634_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_apply_3(v_f_2631_, v_x1_2632_, v_x2_2633_, v_x3_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___redArg(lean_object* v_f_2655_, lean_object* v_init_2656_, lean_object* v_t_2657_){
_start:
{
lean_object* v___f_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___f_2658_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2658_, 0, v_f_2655_);
v___x_2659_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2660_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2659_, v___f_2658_, v_init_2656_, v_t_2657_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr(lean_object* v_00_u03b1_2661_, lean_object* v_00_u03b2_2662_, lean_object* v_cmp_2663_, lean_object* v_00_u03b4_2664_, lean_object* v_inst_2665_, lean_object* v_f_2666_, lean_object* v_init_2667_, lean_object* v_t_2668_){
_start:
{
lean_object* v___f_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___f_2669_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2669_, 0, v_f_2666_);
v___x_2670_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2671_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2670_, v___f_2669_, v_init_2667_, v_t_2668_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___boxed(lean_object* v_00_u03b1_2672_, lean_object* v_00_u03b2_2673_, lean_object* v_cmp_2674_, lean_object* v_00_u03b4_2675_, lean_object* v_inst_2676_, lean_object* v_f_2677_, lean_object* v_init_2678_, lean_object* v_t_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Std_ExtDTreeMap_foldr(v_00_u03b1_2672_, v_00_u03b2_2673_, v_cmp_2674_, v_00_u03b4_2675_, v_inst_2676_, v_f_2677_, v_init_2678_, v_t_2679_);
lean_dec_ref(v_cmp_2674_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition___redArg___lam__0(lean_object* v_f_2681_, lean_object* v_cmp_2682_, lean_object* v_x_2683_, lean_object* v_a_2684_, lean_object* v_b_2685_){
_start:
{
lean_object* v_fst_2686_; lean_object* v_snd_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2701_; 
v_fst_2686_ = lean_ctor_get(v_x_2683_, 0);
v_snd_2687_ = lean_ctor_get(v_x_2683_, 1);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_x_2683_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2689_ = v_x_2683_;
v_isShared_2690_ = v_isSharedCheck_2701_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_snd_2687_);
lean_inc(v_fst_2686_);
lean_dec(v_x_2683_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2701_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; uint8_t v___x_2692_; 
lean_inc(v_b_2685_);
lean_inc(v_a_2684_);
v___x_2691_ = lean_apply_2(v_f_2681_, v_a_2684_, v_b_2685_);
v___x_2692_ = lean_unbox(v___x_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2693_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2682_, v_a_2684_, v_b_2685_, v_snd_2687_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 1, v___x_2693_);
v___x_2695_ = v___x_2689_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_fst_2686_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2682_, v_a_2684_, v_b_2685_, v_fst_2686_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v___x_2697_);
v___x_2699_ = v___x_2689_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_snd_2687_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition___redArg(lean_object* v_cmp_2704_, lean_object* v_f_2705_, lean_object* v_t_2706_){
_start:
{
lean_object* v___f_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___f_2707_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2707_, 0, v_f_2705_);
lean_closure_set(v___f_2707_, 1, v_cmp_2704_);
v___x_2708_ = ((lean_object*)(l_Std_ExtDTreeMap_partition___redArg___closed__0));
v___x_2709_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2707_, v___x_2708_, v_t_2706_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition(lean_object* v_00_u03b1_2710_, lean_object* v_00_u03b2_2711_, lean_object* v_cmp_2712_, lean_object* v_inst_2713_, lean_object* v_f_2714_, lean_object* v_t_2715_){
_start:
{
lean_object* v___f_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___f_2716_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2716_, 0, v_f_2714_);
lean_closure_set(v___f_2716_, 1, v_cmp_2712_);
v___x_2717_ = ((lean_object*)(l_Std_ExtDTreeMap_partition___redArg___closed__0));
v___x_2718_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2716_, v___x_2717_, v_t_2715_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___redArg___lam__0(lean_object* v_f_2719_, lean_object* v_x_2720_, lean_object* v_k_2721_, lean_object* v_v_2722_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = lean_apply_2(v_f_2719_, v_k_2721_, v_v_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___redArg(lean_object* v_inst_2724_, lean_object* v_f_2725_, lean_object* v_t_2726_){
_start:
{
lean_object* v___f_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___f_2727_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2727_, 0, v_f_2725_);
v___x_2728_ = lean_box(0);
v___x_2729_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2724_, v___f_2727_, v___x_2728_, v_t_2726_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM(lean_object* v_00_u03b1_2730_, lean_object* v_00_u03b2_2731_, lean_object* v_cmp_2732_, lean_object* v_m_2733_, lean_object* v_inst_2734_, lean_object* v_inst_2735_, lean_object* v_inst_2736_, lean_object* v_f_2737_, lean_object* v_t_2738_){
_start:
{
lean_object* v___f_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___f_2739_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2739_, 0, v_f_2737_);
v___x_2740_ = lean_box(0);
v___x_2741_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2734_, v___f_2739_, v___x_2740_, v_t_2738_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_00_u03b2_2743_, lean_object* v_cmp_2744_, lean_object* v_m_2745_, lean_object* v_inst_2746_, lean_object* v_inst_2747_, lean_object* v_inst_2748_, lean_object* v_f_2749_, lean_object* v_t_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Std_ExtDTreeMap_forM(v_00_u03b1_2742_, v_00_u03b2_2743_, v_cmp_2744_, v_m_2745_, v_inst_2746_, v_inst_2747_, v_inst_2748_, v_f_2749_, v_t_2750_);
lean_dec_ref(v_cmp_2744_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___redArg___lam__0(lean_object* v_toPure_2752_, lean_object* v_____do__lift_2753_){
_start:
{
lean_object* v_a_2754_; lean_object* v___x_2755_; 
v_a_2754_ = lean_ctor_get(v_____do__lift_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref(v_____do__lift_2753_);
v___x_2755_ = lean_apply_2(v_toPure_2752_, lean_box(0), v_a_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___redArg(lean_object* v_inst_2756_, lean_object* v_f_2757_, lean_object* v_init_2758_, lean_object* v_t_2759_){
_start:
{
lean_object* v_toApplicative_2760_; lean_object* v_toBind_2761_; lean_object* v_toPure_2762_; lean_object* v___x_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; 
v_toApplicative_2760_ = lean_ctor_get(v_inst_2756_, 0);
v_toBind_2761_ = lean_ctor_get(v_inst_2756_, 1);
lean_inc(v_toBind_2761_);
v_toPure_2762_ = lean_ctor_get(v_toApplicative_2760_, 1);
lean_inc(v_toPure_2762_);
v___x_2763_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2756_, v_f_2757_, v_init_2758_, v_t_2759_);
v___f_2764_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2764_, 0, v_toPure_2762_);
v___x_2765_ = lean_apply_4(v_toBind_2761_, lean_box(0), lean_box(0), v___x_2763_, v___f_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn(lean_object* v_00_u03b1_2766_, lean_object* v_00_u03b2_2767_, lean_object* v_cmp_2768_, lean_object* v_00_u03b4_2769_, lean_object* v_m_2770_, lean_object* v_inst_2771_, lean_object* v_inst_2772_, lean_object* v_inst_2773_, lean_object* v_f_2774_, lean_object* v_init_2775_, lean_object* v_t_2776_){
_start:
{
lean_object* v_toApplicative_2777_; lean_object* v_toBind_2778_; lean_object* v_toPure_2779_; lean_object* v___x_2780_; lean_object* v___f_2781_; lean_object* v___x_2782_; 
v_toApplicative_2777_ = lean_ctor_get(v_inst_2771_, 0);
v_toBind_2778_ = lean_ctor_get(v_inst_2771_, 1);
lean_inc(v_toBind_2778_);
v_toPure_2779_ = lean_ctor_get(v_toApplicative_2777_, 1);
lean_inc(v_toPure_2779_);
v___x_2780_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2771_, v_f_2774_, v_init_2775_, v_t_2776_);
v___f_2781_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2781_, 0, v_toPure_2779_);
v___x_2782_ = lean_apply_4(v_toBind_2778_, lean_box(0), lean_box(0), v___x_2780_, v___f_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___boxed(lean_object* v_00_u03b1_2783_, lean_object* v_00_u03b2_2784_, lean_object* v_cmp_2785_, lean_object* v_00_u03b4_2786_, lean_object* v_m_2787_, lean_object* v_inst_2788_, lean_object* v_inst_2789_, lean_object* v_inst_2790_, lean_object* v_f_2791_, lean_object* v_init_2792_, lean_object* v_t_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Std_ExtDTreeMap_forIn(v_00_u03b1_2783_, v_00_u03b2_2784_, v_cmp_2785_, v_00_u03b4_2786_, v_m_2787_, v_inst_2788_, v_inst_2789_, v_inst_2790_, v_f_2791_, v_init_2792_, v_t_2793_);
lean_dec_ref(v_cmp_2785_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2795_, lean_object* v_x_2796_, lean_object* v_k_2797_, lean_object* v_v_2798_){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v_k_2797_);
lean_ctor_set(v___x_2799_, 1, v_v_2798_);
v___x_2800_ = lean_apply_1(v_f_2795_, v___x_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_2801_, lean_object* v_t_2802_, lean_object* v_f_2803_){
_start:
{
lean_object* v___f_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___f_2804_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2804_, 0, v_f_2803_);
v___x_2805_ = lean_box(0);
v___x_2806_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2801_, v___f_2804_, v___x_2805_, v_t_2802_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2807_){
_start:
{
lean_object* v___f_2808_; 
v___f_2808_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2808_, 0, v_inst_2807_);
return v___f_2808_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2809_, lean_object* v_00_u03b2_2810_, lean_object* v_cmp_2811_, lean_object* v_m_2812_, lean_object* v_inst_2813_, lean_object* v_inst_2814_, lean_object* v_inst_2815_){
_start:
{
lean_object* v___f_2816_; 
v___f_2816_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2816_, 0, v_inst_2814_);
return v___f_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2817_, lean_object* v_00_u03b2_2818_, lean_object* v_cmp_2819_, lean_object* v_m_2820_, lean_object* v_inst_2821_, lean_object* v_inst_2822_, lean_object* v_inst_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(v_00_u03b1_2817_, v_00_u03b2_2818_, v_cmp_2819_, v_m_2820_, v_inst_2821_, v_inst_2822_, v_inst_2823_);
lean_dec_ref(v_cmp_2819_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2825_, lean_object* v_a_2826_, lean_object* v_b_2827_, lean_object* v_acc_2828_){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v_a_2826_);
lean_ctor_set(v___x_2829_, 1, v_b_2827_);
v___x_2830_ = lean_apply_2(v_f_2825_, v___x_2829_, v_acc_2828_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_2831_, lean_object* v_00_u03b2_2832_, lean_object* v_m_2833_, lean_object* v_init_2834_, lean_object* v_f_2835_){
_start:
{
lean_object* v_toApplicative_2836_; lean_object* v_toBind_2837_; lean_object* v_toPure_2838_; lean_object* v___f_2839_; lean_object* v___x_2840_; lean_object* v___f_2841_; lean_object* v___x_2842_; 
v_toApplicative_2836_ = lean_ctor_get(v_inst_2831_, 0);
v_toBind_2837_ = lean_ctor_get(v_inst_2831_, 1);
lean_inc(v_toBind_2837_);
v_toPure_2838_ = lean_ctor_get(v_toApplicative_2836_, 1);
lean_inc(v_toPure_2838_);
v___f_2839_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2839_, 0, v_f_2835_);
v___x_2840_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2831_, v___f_2839_, v_init_2834_, v_m_2833_);
v___f_2841_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2841_, 0, v_toPure_2838_);
v___x_2842_ = lean_apply_4(v_toBind_2837_, lean_box(0), lean_box(0), v___x_2840_, v___f_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2843_){
_start:
{
lean_object* v___f_2844_; 
v___f_2844_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2844_, 0, v_inst_2843_);
return v___f_2844_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2845_, lean_object* v_00_u03b2_2846_, lean_object* v_cmp_2847_, lean_object* v_m_2848_, lean_object* v_inst_2849_, lean_object* v_inst_2850_, lean_object* v_inst_2851_){
_start:
{
lean_object* v___f_2852_; 
v___f_2852_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2852_, 0, v_inst_2850_);
return v___f_2852_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2853_, lean_object* v_00_u03b2_2854_, lean_object* v_cmp_2855_, lean_object* v_m_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_inst_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(v_00_u03b1_2853_, v_00_u03b2_2854_, v_cmp_2855_, v_m_2856_, v_inst_2857_, v_inst_2858_, v_inst_2859_);
lean_dec_ref(v_cmp_2855_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2861_, lean_object* v_x_2862_, lean_object* v_k_2863_, lean_object* v_v_2864_){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v_k_2863_);
lean_ctor_set(v___x_2865_, 1, v_v_2864_);
v___x_2866_ = lean_apply_1(v_f_2861_, v___x_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___redArg(lean_object* v_inst_2867_, lean_object* v_f_2868_, lean_object* v_t_2869_){
_start:
{
lean_object* v___f_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___f_2870_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2870_, 0, v_f_2868_);
v___x_2871_ = lean_box(0);
v___x_2872_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2867_, v___f_2870_, v___x_2871_, v_t_2869_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried(lean_object* v_00_u03b1_2873_, lean_object* v_cmp_2874_, lean_object* v_m_2875_, lean_object* v_inst_2876_, lean_object* v_inst_2877_, lean_object* v_00_u03b2_2878_, lean_object* v_inst_2879_, lean_object* v_f_2880_, lean_object* v_t_2881_){
_start:
{
lean_object* v___f_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___f_2882_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2882_, 0, v_f_2880_);
v___x_2883_ = lean_box(0);
v___x_2884_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2876_, v___f_2882_, v___x_2883_, v_t_2881_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2885_, lean_object* v_cmp_2886_, lean_object* v_m_2887_, lean_object* v_inst_2888_, lean_object* v_inst_2889_, lean_object* v_00_u03b2_2890_, lean_object* v_inst_2891_, lean_object* v_f_2892_, lean_object* v_t_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Std_ExtDTreeMap_Const_forMUncurried(v_00_u03b1_2885_, v_cmp_2886_, v_m_2887_, v_inst_2888_, v_inst_2889_, v_00_u03b2_2890_, v_inst_2891_, v_f_2892_, v_t_2893_);
lean_dec_ref(v_cmp_2886_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2895_, lean_object* v_a_2896_, lean_object* v_b_2897_, lean_object* v_acc_2898_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2899_, 0, v_a_2896_);
lean_ctor_set(v___x_2899_, 1, v_b_2897_);
v___x_2900_ = lean_apply_2(v_f_2895_, v___x_2899_, v_acc_2898_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___redArg(lean_object* v_inst_2901_, lean_object* v_f_2902_, lean_object* v_init_2903_, lean_object* v_t_2904_){
_start:
{
lean_object* v_toApplicative_2905_; lean_object* v_toBind_2906_; lean_object* v_toPure_2907_; lean_object* v___f_2908_; lean_object* v___x_2909_; lean_object* v___f_2910_; lean_object* v___x_2911_; 
v_toApplicative_2905_ = lean_ctor_get(v_inst_2901_, 0);
v_toBind_2906_ = lean_ctor_get(v_inst_2901_, 1);
lean_inc(v_toBind_2906_);
v_toPure_2907_ = lean_ctor_get(v_toApplicative_2905_, 1);
lean_inc(v_toPure_2907_);
v___f_2908_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2908_, 0, v_f_2902_);
v___x_2909_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2901_, v___f_2908_, v_init_2903_, v_t_2904_);
v___f_2910_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2910_, 0, v_toPure_2907_);
v___x_2911_ = lean_apply_4(v_toBind_2906_, lean_box(0), lean_box(0), v___x_2909_, v___f_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried(lean_object* v_00_u03b1_2912_, lean_object* v_cmp_2913_, lean_object* v_00_u03b4_2914_, lean_object* v_m_2915_, lean_object* v_inst_2916_, lean_object* v_inst_2917_, lean_object* v_00_u03b2_2918_, lean_object* v_inst_2919_, lean_object* v_f_2920_, lean_object* v_init_2921_, lean_object* v_t_2922_){
_start:
{
lean_object* v_toApplicative_2923_; lean_object* v_toBind_2924_; lean_object* v_toPure_2925_; lean_object* v___f_2926_; lean_object* v___x_2927_; lean_object* v___f_2928_; lean_object* v___x_2929_; 
v_toApplicative_2923_ = lean_ctor_get(v_inst_2916_, 0);
v_toBind_2924_ = lean_ctor_get(v_inst_2916_, 1);
lean_inc(v_toBind_2924_);
v_toPure_2925_ = lean_ctor_get(v_toApplicative_2923_, 1);
lean_inc(v_toPure_2925_);
v___f_2926_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2926_, 0, v_f_2920_);
v___x_2927_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2916_, v___f_2926_, v_init_2921_, v_t_2922_);
v___f_2928_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2928_, 0, v_toPure_2925_);
v___x_2929_ = lean_apply_4(v_toBind_2924_, lean_box(0), lean_box(0), v___x_2927_, v___f_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2930_, lean_object* v_cmp_2931_, lean_object* v_00_u03b4_2932_, lean_object* v_m_2933_, lean_object* v_inst_2934_, lean_object* v_inst_2935_, lean_object* v_00_u03b2_2936_, lean_object* v_inst_2937_, lean_object* v_f_2938_, lean_object* v_init_2939_, lean_object* v_t_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Std_ExtDTreeMap_Const_forInUncurried(v_00_u03b1_2930_, v_cmp_2931_, v_00_u03b4_2932_, v_m_2933_, v_inst_2934_, v_inst_2935_, v_00_u03b2_2936_, v_inst_2937_, v_f_2938_, v_init_2939_, v_t_2940_);
lean_dec_ref(v_cmp_2931_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___lam__0(lean_object* v_p_2942_, lean_object* v___x_2943_, lean_object* v___x_2944_, lean_object* v_a_2945_, lean_object* v_b_2946_, lean_object* v_acc_2947_){
_start:
{
lean_object* v___x_2948_; uint8_t v___x_2949_; 
v___x_2948_ = lean_apply_2(v_p_2942_, v_a_2945_, v_b_2946_);
v___x_2949_ = lean_unbox(v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2943_);
return v___x_2950_;
}
else
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
lean_dec_ref(v___x_2943_);
v___x_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2948_);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
lean_ctor_set(v___x_2952_, 1, v___x_2944_);
v___x_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2954_, lean_object* v___x_2955_, lean_object* v___x_2956_, lean_object* v_a_2957_, lean_object* v_b_2958_, lean_object* v_acc_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Std_ExtDTreeMap_any___redArg___lam__0(v_p_2954_, v___x_2955_, v___x_2956_, v_a_2957_, v_b_2958_, v_acc_2959_);
lean_dec_ref(v_acc_2959_);
return v_res_2960_;
}
}
uint8_t l_Std_ExtDTreeMap_any___redArg(lean_object* v_t_2964_, lean_object* v_p_2965_){
_start:
{
lean_object* v___y_2967_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___f_2975_; lean_object* v___x_2976_; lean_object* v_a_2977_; 
v___x_2972_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2973_ = lean_box(0);
v___x_2974_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_2975_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2975_, 0, v_p_2965_);
lean_closure_set(v___f_2975_, 1, v___x_2974_);
lean_closure_set(v___f_2975_, 2, v___x_2973_);
v___x_2976_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2972_, v___f_2975_, v___x_2974_, v_t_2964_);
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
lean_dec(v___x_2976_);
v___y_2967_ = v_a_2977_;
goto v___jp_2966_;
v___jp_2966_:
{
lean_object* v_fst_2968_; 
v_fst_2968_ = lean_ctor_get(v___y_2967_, 0);
lean_inc(v_fst_2968_);
lean_dec_ref(v___y_2967_);
if (lean_obj_tag(v_fst_2968_) == 0)
{
uint8_t v___x_2969_; 
v___x_2969_ = 0;
return v___x_2969_;
}
else
{
lean_object* v_val_2970_; uint8_t v___x_2971_; 
v_val_2970_ = lean_ctor_get(v_fst_2968_, 0);
lean_inc(v_val_2970_);
lean_dec_ref_known(v_fst_2968_, 1);
v___x_2971_ = lean_unbox(v_val_2970_);
lean_dec(v_val_2970_);
return v___x_2971_;
}
}
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2964_ = stack[0].m_obj;
lean_object* v_p_2965_ = stack[1].m_obj;
uint8_t v_res_2978_;
v_res_2978_ = l_Std_ExtDTreeMap_any___redArg(v_t_2964_, v_p_2965_);
stack->m_num = v_res_2978_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___boxed(lean_object* v_t_2979_, lean_object* v_p_2980_){
_start:
{
uint8_t v_res_2981_; lean_object* v_r_2982_; 
v_res_2981_ = l_Std_ExtDTreeMap_any___redArg(v_t_2979_, v_p_2980_);
v_r_2982_ = lean_box(v_res_2981_);
return v_r_2982_;
}
}
uint8_t l_Std_ExtDTreeMap_any(lean_object* v_00_u03b1_2983_, lean_object* v_00_u03b2_2984_, lean_object* v_cmp_2985_, lean_object* v_inst_2986_, lean_object* v_t_2987_, lean_object* v_p_2988_){
_start:
{
lean_object* v___y_2990_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___f_2998_; lean_object* v___x_2999_; lean_object* v_a_3000_; 
v___x_2995_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2996_ = lean_box(0);
v___x_2997_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_2998_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2998_, 0, v_p_2988_);
lean_closure_set(v___f_2998_, 1, v___x_2997_);
lean_closure_set(v___f_2998_, 2, v___x_2996_);
v___x_2999_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2995_, v___f_2998_, v___x_2997_, v_t_2987_);
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec(v___x_2999_);
v___y_2990_ = v_a_3000_;
goto v___jp_2989_;
v___jp_2989_:
{
lean_object* v_fst_2991_; 
v_fst_2991_ = lean_ctor_get(v___y_2990_, 0);
lean_inc(v_fst_2991_);
lean_dec_ref(v___y_2990_);
if (lean_obj_tag(v_fst_2991_) == 0)
{
uint8_t v___x_2992_; 
v___x_2992_ = 0;
return v___x_2992_;
}
else
{
lean_object* v_val_2993_; uint8_t v___x_2994_; 
v_val_2993_ = lean_ctor_get(v_fst_2991_, 0);
lean_inc(v_val_2993_);
lean_dec_ref_known(v_fst_2991_, 1);
v___x_2994_ = lean_unbox(v_val_2993_);
lean_dec(v_val_2993_);
return v___x_2994_;
}
}
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2985_ = stack[2].m_obj;
lean_object* v_t_2987_ = stack[4].m_obj;
lean_object* v_p_2988_ = stack[5].m_obj;
uint8_t v_res_3001_;
v_res_3001_ = l_Std_ExtDTreeMap_any(lean_box(0), lean_box(0), v_cmp_2985_, lean_box(0), v_t_2987_, v_p_2988_);
stack->m_num = v_res_3001_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___boxed(lean_object* v_00_u03b1_3002_, lean_object* v_00_u03b2_3003_, lean_object* v_cmp_3004_, lean_object* v_inst_3005_, lean_object* v_t_3006_, lean_object* v_p_3007_){
_start:
{
uint8_t v_res_3008_; lean_object* v_r_3009_; 
v_res_3008_ = l_Std_ExtDTreeMap_any(v_00_u03b1_3002_, v_00_u03b2_3003_, v_cmp_3004_, v_inst_3005_, v_t_3006_, v_p_3007_);
lean_dec_ref(v_cmp_3004_);
v_r_3009_ = lean_box(v_res_3008_);
return v_r_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___lam__0(lean_object* v_p_3010_, lean_object* v___x_3011_, lean_object* v___x_3012_, lean_object* v_a_3013_, lean_object* v_b_3014_, lean_object* v_acc_3015_){
_start:
{
lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3016_ = lean_apply_2(v_p_3010_, v_a_3013_, v_b_3014_);
v___x_3017_ = lean_unbox(v___x_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_dec_ref(v___x_3012_);
v___x_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v___x_3011_);
v___x_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3012_);
return v___x_3021_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_3022_, lean_object* v___x_3023_, lean_object* v___x_3024_, lean_object* v_a_3025_, lean_object* v_b_3026_, lean_object* v_acc_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Std_ExtDTreeMap_all___redArg___lam__0(v_p_3022_, v___x_3023_, v___x_3024_, v_a_3025_, v_b_3026_, v_acc_3027_);
lean_dec_ref(v_acc_3027_);
return v_res_3028_;
}
}
uint8_t l_Std_ExtDTreeMap_all___redArg(lean_object* v_t_3029_, lean_object* v_p_3030_){
_start:
{
lean_object* v___y_3032_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___f_3040_; lean_object* v___x_3041_; lean_object* v_a_3042_; 
v___x_3037_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3038_ = lean_box(0);
v___x_3039_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_3040_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3040_, 0, v_p_3030_);
lean_closure_set(v___f_3040_, 1, v___x_3038_);
lean_closure_set(v___f_3040_, 2, v___x_3039_);
v___x_3041_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_3037_, v___f_3040_, v___x_3039_, v_t_3029_);
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec(v___x_3041_);
v___y_3032_ = v_a_3042_;
goto v___jp_3031_;
v___jp_3031_:
{
lean_object* v_fst_3033_; 
v_fst_3033_ = lean_ctor_get(v___y_3032_, 0);
lean_inc(v_fst_3033_);
lean_dec_ref(v___y_3032_);
if (lean_obj_tag(v_fst_3033_) == 0)
{
uint8_t v___x_3034_; 
v___x_3034_ = 1;
return v___x_3034_;
}
else
{
lean_object* v_val_3035_; uint8_t v___x_3036_; 
v_val_3035_ = lean_ctor_get(v_fst_3033_, 0);
lean_inc(v_val_3035_);
lean_dec_ref_known(v_fst_3033_, 1);
v___x_3036_ = lean_unbox(v_val_3035_);
lean_dec(v_val_3035_);
return v___x_3036_;
}
}
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3029_ = stack[0].m_obj;
lean_object* v_p_3030_ = stack[1].m_obj;
uint8_t v_res_3043_;
v_res_3043_ = l_Std_ExtDTreeMap_all___redArg(v_t_3029_, v_p_3030_);
stack->m_num = v_res_3043_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___boxed(lean_object* v_t_3044_, lean_object* v_p_3045_){
_start:
{
uint8_t v_res_3046_; lean_object* v_r_3047_; 
v_res_3046_ = l_Std_ExtDTreeMap_all___redArg(v_t_3044_, v_p_3045_);
v_r_3047_ = lean_box(v_res_3046_);
return v_r_3047_;
}
}
uint8_t l_Std_ExtDTreeMap_all(lean_object* v_00_u03b1_3048_, lean_object* v_00_u03b2_3049_, lean_object* v_cmp_3050_, lean_object* v_inst_3051_, lean_object* v_t_3052_, lean_object* v_p_3053_){
_start:
{
lean_object* v___y_3055_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___f_3063_; lean_object* v___x_3064_; lean_object* v_a_3065_; 
v___x_3060_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3061_ = lean_box(0);
v___x_3062_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_3063_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3063_, 0, v_p_3053_);
lean_closure_set(v___f_3063_, 1, v___x_3061_);
lean_closure_set(v___f_3063_, 2, v___x_3062_);
v___x_3064_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_3060_, v___f_3063_, v___x_3062_, v_t_3052_);
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec(v___x_3064_);
v___y_3055_ = v_a_3065_;
goto v___jp_3054_;
v___jp_3054_:
{
lean_object* v_fst_3056_; 
v_fst_3056_ = lean_ctor_get(v___y_3055_, 0);
lean_inc(v_fst_3056_);
lean_dec_ref(v___y_3055_);
if (lean_obj_tag(v_fst_3056_) == 0)
{
uint8_t v___x_3057_; 
v___x_3057_ = 1;
return v___x_3057_;
}
else
{
lean_object* v_val_3058_; uint8_t v___x_3059_; 
v_val_3058_ = lean_ctor_get(v_fst_3056_, 0);
lean_inc(v_val_3058_);
lean_dec_ref_known(v_fst_3056_, 1);
v___x_3059_ = lean_unbox(v_val_3058_);
lean_dec(v_val_3058_);
return v___x_3059_;
}
}
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3050_ = stack[2].m_obj;
lean_object* v_t_3052_ = stack[4].m_obj;
lean_object* v_p_3053_ = stack[5].m_obj;
uint8_t v_res_3066_;
v_res_3066_ = l_Std_ExtDTreeMap_all(lean_box(0), lean_box(0), v_cmp_3050_, lean_box(0), v_t_3052_, v_p_3053_);
stack->m_num = v_res_3066_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___boxed(lean_object* v_00_u03b1_3067_, lean_object* v_00_u03b2_3068_, lean_object* v_cmp_3069_, lean_object* v_inst_3070_, lean_object* v_t_3071_, lean_object* v_p_3072_){
_start:
{
uint8_t v_res_3073_; lean_object* v_r_3074_; 
v_res_3073_ = l_Std_ExtDTreeMap_all(v_00_u03b1_3067_, v_00_u03b2_3068_, v_cmp_3069_, v_inst_3070_, v_t_3071_, v_p_3072_);
lean_dec_ref(v_cmp_3069_);
v_r_3074_ = lean_box(v_res_3073_);
return v_r_3074_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg___lam__0(lean_object* v_x1_3075_, lean_object* v_x2_3076_, lean_object* v_x3_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3078_, 0, v_x1_3075_);
lean_ctor_set(v___x_3078_, 1, v_x3_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_3079_, lean_object* v_x2_3080_, lean_object* v_x3_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Std_ExtDTreeMap_keys___redArg___lam__0(v_x1_3079_, v_x2_3080_, v_x3_3081_);
lean_dec(v_x2_3080_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg(lean_object* v_t_3084_){
_start:
{
lean_object* v___f_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___f_3085_ = ((lean_object*)(l_Std_ExtDTreeMap_keys___redArg___closed__0));
v___x_3086_ = lean_box(0);
v___x_3087_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3088_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3087_, v___f_3085_, v___x_3086_, v_t_3084_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys(lean_object* v_00_u03b1_3089_, lean_object* v_00_u03b2_3090_, lean_object* v_cmp_3091_, lean_object* v_inst_3092_, lean_object* v_t_3093_){
_start:
{
lean_object* v___f_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___f_3094_ = ((lean_object*)(l_Std_ExtDTreeMap_keys___redArg___closed__0));
v___x_3095_ = lean_box(0);
v___x_3096_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3097_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3096_, v___f_3094_, v___x_3095_, v_t_3093_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___boxed(lean_object* v_00_u03b1_3098_, lean_object* v_00_u03b2_3099_, lean_object* v_cmp_3100_, lean_object* v_inst_3101_, lean_object* v_t_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Std_ExtDTreeMap_keys(v_00_u03b1_3098_, v_00_u03b2_3099_, v_cmp_3100_, v_inst_3101_, v_t_3102_);
lean_dec_ref(v_cmp_3100_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg___lam__0(lean_object* v_l_3104_, lean_object* v_k_3105_, lean_object* v_x_3106_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = lean_array_push(v_l_3104_, v_k_3105_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_3108_, lean_object* v_k_3109_, lean_object* v_x_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Std_ExtDTreeMap_keysArray___redArg___lam__0(v_l_3108_, v_k_3109_, v_x_3110_);
lean_dec(v_x_3110_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg(lean_object* v_t_3113_){
_start:
{
lean_object* v___f_3114_; lean_object* v___y_3116_; 
v___f_3114_ = ((lean_object*)(l_Std_ExtDTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_3113_) == 0)
{
lean_object* v_size_3119_; 
v_size_3119_ = lean_ctor_get(v_t_3113_, 0);
lean_inc(v_size_3119_);
v___y_3116_ = v_size_3119_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3120_; 
v___x_3120_ = lean_unsigned_to_nat(0u);
v___y_3116_ = v___x_3120_;
goto v___jp_3115_;
}
v___jp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_mk_empty_array_with_capacity(v___y_3116_);
lean_dec(v___y_3116_);
v___x_3118_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3114_, v___x_3117_, v_t_3113_);
return v___x_3118_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray(lean_object* v_00_u03b1_3121_, lean_object* v_00_u03b2_3122_, lean_object* v_cmp_3123_, lean_object* v_inst_3124_, lean_object* v_t_3125_){
_start:
{
lean_object* v___f_3126_; lean_object* v___y_3128_; 
v___f_3126_ = ((lean_object*)(l_Std_ExtDTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_3125_) == 0)
{
lean_object* v_size_3131_; 
v_size_3131_ = lean_ctor_get(v_t_3125_, 0);
lean_inc(v_size_3131_);
v___y_3128_ = v_size_3131_;
goto v___jp_3127_;
}
else
{
lean_object* v___x_3132_; 
v___x_3132_ = lean_unsigned_to_nat(0u);
v___y_3128_ = v___x_3132_;
goto v___jp_3127_;
}
v___jp_3127_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = lean_mk_empty_array_with_capacity(v___y_3128_);
lean_dec(v___y_3128_);
v___x_3130_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3126_, v___x_3129_, v_t_3125_);
return v___x_3130_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___boxed(lean_object* v_00_u03b1_3133_, lean_object* v_00_u03b2_3134_, lean_object* v_cmp_3135_, lean_object* v_inst_3136_, lean_object* v_t_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Std_ExtDTreeMap_keysArray(v_00_u03b1_3133_, v_00_u03b2_3134_, v_cmp_3135_, v_inst_3136_, v_t_3137_);
lean_dec_ref(v_cmp_3135_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg___lam__0(lean_object* v_x1_3139_, lean_object* v_x2_3140_, lean_object* v_x3_3141_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_x2_3140_);
lean_ctor_set(v___x_3142_, 1, v_x3_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_3143_, lean_object* v_x2_3144_, lean_object* v_x3_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Std_ExtDTreeMap_values___redArg___lam__0(v_x1_3143_, v_x2_3144_, v_x3_3145_);
lean_dec(v_x1_3143_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg(lean_object* v_t_3148_){
_start:
{
lean_object* v___f_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___f_3149_ = ((lean_object*)(l_Std_ExtDTreeMap_values___redArg___closed__0));
v___x_3150_ = lean_box(0);
v___x_3151_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3152_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3151_, v___f_3149_, v___x_3150_, v_t_3148_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values(lean_object* v_00_u03b1_3153_, lean_object* v_cmp_3154_, lean_object* v_inst_3155_, lean_object* v_00_u03b2_3156_, lean_object* v_t_3157_){
_start:
{
lean_object* v___f_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___f_3158_ = ((lean_object*)(l_Std_ExtDTreeMap_values___redArg___closed__0));
v___x_3159_ = lean_box(0);
v___x_3160_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3161_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3160_, v___f_3158_, v___x_3159_, v_t_3157_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___boxed(lean_object* v_00_u03b1_3162_, lean_object* v_cmp_3163_, lean_object* v_inst_3164_, lean_object* v_00_u03b2_3165_, lean_object* v_t_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Std_ExtDTreeMap_values(v_00_u03b1_3162_, v_cmp_3163_, v_inst_3164_, v_00_u03b2_3165_, v_t_3166_);
lean_dec_ref(v_cmp_3163_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_3168_, lean_object* v_x_3169_, lean_object* v_v_3170_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = lean_array_push(v_l_3168_, v_v_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_3172_, lean_object* v_x_3173_, lean_object* v_v_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(v_l_3172_, v_x_3173_, v_v_3174_);
lean_dec(v_x_3173_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg(lean_object* v_t_3177_){
_start:
{
lean_object* v___f_3178_; lean_object* v___y_3180_; 
v___f_3178_ = ((lean_object*)(l_Std_ExtDTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_3177_) == 0)
{
lean_object* v_size_3183_; 
v_size_3183_ = lean_ctor_get(v_t_3177_, 0);
lean_inc(v_size_3183_);
v___y_3180_ = v_size_3183_;
goto v___jp_3179_;
}
else
{
lean_object* v___x_3184_; 
v___x_3184_ = lean_unsigned_to_nat(0u);
v___y_3180_ = v___x_3184_;
goto v___jp_3179_;
}
v___jp_3179_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = lean_mk_empty_array_with_capacity(v___y_3180_);
lean_dec(v___y_3180_);
v___x_3182_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3178_, v___x_3181_, v_t_3177_);
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray(lean_object* v_00_u03b1_3185_, lean_object* v_cmp_3186_, lean_object* v_inst_3187_, lean_object* v_00_u03b2_3188_, lean_object* v_t_3189_){
_start:
{
lean_object* v___f_3190_; lean_object* v___y_3192_; 
v___f_3190_ = ((lean_object*)(l_Std_ExtDTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_3189_) == 0)
{
lean_object* v_size_3195_; 
v_size_3195_ = lean_ctor_get(v_t_3189_, 0);
lean_inc(v_size_3195_);
v___y_3192_ = v_size_3195_;
goto v___jp_3191_;
}
else
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_unsigned_to_nat(0u);
v___y_3192_ = v___x_3196_;
goto v___jp_3191_;
}
v___jp_3191_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = lean_mk_empty_array_with_capacity(v___y_3192_);
lean_dec(v___y_3192_);
v___x_3194_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3190_, v___x_3193_, v_t_3189_);
return v___x_3194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_3197_, lean_object* v_cmp_3198_, lean_object* v_inst_3199_, lean_object* v_00_u03b2_3200_, lean_object* v_t_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Std_ExtDTreeMap_valuesArray(v_00_u03b1_3197_, v_cmp_3198_, v_inst_3199_, v_00_u03b2_3200_, v_t_3201_);
lean_dec_ref(v_cmp_3198_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___redArg___lam__0(lean_object* v_x1_3203_, lean_object* v_x2_3204_, lean_object* v_x3_3205_){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_x1_3203_);
lean_ctor_set(v___x_3206_, 1, v_x2_3204_);
v___x_3207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
lean_ctor_set(v___x_3207_, 1, v_x3_3205_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___redArg(lean_object* v_t_3209_){
_start:
{
lean_object* v___f_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___f_3210_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3211_ = lean_box(0);
v___x_3212_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3213_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3212_, v___f_3210_, v___x_3211_, v_t_3209_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList(lean_object* v_00_u03b1_3214_, lean_object* v_00_u03b2_3215_, lean_object* v_cmp_3216_, lean_object* v_inst_3217_, lean_object* v_t_3218_){
_start:
{
lean_object* v___f_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___f_3219_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3220_ = lean_box(0);
v___x_3221_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3222_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3221_, v___f_3219_, v___x_3220_, v_t_3218_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___boxed(lean_object* v_00_u03b1_3223_, lean_object* v_00_u03b2_3224_, lean_object* v_cmp_3225_, lean_object* v_inst_3226_, lean_object* v_t_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Std_ExtDTreeMap_toList(v_00_u03b1_3223_, v_00_u03b2_3224_, v_cmp_3225_, v_inst_3226_, v_t_3227_);
lean_dec_ref(v_cmp_3225_);
return v_res_3228_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_3230_, lean_object* v_a_3231_, lean_object* v_x_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_fst_3234_; lean_object* v_snd_3235_; lean_object* v_r_3236_; lean_object* v___x_3237_; 
v_fst_3234_ = lean_ctor_get(v_a_3231_, 0);
lean_inc(v_fst_3234_);
v_snd_3235_ = lean_ctor_get(v_a_3231_, 1);
lean_inc(v_snd_3235_);
lean_dec_ref(v_a_3231_);
v_r_3236_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3230_, v_fst_3234_, v_snd_3235_, v___y_3233_);
v___x_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3237_, 0, v_r_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg(lean_object* v_l_3238_, lean_object* v_cmp_3239_){
_start:
{
lean_object* v___f_3240_; lean_object* v___x_3241_; lean_object* v_r_3242_; lean_object* v___x_3243_; 
v___f_3240_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3240_, 0, v_cmp_3239_);
v___x_3241_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3242_ = lean_box(1);
v___x_3243_ = l_List_forIn_x27_loop___redArg(v___x_3241_, v___f_3240_, v_l_3238_, v_r_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg___boxed(lean_object* v_l_3244_, lean_object* v_cmp_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Std_ExtDTreeMap_ofList___redArg(v_l_3244_, v_cmp_3245_);
lean_dec(v_l_3244_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList(lean_object* v_00_u03b1_3247_, lean_object* v_00_u03b2_3248_, lean_object* v_l_3249_, lean_object* v_cmp_3250_){
_start:
{
lean_object* v___f_3251_; lean_object* v___x_3252_; lean_object* v_r_3253_; lean_object* v___x_3254_; 
v___f_3251_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3251_, 0, v_cmp_3250_);
v___x_3252_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3253_ = lean_box(1);
v___x_3254_ = l_List_forIn_x27_loop___redArg(v___x_3252_, v___f_3251_, v_l_3249_, v_r_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___boxed(lean_object* v_00_u03b1_3255_, lean_object* v_00_u03b2_3256_, lean_object* v_l_3257_, lean_object* v_cmp_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Std_ExtDTreeMap_ofList(v_00_u03b1_3255_, v_00_u03b2_3256_, v_l_3257_, v_cmp_3258_);
lean_dec(v_l_3257_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___redArg___lam__0(lean_object* v_l_3260_, lean_object* v_k_3261_, lean_object* v_v_3262_){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3263_, 0, v_k_3261_);
lean_ctor_set(v___x_3263_, 1, v_v_3262_);
v___x_3264_ = lean_array_push(v_l_3260_, v___x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___redArg(lean_object* v_t_3266_){
_start:
{
lean_object* v___f_3267_; lean_object* v___y_3269_; 
v___f_3267_ = ((lean_object*)(l_Std_ExtDTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3266_) == 0)
{
lean_object* v_size_3272_; 
v_size_3272_ = lean_ctor_get(v_t_3266_, 0);
lean_inc(v_size_3272_);
v___y_3269_ = v_size_3272_;
goto v___jp_3268_;
}
else
{
lean_object* v___x_3273_; 
v___x_3273_ = lean_unsigned_to_nat(0u);
v___y_3269_ = v___x_3273_;
goto v___jp_3268_;
}
v___jp_3268_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = lean_mk_empty_array_with_capacity(v___y_3269_);
lean_dec(v___y_3269_);
v___x_3271_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3267_, v___x_3270_, v_t_3266_);
return v___x_3271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray(lean_object* v_00_u03b1_3274_, lean_object* v_00_u03b2_3275_, lean_object* v_cmp_3276_, lean_object* v_inst_3277_, lean_object* v_t_3278_){
_start:
{
lean_object* v___f_3279_; lean_object* v___y_3281_; 
v___f_3279_ = ((lean_object*)(l_Std_ExtDTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3278_) == 0)
{
lean_object* v_size_3284_; 
v_size_3284_ = lean_ctor_get(v_t_3278_, 0);
lean_inc(v_size_3284_);
v___y_3281_ = v_size_3284_;
goto v___jp_3280_;
}
else
{
lean_object* v___x_3285_; 
v___x_3285_ = lean_unsigned_to_nat(0u);
v___y_3281_ = v___x_3285_;
goto v___jp_3280_;
}
v___jp_3280_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = lean_mk_empty_array_with_capacity(v___y_3281_);
lean_dec(v___y_3281_);
v___x_3283_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3279_, v___x_3282_, v_t_3278_);
return v___x_3283_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___boxed(lean_object* v_00_u03b1_3286_, lean_object* v_00_u03b2_3287_, lean_object* v_cmp_3288_, lean_object* v_inst_3289_, lean_object* v_t_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Std_ExtDTreeMap_toArray(v_00_u03b1_3286_, v_00_u03b2_3287_, v_cmp_3288_, v_inst_3289_, v_t_3290_);
lean_dec_ref(v_cmp_3288_);
return v_res_3291_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray___redArg(lean_object* v_a_3293_, lean_object* v_cmp_3294_){
_start:
{
lean_object* v___f_3295_; lean_object* v___x_3296_; lean_object* v_r_3297_; size_t v_sz_3298_; size_t v___x_3299_; lean_object* v___x_3300_; 
v___f_3295_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3295_, 0, v_cmp_3294_);
v___x_3296_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3297_ = lean_box(1);
v_sz_3298_ = lean_array_size(v_a_3293_);
v___x_3299_ = ((size_t)0ULL);
v___x_3300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3296_, v_a_3293_, v___f_3295_, v_sz_3298_, v___x_3299_, v_r_3297_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray(lean_object* v_00_u03b1_3301_, lean_object* v_00_u03b2_3302_, lean_object* v_a_3303_, lean_object* v_cmp_3304_){
_start:
{
lean_object* v___f_3305_; lean_object* v___x_3306_; lean_object* v_r_3307_; size_t v_sz_3308_; size_t v___x_3309_; lean_object* v___x_3310_; 
v___f_3305_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3305_, 0, v_cmp_3304_);
v___x_3306_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3307_ = lean_box(1);
v_sz_3308_ = lean_array_size(v_a_3303_);
v___x_3309_ = ((size_t)0ULL);
v___x_3310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3306_, v_a_3303_, v___f_3305_, v_sz_3308_, v___x_3309_, v_r_3307_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_modify___redArg(lean_object* v_cmp_3311_, lean_object* v_t_3312_, lean_object* v_a_3313_, lean_object* v_f_3314_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3311_, v_a_3313_, v_f_3314_, v_t_3312_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_modify(lean_object* v_00_u03b1_3316_, lean_object* v_00_u03b2_3317_, lean_object* v_cmp_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_t_3321_, lean_object* v_a_3322_, lean_object* v_f_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3318_, v_a_3322_, v_f_3323_, v_t_3321_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_alter___redArg(lean_object* v_cmp_3325_, lean_object* v_t_3326_, lean_object* v_a_3327_, lean_object* v_f_3328_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3325_, v_a_3327_, v_f_3328_, v_t_3326_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_alter(lean_object* v_00_u03b1_3330_, lean_object* v_00_u03b2_3331_, lean_object* v_cmp_3332_, lean_object* v_inst_3333_, lean_object* v_inst_3334_, lean_object* v_t_3335_, lean_object* v_a_3336_, lean_object* v_f_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3332_, v_a_3336_, v_f_3337_, v_t_3335_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_3339_, lean_object* v_mergeFn_3340_, lean_object* v_a_3341_, lean_object* v_x_3342_){
_start:
{
if (lean_obj_tag(v_x_3342_) == 0)
{
lean_object* v___x_3343_; 
lean_dec(v_a_3341_);
lean_dec(v_mergeFn_3340_);
v___x_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3343_, 0, v_b_u2082_3339_);
return v___x_3343_;
}
else
{
lean_object* v_val_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3352_; 
v_val_3344_ = lean_ctor_get(v_x_3342_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_x_3342_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3346_ = v_x_3342_;
v_isShared_3347_ = v_isSharedCheck_3352_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_val_3344_);
lean_dec(v_x_3342_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3352_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3348_ = lean_apply_3(v_mergeFn_3340_, v_a_3341_, v_val_3344_, v_b_u2082_3339_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3348_);
v___x_3350_ = v___x_3346_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3348_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3353_, lean_object* v_cmp_3354_, lean_object* v_t_3355_, lean_object* v_a_3356_, lean_object* v_b_u2082_3357_){
_start:
{
lean_object* v___f_3358_; lean_object* v___x_3359_; 
lean_inc(v_a_3356_);
v___f_3358_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3358_, 0, v_b_u2082_3357_);
lean_closure_set(v___f_3358_, 1, v_mergeFn_3353_);
lean_closure_set(v___f_3358_, 2, v_a_3356_);
v___x_3359_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3354_, v_a_3356_, v___f_3358_, v_t_3355_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg(lean_object* v_cmp_3360_, lean_object* v_mergeFn_3361_, lean_object* v_t_u2081_3362_, lean_object* v_t_u2082_3363_){
_start:
{
lean_object* v___f_3364_; lean_object* v___x_3365_; 
v___f_3364_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3364_, 0, v_mergeFn_3361_);
lean_closure_set(v___f_3364_, 1, v_cmp_3360_);
v___x_3365_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3364_, v_t_u2081_3362_, v_t_u2082_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith(lean_object* v_00_u03b1_3366_, lean_object* v_00_u03b2_3367_, lean_object* v_cmp_3368_, lean_object* v_inst_3369_, lean_object* v_inst_3370_, lean_object* v_mergeFn_3371_, lean_object* v_t_u2081_3372_, lean_object* v_t_u2082_3373_){
_start:
{
lean_object* v___f_3374_; lean_object* v___x_3375_; 
v___f_3374_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3374_, 0, v_mergeFn_3371_);
lean_closure_set(v___f_3374_, 1, v_cmp_3368_);
v___x_3375_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3374_, v_t_u2081_3372_, v_t_u2082_3373_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___redArg___lam__0(lean_object* v_x1_3376_, lean_object* v_x2_3377_, lean_object* v_x3_3378_){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3379_, 0, v_x1_3376_);
lean_ctor_set(v___x_3379_, 1, v_x2_3377_);
v___x_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
lean_ctor_set(v___x_3380_, 1, v_x3_3378_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___redArg(lean_object* v_t_3382_){
_start:
{
lean_object* v___f_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___f_3383_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toList___redArg___closed__0));
v___x_3384_ = lean_box(0);
v___x_3385_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3386_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3385_, v___f_3383_, v___x_3384_, v_t_3382_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList(lean_object* v_00_u03b1_3387_, lean_object* v_cmp_3388_, lean_object* v_00_u03b2_3389_, lean_object* v_inst_3390_, lean_object* v_t_3391_){
_start:
{
lean_object* v___f_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___f_3392_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toList___redArg___closed__0));
v___x_3393_ = lean_box(0);
v___x_3394_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3395_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3394_, v___f_3392_, v___x_3393_, v_t_3391_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___boxed(lean_object* v_00_u03b1_3396_, lean_object* v_cmp_3397_, lean_object* v_00_u03b2_3398_, lean_object* v_inst_3399_, lean_object* v_t_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Std_ExtDTreeMap_Const_toList(v_00_u03b1_3396_, v_cmp_3397_, v_00_u03b2_3398_, v_inst_3399_, v_t_3400_);
lean_dec_ref(v_cmp_3397_);
return v_res_3401_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0(lean_object* v_cmp_3403_, lean_object* v_a_3404_, lean_object* v_x_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_fst_3407_; lean_object* v_snd_3408_; lean_object* v_r_3409_; lean_object* v___x_3410_; 
v_fst_3407_ = lean_ctor_get(v_a_3404_, 0);
lean_inc(v_fst_3407_);
v_snd_3408_ = lean_ctor_get(v_a_3404_, 1);
lean_inc(v_snd_3408_);
lean_dec_ref(v_a_3404_);
v_r_3409_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3403_, v_fst_3407_, v_snd_3408_, v___y_3406_);
v___x_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3410_, 0, v_r_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg(lean_object* v_l_3411_, lean_object* v_cmp_3412_){
_start:
{
lean_object* v___f_3413_; lean_object* v___x_3414_; lean_object* v_r_3415_; lean_object* v___x_3416_; 
v___f_3413_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3413_, 0, v_cmp_3412_);
v___x_3414_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3415_ = lean_box(1);
v___x_3416_ = l_List_forIn_x27_loop___redArg(v___x_3414_, v___f_3413_, v_l_3411_, v_r_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg___boxed(lean_object* v_l_3417_, lean_object* v_cmp_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Std_ExtDTreeMap_Const_ofList___redArg(v_l_3417_, v_cmp_3418_);
lean_dec(v_l_3417_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList(lean_object* v_00_u03b1_3420_, lean_object* v_00_u03b2_3421_, lean_object* v_l_3422_, lean_object* v_cmp_3423_){
_start:
{
lean_object* v___f_3424_; lean_object* v___x_3425_; lean_object* v_r_3426_; lean_object* v___x_3427_; 
v___f_3424_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3424_, 0, v_cmp_3423_);
v___x_3425_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3426_ = lean_box(1);
v___x_3427_ = l_List_forIn_x27_loop___redArg(v___x_3425_, v___f_3424_, v_l_3422_, v_r_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___boxed(lean_object* v_00_u03b1_3428_, lean_object* v_00_u03b2_3429_, lean_object* v_l_3430_, lean_object* v_cmp_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Std_ExtDTreeMap_Const_ofList(v_00_u03b1_3428_, v_00_u03b2_3429_, v_l_3430_, v_cmp_3431_);
lean_dec(v_l_3430_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg___lam__0(lean_object* v_acc_3433_, lean_object* v_k_3434_, lean_object* v_v_3435_){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v_k_3434_);
lean_ctor_set(v___x_3436_, 1, v_v_3435_);
v___x_3437_ = lean_array_push(v_acc_3433_, v___x_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg(lean_object* v_t_3441_){
_start:
{
lean_object* v___f_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___f_3442_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0));
v___x_3443_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1));
v___x_3444_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3442_, v___x_3443_, v_t_3441_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray(lean_object* v_00_u03b1_3445_, lean_object* v_cmp_3446_, lean_object* v_00_u03b2_3447_, lean_object* v_inst_3448_, lean_object* v_t_3449_){
_start:
{
lean_object* v___f_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___f_3450_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0));
v___x_3451_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1));
v___x_3452_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3450_, v___x_3451_, v_t_3449_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___boxed(lean_object* v_00_u03b1_3453_, lean_object* v_cmp_3454_, lean_object* v_00_u03b2_3455_, lean_object* v_inst_3456_, lean_object* v_t_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Std_ExtDTreeMap_Const_toArray(v_00_u03b1_3453_, v_cmp_3454_, v_00_u03b2_3455_, v_inst_3456_, v_t_3457_);
lean_dec_ref(v_cmp_3454_);
return v_res_3458_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3459_; 
v___x_3459_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray___redArg(lean_object* v_a_3460_, lean_object* v_cmp_3461_){
_start:
{
lean_object* v___f_3462_; lean_object* v___x_3463_; lean_object* v_r_3464_; size_t v_sz_3465_; size_t v___x_3466_; lean_object* v___x_3467_; 
v___f_3462_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3462_, 0, v_cmp_3461_);
v___x_3463_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3464_ = lean_box(1);
v_sz_3465_ = lean_array_size(v_a_3460_);
v___x_3466_ = ((size_t)0ULL);
v___x_3467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3463_, v_a_3460_, v___f_3462_, v_sz_3465_, v___x_3466_, v_r_3464_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray(lean_object* v_00_u03b1_3468_, lean_object* v_00_u03b2_3469_, lean_object* v_a_3470_, lean_object* v_cmp_3471_){
_start:
{
lean_object* v___f_3472_; lean_object* v___x_3473_; lean_object* v_r_3474_; size_t v_sz_3475_; size_t v___x_3476_; lean_object* v___x_3477_; 
v___f_3472_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3472_, 0, v_cmp_3471_);
v___x_3473_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3474_ = lean_box(1);
v_sz_3475_ = lean_array_size(v_a_3470_);
v___x_3476_ = ((size_t)0ULL);
v___x_3477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3473_, v_a_3470_, v___f_3472_, v_sz_3475_, v___x_3476_, v_r_3474_);
return v___x_3477_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_3479_, lean_object* v_a_3480_, lean_object* v_x_3481_, lean_object* v___y_3482_){
_start:
{
uint8_t v___x_3483_; 
lean_inc(v___y_3482_);
lean_inc(v_a_3480_);
lean_inc_ref(v_cmp_3479_);
v___x_3483_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3479_, v_a_3480_, v___y_3482_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3484_ = lean_box(0);
v___x_3485_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3479_, v_a_3480_, v___x_3484_, v___y_3482_);
v___x_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
return v___x_3486_;
}
else
{
lean_object* v___x_3487_; 
lean_dec(v_a_3480_);
lean_dec_ref(v_cmp_3479_);
v___x_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3487_, 0, v___y_3482_);
return v___x_3487_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg(lean_object* v_l_3488_, lean_object* v_cmp_3489_){
_start:
{
lean_object* v___f_3490_; lean_object* v___x_3491_; lean_object* v_r_3492_; lean_object* v___x_3493_; 
v___f_3490_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3490_, 0, v_cmp_3489_);
v___x_3491_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3492_ = lean_box(1);
v___x_3493_ = l_List_forIn_x27_loop___redArg(v___x_3491_, v___f_3490_, v_l_3488_, v_r_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg___boxed(lean_object* v_l_3494_, lean_object* v_cmp_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Std_ExtDTreeMap_Const_unitOfList___redArg(v_l_3494_, v_cmp_3495_);
lean_dec(v_l_3494_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList(lean_object* v_00_u03b1_3497_, lean_object* v_l_3498_, lean_object* v_cmp_3499_){
_start:
{
lean_object* v___f_3500_; lean_object* v___x_3501_; lean_object* v_r_3502_; lean_object* v___x_3503_; 
v___f_3500_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3500_, 0, v_cmp_3499_);
v___x_3501_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3502_ = lean_box(1);
v___x_3503_ = l_List_forIn_x27_loop___redArg(v___x_3501_, v___f_3500_, v_l_3498_, v_r_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___boxed(lean_object* v_00_u03b1_3504_, lean_object* v_l_3505_, lean_object* v_cmp_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Std_ExtDTreeMap_Const_unitOfList(v_00_u03b1_3504_, v_l_3505_, v_cmp_3506_);
lean_dec(v_l_3505_);
return v_res_3507_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray___redArg(lean_object* v_a_3509_, lean_object* v_cmp_3510_){
_start:
{
lean_object* v___f_3511_; lean_object* v___x_3512_; lean_object* v_r_3513_; size_t v_sz_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v___f_3511_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3511_, 0, v_cmp_3510_);
v___x_3512_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3513_ = lean_box(1);
v_sz_3514_ = lean_array_size(v_a_3509_);
v___x_3515_ = ((size_t)0ULL);
v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3512_, v_a_3509_, v___f_3511_, v_sz_3514_, v___x_3515_, v_r_3513_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray(lean_object* v_00_u03b1_3517_, lean_object* v_a_3518_, lean_object* v_cmp_3519_){
_start:
{
lean_object* v___f_3520_; lean_object* v___x_3521_; lean_object* v_r_3522_; size_t v_sz_3523_; size_t v___x_3524_; lean_object* v___x_3525_; 
v___f_3520_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3520_, 0, v_cmp_3519_);
v___x_3521_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3522_ = lean_box(1);
v_sz_3523_ = lean_array_size(v_a_3518_);
v___x_3524_ = ((size_t)0ULL);
v___x_3525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3521_, v_a_3518_, v___f_3520_, v_sz_3523_, v___x_3524_, v_r_3522_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_modify___redArg(lean_object* v_cmp_3526_, lean_object* v_t_3527_, lean_object* v_a_3528_, lean_object* v_f_3529_){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3526_, v_a_3528_, v_f_3529_, v_t_3527_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_modify(lean_object* v_00_u03b1_3531_, lean_object* v_cmp_3532_, lean_object* v_00_u03b2_3533_, lean_object* v_inst_3534_, lean_object* v_t_3535_, lean_object* v_a_3536_, lean_object* v_f_3537_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3532_, v_a_3536_, v_f_3537_, v_t_3535_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_alter___redArg(lean_object* v_cmp_3539_, lean_object* v_t_3540_, lean_object* v_a_3541_, lean_object* v_f_3542_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3539_, v_a_3541_, v_f_3542_, v_t_3540_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_alter(lean_object* v_00_u03b1_3544_, lean_object* v_cmp_3545_, lean_object* v_00_u03b2_3546_, lean_object* v_inst_3547_, lean_object* v_t_3548_, lean_object* v_a_3549_, lean_object* v_f_3550_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3545_, v_a_3549_, v_f_3550_, v_t_3548_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3552_, lean_object* v_cmp_3553_, lean_object* v_t_3554_, lean_object* v_a_3555_, lean_object* v_b_u2082_3556_){
_start:
{
lean_object* v___f_3557_; lean_object* v___x_3558_; 
lean_inc(v_a_3555_);
v___f_3557_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3557_, 0, v_b_u2082_3556_);
lean_closure_set(v___f_3557_, 1, v_mergeFn_3552_);
lean_closure_set(v___f_3557_, 2, v_a_3555_);
v___x_3558_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3553_, v_a_3555_, v___f_3557_, v_t_3554_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith___redArg(lean_object* v_cmp_3559_, lean_object* v_mergeFn_3560_, lean_object* v_t_u2081_3561_, lean_object* v_t_u2082_3562_){
_start:
{
lean_object* v___f_3563_; lean_object* v___x_3564_; 
v___f_3563_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3563_, 0, v_mergeFn_3560_);
lean_closure_set(v___f_3563_, 1, v_cmp_3559_);
v___x_3564_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3563_, v_t_u2081_3561_, v_t_u2082_3562_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith(lean_object* v_00_u03b1_3565_, lean_object* v_cmp_3566_, lean_object* v_00_u03b2_3567_, lean_object* v_inst_3568_, lean_object* v_mergeFn_3569_, lean_object* v_t_u2081_3570_, lean_object* v_t_u2082_3571_){
_start:
{
lean_object* v___f_3572_; lean_object* v___x_3573_; 
v___f_3572_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3572_, 0, v_mergeFn_3569_);
lean_closure_set(v___f_3572_, 1, v_cmp_3566_);
v___x_3573_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3572_, v_t_u2081_3570_, v_t_u2082_3571_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_3574_, lean_object* v_x_3575_, lean_object* v_____s_3576_){
_start:
{
lean_object* v_fst_3577_; lean_object* v_snd_3578_; lean_object* v_acc_3579_; lean_object* v___x_3580_; 
v_fst_3577_ = lean_ctor_get(v_x_3575_, 0);
lean_inc(v_fst_3577_);
v_snd_3578_ = lean_ctor_get(v_x_3575_, 1);
lean_inc(v_snd_3578_);
lean_dec_ref(v_x_3575_);
v_acc_3579_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3574_, v_fst_3577_, v_snd_3578_, v_____s_3576_);
v___x_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3580_, 0, v_acc_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany___redArg(lean_object* v_cmp_3581_, lean_object* v_inst_3582_, lean_object* v_t_3583_, lean_object* v_l_3584_){
_start:
{
lean_object* v___f_3585_; lean_object* v___x_3586_; 
v___f_3585_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3585_, 0, v_cmp_3581_);
v___x_3586_ = lean_apply_4(v_inst_3582_, lean_box(0), v_l_3584_, v_t_3583_, v___f_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany(lean_object* v_00_u03b1_3587_, lean_object* v_00_u03b2_3588_, lean_object* v_cmp_3589_, lean_object* v_inst_3590_, lean_object* v_00_u03c1_3591_, lean_object* v_inst_3592_, lean_object* v_t_3593_, lean_object* v_l_3594_){
_start:
{
lean_object* v___f_3595_; lean_object* v___x_3596_; 
v___f_3595_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3595_, 0, v_cmp_3589_);
v___x_3596_ = lean_apply_4(v_inst_3592_, lean_box(0), v_l_3594_, v_t_3593_, v___f_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_3597_, lean_object* v_a_3598_, lean_object* v_____s_3599_){
_start:
{
lean_object* v_acc_3600_; lean_object* v___x_3601_; 
v_acc_3600_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_3597_, v_a_3598_, v_____s_3599_);
v___x_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3601_, 0, v_acc_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany___redArg(lean_object* v_cmp_3602_, lean_object* v_inst_3603_, lean_object* v_t_3604_, lean_object* v_l_3605_){
_start:
{
lean_object* v___f_3606_; lean_object* v___x_3607_; 
v___f_3606_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3606_, 0, v_cmp_3602_);
v___x_3607_ = lean_apply_4(v_inst_3603_, lean_box(0), v_l_3605_, v_t_3604_, v___f_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany(lean_object* v_00_u03b1_3608_, lean_object* v_00_u03b2_3609_, lean_object* v_cmp_3610_, lean_object* v_inst_3611_, lean_object* v_00_u03c1_3612_, lean_object* v_inst_3613_, lean_object* v_t_3614_, lean_object* v_l_3615_){
_start:
{
lean_object* v___f_3616_; lean_object* v___x_3617_; 
v___f_3616_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3616_, 0, v_cmp_3610_);
v___x_3617_ = lean_apply_4(v_inst_3613_, lean_box(0), v_l_3615_, v_t_3614_, v___f_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0(lean_object* v_cmp_3618_, lean_object* v_x_3619_, lean_object* v_____s_3620_){
_start:
{
lean_object* v_fst_3621_; lean_object* v_snd_3622_; lean_object* v_acc_3623_; lean_object* v___x_3624_; 
v_fst_3621_ = lean_ctor_get(v_x_3619_, 0);
lean_inc(v_fst_3621_);
v_snd_3622_ = lean_ctor_get(v_x_3619_, 1);
lean_inc(v_snd_3622_);
lean_dec_ref(v_x_3619_);
v_acc_3623_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3618_, v_fst_3621_, v_snd_3622_, v_____s_3620_);
v___x_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3624_, 0, v_acc_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany___redArg(lean_object* v_cmp_3625_, lean_object* v_inst_3626_, lean_object* v_t_3627_, lean_object* v_l_3628_){
_start:
{
lean_object* v___f_3629_; lean_object* v___x_3630_; 
v___f_3629_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3629_, 0, v_cmp_3625_);
v___x_3630_ = lean_apply_4(v_inst_3626_, lean_box(0), v_l_3628_, v_t_3627_, v___f_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany(lean_object* v_00_u03b1_3631_, lean_object* v_cmp_3632_, lean_object* v_00_u03b2_3633_, lean_object* v_inst_3634_, lean_object* v_00_u03c1_3635_, lean_object* v_inst_3636_, lean_object* v_t_3637_, lean_object* v_l_3638_){
_start:
{
lean_object* v___f_3639_; lean_object* v___x_3640_; 
v___f_3639_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3639_, 0, v_cmp_3632_);
v___x_3640_ = lean_apply_4(v_inst_3636_, lean_box(0), v_l_3638_, v_t_3637_, v___f_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_3641_, lean_object* v_a_3642_, lean_object* v_____s_3643_){
_start:
{
uint8_t v___x_3644_; 
lean_inc(v_____s_3643_);
lean_inc(v_a_3642_);
lean_inc_ref(v_cmp_3641_);
v___x_3644_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3641_, v_a_3642_, v_____s_3643_);
if (v___x_3644_ == 0)
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3645_ = lean_box(0);
v___x_3646_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3641_, v_a_3642_, v___x_3645_, v_____s_3643_);
v___x_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
return v___x_3647_;
}
else
{
lean_object* v___x_3648_; 
lean_dec(v_a_3642_);
lean_dec_ref(v_cmp_3641_);
v___x_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3648_, 0, v_____s_3643_);
return v___x_3648_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_3649_, lean_object* v_inst_3650_, lean_object* v_t_3651_, lean_object* v_l_3652_){
_start:
{
lean_object* v___f_3653_; lean_object* v___x_3654_; 
v___f_3653_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3653_, 0, v_cmp_3649_);
v___x_3654_ = lean_apply_4(v_inst_3650_, lean_box(0), v_l_3652_, v_t_3651_, v___f_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_3655_, lean_object* v_cmp_3656_, lean_object* v_inst_3657_, lean_object* v_00_u03c1_3658_, lean_object* v_inst_3659_, lean_object* v_t_3660_, lean_object* v_l_3661_){
_start:
{
lean_object* v___f_3662_; lean_object* v___x_3663_; 
v___f_3662_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3662_, 0, v_cmp_3656_);
v___x_3663_ = lean_apply_4(v_inst_3659_, lean_box(0), v_l_3661_, v_t_3660_, v___f_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_union___redArg(lean_object* v_cmp_3664_, lean_object* v_m_u2081_3665_, lean_object* v_m_u2082_3666_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3664_, v_m_u2081_3665_, v_m_u2082_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_union(lean_object* v_00_u03b1_3668_, lean_object* v_00_u03b2_3669_, lean_object* v_cmp_3670_, lean_object* v_inst_3671_, lean_object* v_m_u2081_3672_, lean_object* v_m_u2082_3673_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3670_, v_m_u2081_3672_, v_m_u2082_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instUnionOfTransCmp___redArg(lean_object* v_cmp_3675_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_union), 6, 4);
lean_closure_set(v___x_3676_, 0, lean_box(0));
lean_closure_set(v___x_3676_, 1, lean_box(0));
lean_closure_set(v___x_3676_, 2, v_cmp_3675_);
lean_closure_set(v___x_3676_, 3, lean_box(0));
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instUnionOfTransCmp(lean_object* v_00_u03b1_3677_, lean_object* v_00_u03b2_3678_, lean_object* v_cmp_3679_, lean_object* v_inst_3680_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_union), 6, 4);
lean_closure_set(v___x_3681_, 0, lean_box(0));
lean_closure_set(v___x_3681_, 1, lean_box(0));
lean_closure_set(v___x_3681_, 2, v_cmp_3679_);
lean_closure_set(v___x_3681_, 3, lean_box(0));
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_inter___redArg(lean_object* v_cmp_3682_, lean_object* v_m_u2081_3683_, lean_object* v_m_u2082_3684_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3682_, v_m_u2081_3683_, v_m_u2082_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_inter(lean_object* v_00_u03b1_3686_, lean_object* v_00_u03b2_3687_, lean_object* v_cmp_3688_, lean_object* v_inst_3689_, lean_object* v_m_u2081_3690_, lean_object* v_m_u2082_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3688_, v_m_u2081_3690_, v_m_u2082_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInterOfTransCmp___redArg(lean_object* v_cmp_3693_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_inter), 6, 4);
lean_closure_set(v___x_3694_, 0, lean_box(0));
lean_closure_set(v___x_3694_, 1, lean_box(0));
lean_closure_set(v___x_3694_, 2, v_cmp_3693_);
lean_closure_set(v___x_3694_, 3, lean_box(0));
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInterOfTransCmp(lean_object* v_00_u03b1_3695_, lean_object* v_00_u03b2_3696_, lean_object* v_cmp_3697_, lean_object* v_inst_3698_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_inter), 6, 4);
lean_closure_set(v___x_3699_, 0, lean_box(0));
lean_closure_set(v___x_3699_, 1, lean_box(0));
lean_closure_set(v___x_3699_, 2, v_cmp_3697_);
lean_closure_set(v___x_3699_, 3, lean_box(0));
return v___x_3699_;
}
}
uint8_t l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(lean_object* v_cmp_3700_, lean_object* v_inst_3701_, lean_object* v_x_3702_, lean_object* v_y_3703_){
_start:
{
uint8_t v___x_3704_; 
v___x_3704_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3700_, v_inst_3701_, v_x_3702_, v_y_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3700_ = stack[0].m_obj;
lean_object* v_inst_3701_ = stack[1].m_obj;
lean_object* v_x_3702_ = stack[2].m_obj;
lean_object* v_y_3703_ = stack[3].m_obj;
uint8_t v_res_3705_;
v_res_3705_ = l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(v_cmp_3700_, v_inst_3701_, v_x_3702_, v_y_3703_);
stack->m_num = v_res_3705_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_3706_, lean_object* v_inst_3707_, lean_object* v_x_3708_, lean_object* v_y_3709_){
_start:
{
uint8_t v_res_3710_; lean_object* v_r_3711_; 
v_res_3710_ = l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(v_cmp_3706_, v_inst_3707_, v_x_3708_, v_y_3709_);
v_r_3711_ = lean_box(v_res_3710_);
return v_r_3711_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(lean_object* v_cmp_3712_, lean_object* v_inst_3713_){
_start:
{
lean_object* v___f_3714_; lean_object* v___x_3715_; 
lean_inc_ref(v_cmp_3712_);
v___f_3714_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3714_, 0, v_cmp_3712_);
lean_closure_set(v___f_3714_, 1, v_inst_3713_);
v___x_3715_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_lift_u2082___boxed), 8, 6);
lean_closure_set(v___x_3715_, 0, lean_box(0));
lean_closure_set(v___x_3715_, 1, lean_box(0));
lean_closure_set(v___x_3715_, 2, v_cmp_3712_);
lean_closure_set(v___x_3715_, 3, lean_box(0));
lean_closure_set(v___x_3715_, 4, v___f_3714_);
lean_closure_set(v___x_3715_, 5, lean_box(0));
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp(lean_object* v_00_u03b1_3716_, lean_object* v_00_u03b2_3717_, lean_object* v_cmp_3718_, lean_object* v_inst_3719_, lean_object* v_inst_3720_, lean_object* v_inst_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_3718_, v_inst_3721_);
return v___x_3722_;
}
}
uint8_t l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object* v_cmp_3723_, lean_object* v_inst_3724_, lean_object* v_x_3725_, lean_object* v_x_3726_){
_start:
{
uint8_t v___x_3727_; 
v___x_3727_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3723_, v_inst_3724_, v_x_3725_, v_x_3726_);
return v___x_3727_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3723_ = stack[0].m_obj;
lean_object* v_inst_3724_ = stack[1].m_obj;
lean_object* v_x_3725_ = stack[2].m_obj;
lean_object* v_x_3726_ = stack[3].m_obj;
uint8_t v_res_3728_;
v_res_3728_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(v_cmp_3723_, v_inst_3724_, v_x_3725_, v_x_3726_);
stack->m_num = v_res_3728_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_3729_, lean_object* v_inst_3730_, lean_object* v_x_3731_, lean_object* v_x_3732_){
_start:
{
uint8_t v_res_3733_; lean_object* v_r_3734_; 
v_res_3733_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(v_cmp_3729_, v_inst_3730_, v_x_3731_, v_x_3732_);
v_r_3734_ = lean_box(v_res_3733_);
return v_r_3734_;
}
}
uint8_t l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object* v_00_u03b1_3735_, lean_object* v_00_u03b2_3736_, lean_object* v_cmp_3737_, lean_object* v_inst_3738_, lean_object* v_inst_3739_, lean_object* v_inst_3740_, lean_object* v_inst_3741_, lean_object* v_x_3742_, lean_object* v_x_3743_){
_start:
{
uint8_t v___x_3744_; 
v___x_3744_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3737_, v_inst_3740_, v_x_3742_, v_x_3743_);
return v___x_3744_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3737_ = stack[2].m_obj;
lean_object* v_inst_3740_ = stack[5].m_obj;
lean_object* v_x_3742_ = stack[7].m_obj;
lean_object* v_x_3743_ = stack[8].m_obj;
uint8_t v_res_3745_;
v_res_3745_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_box(0), lean_box(0), v_cmp_3737_, lean_box(0), lean_box(0), v_inst_3740_, lean_box(0), v_x_3742_, v_x_3743_);
stack->m_num = v_res_3745_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_3746_, lean_object* v_00_u03b2_3747_, lean_object* v_cmp_3748_, lean_object* v_inst_3749_, lean_object* v_inst_3750_, lean_object* v_inst_3751_, lean_object* v_inst_3752_, lean_object* v_x_3753_, lean_object* v_x_3754_){
_start:
{
uint8_t v_res_3755_; lean_object* v_r_3756_; 
v_res_3755_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(v_00_u03b1_3746_, v_00_u03b2_3747_, v_cmp_3748_, v_inst_3749_, v_inst_3750_, v_inst_3751_, v_inst_3752_, v_x_3753_, v_x_3754_);
v_r_3756_ = lean_box(v_res_3755_);
return v_r_3756_;
}
}
uint8_t l_Std_ExtDTreeMap_Const_beq___redArg(lean_object* v_cmp_3757_, lean_object* v_inst_3758_, lean_object* v_m_u2081_3759_, lean_object* v_m_u2082_3760_){
_start:
{
uint8_t v___x_3761_; 
v___x_3761_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3757_, v_inst_3758_, v_m_u2081_3759_, v_m_u2082_3760_);
return v___x_3761_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_Const_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3757_ = stack[0].m_obj;
lean_object* v_inst_3758_ = stack[1].m_obj;
lean_object* v_m_u2081_3759_ = stack[2].m_obj;
lean_object* v_m_u2082_3760_ = stack[3].m_obj;
uint8_t v_res_3762_;
v_res_3762_ = l_Std_ExtDTreeMap_Const_beq___redArg(v_cmp_3757_, v_inst_3758_, v_m_u2081_3759_, v_m_u2082_3760_);
stack->m_num = v_res_3762_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_beq___redArg___boxed(lean_object* v_cmp_3763_, lean_object* v_inst_3764_, lean_object* v_m_u2081_3765_, lean_object* v_m_u2082_3766_){
_start:
{
uint8_t v_res_3767_; lean_object* v_r_3768_; 
v_res_3767_ = l_Std_ExtDTreeMap_Const_beq___redArg(v_cmp_3763_, v_inst_3764_, v_m_u2081_3765_, v_m_u2082_3766_);
v_r_3768_ = lean_box(v_res_3767_);
return v_r_3768_;
}
}
uint8_t l_Std_ExtDTreeMap_Const_beq(lean_object* v_00_u03b1_3769_, lean_object* v_cmp_3770_, lean_object* v_00_u03b2_3771_, lean_object* v_inst_3772_, lean_object* v_inst_3773_, lean_object* v_m_u2081_3774_, lean_object* v_m_u2082_3775_){
_start:
{
uint8_t v___x_3776_; 
v___x_3776_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3770_, v_inst_3773_, v_m_u2081_3774_, v_m_u2082_3775_);
return v___x_3776_;
}
}
LEAN_EXPORT void l_Std_ExtDTreeMap_Const_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3770_ = stack[1].m_obj;
lean_object* v_inst_3773_ = stack[4].m_obj;
lean_object* v_m_u2081_3774_ = stack[5].m_obj;
lean_object* v_m_u2082_3775_ = stack[6].m_obj;
uint8_t v_res_3777_;
v_res_3777_ = l_Std_ExtDTreeMap_Const_beq(lean_box(0), v_cmp_3770_, lean_box(0), lean_box(0), v_inst_3773_, v_m_u2081_3774_, v_m_u2082_3775_);
stack->m_num = v_res_3777_;
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_beq___boxed(lean_object* v_00_u03b1_3778_, lean_object* v_cmp_3779_, lean_object* v_00_u03b2_3780_, lean_object* v_inst_3781_, lean_object* v_inst_3782_, lean_object* v_m_u2081_3783_, lean_object* v_m_u2082_3784_){
_start:
{
uint8_t v_res_3785_; lean_object* v_r_3786_; 
v_res_3785_ = l_Std_ExtDTreeMap_Const_beq(v_00_u03b1_3778_, v_cmp_3779_, v_00_u03b2_3780_, v_inst_3781_, v_inst_3782_, v_m_u2081_3783_, v_m_u2082_3784_);
v_r_3786_ = lean_box(v_res_3785_);
return v_r_3786_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_diff___redArg(lean_object* v_cmp_3787_, lean_object* v_m_u2081_3788_, lean_object* v_m_u2082_3789_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_3787_, v_m_u2081_3788_, v_m_u2082_3789_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_diff(lean_object* v_00_u03b1_3791_, lean_object* v_00_u03b2_3792_, lean_object* v_cmp_3793_, lean_object* v_inst_3794_, lean_object* v_m_u2081_3795_, lean_object* v_m_u2082_3796_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_3793_, v_m_u2081_3795_, v_m_u2082_3796_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSDiffOfTransCmp___redArg(lean_object* v_cmp_3798_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_diff), 6, 4);
lean_closure_set(v___x_3799_, 0, lean_box(0));
lean_closure_set(v___x_3799_, 1, lean_box(0));
lean_closure_set(v___x_3799_, 2, v_cmp_3798_);
lean_closure_set(v___x_3799_, 3, lean_box(0));
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSDiffOfTransCmp(lean_object* v_00_u03b1_3800_, lean_object* v_00_u03b2_3801_, lean_object* v_cmp_3802_, lean_object* v_inst_3803_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_diff), 6, 4);
lean_closure_set(v___x_3804_, 0, lean_box(0));
lean_closure_set(v___x_3804_, 1, lean_box(0));
lean_closure_set(v___x_3804_, 2, v_cmp_3802_);
lean_closure_set(v___x_3804_, 3, lean_box(0));
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_3808_, lean_object* v___x_3809_, lean_object* v_m_3810_, lean_object* v_prec_3811_){
_start:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3812_ = ((lean_object*)(l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_3813_ = lean_box(0);
v___x_3814_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3815_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3814_, v___f_3808_, v___x_3813_, v_m_3810_);
v___x_3816_ = l_List_repr___redArg(v___x_3809_, v___x_3815_);
v___x_3817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3812_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = l_Repr_addAppParen(v___x_3817_, v_prec_3811_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_3819_, lean_object* v___x_3820_, lean_object* v_m_3821_, lean_object* v_prec_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(v___f_3819_, v___x_3820_, v_m_3821_, v_prec_3822_);
lean_dec(v_prec_3822_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(lean_object* v_inst_3824_, lean_object* v_inst_3825_){
_start:
{
lean_object* v___f_3826_; lean_object* v___x_3827_; lean_object* v___f_3828_; 
v___f_3826_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3827_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_3827_, 0, lean_box(0));
lean_closure_set(v___x_3827_, 1, lean_box(0));
lean_closure_set(v___x_3827_, 2, v_inst_3824_);
lean_closure_set(v___x_3827_, 3, v_inst_3825_);
v___f_3828_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3828_, 0, v___f_3826_);
lean_closure_set(v___f_3828_, 1, v___x_3827_);
return v___f_3828_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp(lean_object* v_00_u03b1_3829_, lean_object* v_00_u03b2_3830_, lean_object* v_cmp_3831_, lean_object* v_inst_3832_, lean_object* v_inst_3833_, lean_object* v_inst_3834_){
_start:
{
lean_object* v___x_3835_; 
v___x_3835_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(v_inst_3833_, v_inst_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_3836_, lean_object* v_00_u03b2_3837_, lean_object* v_cmp_3838_, lean_object* v_inst_3839_, lean_object* v_inst_3840_, lean_object* v_inst_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l_Std_ExtDTreeMap_instReprOfTransCmp(v_00_u03b1_3836_, v_00_u03b2_3837_, v_cmp_3838_, v_inst_3839_, v_inst_3840_, v_inst_3841_);
lean_dec_ref(v_cmp_3838_);
return v_res_3842_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ExtDTreeMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DTreeMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_ExtDTreeMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_ExtDTreeMap___auto__1 = _init_l_Std_ExtDTreeMap___auto__1();
lean_mark_persistent(l_Std_ExtDTreeMap___auto__1);
l_Std_ExtDTreeMap_ofList___auto__1 = _init_l_Std_ExtDTreeMap_ofList___auto__1();
lean_mark_persistent(l_Std_ExtDTreeMap_ofList___auto__1);
l_Std_ExtDTreeMap_ofArray___auto__1 = _init_l_Std_ExtDTreeMap_ofArray___auto__1();
lean_mark_persistent(l_Std_ExtDTreeMap_ofArray___auto__1);
l_Std_ExtDTreeMap_Const_ofList___auto__1 = _init_l_Std_ExtDTreeMap_Const_ofList___auto__1();
lean_mark_persistent(l_Std_ExtDTreeMap_Const_ofList___auto__1);
l_Std_ExtDTreeMap_Const_ofArray___auto__1 = _init_l_Std_ExtDTreeMap_Const_ofArray___auto__1();
lean_mark_persistent(l_Std_ExtDTreeMap_Const_ofArray___auto__1);
l_Std_ExtDTreeMap_Const_unitOfList___auto__1 = _init_l_Std_ExtDTreeMap_Const_unitOfList___auto__1();
lean_mark_persistent(l_Std_ExtDTreeMap_Const_unitOfList___auto__1);
l_Std_ExtDTreeMap_Const_unitOfArray___auto__1 = _init_l_Std_ExtDTreeMap_Const_unitOfArray___auto__1();
lean_mark_persistent(l_Std_ExtDTreeMap_Const_unitOfArray___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_ExtDTreeMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_ExtDTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_ExtDTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_ExtDTreeMap_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
