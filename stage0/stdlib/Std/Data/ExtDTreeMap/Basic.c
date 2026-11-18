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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall___redArg(){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall___redArg___boxed(lean_object* v___dummy_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_ExtDTreeMap_instCoeTypeForall___redArg();
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall(lean_object* v_00_u03b1_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty___redArg(){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(1);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty___redArg___boxed(lean_object* v___dummy_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_ExtDTreeMap_empty___redArg();
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty(lean_object* v_00_u03b1_177_, lean_object* v_00_u03b2_178_, lean_object* v_cmp_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_box(1);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty___boxed(lean_object* v_00_u03b1_181_, lean_object* v_00_u03b2_182_, lean_object* v_cmp_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_ExtDTreeMap_empty(v_00_u03b1_181_, v_00_u03b2_182_, v_cmp_183_);
lean_dec_ref(v_cmp_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(1);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_ExtDTreeMap_instEmptyCollection___redArg();
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection(lean_object* v_00_u03b1_189_, lean_object* v_00_u03b2_190_, lean_object* v_cmp_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_box(1);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_193_, lean_object* v_00_u03b2_194_, lean_object* v_cmp_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_ExtDTreeMap_instEmptyCollection(v_00_u03b1_193_, v_00_u03b2_194_, v_cmp_195_);
lean_dec_ref(v_cmp_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_box(1);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited___redArg___boxed(lean_object* v___dummy_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_ExtDTreeMap_instInhabited___redArg();
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited(lean_object* v_00_u03b1_201_, lean_object* v_00_u03b2_202_, lean_object* v_cmp_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(1);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited___boxed(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_cmp_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_ExtDTreeMap_instInhabited(v_00_u03b1_205_, v_00_u03b2_206_, v_cmp_207_);
lean_dec_ref(v_cmp_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insert___redArg(lean_object* v_cmp_209_, lean_object* v_t_210_, lean_object* v_a_211_, lean_object* v_b_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_209_, v_a_211_, v_b_212_, v_t_210_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insert(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_cmp_216_, lean_object* v_inst_217_, lean_object* v_t_218_, lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_216_, v_a_219_, v_b_220_, v_t_218_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0(lean_object* v_cmp_222_, lean_object* v_e_223_){
_start:
{
lean_object* v_fst_224_; lean_object* v_snd_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_fst_224_ = lean_ctor_get(v_e_223_, 0);
lean_inc(v_fst_224_);
v_snd_225_ = lean_ctor_get(v_e_223_, 1);
lean_inc(v_snd_225_);
lean_dec_ref(v_e_223_);
v___x_226_ = lean_box(1);
v___x_227_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_222_, v_fst_224_, v_snd_225_, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg(lean_object* v_cmp_228_){
_start:
{
lean_object* v___f_229_; 
v___f_229_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_229_, 0, v_cmp_228_);
return v___f_229_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp(lean_object* v_00_u03b1_230_, lean_object* v_00_u03b2_231_, lean_object* v_cmp_232_, lean_object* v_inst_233_){
_start:
{
lean_object* v___f_234_; 
v___f_234_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_234_, 0, v_cmp_232_);
return v___f_234_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0(lean_object* v_cmp_235_, lean_object* v_e_236_, lean_object* v_s_237_){
_start:
{
lean_object* v_fst_238_; lean_object* v_snd_239_; lean_object* v___x_240_; 
v_fst_238_ = lean_ctor_get(v_e_236_, 0);
lean_inc(v_fst_238_);
v_snd_239_ = lean_ctor_get(v_e_236_, 1);
lean_inc(v_snd_239_);
lean_dec_ref(v_e_236_);
v___x_240_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_235_, v_fst_238_, v_snd_239_, v_s_237_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg(lean_object* v_cmp_241_){
_start:
{
lean_object* v___f_242_; 
v___f_242_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_242_, 0, v_cmp_241_);
return v___f_242_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp(lean_object* v_00_u03b1_243_, lean_object* v_00_u03b2_244_, lean_object* v_cmp_245_, lean_object* v_inst_246_){
_start:
{
lean_object* v___f_247_; 
v___f_247_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_247_, 0, v_cmp_245_);
return v___f_247_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertIfNew___redArg(lean_object* v_cmp_248_, lean_object* v_t_249_, lean_object* v_a_250_, lean_object* v_b_251_){
_start:
{
uint8_t v___x_252_; 
lean_inc(v_t_249_);
lean_inc(v_a_250_);
lean_inc_ref(v_cmp_248_);
v___x_252_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_248_, v_a_250_, v_t_249_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
v___x_253_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_248_, v_a_250_, v_b_251_, v_t_249_);
return v___x_253_;
}
else
{
lean_dec(v_b_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_cmp_248_);
return v_t_249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertIfNew(lean_object* v_00_u03b1_254_, lean_object* v_00_u03b2_255_, lean_object* v_cmp_256_, lean_object* v_inst_257_, lean_object* v_t_258_, lean_object* v_a_259_, lean_object* v_b_260_){
_start:
{
uint8_t v___x_261_; 
lean_inc(v_t_258_);
lean_inc(v_a_259_);
lean_inc_ref(v_cmp_256_);
v___x_261_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_256_, v_a_259_, v_t_258_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
v___x_262_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_256_, v_a_259_, v_b_260_, v_t_258_);
return v___x_262_;
}
else
{
lean_dec(v_b_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_cmp_256_);
return v_t_258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsert___redArg(lean_object* v_cmp_263_, lean_object* v_t_264_, lean_object* v_a_265_, lean_object* v_b_266_){
_start:
{
lean_object* v_sz_267_; lean_object* v_m_268_; lean_object* v___y_270_; 
v_sz_267_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_264_);
v_m_268_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_263_, v_a_265_, v_b_266_, v_t_264_);
if (lean_obj_tag(v_m_268_) == 0)
{
lean_object* v_size_274_; 
v_size_274_ = lean_ctor_get(v_m_268_, 0);
lean_inc(v_size_274_);
v___y_270_ = v_size_274_;
goto v___jp_269_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_unsigned_to_nat(0u);
v___y_270_ = v___x_275_;
goto v___jp_269_;
}
v___jp_269_:
{
uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_nat_dec_eq(v_sz_267_, v___y_270_);
lean_dec(v___y_270_);
lean_dec(v_sz_267_);
v___x_272_ = lean_box(v___x_271_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_m_268_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsert(lean_object* v_00_u03b1_276_, lean_object* v_00_u03b2_277_, lean_object* v_cmp_278_, lean_object* v_inst_279_, lean_object* v_t_280_, lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
lean_object* v_sz_283_; lean_object* v_m_284_; lean_object* v___y_286_; 
v_sz_283_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_280_);
v_m_284_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_278_, v_a_281_, v_b_282_, v_t_280_);
if (lean_obj_tag(v_m_284_) == 0)
{
lean_object* v_size_290_; 
v_size_290_ = lean_ctor_get(v_m_284_, 0);
lean_inc(v_size_290_);
v___y_286_ = v_size_290_;
goto v___jp_285_;
}
else
{
lean_object* v___x_291_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___y_286_ = v___x_291_;
goto v___jp_285_;
}
v___jp_285_:
{
uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_nat_dec_eq(v_sz_283_, v___y_286_);
lean_dec(v___y_286_);
lean_dec(v_sz_283_);
v___x_288_ = lean_box(v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v_m_284_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_292_, lean_object* v_t_293_, lean_object* v_a_294_, lean_object* v_b_295_){
_start:
{
uint8_t v___x_296_; 
lean_inc(v_t_293_);
lean_inc(v_a_294_);
lean_inc_ref(v_cmp_292_);
v___x_296_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_292_, v_a_294_, v_t_293_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_292_, v_a_294_, v_b_295_, v_t_293_);
v___x_298_ = lean_box(v___x_296_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_b_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_cmp_292_);
v___x_300_ = lean_box(v___x_296_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_t_293_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_302_, lean_object* v_00_u03b2_303_, lean_object* v_cmp_304_, lean_object* v_inst_305_, lean_object* v_t_306_, lean_object* v_a_307_, lean_object* v_b_308_){
_start:
{
uint8_t v___x_309_; 
lean_inc(v_t_306_);
lean_inc(v_a_307_);
lean_inc_ref(v_cmp_304_);
v___x_309_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_304_, v_a_307_, v_t_306_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_304_, v_a_307_, v_b_308_, v_t_306_);
v___x_311_ = lean_box(v___x_309_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v___x_310_);
return v___x_312_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v_b_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_cmp_304_);
v___x_313_ = lean_box(v___x_309_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v_t_306_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_315_, lean_object* v_t_316_, lean_object* v_a_317_, lean_object* v_b_318_){
_start:
{
lean_object* v___x_319_; 
lean_inc(v_a_317_);
lean_inc(v_t_316_);
lean_inc_ref(v_cmp_315_);
v___x_319_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_315_, v_t_316_, v_a_317_);
if (lean_obj_tag(v___x_319_) == 0)
{
uint8_t v___x_320_; 
lean_inc(v_t_316_);
lean_inc(v_a_317_);
lean_inc_ref(v_cmp_315_);
v___x_320_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_315_, v_a_317_, v_t_316_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_315_, v_a_317_, v_b_318_, v_t_316_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_319_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
return v___x_322_;
}
else
{
lean_object* v___x_323_; 
lean_dec(v_b_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_cmp_315_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_319_);
lean_ctor_set(v___x_323_, 1, v_t_316_);
return v___x_323_;
}
}
else
{
lean_object* v___x_324_; 
lean_dec(v_b_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_cmp_315_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_319_);
lean_ctor_set(v___x_324_, 1, v_t_316_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_325_, lean_object* v_00_u03b2_326_, lean_object* v_cmp_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_t_330_, lean_object* v_a_331_, lean_object* v_b_332_){
_start:
{
lean_object* v___x_333_; 
lean_inc(v_a_331_);
lean_inc(v_t_330_);
lean_inc_ref(v_cmp_327_);
v___x_333_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_327_, v_t_330_, v_a_331_);
if (lean_obj_tag(v___x_333_) == 0)
{
uint8_t v___x_334_; 
lean_inc(v_t_330_);
lean_inc(v_a_331_);
lean_inc_ref(v_cmp_327_);
v___x_334_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_327_, v_a_331_, v_t_330_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_327_, v_a_331_, v_b_332_, v_t_330_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_333_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; 
lean_dec(v_b_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_cmp_327_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_333_);
lean_ctor_set(v___x_337_, 1, v_t_330_);
return v___x_337_;
}
}
else
{
lean_object* v___x_338_; 
lean_dec(v_b_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_cmp_327_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_333_);
lean_ctor_set(v___x_338_, 1, v_t_330_);
return v___x_338_;
}
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_contains___redArg(lean_object* v_cmp_339_, lean_object* v_t_340_, lean_object* v_a_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_339_, v_a_341_, v_t_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_contains___redArg___boxed(lean_object* v_cmp_343_, lean_object* v_t_344_, lean_object* v_a_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Std_ExtDTreeMap_contains___redArg(v_cmp_343_, v_t_344_, v_a_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_contains(lean_object* v_00_u03b1_348_, lean_object* v_00_u03b2_349_, lean_object* v_cmp_350_, lean_object* v_inst_351_, lean_object* v_t_352_, lean_object* v_a_353_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_350_, v_a_353_, v_t_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_contains___boxed(lean_object* v_00_u03b1_355_, lean_object* v_00_u03b2_356_, lean_object* v_cmp_357_, lean_object* v_inst_358_, lean_object* v_t_359_, lean_object* v_a_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Std_ExtDTreeMap_contains(v_00_u03b1_355_, v_00_u03b2_356_, v_cmp_357_, v_inst_358_, v_t_359_, v_a_360_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg(){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_box(0);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg___boxed(lean_object* v___dummy_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg();
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp(lean_object* v_00_u03b1_367_, lean_object* v_00_u03b2_368_, lean_object* v_cmp_369_, lean_object* v_inst_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___boxed(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_cmp_374_, lean_object* v_inst_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_ExtDTreeMap_instMembershipOfTransCmp(v_00_u03b1_372_, v_00_u03b2_373_, v_cmp_374_, v_inst_375_);
lean_dec_ref(v_cmp_374_);
return v_res_376_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableMem___redArg(lean_object* v_cmp_377_, lean_object* v_m_378_, lean_object* v_a_379_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_377_, v_a_379_, v_m_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_381_, lean_object* v_m_382_, lean_object* v_a_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_Std_ExtDTreeMap_instDecidableMem___redArg(v_cmp_381_, v_m_382_, v_a_383_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableMem(lean_object* v_00_u03b1_386_, lean_object* v_00_u03b2_387_, lean_object* v_cmp_388_, lean_object* v_inst_389_, lean_object* v_m_390_, lean_object* v_a_391_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_388_, v_a_391_, v_m_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_393_, lean_object* v_00_u03b2_394_, lean_object* v_cmp_395_, lean_object* v_inst_396_, lean_object* v_m_397_, lean_object* v_a_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = l_Std_ExtDTreeMap_instDecidableMem(v_00_u03b1_393_, v_00_u03b2_394_, v_cmp_395_, v_inst_396_, v_m_397_, v_a_398_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___redArg(lean_object* v_t_401_){
_start:
{
if (lean_obj_tag(v_t_401_) == 0)
{
lean_object* v_size_402_; 
v_size_402_ = lean_ctor_get(v_t_401_, 0);
lean_inc(v_size_402_);
return v_size_402_;
}
else
{
lean_object* v___x_403_; 
v___x_403_ = lean_unsigned_to_nat(0u);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___redArg___boxed(lean_object* v_t_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_ExtDTreeMap_size___redArg(v_t_404_);
lean_dec(v_t_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size(lean_object* v_00_u03b1_406_, lean_object* v_00_u03b2_407_, lean_object* v_cmp_408_, lean_object* v_t_409_){
_start:
{
if (lean_obj_tag(v_t_409_) == 0)
{
lean_object* v_size_410_; 
v_size_410_ = lean_ctor_get(v_t_409_, 0);
lean_inc(v_size_410_);
return v_size_410_;
}
else
{
lean_object* v___x_411_; 
v___x_411_ = lean_unsigned_to_nat(0u);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___boxed(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_cmp_414_, lean_object* v_t_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_ExtDTreeMap_size(v_00_u03b1_412_, v_00_u03b2_413_, v_cmp_414_, v_t_415_);
lean_dec(v_t_415_);
lean_dec_ref(v_cmp_414_);
return v_res_416_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_isEmpty___redArg(lean_object* v_t_417_){
_start:
{
if (lean_obj_tag(v_t_417_) == 0)
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
else
{
uint8_t v___x_419_; 
v___x_419_ = 1;
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_isEmpty___redArg___boxed(lean_object* v_t_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Std_ExtDTreeMap_isEmpty___redArg(v_t_420_);
lean_dec(v_t_420_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_isEmpty(lean_object* v_00_u03b1_423_, lean_object* v_00_u03b2_424_, lean_object* v_cmp_425_, lean_object* v_t_426_){
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_429_, lean_object* v_00_u03b2_430_, lean_object* v_cmp_431_, lean_object* v_t_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Std_ExtDTreeMap_isEmpty(v_00_u03b1_429_, v_00_u03b2_430_, v_cmp_431_, v_t_432_);
lean_dec(v_t_432_);
lean_dec_ref(v_cmp_431_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_erase___redArg(lean_object* v_cmp_435_, lean_object* v_t_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_435_, v_a_437_, v_t_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_erase(lean_object* v_00_u03b1_439_, lean_object* v_00_u03b2_440_, lean_object* v_cmp_441_, lean_object* v_inst_442_, lean_object* v_t_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_441_, v_a_444_, v_t_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x3f___redArg(lean_object* v_cmp_446_, lean_object* v_t_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_446_, v_t_447_, v_a_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x3f(lean_object* v_00_u03b1_450_, lean_object* v_00_u03b2_451_, lean_object* v_cmp_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_t_455_, lean_object* v_a_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_452_, v_t_455_, v_a_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get___redArg(lean_object* v_cmp_458_, lean_object* v_t_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_458_, v_t_459_, v_a_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get(lean_object* v_00_u03b1_462_, lean_object* v_00_u03b2_463_, lean_object* v_cmp_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_t_467_, lean_object* v_a_468_, lean_object* v_h_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_464_, v_t_467_, v_a_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___redArg(lean_object* v_cmp_471_, lean_object* v_t_472_, lean_object* v_a_473_, lean_object* v_inst_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_471_, v_t_472_, v_a_473_, v_inst_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___redArg___boxed(lean_object* v_cmp_476_, lean_object* v_t_477_, lean_object* v_a_478_, lean_object* v_inst_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_ExtDTreeMap_get_x21___redArg(v_cmp_476_, v_t_477_, v_a_478_, v_inst_479_);
lean_dec(v_inst_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21(lean_object* v_00_u03b1_481_, lean_object* v_00_u03b2_482_, lean_object* v_cmp_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_t_486_, lean_object* v_a_487_, lean_object* v_inst_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_483_, v_t_486_, v_a_487_, v_inst_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___boxed(lean_object* v_00_u03b1_490_, lean_object* v_00_u03b2_491_, lean_object* v_cmp_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_t_495_, lean_object* v_a_496_, lean_object* v_inst_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_ExtDTreeMap_get_x21(v_00_u03b1_490_, v_00_u03b2_491_, v_cmp_492_, v_inst_493_, v_inst_494_, v_t_495_, v_a_496_, v_inst_497_);
lean_dec(v_inst_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg(lean_object* v_cmp_499_, lean_object* v_t_500_, lean_object* v_a_501_, lean_object* v_fallback_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_499_, v_t_500_, v_a_501_, v_fallback_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg___boxed(lean_object* v_cmp_504_, lean_object* v_t_505_, lean_object* v_a_506_, lean_object* v_fallback_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_ExtDTreeMap_getD___redArg(v_cmp_504_, v_t_505_, v_a_506_, v_fallback_507_);
lean_dec(v_fallback_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD(lean_object* v_00_u03b1_509_, lean_object* v_00_u03b2_510_, lean_object* v_cmp_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_t_514_, lean_object* v_a_515_, lean_object* v_fallback_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_511_, v_t_514_, v_a_515_, v_fallback_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___boxed(lean_object* v_00_u03b1_518_, lean_object* v_00_u03b2_519_, lean_object* v_cmp_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_t_523_, lean_object* v_a_524_, lean_object* v_fallback_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_ExtDTreeMap_getD(v_00_u03b1_518_, v_00_u03b2_519_, v_cmp_520_, v_inst_521_, v_inst_522_, v_t_523_, v_a_524_, v_fallback_525_);
lean_dec(v_fallback_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f___redArg(lean_object* v_cmp_527_, lean_object* v_t_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_527_, v_t_528_, v_a_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f(lean_object* v_00_u03b1_531_, lean_object* v_00_u03b2_532_, lean_object* v_cmp_533_, lean_object* v_inst_534_, lean_object* v_t_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_533_, v_t_535_, v_a_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey___redArg(lean_object* v_cmp_538_, lean_object* v_t_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_538_, v_t_539_, v_a_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_, lean_object* v_cmp_544_, lean_object* v_inst_545_, lean_object* v_t_546_, lean_object* v_a_547_, lean_object* v_h_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_544_, v_t_546_, v_a_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___redArg(lean_object* v_cmp_550_, lean_object* v_inst_551_, lean_object* v_t_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_550_, v_t_552_, v_a_553_, v_inst_551_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___redArg___boxed(lean_object* v_cmp_555_, lean_object* v_inst_556_, lean_object* v_t_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_ExtDTreeMap_getKey_x21___redArg(v_cmp_555_, v_inst_556_, v_t_557_, v_a_558_);
lean_dec(v_inst_556_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21(lean_object* v_00_u03b1_560_, lean_object* v_00_u03b2_561_, lean_object* v_cmp_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_t_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_562_, v_t_565_, v_a_566_, v_inst_564_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___boxed(lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_cmp_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_t_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_ExtDTreeMap_getKey_x21(v_00_u03b1_568_, v_00_u03b2_569_, v_cmp_570_, v_inst_571_, v_inst_572_, v_t_573_, v_a_574_);
lean_dec(v_inst_572_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___redArg(lean_object* v_cmp_576_, lean_object* v_t_577_, lean_object* v_a_578_, lean_object* v_fallback_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_576_, v_t_577_, v_a_578_, v_fallback_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_581_, lean_object* v_t_582_, lean_object* v_a_583_, lean_object* v_fallback_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_ExtDTreeMap_getKeyD___redArg(v_cmp_581_, v_t_582_, v_a_583_, v_fallback_584_);
lean_dec(v_fallback_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD(lean_object* v_00_u03b1_586_, lean_object* v_00_u03b2_587_, lean_object* v_cmp_588_, lean_object* v_inst_589_, lean_object* v_t_590_, lean_object* v_a_591_, lean_object* v_fallback_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_588_, v_t_590_, v_a_591_, v_fallback_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_594_, lean_object* v_00_u03b2_595_, lean_object* v_cmp_596_, lean_object* v_inst_597_, lean_object* v_t_598_, lean_object* v_a_599_, lean_object* v_fallback_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_ExtDTreeMap_getKeyD(v_00_u03b1_594_, v_00_u03b2_595_, v_cmp_596_, v_inst_597_, v_t_598_, v_a_599_, v_fallback_600_);
lean_dec(v_fallback_600_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___redArg(lean_object* v_t_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Std_ExtDTreeMap_minEntry_x3f___redArg(v_t_604_);
lean_dec(v_t_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f(lean_object* v_00_u03b1_606_, lean_object* v_00_u03b2_607_, lean_object* v_cmp_608_, lean_object* v_inst_609_, lean_object* v_t_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_612_, lean_object* v_00_u03b2_613_, lean_object* v_cmp_614_, lean_object* v_inst_615_, lean_object* v_t_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_ExtDTreeMap_minEntry_x3f(v_00_u03b1_612_, v_00_u03b2_613_, v_cmp_614_, v_inst_615_, v_t_616_);
lean_dec(v_t_616_);
lean_dec_ref(v_cmp_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___redArg(lean_object* v_t_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___redArg___boxed(lean_object* v_t_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_ExtDTreeMap_minEntry___redArg(v_t_620_);
lean_dec(v_t_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry(lean_object* v_00_u03b1_622_, lean_object* v_00_u03b2_623_, lean_object* v_cmp_624_, lean_object* v_inst_625_, lean_object* v_t_626_, lean_object* v_h_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___boxed(lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_cmp_631_, lean_object* v_inst_632_, lean_object* v_t_633_, lean_object* v_h_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_ExtDTreeMap_minEntry(v_00_u03b1_629_, v_00_u03b2_630_, v_cmp_631_, v_inst_632_, v_t_633_, v_h_634_);
lean_dec(v_t_633_);
lean_dec_ref(v_cmp_631_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___redArg(lean_object* v_inst_636_, lean_object* v_t_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_636_, v_t_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_639_, lean_object* v_t_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_ExtDTreeMap_minEntry_x21___redArg(v_inst_639_, v_t_640_);
lean_dec(v_t_640_);
lean_dec_ref(v_inst_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21(lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_cmp_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_t_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_646_, v_t_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_cmp_651_, lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_t_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Std_ExtDTreeMap_minEntry_x21(v_00_u03b1_649_, v_00_u03b2_650_, v_cmp_651_, v_inst_652_, v_inst_653_, v_t_654_);
lean_dec(v_t_654_);
lean_dec_ref(v_inst_653_);
lean_dec_ref(v_cmp_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___redArg(lean_object* v_t_656_, lean_object* v_fallback_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_656_, v_fallback_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___redArg___boxed(lean_object* v_t_659_, lean_object* v_fallback_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_ExtDTreeMap_minEntryD___redArg(v_t_659_, v_fallback_660_);
lean_dec_ref(v_fallback_660_);
lean_dec(v_t_659_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_cmp_664_, lean_object* v_inst_665_, lean_object* v_t_666_, lean_object* v_fallback_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_666_, v_fallback_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_669_, lean_object* v_00_u03b2_670_, lean_object* v_cmp_671_, lean_object* v_inst_672_, lean_object* v_t_673_, lean_object* v_fallback_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_ExtDTreeMap_minEntryD(v_00_u03b1_669_, v_00_u03b2_670_, v_cmp_671_, v_inst_672_, v_t_673_, v_fallback_674_);
lean_dec_ref(v_fallback_674_);
lean_dec(v_t_673_);
lean_dec_ref(v_cmp_671_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___redArg(lean_object* v_t_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Std_ExtDTreeMap_maxEntry_x3f___redArg(v_t_678_);
lean_dec(v_t_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_cmp_682_, lean_object* v_inst_683_, lean_object* v_t_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_686_, lean_object* v_00_u03b2_687_, lean_object* v_cmp_688_, lean_object* v_inst_689_, lean_object* v_t_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_ExtDTreeMap_maxEntry_x3f(v_00_u03b1_686_, v_00_u03b2_687_, v_cmp_688_, v_inst_689_, v_t_690_);
lean_dec(v_t_690_);
lean_dec_ref(v_cmp_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___redArg(lean_object* v_t_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___redArg___boxed(lean_object* v_t_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Std_ExtDTreeMap_maxEntry___redArg(v_t_694_);
lean_dec(v_t_694_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry(lean_object* v_00_u03b1_696_, lean_object* v_00_u03b2_697_, lean_object* v_cmp_698_, lean_object* v_inst_699_, lean_object* v_t_700_, lean_object* v_h_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_700_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_703_, lean_object* v_00_u03b2_704_, lean_object* v_cmp_705_, lean_object* v_inst_706_, lean_object* v_t_707_, lean_object* v_h_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_ExtDTreeMap_maxEntry(v_00_u03b1_703_, v_00_u03b2_704_, v_cmp_705_, v_inst_706_, v_t_707_, v_h_708_);
lean_dec(v_t_707_);
lean_dec_ref(v_cmp_705_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___redArg(lean_object* v_inst_710_, lean_object* v_t_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_710_, v_t_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_713_, lean_object* v_t_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_ExtDTreeMap_maxEntry_x21___redArg(v_inst_713_, v_t_714_);
lean_dec(v_t_714_);
lean_dec_ref(v_inst_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21(lean_object* v_00_u03b1_716_, lean_object* v_00_u03b2_717_, lean_object* v_cmp_718_, lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_t_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_720_, v_t_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_cmp_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_t_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_ExtDTreeMap_maxEntry_x21(v_00_u03b1_723_, v_00_u03b2_724_, v_cmp_725_, v_inst_726_, v_inst_727_, v_t_728_);
lean_dec(v_t_728_);
lean_dec_ref(v_inst_727_);
lean_dec_ref(v_cmp_725_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___redArg(lean_object* v_t_730_, lean_object* v_fallback_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_730_, v_fallback_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_733_, lean_object* v_fallback_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_ExtDTreeMap_maxEntryD___redArg(v_t_733_, v_fallback_734_);
lean_dec_ref(v_fallback_734_);
lean_dec(v_t_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD(lean_object* v_00_u03b1_736_, lean_object* v_00_u03b2_737_, lean_object* v_cmp_738_, lean_object* v_inst_739_, lean_object* v_t_740_, lean_object* v_fallback_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_740_, v_fallback_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_743_, lean_object* v_00_u03b2_744_, lean_object* v_cmp_745_, lean_object* v_inst_746_, lean_object* v_t_747_, lean_object* v_fallback_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_ExtDTreeMap_maxEntryD(v_00_u03b1_743_, v_00_u03b2_744_, v_cmp_745_, v_inst_746_, v_t_747_, v_fallback_748_);
lean_dec_ref(v_fallback_748_);
lean_dec(v_t_747_);
lean_dec_ref(v_cmp_745_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___redArg(lean_object* v_t_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_ExtDTreeMap_minKey_x3f___redArg(v_t_752_);
lean_dec(v_t_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f(lean_object* v_00_u03b1_754_, lean_object* v_00_u03b2_755_, lean_object* v_cmp_756_, lean_object* v_inst_757_, lean_object* v_t_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_760_, lean_object* v_00_u03b2_761_, lean_object* v_cmp_762_, lean_object* v_inst_763_, lean_object* v_t_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_ExtDTreeMap_minKey_x3f(v_00_u03b1_760_, v_00_u03b2_761_, v_cmp_762_, v_inst_763_, v_t_764_);
lean_dec(v_t_764_);
lean_dec_ref(v_cmp_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___redArg(lean_object* v_t_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___redArg___boxed(lean_object* v_t_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_ExtDTreeMap_minKey___redArg(v_t_768_);
lean_dec(v_t_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey(lean_object* v_00_u03b1_770_, lean_object* v_00_u03b2_771_, lean_object* v_cmp_772_, lean_object* v_inst_773_, lean_object* v_t_774_, lean_object* v_h_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___boxed(lean_object* v_00_u03b1_777_, lean_object* v_00_u03b2_778_, lean_object* v_cmp_779_, lean_object* v_inst_780_, lean_object* v_t_781_, lean_object* v_h_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_ExtDTreeMap_minKey(v_00_u03b1_777_, v_00_u03b2_778_, v_cmp_779_, v_inst_780_, v_t_781_, v_h_782_);
lean_dec(v_t_781_);
lean_dec_ref(v_cmp_779_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___redArg(lean_object* v_inst_784_, lean_object* v_t_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_784_, v_t_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_787_, lean_object* v_t_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_ExtDTreeMap_minKey_x21___redArg(v_inst_787_, v_t_788_);
lean_dec(v_t_788_);
lean_dec(v_inst_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21(lean_object* v_00_u03b1_790_, lean_object* v_00_u03b2_791_, lean_object* v_cmp_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_t_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_794_, v_t_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_797_, lean_object* v_00_u03b2_798_, lean_object* v_cmp_799_, lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_t_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_ExtDTreeMap_minKey_x21(v_00_u03b1_797_, v_00_u03b2_798_, v_cmp_799_, v_inst_800_, v_inst_801_, v_t_802_);
lean_dec(v_t_802_);
lean_dec(v_inst_801_);
lean_dec_ref(v_cmp_799_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___redArg(lean_object* v_t_804_, lean_object* v_fallback_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_804_, v_fallback_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___redArg___boxed(lean_object* v_t_807_, lean_object* v_fallback_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_ExtDTreeMap_minKeyD___redArg(v_t_807_, v_fallback_808_);
lean_dec(v_fallback_808_);
lean_dec(v_t_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD(lean_object* v_00_u03b1_810_, lean_object* v_00_u03b2_811_, lean_object* v_cmp_812_, lean_object* v_inst_813_, lean_object* v_t_814_, lean_object* v_fallback_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_814_, v_fallback_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_817_, lean_object* v_00_u03b2_818_, lean_object* v_cmp_819_, lean_object* v_inst_820_, lean_object* v_t_821_, lean_object* v_fallback_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_ExtDTreeMap_minKeyD(v_00_u03b1_817_, v_00_u03b2_818_, v_cmp_819_, v_inst_820_, v_t_821_, v_fallback_822_);
lean_dec(v_fallback_822_);
lean_dec(v_t_821_);
lean_dec_ref(v_cmp_819_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___redArg(lean_object* v_t_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_ExtDTreeMap_maxKey_x3f___redArg(v_t_826_);
lean_dec(v_t_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f(lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_cmp_830_, lean_object* v_inst_831_, lean_object* v_t_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_834_, lean_object* v_00_u03b2_835_, lean_object* v_cmp_836_, lean_object* v_inst_837_, lean_object* v_t_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_ExtDTreeMap_maxKey_x3f(v_00_u03b1_834_, v_00_u03b2_835_, v_cmp_836_, v_inst_837_, v_t_838_);
lean_dec(v_t_838_);
lean_dec_ref(v_cmp_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___redArg(lean_object* v_t_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___redArg___boxed(lean_object* v_t_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_ExtDTreeMap_maxKey___redArg(v_t_842_);
lean_dec(v_t_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey(lean_object* v_00_u03b1_844_, lean_object* v_00_u03b2_845_, lean_object* v_cmp_846_, lean_object* v_inst_847_, lean_object* v_t_848_, lean_object* v_h_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_848_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___boxed(lean_object* v_00_u03b1_851_, lean_object* v_00_u03b2_852_, lean_object* v_cmp_853_, lean_object* v_inst_854_, lean_object* v_t_855_, lean_object* v_h_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_ExtDTreeMap_maxKey(v_00_u03b1_851_, v_00_u03b2_852_, v_cmp_853_, v_inst_854_, v_t_855_, v_h_856_);
lean_dec(v_t_855_);
lean_dec_ref(v_cmp_853_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___redArg(lean_object* v_inst_858_, lean_object* v_t_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_858_, v_t_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_861_, lean_object* v_t_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_ExtDTreeMap_maxKey_x21___redArg(v_inst_861_, v_t_862_);
lean_dec(v_t_862_);
lean_dec(v_inst_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21(lean_object* v_00_u03b1_864_, lean_object* v_00_u03b2_865_, lean_object* v_cmp_866_, lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_t_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_868_, v_t_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_871_, lean_object* v_00_u03b2_872_, lean_object* v_cmp_873_, lean_object* v_inst_874_, lean_object* v_inst_875_, lean_object* v_t_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_ExtDTreeMap_maxKey_x21(v_00_u03b1_871_, v_00_u03b2_872_, v_cmp_873_, v_inst_874_, v_inst_875_, v_t_876_);
lean_dec(v_t_876_);
lean_dec(v_inst_875_);
lean_dec_ref(v_cmp_873_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___redArg(lean_object* v_t_878_, lean_object* v_fallback_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_878_, v_fallback_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_881_, lean_object* v_fallback_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Std_ExtDTreeMap_maxKeyD___redArg(v_t_881_, v_fallback_882_);
lean_dec(v_fallback_882_);
lean_dec(v_t_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD(lean_object* v_00_u03b1_884_, lean_object* v_00_u03b2_885_, lean_object* v_cmp_886_, lean_object* v_inst_887_, lean_object* v_t_888_, lean_object* v_fallback_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_888_, v_fallback_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_cmp_893_, lean_object* v_inst_894_, lean_object* v_t_895_, lean_object* v_fallback_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Std_ExtDTreeMap_maxKeyD(v_00_u03b1_891_, v_00_u03b2_892_, v_cmp_893_, v_inst_894_, v_t_895_, v_fallback_896_);
lean_dec(v_fallback_896_);
lean_dec(v_t_895_);
lean_dec_ref(v_cmp_893_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_898_, lean_object* v_n_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_898_, v_n_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_901_, lean_object* v_n_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(v_t_901_, v_n_902_);
lean_dec(v_t_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_904_, lean_object* v_00_u03b2_905_, lean_object* v_cmp_906_, lean_object* v_inst_907_, lean_object* v_t_908_, lean_object* v_n_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_908_, v_n_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_911_, lean_object* v_00_u03b2_912_, lean_object* v_cmp_913_, lean_object* v_inst_914_, lean_object* v_t_915_, lean_object* v_n_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Std_ExtDTreeMap_entryAtIdx_x3f(v_00_u03b1_911_, v_00_u03b2_912_, v_cmp_913_, v_inst_914_, v_t_915_, v_n_916_);
lean_dec(v_t_915_);
lean_dec_ref(v_cmp_913_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___redArg(lean_object* v_t_918_, lean_object* v_n_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_918_, v_n_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_921_, lean_object* v_n_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_ExtDTreeMap_entryAtIdx___redArg(v_t_921_, v_n_922_);
lean_dec(v_t_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx(lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_cmp_926_, lean_object* v_inst_927_, lean_object* v_t_928_, lean_object* v_n_929_, lean_object* v_h_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_928_, v_n_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_932_, lean_object* v_00_u03b2_933_, lean_object* v_cmp_934_, lean_object* v_inst_935_, lean_object* v_t_936_, lean_object* v_n_937_, lean_object* v_h_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_ExtDTreeMap_entryAtIdx(v_00_u03b1_932_, v_00_u03b2_933_, v_cmp_934_, v_inst_935_, v_t_936_, v_n_937_, v_h_938_);
lean_dec(v_t_936_);
lean_dec_ref(v_cmp_934_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_940_, lean_object* v_t_941_, lean_object* v_n_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_940_, v_t_941_, v_n_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_944_, lean_object* v_t_945_, lean_object* v_n_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(v_inst_944_, v_t_945_, v_n_946_);
lean_dec(v_t_945_);
lean_dec_ref(v_inst_944_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_948_, lean_object* v_00_u03b2_949_, lean_object* v_cmp_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_t_953_, lean_object* v_n_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_952_, v_t_953_, v_n_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_956_, lean_object* v_00_u03b2_957_, lean_object* v_cmp_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_t_961_, lean_object* v_n_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Std_ExtDTreeMap_entryAtIdx_x21(v_00_u03b1_956_, v_00_u03b2_957_, v_cmp_958_, v_inst_959_, v_inst_960_, v_t_961_, v_n_962_);
lean_dec(v_t_961_);
lean_dec_ref(v_inst_960_);
lean_dec_ref(v_cmp_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___redArg(lean_object* v_t_964_, lean_object* v_n_965_, lean_object* v_fallback_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_964_, v_n_965_, v_fallback_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_968_, lean_object* v_n_969_, lean_object* v_fallback_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Std_ExtDTreeMap_entryAtIdxD___redArg(v_t_968_, v_n_969_, v_fallback_970_);
lean_dec_ref(v_fallback_970_);
lean_dec(v_t_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD(lean_object* v_00_u03b1_972_, lean_object* v_00_u03b2_973_, lean_object* v_cmp_974_, lean_object* v_inst_975_, lean_object* v_t_976_, lean_object* v_n_977_, lean_object* v_fallback_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_976_, v_n_977_, v_fallback_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_980_, lean_object* v_00_u03b2_981_, lean_object* v_cmp_982_, lean_object* v_inst_983_, lean_object* v_t_984_, lean_object* v_n_985_, lean_object* v_fallback_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Std_ExtDTreeMap_entryAtIdxD(v_00_u03b1_980_, v_00_u03b2_981_, v_cmp_982_, v_inst_983_, v_t_984_, v_n_985_, v_fallback_986_);
lean_dec_ref(v_fallback_986_);
lean_dec(v_t_984_);
lean_dec_ref(v_cmp_982_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_988_, lean_object* v_n_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_988_, v_n_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_991_, lean_object* v_n_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(v_t_991_, v_n_992_);
lean_dec(v_t_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_994_, lean_object* v_00_u03b2_995_, lean_object* v_cmp_996_, lean_object* v_inst_997_, lean_object* v_t_998_, lean_object* v_n_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_998_, v_n_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_1001_, lean_object* v_00_u03b2_1002_, lean_object* v_cmp_1003_, lean_object* v_inst_1004_, lean_object* v_t_1005_, lean_object* v_n_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_ExtDTreeMap_keyAtIdx_x3f(v_00_u03b1_1001_, v_00_u03b2_1002_, v_cmp_1003_, v_inst_1004_, v_t_1005_, v_n_1006_);
lean_dec(v_t_1005_);
lean_dec_ref(v_cmp_1003_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___redArg(lean_object* v_t_1008_, lean_object* v_n_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1008_, v_n_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_1011_, lean_object* v_n_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Std_ExtDTreeMap_keyAtIdx___redArg(v_t_1011_, v_n_1012_);
lean_dec(v_t_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_cmp_1016_, lean_object* v_inst_1017_, lean_object* v_t_1018_, lean_object* v_n_1019_, lean_object* v_h_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1018_, v_n_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_1022_, lean_object* v_00_u03b2_1023_, lean_object* v_cmp_1024_, lean_object* v_inst_1025_, lean_object* v_t_1026_, lean_object* v_n_1027_, lean_object* v_h_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Std_ExtDTreeMap_keyAtIdx(v_00_u03b1_1022_, v_00_u03b2_1023_, v_cmp_1024_, v_inst_1025_, v_t_1026_, v_n_1027_, v_h_1028_);
lean_dec(v_t_1026_);
lean_dec_ref(v_cmp_1024_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_1030_, lean_object* v_t_1031_, lean_object* v_n_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1030_, v_t_1031_, v_n_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_1034_, lean_object* v_t_1035_, lean_object* v_n_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(v_inst_1034_, v_t_1035_, v_n_1036_);
lean_dec(v_t_1035_);
lean_dec(v_inst_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_1038_, lean_object* v_00_u03b2_1039_, lean_object* v_cmp_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_t_1043_, lean_object* v_n_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1042_, v_t_1043_, v_n_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_1046_, lean_object* v_00_u03b2_1047_, lean_object* v_cmp_1048_, lean_object* v_inst_1049_, lean_object* v_inst_1050_, lean_object* v_t_1051_, lean_object* v_n_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Std_ExtDTreeMap_keyAtIdx_x21(v_00_u03b1_1046_, v_00_u03b2_1047_, v_cmp_1048_, v_inst_1049_, v_inst_1050_, v_t_1051_, v_n_1052_);
lean_dec(v_t_1051_);
lean_dec(v_inst_1050_);
lean_dec_ref(v_cmp_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___redArg(lean_object* v_t_1054_, lean_object* v_n_1055_, lean_object* v_fallback_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1054_, v_n_1055_, v_fallback_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_1058_, lean_object* v_n_1059_, lean_object* v_fallback_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Std_ExtDTreeMap_keyAtIdxD___redArg(v_t_1058_, v_n_1059_, v_fallback_1060_);
lean_dec(v_fallback_1060_);
lean_dec(v_t_1058_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD(lean_object* v_00_u03b1_1062_, lean_object* v_00_u03b2_1063_, lean_object* v_cmp_1064_, lean_object* v_inst_1065_, lean_object* v_t_1066_, lean_object* v_n_1067_, lean_object* v_fallback_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1066_, v_n_1067_, v_fallback_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_1070_, lean_object* v_00_u03b2_1071_, lean_object* v_cmp_1072_, lean_object* v_inst_1073_, lean_object* v_t_1074_, lean_object* v_n_1075_, lean_object* v_fallback_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Std_ExtDTreeMap_keyAtIdxD(v_00_u03b1_1070_, v_00_u03b2_1071_, v_cmp_1072_, v_inst_1073_, v_t_1074_, v_n_1075_, v_fallback_1076_);
lean_dec(v_fallback_1076_);
lean_dec(v_t_1074_);
lean_dec_ref(v_cmp_1072_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1078_, lean_object* v_t_1079_, lean_object* v_k_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_box(0);
v___x_1082_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1078_, v_k_1080_, v___x_1081_, v_t_1079_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1083_, lean_object* v_00_u03b2_1084_, lean_object* v_cmp_1085_, lean_object* v_inst_1086_, lean_object* v_t_1087_, lean_object* v_k_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1085_, v_k_1088_, v___x_1089_, v_t_1087_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1091_, lean_object* v_t_1092_, lean_object* v_k_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_box(0);
v___x_1095_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1091_, v_k_1093_, v___x_1094_, v_t_1092_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_cmp_1098_, lean_object* v_inst_1099_, lean_object* v_t_1100_, lean_object* v_k_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_box(0);
v___x_1103_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1098_, v_k_1101_, v___x_1102_, v_t_1100_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1104_, lean_object* v_t_1105_, lean_object* v_k_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_box(0);
v___x_1108_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1104_, v_k_1106_, v___x_1107_, v_t_1105_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_cmp_1111_, lean_object* v_inst_1112_, lean_object* v_t_1113_, lean_object* v_k_1114_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_box(0);
v___x_1116_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1111_, v_k_1114_, v___x_1115_, v_t_1113_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1117_, lean_object* v_t_1118_, lean_object* v_k_1119_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_box(0);
v___x_1121_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1117_, v_k_1119_, v___x_1120_, v_t_1118_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1122_, lean_object* v_00_u03b2_1123_, lean_object* v_cmp_1124_, lean_object* v_inst_1125_, lean_object* v_t_1126_, lean_object* v_k_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_box(0);
v___x_1129_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1124_, v_k_1127_, v___x_1128_, v_t_1126_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE___redArg(lean_object* v_cmp_1130_, lean_object* v_t_1131_, lean_object* v_k_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_1130_, v_k_1132_, v_t_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE(lean_object* v_00_u03b1_1134_, lean_object* v_00_u03b2_1135_, lean_object* v_cmp_1136_, lean_object* v_inst_1137_, lean_object* v_t_1138_, lean_object* v_k_1139_, lean_object* v_h_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_1136_, v_k_1139_, v_t_1138_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT___redArg(lean_object* v_cmp_1142_, lean_object* v_t_1143_, lean_object* v_k_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_1142_, v_k_1144_, v_t_1143_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT(lean_object* v_00_u03b1_1146_, lean_object* v_00_u03b2_1147_, lean_object* v_cmp_1148_, lean_object* v_inst_1149_, lean_object* v_t_1150_, lean_object* v_k_1151_, lean_object* v_h_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_1148_, v_k_1151_, v_t_1150_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE___redArg(lean_object* v_cmp_1154_, lean_object* v_t_1155_, lean_object* v_k_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_1154_, v_k_1156_, v_t_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE(lean_object* v_00_u03b1_1158_, lean_object* v_00_u03b2_1159_, lean_object* v_cmp_1160_, lean_object* v_inst_1161_, lean_object* v_t_1162_, lean_object* v_k_1163_, lean_object* v_h_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_1160_, v_k_1163_, v_t_1162_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT___redArg(lean_object* v_cmp_1166_, lean_object* v_t_1167_, lean_object* v_k_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_1166_, v_k_1168_, v_t_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT(lean_object* v_00_u03b1_1170_, lean_object* v_00_u03b2_1171_, lean_object* v_cmp_1172_, lean_object* v_inst_1173_, lean_object* v_t_1174_, lean_object* v_k_1175_, lean_object* v_h_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_1172_, v_k_1175_, v_t_1174_);
return v___x_1177_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1181_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1182_ = lean_unsigned_to_nat(14u);
v___x_1183_ = lean_unsigned_to_nat(22u);
v___x_1184_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1185_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1186_ = l_mkPanicMessageWithDecl(v___x_1185_, v___x_1184_, v___x_1183_, v___x_1182_, v___x_1181_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1187_, lean_object* v_inst_1188_, lean_object* v_t_1189_, lean_object* v_k_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1187_, v_k_1190_, v___x_1191_, v_t_1189_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1196_, lean_object* v_inst_1197_, lean_object* v_t_1198_, lean_object* v_k_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_ExtDTreeMap_getEntryGE_x21___redArg(v_cmp_1196_, v_inst_1197_, v_t_1198_, v_k_1199_);
lean_dec_ref(v_inst_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_cmp_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_t_1206_, lean_object* v_k_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1203_, v_k_1207_, v___x_1208_, v_t_1206_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1213_, lean_object* v_00_u03b2_1214_, lean_object* v_cmp_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_t_1218_, lean_object* v_k_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_ExtDTreeMap_getEntryGE_x21(v_00_u03b1_1213_, v_00_u03b2_1214_, v_cmp_1215_, v_inst_1216_, v_inst_1217_, v_t_1218_, v_k_1219_);
lean_dec_ref(v_inst_1217_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1221_, lean_object* v_inst_1222_, lean_object* v_t_1223_, lean_object* v_k_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1221_, v_k_1224_, v___x_1225_, v_t_1223_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1230_, lean_object* v_inst_1231_, lean_object* v_t_1232_, lean_object* v_k_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Std_ExtDTreeMap_getEntryGT_x21___redArg(v_cmp_1230_, v_inst_1231_, v_t_1232_, v_k_1233_);
lean_dec_ref(v_inst_1231_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1235_, lean_object* v_00_u03b2_1236_, lean_object* v_cmp_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_t_1240_, lean_object* v_k_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_box(0);
v___x_1243_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1237_, v_k_1241_, v___x_1242_, v_t_1240_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1247_, lean_object* v_00_u03b2_1248_, lean_object* v_cmp_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_t_1252_, lean_object* v_k_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Std_ExtDTreeMap_getEntryGT_x21(v_00_u03b1_1247_, v_00_u03b2_1248_, v_cmp_1249_, v_inst_1250_, v_inst_1251_, v_t_1252_, v_k_1253_);
lean_dec_ref(v_inst_1251_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1255_, lean_object* v_inst_1256_, lean_object* v_t_1257_, lean_object* v_k_1258_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_box(0);
v___x_1260_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1255_, v_k_1258_, v___x_1259_, v_t_1257_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1262_ = l_panic___redArg(v_inst_1256_, v___x_1261_);
return v___x_1262_;
}
else
{
lean_object* v_val_1263_; 
v_val_1263_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_val_1263_);
lean_dec_ref_known(v___x_1260_, 1);
return v_val_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1264_, lean_object* v_inst_1265_, lean_object* v_t_1266_, lean_object* v_k_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Std_ExtDTreeMap_getEntryLE_x21___redArg(v_cmp_1264_, v_inst_1265_, v_t_1266_, v_k_1267_);
lean_dec_ref(v_inst_1265_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1269_, lean_object* v_00_u03b2_1270_, lean_object* v_cmp_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_t_1274_, lean_object* v_k_1275_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_box(0);
v___x_1277_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1271_, v_k_1275_, v___x_1276_, v_t_1274_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1279_ = l_panic___redArg(v_inst_1273_, v___x_1278_);
return v___x_1279_;
}
else
{
lean_object* v_val_1280_; 
v_val_1280_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_val_1280_);
lean_dec_ref_known(v___x_1277_, 1);
return v_val_1280_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1281_, lean_object* v_00_u03b2_1282_, lean_object* v_cmp_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_t_1286_, lean_object* v_k_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Std_ExtDTreeMap_getEntryLE_x21(v_00_u03b1_1281_, v_00_u03b2_1282_, v_cmp_1283_, v_inst_1284_, v_inst_1285_, v_t_1286_, v_k_1287_);
lean_dec_ref(v_inst_1285_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1289_, lean_object* v_inst_1290_, lean_object* v_t_1291_, lean_object* v_k_1292_){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_box(0);
v___x_1294_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1289_, v_k_1292_, v___x_1293_, v_t_1291_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1296_ = l_panic___redArg(v_inst_1290_, v___x_1295_);
return v___x_1296_;
}
else
{
lean_object* v_val_1297_; 
v_val_1297_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_val_1297_);
lean_dec_ref_known(v___x_1294_, 1);
return v_val_1297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1298_, lean_object* v_inst_1299_, lean_object* v_t_1300_, lean_object* v_k_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_ExtDTreeMap_getEntryLT_x21___redArg(v_cmp_1298_, v_inst_1299_, v_t_1300_, v_k_1301_);
lean_dec_ref(v_inst_1299_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1303_, lean_object* v_00_u03b2_1304_, lean_object* v_cmp_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_t_1308_, lean_object* v_k_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_box(0);
v___x_1311_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1305_, v_k_1309_, v___x_1310_, v_t_1308_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1313_ = l_panic___redArg(v_inst_1307_, v___x_1312_);
return v___x_1313_;
}
else
{
lean_object* v_val_1314_; 
v_val_1314_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_val_1314_);
lean_dec_ref_known(v___x_1311_, 1);
return v_val_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1315_, lean_object* v_00_u03b2_1316_, lean_object* v_cmp_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_t_1320_, lean_object* v_k_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Std_ExtDTreeMap_getEntryLT_x21(v_00_u03b1_1315_, v_00_u03b2_1316_, v_cmp_1317_, v_inst_1318_, v_inst_1319_, v_t_1320_, v_k_1321_);
lean_dec_ref(v_inst_1319_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___redArg(lean_object* v_cmp_1323_, lean_object* v_t_1324_, lean_object* v_k_1325_, lean_object* v_fallback_1326_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_box(0);
v___x_1328_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1323_, v_k_1325_, v___x_1327_, v_t_1324_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_inc_ref(v_fallback_1326_);
return v_fallback_1326_;
}
else
{
lean_object* v_val_1329_; 
v_val_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_val_1329_);
lean_dec_ref_known(v___x_1328_, 1);
return v_val_1329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1330_, lean_object* v_t_1331_, lean_object* v_k_1332_, lean_object* v_fallback_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Std_ExtDTreeMap_getEntryGED___redArg(v_cmp_1330_, v_t_1331_, v_k_1332_, v_fallback_1333_);
lean_dec_ref(v_fallback_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED(lean_object* v_00_u03b1_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_cmp_1337_, lean_object* v_inst_1338_, lean_object* v_t_1339_, lean_object* v_k_1340_, lean_object* v_fallback_1341_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_box(0);
v___x_1343_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1337_, v_k_1340_, v___x_1342_, v_t_1339_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_inc_ref(v_fallback_1341_);
return v_fallback_1341_;
}
else
{
lean_object* v_val_1344_; 
v_val_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v___x_1343_, 1);
return v_val_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_00_u03b2_1346_, lean_object* v_cmp_1347_, lean_object* v_inst_1348_, lean_object* v_t_1349_, lean_object* v_k_1350_, lean_object* v_fallback_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Std_ExtDTreeMap_getEntryGED(v_00_u03b1_1345_, v_00_u03b2_1346_, v_cmp_1347_, v_inst_1348_, v_t_1349_, v_k_1350_, v_fallback_1351_);
lean_dec_ref(v_fallback_1351_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1353_, lean_object* v_t_1354_, lean_object* v_k_1355_, lean_object* v_fallback_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_box(0);
v___x_1358_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1353_, v_k_1355_, v___x_1357_, v_t_1354_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_inc_ref(v_fallback_1356_);
return v_fallback_1356_;
}
else
{
lean_object* v_val_1359_; 
v_val_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_val_1359_);
lean_dec_ref_known(v___x_1358_, 1);
return v_val_1359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1360_, lean_object* v_t_1361_, lean_object* v_k_1362_, lean_object* v_fallback_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Std_ExtDTreeMap_getEntryGTD___redArg(v_cmp_1360_, v_t_1361_, v_k_1362_, v_fallback_1363_);
lean_dec_ref(v_fallback_1363_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD(lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_cmp_1367_, lean_object* v_inst_1368_, lean_object* v_t_1369_, lean_object* v_k_1370_, lean_object* v_fallback_1371_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_box(0);
v___x_1373_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1367_, v_k_1370_, v___x_1372_, v_t_1369_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_inc_ref(v_fallback_1371_);
return v_fallback_1371_;
}
else
{
lean_object* v_val_1374_; 
v_val_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_val_1374_);
lean_dec_ref_known(v___x_1373_, 1);
return v_val_1374_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1375_, lean_object* v_00_u03b2_1376_, lean_object* v_cmp_1377_, lean_object* v_inst_1378_, lean_object* v_t_1379_, lean_object* v_k_1380_, lean_object* v_fallback_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Std_ExtDTreeMap_getEntryGTD(v_00_u03b1_1375_, v_00_u03b2_1376_, v_cmp_1377_, v_inst_1378_, v_t_1379_, v_k_1380_, v_fallback_1381_);
lean_dec_ref(v_fallback_1381_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___redArg(lean_object* v_cmp_1383_, lean_object* v_t_1384_, lean_object* v_k_1385_, lean_object* v_fallback_1386_){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1383_, v_k_1385_, v___x_1387_, v_t_1384_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_inc_ref(v_fallback_1386_);
return v_fallback_1386_;
}
else
{
lean_object* v_val_1389_; 
v_val_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_val_1389_);
lean_dec_ref_known(v___x_1388_, 1);
return v_val_1389_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1390_, lean_object* v_t_1391_, lean_object* v_k_1392_, lean_object* v_fallback_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Std_ExtDTreeMap_getEntryLED___redArg(v_cmp_1390_, v_t_1391_, v_k_1392_, v_fallback_1393_);
lean_dec_ref(v_fallback_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED(lean_object* v_00_u03b1_1395_, lean_object* v_00_u03b2_1396_, lean_object* v_cmp_1397_, lean_object* v_inst_1398_, lean_object* v_t_1399_, lean_object* v_k_1400_, lean_object* v_fallback_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1397_, v_k_1400_, v___x_1402_, v_t_1399_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_inc_ref(v_fallback_1401_);
return v_fallback_1401_;
}
else
{
lean_object* v_val_1404_; 
v_val_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_val_1404_);
lean_dec_ref_known(v___x_1403_, 1);
return v_val_1404_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1405_, lean_object* v_00_u03b2_1406_, lean_object* v_cmp_1407_, lean_object* v_inst_1408_, lean_object* v_t_1409_, lean_object* v_k_1410_, lean_object* v_fallback_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Std_ExtDTreeMap_getEntryLED(v_00_u03b1_1405_, v_00_u03b2_1406_, v_cmp_1407_, v_inst_1408_, v_t_1409_, v_k_1410_, v_fallback_1411_);
lean_dec_ref(v_fallback_1411_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1413_, lean_object* v_t_1414_, lean_object* v_k_1415_, lean_object* v_fallback_1416_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_box(0);
v___x_1418_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1413_, v_k_1415_, v___x_1417_, v_t_1414_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_inc_ref(v_fallback_1416_);
return v_fallback_1416_;
}
else
{
lean_object* v_val_1419_; 
v_val_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_val_1419_);
lean_dec_ref_known(v___x_1418_, 1);
return v_val_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1420_, lean_object* v_t_1421_, lean_object* v_k_1422_, lean_object* v_fallback_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Std_ExtDTreeMap_getEntryLTD___redArg(v_cmp_1420_, v_t_1421_, v_k_1422_, v_fallback_1423_);
lean_dec_ref(v_fallback_1423_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD(lean_object* v_00_u03b1_1425_, lean_object* v_00_u03b2_1426_, lean_object* v_cmp_1427_, lean_object* v_inst_1428_, lean_object* v_t_1429_, lean_object* v_k_1430_, lean_object* v_fallback_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_box(0);
v___x_1433_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1427_, v_k_1430_, v___x_1432_, v_t_1429_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_inc_ref(v_fallback_1431_);
return v_fallback_1431_;
}
else
{
lean_object* v_val_1434_; 
v_val_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_val_1434_);
lean_dec_ref_known(v___x_1433_, 1);
return v_val_1434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_00_u03b2_1436_, lean_object* v_cmp_1437_, lean_object* v_inst_1438_, lean_object* v_t_1439_, lean_object* v_k_1440_, lean_object* v_fallback_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Std_ExtDTreeMap_getEntryLTD(v_00_u03b1_1435_, v_00_u03b2_1436_, v_cmp_1437_, v_inst_1438_, v_t_1439_, v_k_1440_, v_fallback_1441_);
lean_dec_ref(v_fallback_1441_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1443_, lean_object* v_t_1444_, lean_object* v_k_1445_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_box(0);
v___x_1447_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1443_, v_k_1445_, v___x_1446_, v_t_1444_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1448_, lean_object* v_00_u03b2_1449_, lean_object* v_cmp_1450_, lean_object* v_inst_1451_, lean_object* v_t_1452_, lean_object* v_k_1453_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_box(0);
v___x_1455_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1450_, v_k_1453_, v___x_1454_, v_t_1452_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1456_, lean_object* v_t_1457_, lean_object* v_k_1458_){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_box(0);
v___x_1460_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1456_, v_k_1458_, v___x_1459_, v_t_1457_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1461_, lean_object* v_00_u03b2_1462_, lean_object* v_cmp_1463_, lean_object* v_inst_1464_, lean_object* v_t_1465_, lean_object* v_k_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1463_, v_k_1466_, v___x_1467_, v_t_1465_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1469_, lean_object* v_t_1470_, lean_object* v_k_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_box(0);
v___x_1473_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1469_, v_k_1471_, v___x_1472_, v_t_1470_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1474_, lean_object* v_00_u03b2_1475_, lean_object* v_cmp_1476_, lean_object* v_inst_1477_, lean_object* v_t_1478_, lean_object* v_k_1479_){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_box(0);
v___x_1481_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1476_, v_k_1479_, v___x_1480_, v_t_1478_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1482_, lean_object* v_t_1483_, lean_object* v_k_1484_){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_box(0);
v___x_1486_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1482_, v_k_1484_, v___x_1485_, v_t_1483_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1487_, lean_object* v_00_u03b2_1488_, lean_object* v_cmp_1489_, lean_object* v_inst_1490_, lean_object* v_t_1491_, lean_object* v_k_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1489_, v_k_1492_, v___x_1493_, v_t_1491_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE___redArg(lean_object* v_cmp_1495_, lean_object* v_t_1496_, lean_object* v_k_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1495_, v_k_1497_, v_t_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE(lean_object* v_00_u03b1_1499_, lean_object* v_00_u03b2_1500_, lean_object* v_cmp_1501_, lean_object* v_inst_1502_, lean_object* v_t_1503_, lean_object* v_k_1504_, lean_object* v_h_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1501_, v_k_1504_, v_t_1503_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT___redArg(lean_object* v_cmp_1507_, lean_object* v_t_1508_, lean_object* v_k_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1507_, v_k_1509_, v_t_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT(lean_object* v_00_u03b1_1511_, lean_object* v_00_u03b2_1512_, lean_object* v_cmp_1513_, lean_object* v_inst_1514_, lean_object* v_t_1515_, lean_object* v_k_1516_, lean_object* v_h_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1513_, v_k_1516_, v_t_1515_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE___redArg(lean_object* v_cmp_1519_, lean_object* v_t_1520_, lean_object* v_k_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1519_, v_k_1521_, v_t_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE(lean_object* v_00_u03b1_1523_, lean_object* v_00_u03b2_1524_, lean_object* v_cmp_1525_, lean_object* v_inst_1526_, lean_object* v_t_1527_, lean_object* v_k_1528_, lean_object* v_h_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1525_, v_k_1528_, v_t_1527_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT___redArg(lean_object* v_cmp_1531_, lean_object* v_t_1532_, lean_object* v_k_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1531_, v_k_1533_, v_t_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT(lean_object* v_00_u03b1_1535_, lean_object* v_00_u03b2_1536_, lean_object* v_cmp_1537_, lean_object* v_inst_1538_, lean_object* v_t_1539_, lean_object* v_k_1540_, lean_object* v_h_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1537_, v_k_1540_, v_t_1539_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1543_, lean_object* v_inst_1544_, lean_object* v_t_1545_, lean_object* v_k_1546_){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_box(0);
v___x_1548_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1543_, v_k_1546_, v___x_1547_, v_t_1545_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1552_, lean_object* v_inst_1553_, lean_object* v_t_1554_, lean_object* v_k_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Std_ExtDTreeMap_getKeyGE_x21___redArg(v_cmp_1552_, v_inst_1553_, v_t_1554_, v_k_1555_);
lean_dec(v_inst_1553_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1557_, lean_object* v_00_u03b2_1558_, lean_object* v_cmp_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v_t_1562_, lean_object* v_k_1563_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_box(0);
v___x_1565_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1559_, v_k_1563_, v___x_1564_, v_t_1562_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1569_, lean_object* v_00_u03b2_1570_, lean_object* v_cmp_1571_, lean_object* v_inst_1572_, lean_object* v_inst_1573_, lean_object* v_t_1574_, lean_object* v_k_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Std_ExtDTreeMap_getKeyGE_x21(v_00_u03b1_1569_, v_00_u03b2_1570_, v_cmp_1571_, v_inst_1572_, v_inst_1573_, v_t_1574_, v_k_1575_);
lean_dec(v_inst_1573_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1577_, lean_object* v_inst_1578_, lean_object* v_t_1579_, lean_object* v_k_1580_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = lean_box(0);
v___x_1582_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1577_, v_k_1580_, v___x_1581_, v_t_1579_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1586_, lean_object* v_inst_1587_, lean_object* v_t_1588_, lean_object* v_k_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Std_ExtDTreeMap_getKeyGT_x21___redArg(v_cmp_1586_, v_inst_1587_, v_t_1588_, v_k_1589_);
lean_dec(v_inst_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1591_, lean_object* v_00_u03b2_1592_, lean_object* v_cmp_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_t_1596_, lean_object* v_k_1597_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_box(0);
v___x_1599_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1593_, v_k_1597_, v___x_1598_, v_t_1596_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1603_, lean_object* v_00_u03b2_1604_, lean_object* v_cmp_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_t_1608_, lean_object* v_k_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Std_ExtDTreeMap_getKeyGT_x21(v_00_u03b1_1603_, v_00_u03b2_1604_, v_cmp_1605_, v_inst_1606_, v_inst_1607_, v_t_1608_, v_k_1609_);
lean_dec(v_inst_1607_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1611_, lean_object* v_inst_1612_, lean_object* v_t_1613_, lean_object* v_k_1614_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_box(0);
v___x_1616_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1611_, v_k_1614_, v___x_1615_, v_t_1613_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1618_ = l_panic___redArg(v_inst_1612_, v___x_1617_);
return v___x_1618_;
}
else
{
lean_object* v_val_1619_; 
v_val_1619_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_val_1619_);
lean_dec_ref_known(v___x_1616_, 1);
return v_val_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1620_, lean_object* v_inst_1621_, lean_object* v_t_1622_, lean_object* v_k_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Std_ExtDTreeMap_getKeyLE_x21___redArg(v_cmp_1620_, v_inst_1621_, v_t_1622_, v_k_1623_);
lean_dec(v_inst_1621_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1625_, lean_object* v_00_u03b2_1626_, lean_object* v_cmp_1627_, lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_t_1630_, lean_object* v_k_1631_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = lean_box(0);
v___x_1633_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1627_, v_k_1631_, v___x_1632_, v_t_1630_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1635_ = l_panic___redArg(v_inst_1629_, v___x_1634_);
return v___x_1635_;
}
else
{
lean_object* v_val_1636_; 
v_val_1636_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_val_1636_);
lean_dec_ref_known(v___x_1633_, 1);
return v_val_1636_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1637_, lean_object* v_00_u03b2_1638_, lean_object* v_cmp_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_t_1642_, lean_object* v_k_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Std_ExtDTreeMap_getKeyLE_x21(v_00_u03b1_1637_, v_00_u03b2_1638_, v_cmp_1639_, v_inst_1640_, v_inst_1641_, v_t_1642_, v_k_1643_);
lean_dec(v_inst_1641_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1645_, lean_object* v_inst_1646_, lean_object* v_t_1647_, lean_object* v_k_1648_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = lean_box(0);
v___x_1650_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1645_, v_k_1648_, v___x_1649_, v_t_1647_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1652_ = l_panic___redArg(v_inst_1646_, v___x_1651_);
return v___x_1652_;
}
else
{
lean_object* v_val_1653_; 
v_val_1653_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_val_1653_);
lean_dec_ref_known(v___x_1650_, 1);
return v_val_1653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1654_, lean_object* v_inst_1655_, lean_object* v_t_1656_, lean_object* v_k_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Std_ExtDTreeMap_getKeyLT_x21___redArg(v_cmp_1654_, v_inst_1655_, v_t_1656_, v_k_1657_);
lean_dec(v_inst_1655_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1659_, lean_object* v_00_u03b2_1660_, lean_object* v_cmp_1661_, lean_object* v_inst_1662_, lean_object* v_inst_1663_, lean_object* v_t_1664_, lean_object* v_k_1665_){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_box(0);
v___x_1667_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1661_, v_k_1665_, v___x_1666_, v_t_1664_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1669_ = l_panic___redArg(v_inst_1663_, v___x_1668_);
return v___x_1669_;
}
else
{
lean_object* v_val_1670_; 
v_val_1670_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_val_1670_);
lean_dec_ref_known(v___x_1667_, 1);
return v_val_1670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1671_, lean_object* v_00_u03b2_1672_, lean_object* v_cmp_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_t_1676_, lean_object* v_k_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Std_ExtDTreeMap_getKeyLT_x21(v_00_u03b1_1671_, v_00_u03b2_1672_, v_cmp_1673_, v_inst_1674_, v_inst_1675_, v_t_1676_, v_k_1677_);
lean_dec(v_inst_1675_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___redArg(lean_object* v_cmp_1679_, lean_object* v_t_1680_, lean_object* v_k_1681_, lean_object* v_fallback_1682_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_box(0);
v___x_1684_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1679_, v_k_1681_, v___x_1683_, v_t_1680_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_inc(v_fallback_1682_);
return v_fallback_1682_;
}
else
{
lean_object* v_val_1685_; 
v_val_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_val_1685_);
lean_dec_ref_known(v___x_1684_, 1);
return v_val_1685_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1686_, lean_object* v_t_1687_, lean_object* v_k_1688_, lean_object* v_fallback_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_ExtDTreeMap_getKeyGED___redArg(v_cmp_1686_, v_t_1687_, v_k_1688_, v_fallback_1689_);
lean_dec(v_fallback_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED(lean_object* v_00_u03b1_1691_, lean_object* v_00_u03b2_1692_, lean_object* v_cmp_1693_, lean_object* v_inst_1694_, lean_object* v_t_1695_, lean_object* v_k_1696_, lean_object* v_fallback_1697_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = lean_box(0);
v___x_1699_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1693_, v_k_1696_, v___x_1698_, v_t_1695_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_inc(v_fallback_1697_);
return v_fallback_1697_;
}
else
{
lean_object* v_val_1700_; 
v_val_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v___x_1699_, 1);
return v_val_1700_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1701_, lean_object* v_00_u03b2_1702_, lean_object* v_cmp_1703_, lean_object* v_inst_1704_, lean_object* v_t_1705_, lean_object* v_k_1706_, lean_object* v_fallback_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Std_ExtDTreeMap_getKeyGED(v_00_u03b1_1701_, v_00_u03b2_1702_, v_cmp_1703_, v_inst_1704_, v_t_1705_, v_k_1706_, v_fallback_1707_);
lean_dec(v_fallback_1707_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1709_, lean_object* v_t_1710_, lean_object* v_k_1711_, lean_object* v_fallback_1712_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_box(0);
v___x_1714_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1709_, v_k_1711_, v___x_1713_, v_t_1710_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_inc(v_fallback_1712_);
return v_fallback_1712_;
}
else
{
lean_object* v_val_1715_; 
v_val_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_val_1715_);
lean_dec_ref_known(v___x_1714_, 1);
return v_val_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1716_, lean_object* v_t_1717_, lean_object* v_k_1718_, lean_object* v_fallback_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Std_ExtDTreeMap_getKeyGTD___redArg(v_cmp_1716_, v_t_1717_, v_k_1718_, v_fallback_1719_);
lean_dec(v_fallback_1719_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD(lean_object* v_00_u03b1_1721_, lean_object* v_00_u03b2_1722_, lean_object* v_cmp_1723_, lean_object* v_inst_1724_, lean_object* v_t_1725_, lean_object* v_k_1726_, lean_object* v_fallback_1727_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_box(0);
v___x_1729_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1723_, v_k_1726_, v___x_1728_, v_t_1725_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_inc(v_fallback_1727_);
return v_fallback_1727_;
}
else
{
lean_object* v_val_1730_; 
v_val_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_val_1730_);
lean_dec_ref_known(v___x_1729_, 1);
return v_val_1730_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1731_, lean_object* v_00_u03b2_1732_, lean_object* v_cmp_1733_, lean_object* v_inst_1734_, lean_object* v_t_1735_, lean_object* v_k_1736_, lean_object* v_fallback_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Std_ExtDTreeMap_getKeyGTD(v_00_u03b1_1731_, v_00_u03b2_1732_, v_cmp_1733_, v_inst_1734_, v_t_1735_, v_k_1736_, v_fallback_1737_);
lean_dec(v_fallback_1737_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___redArg(lean_object* v_cmp_1739_, lean_object* v_t_1740_, lean_object* v_k_1741_, lean_object* v_fallback_1742_){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_box(0);
v___x_1744_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1739_, v_k_1741_, v___x_1743_, v_t_1740_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_inc(v_fallback_1742_);
return v_fallback_1742_;
}
else
{
lean_object* v_val_1745_; 
v_val_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_val_1745_);
lean_dec_ref_known(v___x_1744_, 1);
return v_val_1745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1746_, lean_object* v_t_1747_, lean_object* v_k_1748_, lean_object* v_fallback_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Std_ExtDTreeMap_getKeyLED___redArg(v_cmp_1746_, v_t_1747_, v_k_1748_, v_fallback_1749_);
lean_dec(v_fallback_1749_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED(lean_object* v_00_u03b1_1751_, lean_object* v_00_u03b2_1752_, lean_object* v_cmp_1753_, lean_object* v_inst_1754_, lean_object* v_t_1755_, lean_object* v_k_1756_, lean_object* v_fallback_1757_){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_box(0);
v___x_1759_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1753_, v_k_1756_, v___x_1758_, v_t_1755_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_inc(v_fallback_1757_);
return v_fallback_1757_;
}
else
{
lean_object* v_val_1760_; 
v_val_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_val_1760_);
lean_dec_ref_known(v___x_1759_, 1);
return v_val_1760_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1761_, lean_object* v_00_u03b2_1762_, lean_object* v_cmp_1763_, lean_object* v_inst_1764_, lean_object* v_t_1765_, lean_object* v_k_1766_, lean_object* v_fallback_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Std_ExtDTreeMap_getKeyLED(v_00_u03b1_1761_, v_00_u03b2_1762_, v_cmp_1763_, v_inst_1764_, v_t_1765_, v_k_1766_, v_fallback_1767_);
lean_dec(v_fallback_1767_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1769_, lean_object* v_t_1770_, lean_object* v_k_1771_, lean_object* v_fallback_1772_){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_box(0);
v___x_1774_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1769_, v_k_1771_, v___x_1773_, v_t_1770_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_inc(v_fallback_1772_);
return v_fallback_1772_;
}
else
{
lean_object* v_val_1775_; 
v_val_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_val_1775_);
lean_dec_ref_known(v___x_1774_, 1);
return v_val_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1776_, lean_object* v_t_1777_, lean_object* v_k_1778_, lean_object* v_fallback_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Std_ExtDTreeMap_getKeyLTD___redArg(v_cmp_1776_, v_t_1777_, v_k_1778_, v_fallback_1779_);
lean_dec(v_fallback_1779_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD(lean_object* v_00_u03b1_1781_, lean_object* v_00_u03b2_1782_, lean_object* v_cmp_1783_, lean_object* v_inst_1784_, lean_object* v_t_1785_, lean_object* v_k_1786_, lean_object* v_fallback_1787_){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_box(0);
v___x_1789_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1783_, v_k_1786_, v___x_1788_, v_t_1785_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_inc(v_fallback_1787_);
return v_fallback_1787_;
}
else
{
lean_object* v_val_1790_; 
v_val_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_val_1790_);
lean_dec_ref_known(v___x_1789_, 1);
return v_val_1790_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1791_, lean_object* v_00_u03b2_1792_, lean_object* v_cmp_1793_, lean_object* v_inst_1794_, lean_object* v_t_1795_, lean_object* v_k_1796_, lean_object* v_fallback_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Std_ExtDTreeMap_getKeyLTD(v_00_u03b1_1791_, v_00_u03b2_1792_, v_cmp_1793_, v_inst_1794_, v_t_1795_, v_k_1796_, v_fallback_1797_);
lean_dec(v_fallback_1797_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1799_, lean_object* v_t_1800_, lean_object* v_a_1801_, lean_object* v_b_1802_){
_start:
{
lean_object* v___x_1803_; 
lean_inc(v_a_1801_);
lean_inc(v_t_1800_);
lean_inc_ref(v_cmp_1799_);
v___x_1803_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1799_, v_t_1800_, v_a_1801_);
if (lean_obj_tag(v___x_1803_) == 0)
{
uint8_t v___x_1804_; 
lean_inc(v_t_1800_);
lean_inc(v_a_1801_);
lean_inc_ref(v_cmp_1799_);
v___x_1804_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1799_, v_a_1801_, v_t_1800_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1799_, v_a_1801_, v_b_1802_, v_t_1800_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1803_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; 
lean_dec(v_b_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_cmp_1799_);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1803_);
lean_ctor_set(v___x_1807_, 1, v_t_1800_);
return v___x_1807_;
}
}
else
{
lean_object* v___x_1808_; 
lean_dec(v_b_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_cmp_1799_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1803_);
lean_ctor_set(v___x_1808_, 1, v_t_1800_);
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1809_, lean_object* v_cmp_1810_, lean_object* v_00_u03b2_1811_, lean_object* v_inst_1812_, lean_object* v_t_1813_, lean_object* v_a_1814_, lean_object* v_b_1815_){
_start:
{
lean_object* v___x_1816_; 
lean_inc(v_a_1814_);
lean_inc(v_t_1813_);
lean_inc_ref(v_cmp_1810_);
v___x_1816_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1810_, v_t_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1816_) == 0)
{
uint8_t v___x_1817_; 
lean_inc(v_t_1813_);
lean_inc(v_a_1814_);
lean_inc_ref(v_cmp_1810_);
v___x_1817_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1810_, v_a_1814_, v_t_1813_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1810_, v_a_1814_, v_b_1815_, v_t_1813_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1816_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
return v___x_1819_;
}
else
{
lean_object* v___x_1820_; 
lean_dec(v_b_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_cmp_1810_);
v___x_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1816_);
lean_ctor_set(v___x_1820_, 1, v_t_1813_);
return v___x_1820_;
}
}
else
{
lean_object* v___x_1821_; 
lean_dec(v_b_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_cmp_1810_);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1816_);
lean_ctor_set(v___x_1821_, 1, v_t_1813_);
return v___x_1821_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x3f___redArg(lean_object* v_cmp_1822_, lean_object* v_t_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1822_, v_t_1823_, v_a_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x3f(lean_object* v_00_u03b1_1826_, lean_object* v_cmp_1827_, lean_object* v_00_u03b2_1828_, lean_object* v_inst_1829_, lean_object* v_t_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1827_, v_t_1830_, v_a_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get___redArg(lean_object* v_cmp_1833_, lean_object* v_t_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1833_, v_t_1834_, v_a_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get(lean_object* v_00_u03b1_1837_, lean_object* v_cmp_1838_, lean_object* v_00_u03b2_1839_, lean_object* v_inst_1840_, lean_object* v_t_1841_, lean_object* v_a_1842_, lean_object* v_h_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1838_, v_t_1841_, v_a_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___redArg(lean_object* v_cmp_1845_, lean_object* v_inst_1846_, lean_object* v_t_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1845_, v_inst_1846_, v_t_1847_, v_a_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___redArg___boxed(lean_object* v_cmp_1850_, lean_object* v_inst_1851_, lean_object* v_t_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Std_ExtDTreeMap_Const_get_x21___redArg(v_cmp_1850_, v_inst_1851_, v_t_1852_, v_a_1853_);
lean_dec(v_inst_1851_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21(lean_object* v_00_u03b1_1855_, lean_object* v_cmp_1856_, lean_object* v_00_u03b2_1857_, lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_t_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1856_, v_inst_1859_, v_t_1860_, v_a_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___boxed(lean_object* v_00_u03b1_1863_, lean_object* v_cmp_1864_, lean_object* v_00_u03b2_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_t_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Std_ExtDTreeMap_Const_get_x21(v_00_u03b1_1863_, v_cmp_1864_, v_00_u03b2_1865_, v_inst_1866_, v_inst_1867_, v_t_1868_, v_a_1869_);
lean_dec(v_inst_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___redArg(lean_object* v_cmp_1871_, lean_object* v_t_1872_, lean_object* v_a_1873_, lean_object* v_fallback_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1871_, v_t_1872_, v_a_1873_, v_fallback_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___redArg___boxed(lean_object* v_cmp_1876_, lean_object* v_t_1877_, lean_object* v_a_1878_, lean_object* v_fallback_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Std_ExtDTreeMap_Const_getD___redArg(v_cmp_1876_, v_t_1877_, v_a_1878_, v_fallback_1879_);
lean_dec(v_fallback_1879_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD(lean_object* v_00_u03b1_1881_, lean_object* v_cmp_1882_, lean_object* v_00_u03b2_1883_, lean_object* v_inst_1884_, lean_object* v_t_1885_, lean_object* v_a_1886_, lean_object* v_fallback_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1882_, v_t_1885_, v_a_1886_, v_fallback_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___boxed(lean_object* v_00_u03b1_1889_, lean_object* v_cmp_1890_, lean_object* v_00_u03b2_1891_, lean_object* v_inst_1892_, lean_object* v_t_1893_, lean_object* v_a_1894_, lean_object* v_fallback_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Std_ExtDTreeMap_Const_getD(v_00_u03b1_1889_, v_cmp_1890_, v_00_u03b2_1891_, v_inst_1892_, v_t_1893_, v_a_1894_, v_fallback_1895_);
lean_dec(v_fallback_1895_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(lean_object* v_t_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(v_t_1899_);
lean_dec(v_t_1899_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f(lean_object* v_00_u03b1_1901_, lean_object* v_cmp_1902_, lean_object* v_00_u03b2_1903_, lean_object* v_inst_1904_, lean_object* v_t_1905_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1907_, lean_object* v_cmp_1908_, lean_object* v_00_u03b2_1909_, lean_object* v_inst_1910_, lean_object* v_t_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Std_ExtDTreeMap_Const_minEntry_x3f(v_00_u03b1_1907_, v_cmp_1908_, v_00_u03b2_1909_, v_inst_1910_, v_t_1911_);
lean_dec(v_t_1911_);
lean_dec_ref(v_cmp_1908_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___redArg(lean_object* v_t_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___redArg___boxed(lean_object* v_t_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Std_ExtDTreeMap_Const_minEntry___redArg(v_t_1915_);
lean_dec(v_t_1915_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry(lean_object* v_00_u03b1_1917_, lean_object* v_cmp_1918_, lean_object* v_00_u03b2_1919_, lean_object* v_inst_1920_, lean_object* v_t_1921_, lean_object* v_h_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___boxed(lean_object* v_00_u03b1_1924_, lean_object* v_cmp_1925_, lean_object* v_00_u03b2_1926_, lean_object* v_inst_1927_, lean_object* v_t_1928_, lean_object* v_h_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Std_ExtDTreeMap_Const_minEntry(v_00_u03b1_1924_, v_cmp_1925_, v_00_u03b2_1926_, v_inst_1927_, v_t_1928_, v_h_1929_);
lean_dec(v_t_1928_);
lean_dec_ref(v_cmp_1925_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(lean_object* v_inst_1931_, lean_object* v_t_1932_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1931_, v_t_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1934_, lean_object* v_t_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(v_inst_1934_, v_t_1935_);
lean_dec(v_t_1935_);
lean_dec_ref(v_inst_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21(lean_object* v_00_u03b1_1937_, lean_object* v_cmp_1938_, lean_object* v_00_u03b2_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_t_1942_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1941_, v_t_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1944_, lean_object* v_cmp_1945_, lean_object* v_00_u03b2_1946_, lean_object* v_inst_1947_, lean_object* v_inst_1948_, lean_object* v_t_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Std_ExtDTreeMap_Const_minEntry_x21(v_00_u03b1_1944_, v_cmp_1945_, v_00_u03b2_1946_, v_inst_1947_, v_inst_1948_, v_t_1949_);
lean_dec(v_t_1949_);
lean_dec_ref(v_inst_1948_);
lean_dec_ref(v_cmp_1945_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___redArg(lean_object* v_t_1951_, lean_object* v_fallback_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1951_, v_fallback_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___redArg___boxed(lean_object* v_t_1954_, lean_object* v_fallback_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Std_ExtDTreeMap_Const_minEntryD___redArg(v_t_1954_, v_fallback_1955_);
lean_dec_ref(v_fallback_1955_);
lean_dec(v_t_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD(lean_object* v_00_u03b1_1957_, lean_object* v_cmp_1958_, lean_object* v_00_u03b2_1959_, lean_object* v_inst_1960_, lean_object* v_t_1961_, lean_object* v_fallback_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1961_, v_fallback_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___boxed(lean_object* v_00_u03b1_1964_, lean_object* v_cmp_1965_, lean_object* v_00_u03b2_1966_, lean_object* v_inst_1967_, lean_object* v_t_1968_, lean_object* v_fallback_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Std_ExtDTreeMap_Const_minEntryD(v_00_u03b1_1964_, v_cmp_1965_, v_00_u03b2_1966_, v_inst_1967_, v_t_1968_, v_fallback_1969_);
lean_dec_ref(v_fallback_1969_);
lean_dec(v_t_1968_);
lean_dec_ref(v_cmp_1965_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(lean_object* v_t_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(v_t_1973_);
lean_dec(v_t_1973_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f(lean_object* v_00_u03b1_1975_, lean_object* v_cmp_1976_, lean_object* v_00_u03b2_1977_, lean_object* v_inst_1978_, lean_object* v_t_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1981_, lean_object* v_cmp_1982_, lean_object* v_00_u03b2_1983_, lean_object* v_inst_1984_, lean_object* v_t_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Std_ExtDTreeMap_Const_maxEntry_x3f(v_00_u03b1_1981_, v_cmp_1982_, v_00_u03b2_1983_, v_inst_1984_, v_t_1985_);
lean_dec(v_t_1985_);
lean_dec_ref(v_cmp_1982_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___redArg(lean_object* v_t_1987_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___redArg___boxed(lean_object* v_t_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Std_ExtDTreeMap_Const_maxEntry___redArg(v_t_1989_);
lean_dec(v_t_1989_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry(lean_object* v_00_u03b1_1991_, lean_object* v_cmp_1992_, lean_object* v_00_u03b2_1993_, lean_object* v_inst_1994_, lean_object* v_t_1995_, lean_object* v_h_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1995_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___boxed(lean_object* v_00_u03b1_1998_, lean_object* v_cmp_1999_, lean_object* v_00_u03b2_2000_, lean_object* v_inst_2001_, lean_object* v_t_2002_, lean_object* v_h_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Std_ExtDTreeMap_Const_maxEntry(v_00_u03b1_1998_, v_cmp_1999_, v_00_u03b2_2000_, v_inst_2001_, v_t_2002_, v_h_2003_);
lean_dec(v_t_2002_);
lean_dec_ref(v_cmp_1999_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(lean_object* v_inst_2005_, lean_object* v_t_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_2005_, v_t_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_2008_, lean_object* v_t_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(v_inst_2008_, v_t_2009_);
lean_dec(v_t_2009_);
lean_dec_ref(v_inst_2008_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21(lean_object* v_00_u03b1_2011_, lean_object* v_cmp_2012_, lean_object* v_00_u03b2_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_t_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_2015_, v_t_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_2018_, lean_object* v_cmp_2019_, lean_object* v_00_u03b2_2020_, lean_object* v_inst_2021_, lean_object* v_inst_2022_, lean_object* v_t_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Std_ExtDTreeMap_Const_maxEntry_x21(v_00_u03b1_2018_, v_cmp_2019_, v_00_u03b2_2020_, v_inst_2021_, v_inst_2022_, v_t_2023_);
lean_dec(v_t_2023_);
lean_dec_ref(v_inst_2022_);
lean_dec_ref(v_cmp_2019_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___redArg(lean_object* v_t_2025_, lean_object* v_fallback_2026_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_2025_, v_fallback_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___redArg___boxed(lean_object* v_t_2028_, lean_object* v_fallback_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Std_ExtDTreeMap_Const_maxEntryD___redArg(v_t_2028_, v_fallback_2029_);
lean_dec_ref(v_fallback_2029_);
lean_dec(v_t_2028_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD(lean_object* v_00_u03b1_2031_, lean_object* v_cmp_2032_, lean_object* v_00_u03b2_2033_, lean_object* v_inst_2034_, lean_object* v_t_2035_, lean_object* v_fallback_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_2035_, v_fallback_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___boxed(lean_object* v_00_u03b1_2038_, lean_object* v_cmp_2039_, lean_object* v_00_u03b2_2040_, lean_object* v_inst_2041_, lean_object* v_t_2042_, lean_object* v_fallback_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Std_ExtDTreeMap_Const_maxEntryD(v_00_u03b1_2038_, v_cmp_2039_, v_00_u03b2_2040_, v_inst_2041_, v_t_2042_, v_fallback_2043_);
lean_dec_ref(v_fallback_2043_);
lean_dec(v_t_2042_);
lean_dec_ref(v_cmp_2039_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(lean_object* v_t_2045_, lean_object* v_n_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_2045_, v_n_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_2048_, lean_object* v_n_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(v_t_2048_, v_n_2049_);
lean_dec(v_t_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_2051_, lean_object* v_cmp_2052_, lean_object* v_00_u03b2_2053_, lean_object* v_inst_2054_, lean_object* v_t_2055_, lean_object* v_n_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_2055_, v_n_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_2058_, lean_object* v_cmp_2059_, lean_object* v_00_u03b2_2060_, lean_object* v_inst_2061_, lean_object* v_t_2062_, lean_object* v_n_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(v_00_u03b1_2058_, v_cmp_2059_, v_00_u03b2_2060_, v_inst_2061_, v_t_2062_, v_n_2063_);
lean_dec(v_t_2062_);
lean_dec_ref(v_cmp_2059_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(lean_object* v_t_2065_, lean_object* v_n_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_2065_, v_n_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___redArg___boxed(lean_object* v_t_2068_, lean_object* v_n_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(v_t_2068_, v_n_2069_);
lean_dec(v_t_2068_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx(lean_object* v_00_u03b1_2071_, lean_object* v_cmp_2072_, lean_object* v_00_u03b2_2073_, lean_object* v_inst_2074_, lean_object* v_t_2075_, lean_object* v_n_2076_, lean_object* v_h_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_2075_, v_n_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_2079_, lean_object* v_cmp_2080_, lean_object* v_00_u03b2_2081_, lean_object* v_inst_2082_, lean_object* v_t_2083_, lean_object* v_n_2084_, lean_object* v_h_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Std_ExtDTreeMap_Const_entryAtIdx(v_00_u03b1_2079_, v_cmp_2080_, v_00_u03b2_2081_, v_inst_2082_, v_t_2083_, v_n_2084_, v_h_2085_);
lean_dec(v_t_2083_);
lean_dec_ref(v_cmp_2080_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(lean_object* v_inst_2087_, lean_object* v_t_2088_, lean_object* v_n_2089_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_2087_, v_t_2088_, v_n_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_2091_, lean_object* v_t_2092_, lean_object* v_n_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(v_inst_2091_, v_t_2092_, v_n_2093_);
lean_dec(v_t_2092_);
lean_dec_ref(v_inst_2091_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21(lean_object* v_00_u03b1_2095_, lean_object* v_cmp_2096_, lean_object* v_00_u03b2_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_t_2100_, lean_object* v_n_2101_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_2099_, v_t_2100_, v_n_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_2103_, lean_object* v_cmp_2104_, lean_object* v_00_u03b2_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_t_2108_, lean_object* v_n_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x21(v_00_u03b1_2103_, v_cmp_2104_, v_00_u03b2_2105_, v_inst_2106_, v_inst_2107_, v_t_2108_, v_n_2109_);
lean_dec(v_t_2108_);
lean_dec_ref(v_inst_2107_);
lean_dec_ref(v_cmp_2104_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(lean_object* v_t_2111_, lean_object* v_n_2112_, lean_object* v_fallback_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_2111_, v_n_2112_, v_fallback_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_2115_, lean_object* v_n_2116_, lean_object* v_fallback_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(v_t_2115_, v_n_2116_, v_fallback_2117_);
lean_dec_ref(v_fallback_2117_);
lean_dec(v_t_2115_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD(lean_object* v_00_u03b1_2119_, lean_object* v_cmp_2120_, lean_object* v_00_u03b2_2121_, lean_object* v_inst_2122_, lean_object* v_t_2123_, lean_object* v_n_2124_, lean_object* v_fallback_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_2123_, v_n_2124_, v_fallback_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_2127_, lean_object* v_cmp_2128_, lean_object* v_00_u03b2_2129_, lean_object* v_inst_2130_, lean_object* v_t_2131_, lean_object* v_n_2132_, lean_object* v_fallback_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Std_ExtDTreeMap_Const_entryAtIdxD(v_00_u03b1_2127_, v_cmp_2128_, v_00_u03b2_2129_, v_inst_2130_, v_t_2131_, v_n_2132_, v_fallback_2133_);
lean_dec_ref(v_fallback_2133_);
lean_dec(v_t_2131_);
lean_dec_ref(v_cmp_2128_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_2135_, lean_object* v_t_2136_, lean_object* v_k_2137_){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = lean_box(0);
v___x_2139_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2135_, v_k_2137_, v___x_2138_, v_t_2136_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x3f(lean_object* v_00_u03b1_2140_, lean_object* v_cmp_2141_, lean_object* v_00_u03b2_2142_, lean_object* v_inst_2143_, lean_object* v_t_2144_, lean_object* v_k_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_box(0);
v___x_2147_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2141_, v_k_2145_, v___x_2146_, v_t_2144_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_2148_, lean_object* v_t_2149_, lean_object* v_k_2150_){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = lean_box(0);
v___x_2152_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2148_, v_k_2150_, v___x_2151_, v_t_2149_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x3f(lean_object* v_00_u03b1_2153_, lean_object* v_cmp_2154_, lean_object* v_00_u03b2_2155_, lean_object* v_inst_2156_, lean_object* v_t_2157_, lean_object* v_k_2158_){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_box(0);
v___x_2160_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2154_, v_k_2158_, v___x_2159_, v_t_2157_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_2161_, lean_object* v_t_2162_, lean_object* v_k_2163_){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_box(0);
v___x_2165_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2161_, v_k_2163_, v___x_2164_, v_t_2162_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x3f(lean_object* v_00_u03b1_2166_, lean_object* v_cmp_2167_, lean_object* v_00_u03b2_2168_, lean_object* v_inst_2169_, lean_object* v_t_2170_, lean_object* v_k_2171_){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_box(0);
v___x_2173_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2167_, v_k_2171_, v___x_2172_, v_t_2170_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_2174_, lean_object* v_t_2175_, lean_object* v_k_2176_){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = lean_box(0);
v___x_2178_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2174_, v_k_2176_, v___x_2177_, v_t_2175_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x3f(lean_object* v_00_u03b1_2179_, lean_object* v_cmp_2180_, lean_object* v_00_u03b2_2181_, lean_object* v_inst_2182_, lean_object* v_t_2183_, lean_object* v_k_2184_){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = lean_box(0);
v___x_2186_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2180_, v_k_2184_, v___x_2185_, v_t_2183_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE___redArg(lean_object* v_cmp_2187_, lean_object* v_t_2188_, lean_object* v_k_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_2187_, v_k_2189_, v_t_2188_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE(lean_object* v_00_u03b1_2191_, lean_object* v_cmp_2192_, lean_object* v_00_u03b2_2193_, lean_object* v_inst_2194_, lean_object* v_t_2195_, lean_object* v_k_2196_, lean_object* v_h_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_2192_, v_k_2196_, v_t_2195_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT___redArg(lean_object* v_cmp_2199_, lean_object* v_t_2200_, lean_object* v_k_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_2199_, v_k_2201_, v_t_2200_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT(lean_object* v_00_u03b1_2203_, lean_object* v_cmp_2204_, lean_object* v_00_u03b2_2205_, lean_object* v_inst_2206_, lean_object* v_t_2207_, lean_object* v_k_2208_, lean_object* v_h_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_2204_, v_k_2208_, v_t_2207_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE___redArg(lean_object* v_cmp_2211_, lean_object* v_t_2212_, lean_object* v_k_2213_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_2211_, v_k_2213_, v_t_2212_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE(lean_object* v_00_u03b1_2215_, lean_object* v_cmp_2216_, lean_object* v_00_u03b2_2217_, lean_object* v_inst_2218_, lean_object* v_t_2219_, lean_object* v_k_2220_, lean_object* v_h_2221_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_2216_, v_k_2220_, v_t_2219_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT___redArg(lean_object* v_cmp_2223_, lean_object* v_t_2224_, lean_object* v_k_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_2223_, v_k_2225_, v_t_2224_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT(lean_object* v_00_u03b1_2227_, lean_object* v_cmp_2228_, lean_object* v_00_u03b2_2229_, lean_object* v_inst_2230_, lean_object* v_t_2231_, lean_object* v_k_2232_, lean_object* v_h_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_2228_, v_k_2232_, v_t_2231_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg(lean_object* v_cmp_2235_, lean_object* v_inst_2236_, lean_object* v_t_2237_, lean_object* v_k_2238_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_box(0);
v___x_2240_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2235_, v_k_2238_, v___x_2239_, v_t_2237_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2242_ = l_panic___redArg(v_inst_2236_, v___x_2241_);
return v___x_2242_;
}
else
{
lean_object* v_val_2243_; 
v_val_2243_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_val_2243_);
lean_dec_ref_known(v___x_2240_, 1);
return v_val_2243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_2244_, lean_object* v_inst_2245_, lean_object* v_t_2246_, lean_object* v_k_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg(v_cmp_2244_, v_inst_2245_, v_t_2246_, v_k_2247_);
lean_dec_ref(v_inst_2245_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21(lean_object* v_00_u03b1_2249_, lean_object* v_cmp_2250_, lean_object* v_00_u03b2_2251_, lean_object* v_inst_2252_, lean_object* v_inst_2253_, lean_object* v_t_2254_, lean_object* v_k_2255_){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_box(0);
v___x_2257_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2250_, v_k_2255_, v___x_2256_, v_t_2254_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2259_ = l_panic___redArg(v_inst_2253_, v___x_2258_);
return v___x_2259_;
}
else
{
lean_object* v_val_2260_; 
v_val_2260_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_val_2260_);
lean_dec_ref_known(v___x_2257_, 1);
return v_val_2260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_2261_, lean_object* v_cmp_2262_, lean_object* v_00_u03b2_2263_, lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_t_2266_, lean_object* v_k_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Std_ExtDTreeMap_Const_getEntryGE_x21(v_00_u03b1_2261_, v_cmp_2262_, v_00_u03b2_2263_, v_inst_2264_, v_inst_2265_, v_t_2266_, v_k_2267_);
lean_dec_ref(v_inst_2265_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(lean_object* v_cmp_2269_, lean_object* v_inst_2270_, lean_object* v_t_2271_, lean_object* v_k_2272_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2269_, v_k_2272_, v___x_2273_, v_t_2271_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2276_ = l_panic___redArg(v_inst_2270_, v___x_2275_);
return v___x_2276_;
}
else
{
lean_object* v_val_2277_; 
v_val_2277_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_val_2277_);
lean_dec_ref_known(v___x_2274_, 1);
return v_val_2277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_2278_, lean_object* v_inst_2279_, lean_object* v_t_2280_, lean_object* v_k_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(v_cmp_2278_, v_inst_2279_, v_t_2280_, v_k_2281_);
lean_dec_ref(v_inst_2279_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21(lean_object* v_00_u03b1_2283_, lean_object* v_cmp_2284_, lean_object* v_00_u03b2_2285_, lean_object* v_inst_2286_, lean_object* v_inst_2287_, lean_object* v_t_2288_, lean_object* v_k_2289_){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_box(0);
v___x_2291_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2284_, v_k_2289_, v___x_2290_, v_t_2288_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2293_ = l_panic___redArg(v_inst_2287_, v___x_2292_);
return v___x_2293_;
}
else
{
lean_object* v_val_2294_; 
v_val_2294_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_val_2294_);
lean_dec_ref_known(v___x_2291_, 1);
return v_val_2294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_2295_, lean_object* v_cmp_2296_, lean_object* v_00_u03b2_2297_, lean_object* v_inst_2298_, lean_object* v_inst_2299_, lean_object* v_t_2300_, lean_object* v_k_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Std_ExtDTreeMap_Const_getEntryGT_x21(v_00_u03b1_2295_, v_cmp_2296_, v_00_u03b2_2297_, v_inst_2298_, v_inst_2299_, v_t_2300_, v_k_2301_);
lean_dec_ref(v_inst_2299_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(lean_object* v_cmp_2303_, lean_object* v_inst_2304_, lean_object* v_t_2305_, lean_object* v_k_2306_){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = lean_box(0);
v___x_2308_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2303_, v_k_2306_, v___x_2307_, v_t_2305_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2310_ = l_panic___redArg(v_inst_2304_, v___x_2309_);
return v___x_2310_;
}
else
{
lean_object* v_val_2311_; 
v_val_2311_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_val_2311_);
lean_dec_ref_known(v___x_2308_, 1);
return v_val_2311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_2312_, lean_object* v_inst_2313_, lean_object* v_t_2314_, lean_object* v_k_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(v_cmp_2312_, v_inst_2313_, v_t_2314_, v_k_2315_);
lean_dec_ref(v_inst_2313_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21(lean_object* v_00_u03b1_2317_, lean_object* v_cmp_2318_, lean_object* v_00_u03b2_2319_, lean_object* v_inst_2320_, lean_object* v_inst_2321_, lean_object* v_t_2322_, lean_object* v_k_2323_){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_box(0);
v___x_2325_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2318_, v_k_2323_, v___x_2324_, v_t_2322_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2327_ = l_panic___redArg(v_inst_2321_, v___x_2326_);
return v___x_2327_;
}
else
{
lean_object* v_val_2328_; 
v_val_2328_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_val_2328_);
lean_dec_ref_known(v___x_2325_, 1);
return v_val_2328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2329_, lean_object* v_cmp_2330_, lean_object* v_00_u03b2_2331_, lean_object* v_inst_2332_, lean_object* v_inst_2333_, lean_object* v_t_2334_, lean_object* v_k_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Std_ExtDTreeMap_Const_getEntryLE_x21(v_00_u03b1_2329_, v_cmp_2330_, v_00_u03b2_2331_, v_inst_2332_, v_inst_2333_, v_t_2334_, v_k_2335_);
lean_dec_ref(v_inst_2333_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(lean_object* v_cmp_2337_, lean_object* v_inst_2338_, lean_object* v_t_2339_, lean_object* v_k_2340_){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = lean_box(0);
v___x_2342_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2337_, v_k_2340_, v___x_2341_, v_t_2339_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2344_ = l_panic___redArg(v_inst_2338_, v___x_2343_);
return v___x_2344_;
}
else
{
lean_object* v_val_2345_; 
v_val_2345_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_val_2345_);
lean_dec_ref_known(v___x_2342_, 1);
return v_val_2345_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_2346_, lean_object* v_inst_2347_, lean_object* v_t_2348_, lean_object* v_k_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(v_cmp_2346_, v_inst_2347_, v_t_2348_, v_k_2349_);
lean_dec_ref(v_inst_2347_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21(lean_object* v_00_u03b1_2351_, lean_object* v_cmp_2352_, lean_object* v_00_u03b2_2353_, lean_object* v_inst_2354_, lean_object* v_inst_2355_, lean_object* v_t_2356_, lean_object* v_k_2357_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_box(0);
v___x_2359_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2352_, v_k_2357_, v___x_2358_, v_t_2356_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2361_ = l_panic___redArg(v_inst_2355_, v___x_2360_);
return v___x_2361_;
}
else
{
lean_object* v_val_2362_; 
v_val_2362_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_val_2362_);
lean_dec_ref_known(v___x_2359_, 1);
return v_val_2362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2363_, lean_object* v_cmp_2364_, lean_object* v_00_u03b2_2365_, lean_object* v_inst_2366_, lean_object* v_inst_2367_, lean_object* v_t_2368_, lean_object* v_k_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Std_ExtDTreeMap_Const_getEntryLT_x21(v_00_u03b1_2363_, v_cmp_2364_, v_00_u03b2_2365_, v_inst_2366_, v_inst_2367_, v_t_2368_, v_k_2369_);
lean_dec_ref(v_inst_2367_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___redArg(lean_object* v_cmp_2371_, lean_object* v_t_2372_, lean_object* v_k_2373_, lean_object* v_fallback_2374_){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_box(0);
v___x_2376_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2371_, v_k_2373_, v___x_2375_, v_t_2372_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_inc_ref(v_fallback_2374_);
return v_fallback_2374_;
}
else
{
lean_object* v_val_2377_; 
v_val_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_val_2377_);
lean_dec_ref_known(v___x_2376_, 1);
return v_val_2377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2378_, lean_object* v_t_2379_, lean_object* v_k_2380_, lean_object* v_fallback_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Std_ExtDTreeMap_Const_getEntryGED___redArg(v_cmp_2378_, v_t_2379_, v_k_2380_, v_fallback_2381_);
lean_dec_ref(v_fallback_2381_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED(lean_object* v_00_u03b1_2383_, lean_object* v_cmp_2384_, lean_object* v_00_u03b2_2385_, lean_object* v_inst_2386_, lean_object* v_t_2387_, lean_object* v_k_2388_, lean_object* v_fallback_2389_){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_box(0);
v___x_2391_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2384_, v_k_2388_, v___x_2390_, v_t_2387_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_inc_ref(v_fallback_2389_);
return v_fallback_2389_;
}
else
{
lean_object* v_val_2392_; 
v_val_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_val_2392_);
lean_dec_ref_known(v___x_2391_, 1);
return v_val_2392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2393_, lean_object* v_cmp_2394_, lean_object* v_00_u03b2_2395_, lean_object* v_inst_2396_, lean_object* v_t_2397_, lean_object* v_k_2398_, lean_object* v_fallback_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Std_ExtDTreeMap_Const_getEntryGED(v_00_u03b1_2393_, v_cmp_2394_, v_00_u03b2_2395_, v_inst_2396_, v_t_2397_, v_k_2398_, v_fallback_2399_);
lean_dec_ref(v_fallback_2399_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(lean_object* v_cmp_2401_, lean_object* v_t_2402_, lean_object* v_k_2403_, lean_object* v_fallback_2404_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = lean_box(0);
v___x_2406_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2401_, v_k_2403_, v___x_2405_, v_t_2402_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_inc_ref(v_fallback_2404_);
return v_fallback_2404_;
}
else
{
lean_object* v_val_2407_; 
v_val_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_val_2407_);
lean_dec_ref_known(v___x_2406_, 1);
return v_val_2407_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2408_, lean_object* v_t_2409_, lean_object* v_k_2410_, lean_object* v_fallback_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(v_cmp_2408_, v_t_2409_, v_k_2410_, v_fallback_2411_);
lean_dec_ref(v_fallback_2411_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD(lean_object* v_00_u03b1_2413_, lean_object* v_cmp_2414_, lean_object* v_00_u03b2_2415_, lean_object* v_inst_2416_, lean_object* v_t_2417_, lean_object* v_k_2418_, lean_object* v_fallback_2419_){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_box(0);
v___x_2421_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2414_, v_k_2418_, v___x_2420_, v_t_2417_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_inc_ref(v_fallback_2419_);
return v_fallback_2419_;
}
else
{
lean_object* v_val_2422_; 
v_val_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_val_2422_);
lean_dec_ref_known(v___x_2421_, 1);
return v_val_2422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2423_, lean_object* v_cmp_2424_, lean_object* v_00_u03b2_2425_, lean_object* v_inst_2426_, lean_object* v_t_2427_, lean_object* v_k_2428_, lean_object* v_fallback_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Std_ExtDTreeMap_Const_getEntryGTD(v_00_u03b1_2423_, v_cmp_2424_, v_00_u03b2_2425_, v_inst_2426_, v_t_2427_, v_k_2428_, v_fallback_2429_);
lean_dec_ref(v_fallback_2429_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___redArg(lean_object* v_cmp_2431_, lean_object* v_t_2432_, lean_object* v_k_2433_, lean_object* v_fallback_2434_){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = lean_box(0);
v___x_2436_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2431_, v_k_2433_, v___x_2435_, v_t_2432_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_inc_ref(v_fallback_2434_);
return v_fallback_2434_;
}
else
{
lean_object* v_val_2437_; 
v_val_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_val_2437_);
lean_dec_ref_known(v___x_2436_, 1);
return v_val_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2438_, lean_object* v_t_2439_, lean_object* v_k_2440_, lean_object* v_fallback_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Std_ExtDTreeMap_Const_getEntryLED___redArg(v_cmp_2438_, v_t_2439_, v_k_2440_, v_fallback_2441_);
lean_dec_ref(v_fallback_2441_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED(lean_object* v_00_u03b1_2443_, lean_object* v_cmp_2444_, lean_object* v_00_u03b2_2445_, lean_object* v_inst_2446_, lean_object* v_t_2447_, lean_object* v_k_2448_, lean_object* v_fallback_2449_){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_box(0);
v___x_2451_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2444_, v_k_2448_, v___x_2450_, v_t_2447_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_inc_ref(v_fallback_2449_);
return v_fallback_2449_;
}
else
{
lean_object* v_val_2452_; 
v_val_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_val_2452_);
lean_dec_ref_known(v___x_2451_, 1);
return v_val_2452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2453_, lean_object* v_cmp_2454_, lean_object* v_00_u03b2_2455_, lean_object* v_inst_2456_, lean_object* v_t_2457_, lean_object* v_k_2458_, lean_object* v_fallback_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Std_ExtDTreeMap_Const_getEntryLED(v_00_u03b1_2453_, v_cmp_2454_, v_00_u03b2_2455_, v_inst_2456_, v_t_2457_, v_k_2458_, v_fallback_2459_);
lean_dec_ref(v_fallback_2459_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(lean_object* v_cmp_2461_, lean_object* v_t_2462_, lean_object* v_k_2463_, lean_object* v_fallback_2464_){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = lean_box(0);
v___x_2466_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2461_, v_k_2463_, v___x_2465_, v_t_2462_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_inc_ref(v_fallback_2464_);
return v_fallback_2464_;
}
else
{
lean_object* v_val_2467_; 
v_val_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_val_2467_);
lean_dec_ref_known(v___x_2466_, 1);
return v_val_2467_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2468_, lean_object* v_t_2469_, lean_object* v_k_2470_, lean_object* v_fallback_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(v_cmp_2468_, v_t_2469_, v_k_2470_, v_fallback_2471_);
lean_dec_ref(v_fallback_2471_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD(lean_object* v_00_u03b1_2473_, lean_object* v_cmp_2474_, lean_object* v_00_u03b2_2475_, lean_object* v_inst_2476_, lean_object* v_t_2477_, lean_object* v_k_2478_, lean_object* v_fallback_2479_){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = lean_box(0);
v___x_2481_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2474_, v_k_2478_, v___x_2480_, v_t_2477_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_inc_ref(v_fallback_2479_);
return v_fallback_2479_;
}
else
{
lean_object* v_val_2482_; 
v_val_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_val_2482_);
lean_dec_ref_known(v___x_2481_, 1);
return v_val_2482_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2483_, lean_object* v_cmp_2484_, lean_object* v_00_u03b2_2485_, lean_object* v_inst_2486_, lean_object* v_t_2487_, lean_object* v_k_2488_, lean_object* v_fallback_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Std_ExtDTreeMap_Const_getEntryLTD(v_00_u03b1_2483_, v_cmp_2484_, v_00_u03b2_2485_, v_inst_2486_, v_t_2487_, v_k_2488_, v_fallback_2489_);
lean_dec_ref(v_fallback_2489_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter___redArg(lean_object* v_f_2491_, lean_object* v_t_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2491_, v_t_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter(lean_object* v_00_u03b1_2494_, lean_object* v_00_u03b2_2495_, lean_object* v_cmp_2496_, lean_object* v_f_2497_, lean_object* v_t_2498_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2497_, v_t_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter___boxed(lean_object* v_00_u03b1_2500_, lean_object* v_00_u03b2_2501_, lean_object* v_cmp_2502_, lean_object* v_f_2503_, lean_object* v_t_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Std_ExtDTreeMap_filter(v_00_u03b1_2500_, v_00_u03b2_2501_, v_cmp_2502_, v_f_2503_, v_t_2504_);
lean_dec_ref(v_cmp_2502_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap___redArg(lean_object* v_f_2506_, lean_object* v_t_2507_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_2506_, v_t_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap(lean_object* v_00_u03b1_2509_, lean_object* v_00_u03b2_2510_, lean_object* v_00_u03b3_2511_, lean_object* v_cmp_2512_, lean_object* v_f_2513_, lean_object* v_t_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_2513_, v_t_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap___boxed(lean_object* v_00_u03b1_2516_, lean_object* v_00_u03b2_2517_, lean_object* v_00_u03b3_2518_, lean_object* v_cmp_2519_, lean_object* v_f_2520_, lean_object* v_t_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Std_ExtDTreeMap_filterMap(v_00_u03b1_2516_, v_00_u03b2_2517_, v_00_u03b3_2518_, v_cmp_2519_, v_f_2520_, v_t_2521_);
lean_dec_ref(v_cmp_2519_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map___redArg(lean_object* v_f_2523_, lean_object* v_t_2524_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_2523_, v_t_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map(lean_object* v_00_u03b1_2526_, lean_object* v_00_u03b2_2527_, lean_object* v_00_u03b3_2528_, lean_object* v_cmp_2529_, lean_object* v_f_2530_, lean_object* v_t_2531_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_2530_, v_t_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map___boxed(lean_object* v_00_u03b1_2533_, lean_object* v_00_u03b2_2534_, lean_object* v_00_u03b3_2535_, lean_object* v_cmp_2536_, lean_object* v_f_2537_, lean_object* v_t_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Std_ExtDTreeMap_map(v_00_u03b1_2533_, v_00_u03b2_2534_, v_00_u03b3_2535_, v_cmp_2536_, v_f_2537_, v_t_2538_);
lean_dec_ref(v_cmp_2536_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM___redArg(lean_object* v_inst_2540_, lean_object* v_f_2541_, lean_object* v_init_2542_, lean_object* v_t_2543_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2540_, v_f_2541_, v_init_2542_, v_t_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM(lean_object* v_00_u03b1_2545_, lean_object* v_00_u03b2_2546_, lean_object* v_cmp_2547_, lean_object* v_00_u03b4_2548_, lean_object* v_m_2549_, lean_object* v_inst_2550_, lean_object* v_inst_2551_, lean_object* v_inst_2552_, lean_object* v_f_2553_, lean_object* v_init_2554_, lean_object* v_t_2555_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2550_, v_f_2553_, v_init_2554_, v_t_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM___boxed(lean_object* v_00_u03b1_2557_, lean_object* v_00_u03b2_2558_, lean_object* v_cmp_2559_, lean_object* v_00_u03b4_2560_, lean_object* v_m_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_inst_2564_, lean_object* v_f_2565_, lean_object* v_init_2566_, lean_object* v_t_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Std_ExtDTreeMap_foldlM(v_00_u03b1_2557_, v_00_u03b2_2558_, v_cmp_2559_, v_00_u03b4_2560_, v_m_2561_, v_inst_2562_, v_inst_2563_, v_inst_2564_, v_f_2565_, v_init_2566_, v_t_2567_);
lean_dec_ref(v_cmp_2559_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl___redArg(lean_object* v_f_2569_, lean_object* v_init_2570_, lean_object* v_t_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2569_, v_init_2570_, v_t_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl(lean_object* v_00_u03b1_2573_, lean_object* v_00_u03b2_2574_, lean_object* v_cmp_2575_, lean_object* v_00_u03b4_2576_, lean_object* v_inst_2577_, lean_object* v_f_2578_, lean_object* v_init_2579_, lean_object* v_t_2580_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2578_, v_init_2579_, v_t_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl___boxed(lean_object* v_00_u03b1_2582_, lean_object* v_00_u03b2_2583_, lean_object* v_cmp_2584_, lean_object* v_00_u03b4_2585_, lean_object* v_inst_2586_, lean_object* v_f_2587_, lean_object* v_init_2588_, lean_object* v_t_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Std_ExtDTreeMap_foldl(v_00_u03b1_2582_, v_00_u03b2_2583_, v_cmp_2584_, v_00_u03b4_2585_, v_inst_2586_, v_f_2587_, v_init_2588_, v_t_2589_);
lean_dec_ref(v_cmp_2584_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM___redArg(lean_object* v_inst_2591_, lean_object* v_f_2592_, lean_object* v_init_2593_, lean_object* v_t_2594_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2591_, v_f_2592_, v_init_2593_, v_t_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM(lean_object* v_00_u03b1_2596_, lean_object* v_00_u03b2_2597_, lean_object* v_cmp_2598_, lean_object* v_00_u03b4_2599_, lean_object* v_m_2600_, lean_object* v_inst_2601_, lean_object* v_inst_2602_, lean_object* v_inst_2603_, lean_object* v_f_2604_, lean_object* v_init_2605_, lean_object* v_t_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2601_, v_f_2604_, v_init_2605_, v_t_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM___boxed(lean_object* v_00_u03b1_2608_, lean_object* v_00_u03b2_2609_, lean_object* v_cmp_2610_, lean_object* v_00_u03b4_2611_, lean_object* v_m_2612_, lean_object* v_inst_2613_, lean_object* v_inst_2614_, lean_object* v_inst_2615_, lean_object* v_f_2616_, lean_object* v_init_2617_, lean_object* v_t_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Std_ExtDTreeMap_foldrM(v_00_u03b1_2608_, v_00_u03b2_2609_, v_cmp_2610_, v_00_u03b4_2611_, v_m_2612_, v_inst_2613_, v_inst_2614_, v_inst_2615_, v_f_2616_, v_init_2617_, v_t_2618_);
lean_dec_ref(v_cmp_2610_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___redArg___lam__0(lean_object* v_f_2620_, lean_object* v_x1_2621_, lean_object* v_x2_2622_, lean_object* v_x3_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_apply_3(v_f_2620_, v_x1_2621_, v_x2_2622_, v_x3_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___redArg(lean_object* v_f_2644_, lean_object* v_init_2645_, lean_object* v_t_2646_){
_start:
{
lean_object* v___f_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___f_2647_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2647_, 0, v_f_2644_);
v___x_2648_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2649_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2648_, v___f_2647_, v_init_2645_, v_t_2646_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr(lean_object* v_00_u03b1_2650_, lean_object* v_00_u03b2_2651_, lean_object* v_cmp_2652_, lean_object* v_00_u03b4_2653_, lean_object* v_inst_2654_, lean_object* v_f_2655_, lean_object* v_init_2656_, lean_object* v_t_2657_){
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___boxed(lean_object* v_00_u03b1_2661_, lean_object* v_00_u03b2_2662_, lean_object* v_cmp_2663_, lean_object* v_00_u03b4_2664_, lean_object* v_inst_2665_, lean_object* v_f_2666_, lean_object* v_init_2667_, lean_object* v_t_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Std_ExtDTreeMap_foldr(v_00_u03b1_2661_, v_00_u03b2_2662_, v_cmp_2663_, v_00_u03b4_2664_, v_inst_2665_, v_f_2666_, v_init_2667_, v_t_2668_);
lean_dec_ref(v_cmp_2663_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition___redArg___lam__0(lean_object* v_f_2670_, lean_object* v_cmp_2671_, lean_object* v_x_2672_, lean_object* v_a_2673_, lean_object* v_b_2674_){
_start:
{
lean_object* v_fst_2675_; lean_object* v_snd_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2690_; 
v_fst_2675_ = lean_ctor_get(v_x_2672_, 0);
v_snd_2676_ = lean_ctor_get(v_x_2672_, 1);
v_isSharedCheck_2690_ = !lean_is_exclusive(v_x_2672_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2678_ = v_x_2672_;
v_isShared_2679_ = v_isSharedCheck_2690_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_snd_2676_);
lean_inc(v_fst_2675_);
lean_dec(v_x_2672_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2690_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; uint8_t v___x_2681_; 
lean_inc(v_b_2674_);
lean_inc(v_a_2673_);
v___x_2680_ = lean_apply_2(v_f_2670_, v_a_2673_, v_b_2674_);
v___x_2681_ = lean_unbox(v___x_2680_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2682_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2671_, v_a_2673_, v_b_2674_, v_snd_2676_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___x_2682_);
v___x_2684_ = v___x_2678_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_fst_2675_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2686_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2671_, v_a_2673_, v_b_2674_, v_fst_2675_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2686_);
v___x_2688_ = v___x_2678_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v_snd_2676_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition___redArg(lean_object* v_cmp_2693_, lean_object* v_f_2694_, lean_object* v_t_2695_){
_start:
{
lean_object* v___f_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___f_2696_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2696_, 0, v_f_2694_);
lean_closure_set(v___f_2696_, 1, v_cmp_2693_);
v___x_2697_ = ((lean_object*)(l_Std_ExtDTreeMap_partition___redArg___closed__0));
v___x_2698_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2696_, v___x_2697_, v_t_2695_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition(lean_object* v_00_u03b1_2699_, lean_object* v_00_u03b2_2700_, lean_object* v_cmp_2701_, lean_object* v_inst_2702_, lean_object* v_f_2703_, lean_object* v_t_2704_){
_start:
{
lean_object* v___f_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___f_2705_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2705_, 0, v_f_2703_);
lean_closure_set(v___f_2705_, 1, v_cmp_2701_);
v___x_2706_ = ((lean_object*)(l_Std_ExtDTreeMap_partition___redArg___closed__0));
v___x_2707_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2705_, v___x_2706_, v_t_2704_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___redArg___lam__0(lean_object* v_f_2708_, lean_object* v_x_2709_, lean_object* v_k_2710_, lean_object* v_v_2711_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = lean_apply_2(v_f_2708_, v_k_2710_, v_v_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___redArg(lean_object* v_inst_2713_, lean_object* v_f_2714_, lean_object* v_t_2715_){
_start:
{
lean_object* v___f_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___f_2716_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2716_, 0, v_f_2714_);
v___x_2717_ = lean_box(0);
v___x_2718_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2713_, v___f_2716_, v___x_2717_, v_t_2715_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM(lean_object* v_00_u03b1_2719_, lean_object* v_00_u03b2_2720_, lean_object* v_cmp_2721_, lean_object* v_m_2722_, lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_f_2726_, lean_object* v_t_2727_){
_start:
{
lean_object* v___f_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___f_2728_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2728_, 0, v_f_2726_);
v___x_2729_ = lean_box(0);
v___x_2730_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2723_, v___f_2728_, v___x_2729_, v_t_2727_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___boxed(lean_object* v_00_u03b1_2731_, lean_object* v_00_u03b2_2732_, lean_object* v_cmp_2733_, lean_object* v_m_2734_, lean_object* v_inst_2735_, lean_object* v_inst_2736_, lean_object* v_inst_2737_, lean_object* v_f_2738_, lean_object* v_t_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Std_ExtDTreeMap_forM(v_00_u03b1_2731_, v_00_u03b2_2732_, v_cmp_2733_, v_m_2734_, v_inst_2735_, v_inst_2736_, v_inst_2737_, v_f_2738_, v_t_2739_);
lean_dec_ref(v_cmp_2733_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___redArg___lam__0(lean_object* v_toPure_2741_, lean_object* v_____do__lift_2742_){
_start:
{
lean_object* v_a_2743_; lean_object* v___x_2744_; 
v_a_2743_ = lean_ctor_get(v_____do__lift_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref(v_____do__lift_2742_);
v___x_2744_ = lean_apply_2(v_toPure_2741_, lean_box(0), v_a_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___redArg(lean_object* v_inst_2745_, lean_object* v_f_2746_, lean_object* v_init_2747_, lean_object* v_t_2748_){
_start:
{
lean_object* v_toApplicative_2749_; lean_object* v_toBind_2750_; lean_object* v_toPure_2751_; lean_object* v___x_2752_; lean_object* v___f_2753_; lean_object* v___x_2754_; 
v_toApplicative_2749_ = lean_ctor_get(v_inst_2745_, 0);
v_toBind_2750_ = lean_ctor_get(v_inst_2745_, 1);
lean_inc(v_toBind_2750_);
v_toPure_2751_ = lean_ctor_get(v_toApplicative_2749_, 1);
lean_inc(v_toPure_2751_);
v___x_2752_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2745_, v_f_2746_, v_init_2747_, v_t_2748_);
v___f_2753_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2753_, 0, v_toPure_2751_);
v___x_2754_ = lean_apply_4(v_toBind_2750_, lean_box(0), lean_box(0), v___x_2752_, v___f_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn(lean_object* v_00_u03b1_2755_, lean_object* v_00_u03b2_2756_, lean_object* v_cmp_2757_, lean_object* v_00_u03b4_2758_, lean_object* v_m_2759_, lean_object* v_inst_2760_, lean_object* v_inst_2761_, lean_object* v_inst_2762_, lean_object* v_f_2763_, lean_object* v_init_2764_, lean_object* v_t_2765_){
_start:
{
lean_object* v_toApplicative_2766_; lean_object* v_toBind_2767_; lean_object* v_toPure_2768_; lean_object* v___x_2769_; lean_object* v___f_2770_; lean_object* v___x_2771_; 
v_toApplicative_2766_ = lean_ctor_get(v_inst_2760_, 0);
v_toBind_2767_ = lean_ctor_get(v_inst_2760_, 1);
lean_inc(v_toBind_2767_);
v_toPure_2768_ = lean_ctor_get(v_toApplicative_2766_, 1);
lean_inc(v_toPure_2768_);
v___x_2769_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2760_, v_f_2763_, v_init_2764_, v_t_2765_);
v___f_2770_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2770_, 0, v_toPure_2768_);
v___x_2771_ = lean_apply_4(v_toBind_2767_, lean_box(0), lean_box(0), v___x_2769_, v___f_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___boxed(lean_object* v_00_u03b1_2772_, lean_object* v_00_u03b2_2773_, lean_object* v_cmp_2774_, lean_object* v_00_u03b4_2775_, lean_object* v_m_2776_, lean_object* v_inst_2777_, lean_object* v_inst_2778_, lean_object* v_inst_2779_, lean_object* v_f_2780_, lean_object* v_init_2781_, lean_object* v_t_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Std_ExtDTreeMap_forIn(v_00_u03b1_2772_, v_00_u03b2_2773_, v_cmp_2774_, v_00_u03b4_2775_, v_m_2776_, v_inst_2777_, v_inst_2778_, v_inst_2779_, v_f_2780_, v_init_2781_, v_t_2782_);
lean_dec_ref(v_cmp_2774_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2784_, lean_object* v_x_2785_, lean_object* v_k_2786_, lean_object* v_v_2787_){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2788_, 0, v_k_2786_);
lean_ctor_set(v___x_2788_, 1, v_v_2787_);
v___x_2789_ = lean_apply_1(v_f_2784_, v___x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_2790_, lean_object* v_t_2791_, lean_object* v_f_2792_){
_start:
{
lean_object* v___f_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___f_2793_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2793_, 0, v_f_2792_);
v___x_2794_ = lean_box(0);
v___x_2795_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2790_, v___f_2793_, v___x_2794_, v_t_2791_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2796_){
_start:
{
lean_object* v___f_2797_; 
v___f_2797_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2797_, 0, v_inst_2796_);
return v___f_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2798_, lean_object* v_00_u03b2_2799_, lean_object* v_cmp_2800_, lean_object* v_m_2801_, lean_object* v_inst_2802_, lean_object* v_inst_2803_, lean_object* v_inst_2804_){
_start:
{
lean_object* v___f_2805_; 
v___f_2805_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2805_, 0, v_inst_2803_);
return v___f_2805_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2806_, lean_object* v_00_u03b2_2807_, lean_object* v_cmp_2808_, lean_object* v_m_2809_, lean_object* v_inst_2810_, lean_object* v_inst_2811_, lean_object* v_inst_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(v_00_u03b1_2806_, v_00_u03b2_2807_, v_cmp_2808_, v_m_2809_, v_inst_2810_, v_inst_2811_, v_inst_2812_);
lean_dec_ref(v_cmp_2808_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2814_, lean_object* v_a_2815_, lean_object* v_b_2816_, lean_object* v_acc_2817_){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2818_, 0, v_a_2815_);
lean_ctor_set(v___x_2818_, 1, v_b_2816_);
v___x_2819_ = lean_apply_2(v_f_2814_, v___x_2818_, v_acc_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_2820_, lean_object* v_00_u03b2_2821_, lean_object* v_m_2822_, lean_object* v_init_2823_, lean_object* v_f_2824_){
_start:
{
lean_object* v_toApplicative_2825_; lean_object* v_toBind_2826_; lean_object* v_toPure_2827_; lean_object* v___f_2828_; lean_object* v___x_2829_; lean_object* v___f_2830_; lean_object* v___x_2831_; 
v_toApplicative_2825_ = lean_ctor_get(v_inst_2820_, 0);
v_toBind_2826_ = lean_ctor_get(v_inst_2820_, 1);
lean_inc(v_toBind_2826_);
v_toPure_2827_ = lean_ctor_get(v_toApplicative_2825_, 1);
lean_inc(v_toPure_2827_);
v___f_2828_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2828_, 0, v_f_2824_);
v___x_2829_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2820_, v___f_2828_, v_init_2823_, v_m_2822_);
v___f_2830_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2830_, 0, v_toPure_2827_);
v___x_2831_ = lean_apply_4(v_toBind_2826_, lean_box(0), lean_box(0), v___x_2829_, v___f_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2832_){
_start:
{
lean_object* v___f_2833_; 
v___f_2833_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2833_, 0, v_inst_2832_);
return v___f_2833_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2834_, lean_object* v_00_u03b2_2835_, lean_object* v_cmp_2836_, lean_object* v_m_2837_, lean_object* v_inst_2838_, lean_object* v_inst_2839_, lean_object* v_inst_2840_){
_start:
{
lean_object* v___f_2841_; 
v___f_2841_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2841_, 0, v_inst_2839_);
return v___f_2841_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2842_, lean_object* v_00_u03b2_2843_, lean_object* v_cmp_2844_, lean_object* v_m_2845_, lean_object* v_inst_2846_, lean_object* v_inst_2847_, lean_object* v_inst_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(v_00_u03b1_2842_, v_00_u03b2_2843_, v_cmp_2844_, v_m_2845_, v_inst_2846_, v_inst_2847_, v_inst_2848_);
lean_dec_ref(v_cmp_2844_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2850_, lean_object* v_x_2851_, lean_object* v_k_2852_, lean_object* v_v_2853_){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v_k_2852_);
lean_ctor_set(v___x_2854_, 1, v_v_2853_);
v___x_2855_ = lean_apply_1(v_f_2850_, v___x_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___redArg(lean_object* v_inst_2856_, lean_object* v_f_2857_, lean_object* v_t_2858_){
_start:
{
lean_object* v___f_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___f_2859_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2859_, 0, v_f_2857_);
v___x_2860_ = lean_box(0);
v___x_2861_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2856_, v___f_2859_, v___x_2860_, v_t_2858_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried(lean_object* v_00_u03b1_2862_, lean_object* v_cmp_2863_, lean_object* v_m_2864_, lean_object* v_inst_2865_, lean_object* v_inst_2866_, lean_object* v_00_u03b2_2867_, lean_object* v_inst_2868_, lean_object* v_f_2869_, lean_object* v_t_2870_){
_start:
{
lean_object* v___f_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___f_2871_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2871_, 0, v_f_2869_);
v___x_2872_ = lean_box(0);
v___x_2873_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2865_, v___f_2871_, v___x_2872_, v_t_2870_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2874_, lean_object* v_cmp_2875_, lean_object* v_m_2876_, lean_object* v_inst_2877_, lean_object* v_inst_2878_, lean_object* v_00_u03b2_2879_, lean_object* v_inst_2880_, lean_object* v_f_2881_, lean_object* v_t_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Std_ExtDTreeMap_Const_forMUncurried(v_00_u03b1_2874_, v_cmp_2875_, v_m_2876_, v_inst_2877_, v_inst_2878_, v_00_u03b2_2879_, v_inst_2880_, v_f_2881_, v_t_2882_);
lean_dec_ref(v_cmp_2875_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2884_, lean_object* v_a_2885_, lean_object* v_b_2886_, lean_object* v_acc_2887_){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2888_, 0, v_a_2885_);
lean_ctor_set(v___x_2888_, 1, v_b_2886_);
v___x_2889_ = lean_apply_2(v_f_2884_, v___x_2888_, v_acc_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___redArg(lean_object* v_inst_2890_, lean_object* v_f_2891_, lean_object* v_init_2892_, lean_object* v_t_2893_){
_start:
{
lean_object* v_toApplicative_2894_; lean_object* v_toBind_2895_; lean_object* v_toPure_2896_; lean_object* v___f_2897_; lean_object* v___x_2898_; lean_object* v___f_2899_; lean_object* v___x_2900_; 
v_toApplicative_2894_ = lean_ctor_get(v_inst_2890_, 0);
v_toBind_2895_ = lean_ctor_get(v_inst_2890_, 1);
lean_inc(v_toBind_2895_);
v_toPure_2896_ = lean_ctor_get(v_toApplicative_2894_, 1);
lean_inc(v_toPure_2896_);
v___f_2897_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2897_, 0, v_f_2891_);
v___x_2898_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2890_, v___f_2897_, v_init_2892_, v_t_2893_);
v___f_2899_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2899_, 0, v_toPure_2896_);
v___x_2900_ = lean_apply_4(v_toBind_2895_, lean_box(0), lean_box(0), v___x_2898_, v___f_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried(lean_object* v_00_u03b1_2901_, lean_object* v_cmp_2902_, lean_object* v_00_u03b4_2903_, lean_object* v_m_2904_, lean_object* v_inst_2905_, lean_object* v_inst_2906_, lean_object* v_00_u03b2_2907_, lean_object* v_inst_2908_, lean_object* v_f_2909_, lean_object* v_init_2910_, lean_object* v_t_2911_){
_start:
{
lean_object* v_toApplicative_2912_; lean_object* v_toBind_2913_; lean_object* v_toPure_2914_; lean_object* v___f_2915_; lean_object* v___x_2916_; lean_object* v___f_2917_; lean_object* v___x_2918_; 
v_toApplicative_2912_ = lean_ctor_get(v_inst_2905_, 0);
v_toBind_2913_ = lean_ctor_get(v_inst_2905_, 1);
lean_inc(v_toBind_2913_);
v_toPure_2914_ = lean_ctor_get(v_toApplicative_2912_, 1);
lean_inc(v_toPure_2914_);
v___f_2915_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2915_, 0, v_f_2909_);
v___x_2916_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2905_, v___f_2915_, v_init_2910_, v_t_2911_);
v___f_2917_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2917_, 0, v_toPure_2914_);
v___x_2918_ = lean_apply_4(v_toBind_2913_, lean_box(0), lean_box(0), v___x_2916_, v___f_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2919_, lean_object* v_cmp_2920_, lean_object* v_00_u03b4_2921_, lean_object* v_m_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_00_u03b2_2925_, lean_object* v_inst_2926_, lean_object* v_f_2927_, lean_object* v_init_2928_, lean_object* v_t_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Std_ExtDTreeMap_Const_forInUncurried(v_00_u03b1_2919_, v_cmp_2920_, v_00_u03b4_2921_, v_m_2922_, v_inst_2923_, v_inst_2924_, v_00_u03b2_2925_, v_inst_2926_, v_f_2927_, v_init_2928_, v_t_2929_);
lean_dec_ref(v_cmp_2920_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___lam__0(lean_object* v_p_2931_, lean_object* v___x_2932_, lean_object* v___x_2933_, lean_object* v_a_2934_, lean_object* v_b_2935_, lean_object* v_acc_2936_){
_start:
{
lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2937_ = lean_apply_2(v_p_2931_, v_a_2934_, v_b_2935_);
v___x_2938_ = lean_unbox(v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2932_);
return v___x_2939_;
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec_ref(v___x_2932_);
v___x_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2937_);
v___x_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_ctor_set(v___x_2941_, 1, v___x_2933_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
return v___x_2942_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2943_, lean_object* v___x_2944_, lean_object* v___x_2945_, lean_object* v_a_2946_, lean_object* v_b_2947_, lean_object* v_acc_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Std_ExtDTreeMap_any___redArg___lam__0(v_p_2943_, v___x_2944_, v___x_2945_, v_a_2946_, v_b_2947_, v_acc_2948_);
lean_dec_ref(v_acc_2948_);
return v_res_2949_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_any___redArg(lean_object* v_t_2953_, lean_object* v_p_2954_){
_start:
{
lean_object* v___y_2956_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___f_2964_; lean_object* v___x_2965_; lean_object* v_a_2966_; 
v___x_2961_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2962_ = lean_box(0);
v___x_2963_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_2964_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2964_, 0, v_p_2954_);
lean_closure_set(v___f_2964_, 1, v___x_2963_);
lean_closure_set(v___f_2964_, 2, v___x_2962_);
v___x_2965_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2961_, v___f_2964_, v___x_2963_, v_t_2953_);
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec(v___x_2965_);
v___y_2956_ = v_a_2966_;
goto v___jp_2955_;
v___jp_2955_:
{
lean_object* v_fst_2957_; 
v_fst_2957_ = lean_ctor_get(v___y_2956_, 0);
lean_inc(v_fst_2957_);
lean_dec_ref(v___y_2956_);
if (lean_obj_tag(v_fst_2957_) == 0)
{
uint8_t v___x_2958_; 
v___x_2958_ = 0;
return v___x_2958_;
}
else
{
lean_object* v_val_2959_; uint8_t v___x_2960_; 
v_val_2959_ = lean_ctor_get(v_fst_2957_, 0);
lean_inc(v_val_2959_);
lean_dec_ref_known(v_fst_2957_, 1);
v___x_2960_ = lean_unbox(v_val_2959_);
lean_dec(v_val_2959_);
return v___x_2960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___boxed(lean_object* v_t_2967_, lean_object* v_p_2968_){
_start:
{
uint8_t v_res_2969_; lean_object* v_r_2970_; 
v_res_2969_ = l_Std_ExtDTreeMap_any___redArg(v_t_2967_, v_p_2968_);
v_r_2970_ = lean_box(v_res_2969_);
return v_r_2970_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_any(lean_object* v_00_u03b1_2971_, lean_object* v_00_u03b2_2972_, lean_object* v_cmp_2973_, lean_object* v_inst_2974_, lean_object* v_t_2975_, lean_object* v_p_2976_){
_start:
{
lean_object* v___y_2978_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___f_2986_; lean_object* v___x_2987_; lean_object* v_a_2988_; 
v___x_2983_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2984_ = lean_box(0);
v___x_2985_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_2986_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2986_, 0, v_p_2976_);
lean_closure_set(v___f_2986_, 1, v___x_2985_);
lean_closure_set(v___f_2986_, 2, v___x_2984_);
v___x_2987_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2983_, v___f_2986_, v___x_2985_, v_t_2975_);
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec(v___x_2987_);
v___y_2978_ = v_a_2988_;
goto v___jp_2977_;
v___jp_2977_:
{
lean_object* v_fst_2979_; 
v_fst_2979_ = lean_ctor_get(v___y_2978_, 0);
lean_inc(v_fst_2979_);
lean_dec_ref(v___y_2978_);
if (lean_obj_tag(v_fst_2979_) == 0)
{
uint8_t v___x_2980_; 
v___x_2980_ = 0;
return v___x_2980_;
}
else
{
lean_object* v_val_2981_; uint8_t v___x_2982_; 
v_val_2981_ = lean_ctor_get(v_fst_2979_, 0);
lean_inc(v_val_2981_);
lean_dec_ref_known(v_fst_2979_, 1);
v___x_2982_ = lean_unbox(v_val_2981_);
lean_dec(v_val_2981_);
return v___x_2982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___boxed(lean_object* v_00_u03b1_2989_, lean_object* v_00_u03b2_2990_, lean_object* v_cmp_2991_, lean_object* v_inst_2992_, lean_object* v_t_2993_, lean_object* v_p_2994_){
_start:
{
uint8_t v_res_2995_; lean_object* v_r_2996_; 
v_res_2995_ = l_Std_ExtDTreeMap_any(v_00_u03b1_2989_, v_00_u03b2_2990_, v_cmp_2991_, v_inst_2992_, v_t_2993_, v_p_2994_);
lean_dec_ref(v_cmp_2991_);
v_r_2996_ = lean_box(v_res_2995_);
return v_r_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___lam__0(lean_object* v_p_2997_, lean_object* v___x_2998_, lean_object* v___x_2999_, lean_object* v_a_3000_, lean_object* v_b_3001_, lean_object* v_acc_3002_){
_start:
{
lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3003_ = lean_apply_2(v_p_2997_, v_a_3000_, v_b_3001_);
v___x_3004_ = lean_unbox(v___x_3003_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
lean_dec_ref(v___x_2999_);
v___x_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3003_);
v___x_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
lean_ctor_set(v___x_3006_, 1, v___x_2998_);
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
return v___x_3007_;
}
else
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_2999_);
return v___x_3008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_3009_, lean_object* v___x_3010_, lean_object* v___x_3011_, lean_object* v_a_3012_, lean_object* v_b_3013_, lean_object* v_acc_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Std_ExtDTreeMap_all___redArg___lam__0(v_p_3009_, v___x_3010_, v___x_3011_, v_a_3012_, v_b_3013_, v_acc_3014_);
lean_dec_ref(v_acc_3014_);
return v_res_3015_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_all___redArg(lean_object* v_t_3016_, lean_object* v_p_3017_){
_start:
{
lean_object* v___y_3019_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___f_3027_; lean_object* v___x_3028_; lean_object* v_a_3029_; 
v___x_3024_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3025_ = lean_box(0);
v___x_3026_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_3027_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3027_, 0, v_p_3017_);
lean_closure_set(v___f_3027_, 1, v___x_3025_);
lean_closure_set(v___f_3027_, 2, v___x_3026_);
v___x_3028_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_3024_, v___f_3027_, v___x_3026_, v_t_3016_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___y_3019_ = v_a_3029_;
goto v___jp_3018_;
v___jp_3018_:
{
lean_object* v_fst_3020_; 
v_fst_3020_ = lean_ctor_get(v___y_3019_, 0);
lean_inc(v_fst_3020_);
lean_dec_ref(v___y_3019_);
if (lean_obj_tag(v_fst_3020_) == 0)
{
uint8_t v___x_3021_; 
v___x_3021_ = 1;
return v___x_3021_;
}
else
{
lean_object* v_val_3022_; uint8_t v___x_3023_; 
v_val_3022_ = lean_ctor_get(v_fst_3020_, 0);
lean_inc(v_val_3022_);
lean_dec_ref_known(v_fst_3020_, 1);
v___x_3023_ = lean_unbox(v_val_3022_);
lean_dec(v_val_3022_);
return v___x_3023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___boxed(lean_object* v_t_3030_, lean_object* v_p_3031_){
_start:
{
uint8_t v_res_3032_; lean_object* v_r_3033_; 
v_res_3032_ = l_Std_ExtDTreeMap_all___redArg(v_t_3030_, v_p_3031_);
v_r_3033_ = lean_box(v_res_3032_);
return v_r_3033_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_all(lean_object* v_00_u03b1_3034_, lean_object* v_00_u03b2_3035_, lean_object* v_cmp_3036_, lean_object* v_inst_3037_, lean_object* v_t_3038_, lean_object* v_p_3039_){
_start:
{
lean_object* v___y_3041_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___f_3049_; lean_object* v___x_3050_; lean_object* v_a_3051_; 
v___x_3046_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3047_ = lean_box(0);
v___x_3048_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_3049_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3049_, 0, v_p_3039_);
lean_closure_set(v___f_3049_, 1, v___x_3047_);
lean_closure_set(v___f_3049_, 2, v___x_3048_);
v___x_3050_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_3046_, v___f_3049_, v___x_3048_, v_t_3038_);
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec(v___x_3050_);
v___y_3041_ = v_a_3051_;
goto v___jp_3040_;
v___jp_3040_:
{
lean_object* v_fst_3042_; 
v_fst_3042_ = lean_ctor_get(v___y_3041_, 0);
lean_inc(v_fst_3042_);
lean_dec_ref(v___y_3041_);
if (lean_obj_tag(v_fst_3042_) == 0)
{
uint8_t v___x_3043_; 
v___x_3043_ = 1;
return v___x_3043_;
}
else
{
lean_object* v_val_3044_; uint8_t v___x_3045_; 
v_val_3044_ = lean_ctor_get(v_fst_3042_, 0);
lean_inc(v_val_3044_);
lean_dec_ref_known(v_fst_3042_, 1);
v___x_3045_ = lean_unbox(v_val_3044_);
lean_dec(v_val_3044_);
return v___x_3045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___boxed(lean_object* v_00_u03b1_3052_, lean_object* v_00_u03b2_3053_, lean_object* v_cmp_3054_, lean_object* v_inst_3055_, lean_object* v_t_3056_, lean_object* v_p_3057_){
_start:
{
uint8_t v_res_3058_; lean_object* v_r_3059_; 
v_res_3058_ = l_Std_ExtDTreeMap_all(v_00_u03b1_3052_, v_00_u03b2_3053_, v_cmp_3054_, v_inst_3055_, v_t_3056_, v_p_3057_);
lean_dec_ref(v_cmp_3054_);
v_r_3059_ = lean_box(v_res_3058_);
return v_r_3059_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg___lam__0(lean_object* v_x1_3060_, lean_object* v_x2_3061_, lean_object* v_x3_3062_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3063_, 0, v_x1_3060_);
lean_ctor_set(v___x_3063_, 1, v_x3_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_3064_, lean_object* v_x2_3065_, lean_object* v_x3_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Std_ExtDTreeMap_keys___redArg___lam__0(v_x1_3064_, v_x2_3065_, v_x3_3066_);
lean_dec(v_x2_3065_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg(lean_object* v_t_3069_){
_start:
{
lean_object* v___f_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___f_3070_ = ((lean_object*)(l_Std_ExtDTreeMap_keys___redArg___closed__0));
v___x_3071_ = lean_box(0);
v___x_3072_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3073_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3072_, v___f_3070_, v___x_3071_, v_t_3069_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys(lean_object* v_00_u03b1_3074_, lean_object* v_00_u03b2_3075_, lean_object* v_cmp_3076_, lean_object* v_inst_3077_, lean_object* v_t_3078_){
_start:
{
lean_object* v___f_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___f_3079_ = ((lean_object*)(l_Std_ExtDTreeMap_keys___redArg___closed__0));
v___x_3080_ = lean_box(0);
v___x_3081_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3082_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3081_, v___f_3079_, v___x_3080_, v_t_3078_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___boxed(lean_object* v_00_u03b1_3083_, lean_object* v_00_u03b2_3084_, lean_object* v_cmp_3085_, lean_object* v_inst_3086_, lean_object* v_t_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Std_ExtDTreeMap_keys(v_00_u03b1_3083_, v_00_u03b2_3084_, v_cmp_3085_, v_inst_3086_, v_t_3087_);
lean_dec_ref(v_cmp_3085_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg___lam__0(lean_object* v_l_3089_, lean_object* v_k_3090_, lean_object* v_x_3091_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = lean_array_push(v_l_3089_, v_k_3090_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_3093_, lean_object* v_k_3094_, lean_object* v_x_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Std_ExtDTreeMap_keysArray___redArg___lam__0(v_l_3093_, v_k_3094_, v_x_3095_);
lean_dec(v_x_3095_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg(lean_object* v_t_3098_){
_start:
{
lean_object* v___f_3099_; lean_object* v___y_3101_; 
v___f_3099_ = ((lean_object*)(l_Std_ExtDTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_3098_) == 0)
{
lean_object* v_size_3104_; 
v_size_3104_ = lean_ctor_get(v_t_3098_, 0);
lean_inc(v_size_3104_);
v___y_3101_ = v_size_3104_;
goto v___jp_3100_;
}
else
{
lean_object* v___x_3105_; 
v___x_3105_ = lean_unsigned_to_nat(0u);
v___y_3101_ = v___x_3105_;
goto v___jp_3100_;
}
v___jp_3100_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_mk_empty_array_with_capacity(v___y_3101_);
lean_dec(v___y_3101_);
v___x_3103_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3099_, v___x_3102_, v_t_3098_);
return v___x_3103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray(lean_object* v_00_u03b1_3106_, lean_object* v_00_u03b2_3107_, lean_object* v_cmp_3108_, lean_object* v_inst_3109_, lean_object* v_t_3110_){
_start:
{
lean_object* v___f_3111_; lean_object* v___y_3113_; 
v___f_3111_ = ((lean_object*)(l_Std_ExtDTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_3110_) == 0)
{
lean_object* v_size_3116_; 
v_size_3116_ = lean_ctor_get(v_t_3110_, 0);
lean_inc(v_size_3116_);
v___y_3113_ = v_size_3116_;
goto v___jp_3112_;
}
else
{
lean_object* v___x_3117_; 
v___x_3117_ = lean_unsigned_to_nat(0u);
v___y_3113_ = v___x_3117_;
goto v___jp_3112_;
}
v___jp_3112_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = lean_mk_empty_array_with_capacity(v___y_3113_);
lean_dec(v___y_3113_);
v___x_3115_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3111_, v___x_3114_, v_t_3110_);
return v___x_3115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___boxed(lean_object* v_00_u03b1_3118_, lean_object* v_00_u03b2_3119_, lean_object* v_cmp_3120_, lean_object* v_inst_3121_, lean_object* v_t_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Std_ExtDTreeMap_keysArray(v_00_u03b1_3118_, v_00_u03b2_3119_, v_cmp_3120_, v_inst_3121_, v_t_3122_);
lean_dec_ref(v_cmp_3120_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg___lam__0(lean_object* v_x1_3124_, lean_object* v_x2_3125_, lean_object* v_x3_3126_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3127_, 0, v_x2_3125_);
lean_ctor_set(v___x_3127_, 1, v_x3_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_3128_, lean_object* v_x2_3129_, lean_object* v_x3_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Std_ExtDTreeMap_values___redArg___lam__0(v_x1_3128_, v_x2_3129_, v_x3_3130_);
lean_dec(v_x1_3128_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg(lean_object* v_t_3133_){
_start:
{
lean_object* v___f_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___f_3134_ = ((lean_object*)(l_Std_ExtDTreeMap_values___redArg___closed__0));
v___x_3135_ = lean_box(0);
v___x_3136_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3137_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3136_, v___f_3134_, v___x_3135_, v_t_3133_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values(lean_object* v_00_u03b1_3138_, lean_object* v_cmp_3139_, lean_object* v_inst_3140_, lean_object* v_00_u03b2_3141_, lean_object* v_t_3142_){
_start:
{
lean_object* v___f_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___f_3143_ = ((lean_object*)(l_Std_ExtDTreeMap_values___redArg___closed__0));
v___x_3144_ = lean_box(0);
v___x_3145_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3146_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3145_, v___f_3143_, v___x_3144_, v_t_3142_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___boxed(lean_object* v_00_u03b1_3147_, lean_object* v_cmp_3148_, lean_object* v_inst_3149_, lean_object* v_00_u03b2_3150_, lean_object* v_t_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Std_ExtDTreeMap_values(v_00_u03b1_3147_, v_cmp_3148_, v_inst_3149_, v_00_u03b2_3150_, v_t_3151_);
lean_dec_ref(v_cmp_3148_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_3153_, lean_object* v_x_3154_, lean_object* v_v_3155_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = lean_array_push(v_l_3153_, v_v_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_3157_, lean_object* v_x_3158_, lean_object* v_v_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(v_l_3157_, v_x_3158_, v_v_3159_);
lean_dec(v_x_3158_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg(lean_object* v_t_3162_){
_start:
{
lean_object* v___f_3163_; lean_object* v___y_3165_; 
v___f_3163_ = ((lean_object*)(l_Std_ExtDTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_3162_) == 0)
{
lean_object* v_size_3168_; 
v_size_3168_ = lean_ctor_get(v_t_3162_, 0);
lean_inc(v_size_3168_);
v___y_3165_ = v_size_3168_;
goto v___jp_3164_;
}
else
{
lean_object* v___x_3169_; 
v___x_3169_ = lean_unsigned_to_nat(0u);
v___y_3165_ = v___x_3169_;
goto v___jp_3164_;
}
v___jp_3164_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = lean_mk_empty_array_with_capacity(v___y_3165_);
lean_dec(v___y_3165_);
v___x_3167_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3163_, v___x_3166_, v_t_3162_);
return v___x_3167_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray(lean_object* v_00_u03b1_3170_, lean_object* v_cmp_3171_, lean_object* v_inst_3172_, lean_object* v_00_u03b2_3173_, lean_object* v_t_3174_){
_start:
{
lean_object* v___f_3175_; lean_object* v___y_3177_; 
v___f_3175_ = ((lean_object*)(l_Std_ExtDTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_3174_) == 0)
{
lean_object* v_size_3180_; 
v_size_3180_ = lean_ctor_get(v_t_3174_, 0);
lean_inc(v_size_3180_);
v___y_3177_ = v_size_3180_;
goto v___jp_3176_;
}
else
{
lean_object* v___x_3181_; 
v___x_3181_ = lean_unsigned_to_nat(0u);
v___y_3177_ = v___x_3181_;
goto v___jp_3176_;
}
v___jp_3176_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = lean_mk_empty_array_with_capacity(v___y_3177_);
lean_dec(v___y_3177_);
v___x_3179_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3175_, v___x_3178_, v_t_3174_);
return v___x_3179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_3182_, lean_object* v_cmp_3183_, lean_object* v_inst_3184_, lean_object* v_00_u03b2_3185_, lean_object* v_t_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Std_ExtDTreeMap_valuesArray(v_00_u03b1_3182_, v_cmp_3183_, v_inst_3184_, v_00_u03b2_3185_, v_t_3186_);
lean_dec_ref(v_cmp_3183_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___redArg___lam__0(lean_object* v_x1_3188_, lean_object* v_x2_3189_, lean_object* v_x3_3190_){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v_x1_3188_);
lean_ctor_set(v___x_3191_, 1, v_x2_3189_);
v___x_3192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v_x3_3190_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___redArg(lean_object* v_t_3194_){
_start:
{
lean_object* v___f_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___f_3195_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3196_ = lean_box(0);
v___x_3197_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3198_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3197_, v___f_3195_, v___x_3196_, v_t_3194_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList(lean_object* v_00_u03b1_3199_, lean_object* v_00_u03b2_3200_, lean_object* v_cmp_3201_, lean_object* v_inst_3202_, lean_object* v_t_3203_){
_start:
{
lean_object* v___f_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___f_3204_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3205_ = lean_box(0);
v___x_3206_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3207_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3206_, v___f_3204_, v___x_3205_, v_t_3203_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___boxed(lean_object* v_00_u03b1_3208_, lean_object* v_00_u03b2_3209_, lean_object* v_cmp_3210_, lean_object* v_inst_3211_, lean_object* v_t_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Std_ExtDTreeMap_toList(v_00_u03b1_3208_, v_00_u03b2_3209_, v_cmp_3210_, v_inst_3211_, v_t_3212_);
lean_dec_ref(v_cmp_3210_);
return v_res_3213_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_3215_, lean_object* v_a_3216_, lean_object* v_x_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_fst_3219_; lean_object* v_snd_3220_; lean_object* v_r_3221_; lean_object* v___x_3222_; 
v_fst_3219_ = lean_ctor_get(v_a_3216_, 0);
lean_inc(v_fst_3219_);
v_snd_3220_ = lean_ctor_get(v_a_3216_, 1);
lean_inc(v_snd_3220_);
lean_dec_ref(v_a_3216_);
v_r_3221_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3215_, v_fst_3219_, v_snd_3220_, v___y_3218_);
v___x_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3222_, 0, v_r_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg(lean_object* v_l_3223_, lean_object* v_cmp_3224_){
_start:
{
lean_object* v___f_3225_; lean_object* v___x_3226_; lean_object* v_r_3227_; lean_object* v___x_3228_; 
v___f_3225_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3225_, 0, v_cmp_3224_);
v___x_3226_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3227_ = lean_box(1);
v___x_3228_ = l_List_forIn_x27_loop___redArg(v___x_3226_, v___f_3225_, v_l_3223_, v_r_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg___boxed(lean_object* v_l_3229_, lean_object* v_cmp_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Std_ExtDTreeMap_ofList___redArg(v_l_3229_, v_cmp_3230_);
lean_dec(v_l_3229_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList(lean_object* v_00_u03b1_3232_, lean_object* v_00_u03b2_3233_, lean_object* v_l_3234_, lean_object* v_cmp_3235_){
_start:
{
lean_object* v___f_3236_; lean_object* v___x_3237_; lean_object* v_r_3238_; lean_object* v___x_3239_; 
v___f_3236_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3236_, 0, v_cmp_3235_);
v___x_3237_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3238_ = lean_box(1);
v___x_3239_ = l_List_forIn_x27_loop___redArg(v___x_3237_, v___f_3236_, v_l_3234_, v_r_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___boxed(lean_object* v_00_u03b1_3240_, lean_object* v_00_u03b2_3241_, lean_object* v_l_3242_, lean_object* v_cmp_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Std_ExtDTreeMap_ofList(v_00_u03b1_3240_, v_00_u03b2_3241_, v_l_3242_, v_cmp_3243_);
lean_dec(v_l_3242_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___redArg___lam__0(lean_object* v_l_3245_, lean_object* v_k_3246_, lean_object* v_v_3247_){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_k_3246_);
lean_ctor_set(v___x_3248_, 1, v_v_3247_);
v___x_3249_ = lean_array_push(v_l_3245_, v___x_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___redArg(lean_object* v_t_3251_){
_start:
{
lean_object* v___f_3252_; lean_object* v___y_3254_; 
v___f_3252_ = ((lean_object*)(l_Std_ExtDTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3251_) == 0)
{
lean_object* v_size_3257_; 
v_size_3257_ = lean_ctor_get(v_t_3251_, 0);
lean_inc(v_size_3257_);
v___y_3254_ = v_size_3257_;
goto v___jp_3253_;
}
else
{
lean_object* v___x_3258_; 
v___x_3258_ = lean_unsigned_to_nat(0u);
v___y_3254_ = v___x_3258_;
goto v___jp_3253_;
}
v___jp_3253_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = lean_mk_empty_array_with_capacity(v___y_3254_);
lean_dec(v___y_3254_);
v___x_3256_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3252_, v___x_3255_, v_t_3251_);
return v___x_3256_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray(lean_object* v_00_u03b1_3259_, lean_object* v_00_u03b2_3260_, lean_object* v_cmp_3261_, lean_object* v_inst_3262_, lean_object* v_t_3263_){
_start:
{
lean_object* v___f_3264_; lean_object* v___y_3266_; 
v___f_3264_ = ((lean_object*)(l_Std_ExtDTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3263_) == 0)
{
lean_object* v_size_3269_; 
v_size_3269_ = lean_ctor_get(v_t_3263_, 0);
lean_inc(v_size_3269_);
v___y_3266_ = v_size_3269_;
goto v___jp_3265_;
}
else
{
lean_object* v___x_3270_; 
v___x_3270_ = lean_unsigned_to_nat(0u);
v___y_3266_ = v___x_3270_;
goto v___jp_3265_;
}
v___jp_3265_:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = lean_mk_empty_array_with_capacity(v___y_3266_);
lean_dec(v___y_3266_);
v___x_3268_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3264_, v___x_3267_, v_t_3263_);
return v___x_3268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___boxed(lean_object* v_00_u03b1_3271_, lean_object* v_00_u03b2_3272_, lean_object* v_cmp_3273_, lean_object* v_inst_3274_, lean_object* v_t_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Std_ExtDTreeMap_toArray(v_00_u03b1_3271_, v_00_u03b2_3272_, v_cmp_3273_, v_inst_3274_, v_t_3275_);
lean_dec_ref(v_cmp_3273_);
return v_res_3276_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray___redArg(lean_object* v_a_3278_, lean_object* v_cmp_3279_){
_start:
{
lean_object* v___f_3280_; lean_object* v___x_3281_; lean_object* v_r_3282_; size_t v_sz_3283_; size_t v___x_3284_; lean_object* v___x_3285_; 
v___f_3280_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3280_, 0, v_cmp_3279_);
v___x_3281_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3282_ = lean_box(1);
v_sz_3283_ = lean_array_size(v_a_3278_);
v___x_3284_ = ((size_t)0ULL);
v___x_3285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3281_, v_a_3278_, v___f_3280_, v_sz_3283_, v___x_3284_, v_r_3282_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray(lean_object* v_00_u03b1_3286_, lean_object* v_00_u03b2_3287_, lean_object* v_a_3288_, lean_object* v_cmp_3289_){
_start:
{
lean_object* v___f_3290_; lean_object* v___x_3291_; lean_object* v_r_3292_; size_t v_sz_3293_; size_t v___x_3294_; lean_object* v___x_3295_; 
v___f_3290_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3290_, 0, v_cmp_3289_);
v___x_3291_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3292_ = lean_box(1);
v_sz_3293_ = lean_array_size(v_a_3288_);
v___x_3294_ = ((size_t)0ULL);
v___x_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3291_, v_a_3288_, v___f_3290_, v_sz_3293_, v___x_3294_, v_r_3292_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_modify___redArg(lean_object* v_cmp_3296_, lean_object* v_t_3297_, lean_object* v_a_3298_, lean_object* v_f_3299_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3296_, v_a_3298_, v_f_3299_, v_t_3297_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_modify(lean_object* v_00_u03b1_3301_, lean_object* v_00_u03b2_3302_, lean_object* v_cmp_3303_, lean_object* v_inst_3304_, lean_object* v_inst_3305_, lean_object* v_t_3306_, lean_object* v_a_3307_, lean_object* v_f_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3303_, v_a_3307_, v_f_3308_, v_t_3306_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_alter___redArg(lean_object* v_cmp_3310_, lean_object* v_t_3311_, lean_object* v_a_3312_, lean_object* v_f_3313_){
_start:
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3310_, v_a_3312_, v_f_3313_, v_t_3311_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_alter(lean_object* v_00_u03b1_3315_, lean_object* v_00_u03b2_3316_, lean_object* v_cmp_3317_, lean_object* v_inst_3318_, lean_object* v_inst_3319_, lean_object* v_t_3320_, lean_object* v_a_3321_, lean_object* v_f_3322_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3317_, v_a_3321_, v_f_3322_, v_t_3320_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_3324_, lean_object* v_mergeFn_3325_, lean_object* v_a_3326_, lean_object* v_x_3327_){
_start:
{
if (lean_obj_tag(v_x_3327_) == 0)
{
lean_object* v___x_3328_; 
lean_dec(v_a_3326_);
lean_dec(v_mergeFn_3325_);
v___x_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_b_u2082_3324_);
return v___x_3328_;
}
else
{
lean_object* v_val_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3337_; 
v_val_3329_ = lean_ctor_get(v_x_3327_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_x_3327_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3331_ = v_x_3327_;
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_val_3329_);
lean_dec(v_x_3327_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3333_ = lean_apply_3(v_mergeFn_3325_, v_a_3326_, v_val_3329_, v_b_u2082_3324_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3333_);
v___x_3335_ = v___x_3331_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3338_, lean_object* v_cmp_3339_, lean_object* v_t_3340_, lean_object* v_a_3341_, lean_object* v_b_u2082_3342_){
_start:
{
lean_object* v___f_3343_; lean_object* v___x_3344_; 
lean_inc(v_a_3341_);
v___f_3343_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3343_, 0, v_b_u2082_3342_);
lean_closure_set(v___f_3343_, 1, v_mergeFn_3338_);
lean_closure_set(v___f_3343_, 2, v_a_3341_);
v___x_3344_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3339_, v_a_3341_, v___f_3343_, v_t_3340_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg(lean_object* v_cmp_3345_, lean_object* v_mergeFn_3346_, lean_object* v_t_u2081_3347_, lean_object* v_t_u2082_3348_){
_start:
{
lean_object* v___f_3349_; lean_object* v___x_3350_; 
v___f_3349_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3349_, 0, v_mergeFn_3346_);
lean_closure_set(v___f_3349_, 1, v_cmp_3345_);
v___x_3350_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3349_, v_t_u2081_3347_, v_t_u2082_3348_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith(lean_object* v_00_u03b1_3351_, lean_object* v_00_u03b2_3352_, lean_object* v_cmp_3353_, lean_object* v_inst_3354_, lean_object* v_inst_3355_, lean_object* v_mergeFn_3356_, lean_object* v_t_u2081_3357_, lean_object* v_t_u2082_3358_){
_start:
{
lean_object* v___f_3359_; lean_object* v___x_3360_; 
v___f_3359_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3359_, 0, v_mergeFn_3356_);
lean_closure_set(v___f_3359_, 1, v_cmp_3353_);
v___x_3360_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3359_, v_t_u2081_3357_, v_t_u2082_3358_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___redArg___lam__0(lean_object* v_x1_3361_, lean_object* v_x2_3362_, lean_object* v_x3_3363_){
_start:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v_x1_3361_);
lean_ctor_set(v___x_3364_, 1, v_x2_3362_);
v___x_3365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
lean_ctor_set(v___x_3365_, 1, v_x3_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___redArg(lean_object* v_t_3367_){
_start:
{
lean_object* v___f_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___f_3368_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toList___redArg___closed__0));
v___x_3369_ = lean_box(0);
v___x_3370_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3371_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3370_, v___f_3368_, v___x_3369_, v_t_3367_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList(lean_object* v_00_u03b1_3372_, lean_object* v_cmp_3373_, lean_object* v_00_u03b2_3374_, lean_object* v_inst_3375_, lean_object* v_t_3376_){
_start:
{
lean_object* v___f_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___f_3377_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toList___redArg___closed__0));
v___x_3378_ = lean_box(0);
v___x_3379_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3380_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3379_, v___f_3377_, v___x_3378_, v_t_3376_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___boxed(lean_object* v_00_u03b1_3381_, lean_object* v_cmp_3382_, lean_object* v_00_u03b2_3383_, lean_object* v_inst_3384_, lean_object* v_t_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Std_ExtDTreeMap_Const_toList(v_00_u03b1_3381_, v_cmp_3382_, v_00_u03b2_3383_, v_inst_3384_, v_t_3385_);
lean_dec_ref(v_cmp_3382_);
return v_res_3386_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_3387_; 
v___x_3387_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0(lean_object* v_cmp_3388_, lean_object* v_a_3389_, lean_object* v_x_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_fst_3392_; lean_object* v_snd_3393_; lean_object* v_r_3394_; lean_object* v___x_3395_; 
v_fst_3392_ = lean_ctor_get(v_a_3389_, 0);
lean_inc(v_fst_3392_);
v_snd_3393_ = lean_ctor_get(v_a_3389_, 1);
lean_inc(v_snd_3393_);
lean_dec_ref(v_a_3389_);
v_r_3394_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3388_, v_fst_3392_, v_snd_3393_, v___y_3391_);
v___x_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3395_, 0, v_r_3394_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg(lean_object* v_l_3396_, lean_object* v_cmp_3397_){
_start:
{
lean_object* v___f_3398_; lean_object* v___x_3399_; lean_object* v_r_3400_; lean_object* v___x_3401_; 
v___f_3398_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3398_, 0, v_cmp_3397_);
v___x_3399_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3400_ = lean_box(1);
v___x_3401_ = l_List_forIn_x27_loop___redArg(v___x_3399_, v___f_3398_, v_l_3396_, v_r_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg___boxed(lean_object* v_l_3402_, lean_object* v_cmp_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_Std_ExtDTreeMap_Const_ofList___redArg(v_l_3402_, v_cmp_3403_);
lean_dec(v_l_3402_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList(lean_object* v_00_u03b1_3405_, lean_object* v_00_u03b2_3406_, lean_object* v_l_3407_, lean_object* v_cmp_3408_){
_start:
{
lean_object* v___f_3409_; lean_object* v___x_3410_; lean_object* v_r_3411_; lean_object* v___x_3412_; 
v___f_3409_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3409_, 0, v_cmp_3408_);
v___x_3410_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3411_ = lean_box(1);
v___x_3412_ = l_List_forIn_x27_loop___redArg(v___x_3410_, v___f_3409_, v_l_3407_, v_r_3411_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___boxed(lean_object* v_00_u03b1_3413_, lean_object* v_00_u03b2_3414_, lean_object* v_l_3415_, lean_object* v_cmp_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Std_ExtDTreeMap_Const_ofList(v_00_u03b1_3413_, v_00_u03b2_3414_, v_l_3415_, v_cmp_3416_);
lean_dec(v_l_3415_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg___lam__0(lean_object* v_acc_3418_, lean_object* v_k_3419_, lean_object* v_v_3420_){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3421_, 0, v_k_3419_);
lean_ctor_set(v___x_3421_, 1, v_v_3420_);
v___x_3422_ = lean_array_push(v_acc_3418_, v___x_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg(lean_object* v_t_3426_){
_start:
{
lean_object* v___f_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___f_3427_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0));
v___x_3428_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1));
v___x_3429_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3427_, v___x_3428_, v_t_3426_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray(lean_object* v_00_u03b1_3430_, lean_object* v_cmp_3431_, lean_object* v_00_u03b2_3432_, lean_object* v_inst_3433_, lean_object* v_t_3434_){
_start:
{
lean_object* v___f_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___f_3435_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0));
v___x_3436_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1));
v___x_3437_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3435_, v___x_3436_, v_t_3434_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___boxed(lean_object* v_00_u03b1_3438_, lean_object* v_cmp_3439_, lean_object* v_00_u03b2_3440_, lean_object* v_inst_3441_, lean_object* v_t_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Std_ExtDTreeMap_Const_toArray(v_00_u03b1_3438_, v_cmp_3439_, v_00_u03b2_3440_, v_inst_3441_, v_t_3442_);
lean_dec_ref(v_cmp_3439_);
return v_res_3443_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray___redArg(lean_object* v_a_3445_, lean_object* v_cmp_3446_){
_start:
{
lean_object* v___f_3447_; lean_object* v___x_3448_; lean_object* v_r_3449_; size_t v_sz_3450_; size_t v___x_3451_; lean_object* v___x_3452_; 
v___f_3447_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3447_, 0, v_cmp_3446_);
v___x_3448_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3449_ = lean_box(1);
v_sz_3450_ = lean_array_size(v_a_3445_);
v___x_3451_ = ((size_t)0ULL);
v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3448_, v_a_3445_, v___f_3447_, v_sz_3450_, v___x_3451_, v_r_3449_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray(lean_object* v_00_u03b1_3453_, lean_object* v_00_u03b2_3454_, lean_object* v_a_3455_, lean_object* v_cmp_3456_){
_start:
{
lean_object* v___f_3457_; lean_object* v___x_3458_; lean_object* v_r_3459_; size_t v_sz_3460_; size_t v___x_3461_; lean_object* v___x_3462_; 
v___f_3457_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3457_, 0, v_cmp_3456_);
v___x_3458_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3459_ = lean_box(1);
v_sz_3460_ = lean_array_size(v_a_3455_);
v___x_3461_ = ((size_t)0ULL);
v___x_3462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3458_, v_a_3455_, v___f_3457_, v_sz_3460_, v___x_3461_, v_r_3459_);
return v___x_3462_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_3464_, lean_object* v_a_3465_, lean_object* v_x_3466_, lean_object* v___y_3467_){
_start:
{
uint8_t v___x_3468_; 
lean_inc(v___y_3467_);
lean_inc(v_a_3465_);
lean_inc_ref(v_cmp_3464_);
v___x_3468_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3464_, v_a_3465_, v___y_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = lean_box(0);
v___x_3470_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3464_, v_a_3465_, v___x_3469_, v___y_3467_);
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
return v___x_3471_;
}
else
{
lean_object* v___x_3472_; 
lean_dec(v_a_3465_);
lean_dec_ref(v_cmp_3464_);
v___x_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3472_, 0, v___y_3467_);
return v___x_3472_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg(lean_object* v_l_3473_, lean_object* v_cmp_3474_){
_start:
{
lean_object* v___f_3475_; lean_object* v___x_3476_; lean_object* v_r_3477_; lean_object* v___x_3478_; 
v___f_3475_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3475_, 0, v_cmp_3474_);
v___x_3476_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3477_ = lean_box(1);
v___x_3478_ = l_List_forIn_x27_loop___redArg(v___x_3476_, v___f_3475_, v_l_3473_, v_r_3477_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg___boxed(lean_object* v_l_3479_, lean_object* v_cmp_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Std_ExtDTreeMap_Const_unitOfList___redArg(v_l_3479_, v_cmp_3480_);
lean_dec(v_l_3479_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList(lean_object* v_00_u03b1_3482_, lean_object* v_l_3483_, lean_object* v_cmp_3484_){
_start:
{
lean_object* v___f_3485_; lean_object* v___x_3486_; lean_object* v_r_3487_; lean_object* v___x_3488_; 
v___f_3485_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3485_, 0, v_cmp_3484_);
v___x_3486_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3487_ = lean_box(1);
v___x_3488_ = l_List_forIn_x27_loop___redArg(v___x_3486_, v___f_3485_, v_l_3483_, v_r_3487_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___boxed(lean_object* v_00_u03b1_3489_, lean_object* v_l_3490_, lean_object* v_cmp_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Std_ExtDTreeMap_Const_unitOfList(v_00_u03b1_3489_, v_l_3490_, v_cmp_3491_);
lean_dec(v_l_3490_);
return v_res_3492_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray___redArg(lean_object* v_a_3494_, lean_object* v_cmp_3495_){
_start:
{
lean_object* v___f_3496_; lean_object* v___x_3497_; lean_object* v_r_3498_; size_t v_sz_3499_; size_t v___x_3500_; lean_object* v___x_3501_; 
v___f_3496_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3496_, 0, v_cmp_3495_);
v___x_3497_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3498_ = lean_box(1);
v_sz_3499_ = lean_array_size(v_a_3494_);
v___x_3500_ = ((size_t)0ULL);
v___x_3501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3497_, v_a_3494_, v___f_3496_, v_sz_3499_, v___x_3500_, v_r_3498_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray(lean_object* v_00_u03b1_3502_, lean_object* v_a_3503_, lean_object* v_cmp_3504_){
_start:
{
lean_object* v___f_3505_; lean_object* v___x_3506_; lean_object* v_r_3507_; size_t v_sz_3508_; size_t v___x_3509_; lean_object* v___x_3510_; 
v___f_3505_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3505_, 0, v_cmp_3504_);
v___x_3506_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3507_ = lean_box(1);
v_sz_3508_ = lean_array_size(v_a_3503_);
v___x_3509_ = ((size_t)0ULL);
v___x_3510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3506_, v_a_3503_, v___f_3505_, v_sz_3508_, v___x_3509_, v_r_3507_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_modify___redArg(lean_object* v_cmp_3511_, lean_object* v_t_3512_, lean_object* v_a_3513_, lean_object* v_f_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3511_, v_a_3513_, v_f_3514_, v_t_3512_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_modify(lean_object* v_00_u03b1_3516_, lean_object* v_cmp_3517_, lean_object* v_00_u03b2_3518_, lean_object* v_inst_3519_, lean_object* v_t_3520_, lean_object* v_a_3521_, lean_object* v_f_3522_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3517_, v_a_3521_, v_f_3522_, v_t_3520_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_alter___redArg(lean_object* v_cmp_3524_, lean_object* v_t_3525_, lean_object* v_a_3526_, lean_object* v_f_3527_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3524_, v_a_3526_, v_f_3527_, v_t_3525_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_alter(lean_object* v_00_u03b1_3529_, lean_object* v_cmp_3530_, lean_object* v_00_u03b2_3531_, lean_object* v_inst_3532_, lean_object* v_t_3533_, lean_object* v_a_3534_, lean_object* v_f_3535_){
_start:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3530_, v_a_3534_, v_f_3535_, v_t_3533_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3537_, lean_object* v_cmp_3538_, lean_object* v_t_3539_, lean_object* v_a_3540_, lean_object* v_b_u2082_3541_){
_start:
{
lean_object* v___f_3542_; lean_object* v___x_3543_; 
lean_inc(v_a_3540_);
v___f_3542_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3542_, 0, v_b_u2082_3541_);
lean_closure_set(v___f_3542_, 1, v_mergeFn_3537_);
lean_closure_set(v___f_3542_, 2, v_a_3540_);
v___x_3543_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3538_, v_a_3540_, v___f_3542_, v_t_3539_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith___redArg(lean_object* v_cmp_3544_, lean_object* v_mergeFn_3545_, lean_object* v_t_u2081_3546_, lean_object* v_t_u2082_3547_){
_start:
{
lean_object* v___f_3548_; lean_object* v___x_3549_; 
v___f_3548_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3548_, 0, v_mergeFn_3545_);
lean_closure_set(v___f_3548_, 1, v_cmp_3544_);
v___x_3549_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3548_, v_t_u2081_3546_, v_t_u2082_3547_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith(lean_object* v_00_u03b1_3550_, lean_object* v_cmp_3551_, lean_object* v_00_u03b2_3552_, lean_object* v_inst_3553_, lean_object* v_mergeFn_3554_, lean_object* v_t_u2081_3555_, lean_object* v_t_u2082_3556_){
_start:
{
lean_object* v___f_3557_; lean_object* v___x_3558_; 
v___f_3557_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3557_, 0, v_mergeFn_3554_);
lean_closure_set(v___f_3557_, 1, v_cmp_3551_);
v___x_3558_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3557_, v_t_u2081_3555_, v_t_u2082_3556_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_3559_, lean_object* v_x_3560_, lean_object* v_____s_3561_){
_start:
{
lean_object* v_fst_3562_; lean_object* v_snd_3563_; lean_object* v_acc_3564_; lean_object* v___x_3565_; 
v_fst_3562_ = lean_ctor_get(v_x_3560_, 0);
lean_inc(v_fst_3562_);
v_snd_3563_ = lean_ctor_get(v_x_3560_, 1);
lean_inc(v_snd_3563_);
lean_dec_ref(v_x_3560_);
v_acc_3564_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3559_, v_fst_3562_, v_snd_3563_, v_____s_3561_);
v___x_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3565_, 0, v_acc_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany___redArg(lean_object* v_cmp_3566_, lean_object* v_inst_3567_, lean_object* v_t_3568_, lean_object* v_l_3569_){
_start:
{
lean_object* v___f_3570_; lean_object* v___x_3571_; 
v___f_3570_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3570_, 0, v_cmp_3566_);
v___x_3571_ = lean_apply_4(v_inst_3567_, lean_box(0), v_l_3569_, v_t_3568_, v___f_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany(lean_object* v_00_u03b1_3572_, lean_object* v_00_u03b2_3573_, lean_object* v_cmp_3574_, lean_object* v_inst_3575_, lean_object* v_00_u03c1_3576_, lean_object* v_inst_3577_, lean_object* v_t_3578_, lean_object* v_l_3579_){
_start:
{
lean_object* v___f_3580_; lean_object* v___x_3581_; 
v___f_3580_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3580_, 0, v_cmp_3574_);
v___x_3581_ = lean_apply_4(v_inst_3577_, lean_box(0), v_l_3579_, v_t_3578_, v___f_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_3582_, lean_object* v_a_3583_, lean_object* v_____s_3584_){
_start:
{
lean_object* v_acc_3585_; lean_object* v___x_3586_; 
v_acc_3585_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_3582_, v_a_3583_, v_____s_3584_);
v___x_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3586_, 0, v_acc_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany___redArg(lean_object* v_cmp_3587_, lean_object* v_inst_3588_, lean_object* v_t_3589_, lean_object* v_l_3590_){
_start:
{
lean_object* v___f_3591_; lean_object* v___x_3592_; 
v___f_3591_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3591_, 0, v_cmp_3587_);
v___x_3592_ = lean_apply_4(v_inst_3588_, lean_box(0), v_l_3590_, v_t_3589_, v___f_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany(lean_object* v_00_u03b1_3593_, lean_object* v_00_u03b2_3594_, lean_object* v_cmp_3595_, lean_object* v_inst_3596_, lean_object* v_00_u03c1_3597_, lean_object* v_inst_3598_, lean_object* v_t_3599_, lean_object* v_l_3600_){
_start:
{
lean_object* v___f_3601_; lean_object* v___x_3602_; 
v___f_3601_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3601_, 0, v_cmp_3595_);
v___x_3602_ = lean_apply_4(v_inst_3598_, lean_box(0), v_l_3600_, v_t_3599_, v___f_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0(lean_object* v_cmp_3603_, lean_object* v_x_3604_, lean_object* v_____s_3605_){
_start:
{
lean_object* v_fst_3606_; lean_object* v_snd_3607_; lean_object* v_acc_3608_; lean_object* v___x_3609_; 
v_fst_3606_ = lean_ctor_get(v_x_3604_, 0);
lean_inc(v_fst_3606_);
v_snd_3607_ = lean_ctor_get(v_x_3604_, 1);
lean_inc(v_snd_3607_);
lean_dec_ref(v_x_3604_);
v_acc_3608_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3603_, v_fst_3606_, v_snd_3607_, v_____s_3605_);
v___x_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3609_, 0, v_acc_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany___redArg(lean_object* v_cmp_3610_, lean_object* v_inst_3611_, lean_object* v_t_3612_, lean_object* v_l_3613_){
_start:
{
lean_object* v___f_3614_; lean_object* v___x_3615_; 
v___f_3614_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3614_, 0, v_cmp_3610_);
v___x_3615_ = lean_apply_4(v_inst_3611_, lean_box(0), v_l_3613_, v_t_3612_, v___f_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany(lean_object* v_00_u03b1_3616_, lean_object* v_cmp_3617_, lean_object* v_00_u03b2_3618_, lean_object* v_inst_3619_, lean_object* v_00_u03c1_3620_, lean_object* v_inst_3621_, lean_object* v_t_3622_, lean_object* v_l_3623_){
_start:
{
lean_object* v___f_3624_; lean_object* v___x_3625_; 
v___f_3624_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3624_, 0, v_cmp_3617_);
v___x_3625_ = lean_apply_4(v_inst_3621_, lean_box(0), v_l_3623_, v_t_3622_, v___f_3624_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_3626_, lean_object* v_a_3627_, lean_object* v_____s_3628_){
_start:
{
uint8_t v___x_3629_; 
lean_inc(v_____s_3628_);
lean_inc(v_a_3627_);
lean_inc_ref(v_cmp_3626_);
v___x_3629_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3626_, v_a_3627_, v_____s_3628_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3630_ = lean_box(0);
v___x_3631_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3626_, v_a_3627_, v___x_3630_, v_____s_3628_);
v___x_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
return v___x_3632_;
}
else
{
lean_object* v___x_3633_; 
lean_dec(v_a_3627_);
lean_dec_ref(v_cmp_3626_);
v___x_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3633_, 0, v_____s_3628_);
return v___x_3633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_3634_, lean_object* v_inst_3635_, lean_object* v_t_3636_, lean_object* v_l_3637_){
_start:
{
lean_object* v___f_3638_; lean_object* v___x_3639_; 
v___f_3638_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3638_, 0, v_cmp_3634_);
v___x_3639_ = lean_apply_4(v_inst_3635_, lean_box(0), v_l_3637_, v_t_3636_, v___f_3638_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_3640_, lean_object* v_cmp_3641_, lean_object* v_inst_3642_, lean_object* v_00_u03c1_3643_, lean_object* v_inst_3644_, lean_object* v_t_3645_, lean_object* v_l_3646_){
_start:
{
lean_object* v___f_3647_; lean_object* v___x_3648_; 
v___f_3647_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3647_, 0, v_cmp_3641_);
v___x_3648_ = lean_apply_4(v_inst_3644_, lean_box(0), v_l_3646_, v_t_3645_, v___f_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_union___redArg(lean_object* v_cmp_3649_, lean_object* v_m_u2081_3650_, lean_object* v_m_u2082_3651_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3649_, v_m_u2081_3650_, v_m_u2082_3651_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_union(lean_object* v_00_u03b1_3653_, lean_object* v_00_u03b2_3654_, lean_object* v_cmp_3655_, lean_object* v_inst_3656_, lean_object* v_m_u2081_3657_, lean_object* v_m_u2082_3658_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3655_, v_m_u2081_3657_, v_m_u2082_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instUnionOfTransCmp___redArg(lean_object* v_cmp_3660_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_union), 6, 4);
lean_closure_set(v___x_3661_, 0, lean_box(0));
lean_closure_set(v___x_3661_, 1, lean_box(0));
lean_closure_set(v___x_3661_, 2, v_cmp_3660_);
lean_closure_set(v___x_3661_, 3, lean_box(0));
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instUnionOfTransCmp(lean_object* v_00_u03b1_3662_, lean_object* v_00_u03b2_3663_, lean_object* v_cmp_3664_, lean_object* v_inst_3665_){
_start:
{
lean_object* v___x_3666_; 
v___x_3666_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_union), 6, 4);
lean_closure_set(v___x_3666_, 0, lean_box(0));
lean_closure_set(v___x_3666_, 1, lean_box(0));
lean_closure_set(v___x_3666_, 2, v_cmp_3664_);
lean_closure_set(v___x_3666_, 3, lean_box(0));
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_inter___redArg(lean_object* v_cmp_3667_, lean_object* v_m_u2081_3668_, lean_object* v_m_u2082_3669_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3667_, v_m_u2081_3668_, v_m_u2082_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_inter(lean_object* v_00_u03b1_3671_, lean_object* v_00_u03b2_3672_, lean_object* v_cmp_3673_, lean_object* v_inst_3674_, lean_object* v_m_u2081_3675_, lean_object* v_m_u2082_3676_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3673_, v_m_u2081_3675_, v_m_u2082_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInterOfTransCmp___redArg(lean_object* v_cmp_3678_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_inter), 6, 4);
lean_closure_set(v___x_3679_, 0, lean_box(0));
lean_closure_set(v___x_3679_, 1, lean_box(0));
lean_closure_set(v___x_3679_, 2, v_cmp_3678_);
lean_closure_set(v___x_3679_, 3, lean_box(0));
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInterOfTransCmp(lean_object* v_00_u03b1_3680_, lean_object* v_00_u03b2_3681_, lean_object* v_cmp_3682_, lean_object* v_inst_3683_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_inter), 6, 4);
lean_closure_set(v___x_3684_, 0, lean_box(0));
lean_closure_set(v___x_3684_, 1, lean_box(0));
lean_closure_set(v___x_3684_, 2, v_cmp_3682_);
lean_closure_set(v___x_3684_, 3, lean_box(0));
return v___x_3684_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(lean_object* v_cmp_3685_, lean_object* v_inst_3686_, lean_object* v_x_3687_, lean_object* v_y_3688_){
_start:
{
uint8_t v___x_3689_; 
v___x_3689_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3685_, v_inst_3686_, v_x_3687_, v_y_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_3690_, lean_object* v_inst_3691_, lean_object* v_x_3692_, lean_object* v_y_3693_){
_start:
{
uint8_t v_res_3694_; lean_object* v_r_3695_; 
v_res_3694_ = l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(v_cmp_3690_, v_inst_3691_, v_x_3692_, v_y_3693_);
v_r_3695_ = lean_box(v_res_3694_);
return v_r_3695_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(lean_object* v_cmp_3696_, lean_object* v_inst_3697_){
_start:
{
lean_object* v___f_3698_; lean_object* v___x_3699_; 
lean_inc_ref(v_cmp_3696_);
v___f_3698_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3698_, 0, v_cmp_3696_);
lean_closure_set(v___f_3698_, 1, v_inst_3697_);
v___x_3699_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_lift_u2082___boxed), 8, 6);
lean_closure_set(v___x_3699_, 0, lean_box(0));
lean_closure_set(v___x_3699_, 1, lean_box(0));
lean_closure_set(v___x_3699_, 2, v_cmp_3696_);
lean_closure_set(v___x_3699_, 3, lean_box(0));
lean_closure_set(v___x_3699_, 4, v___f_3698_);
lean_closure_set(v___x_3699_, 5, lean_box(0));
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp(lean_object* v_00_u03b1_3700_, lean_object* v_00_u03b2_3701_, lean_object* v_cmp_3702_, lean_object* v_inst_3703_, lean_object* v_inst_3704_, lean_object* v_inst_3705_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_3702_, v_inst_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object* v_cmp_3707_, lean_object* v_inst_3708_, lean_object* v_x_3709_, lean_object* v_x_3710_){
_start:
{
uint8_t v___x_3711_; 
v___x_3711_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3707_, v_inst_3708_, v_x_3709_, v_x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_3712_, lean_object* v_inst_3713_, lean_object* v_x_3714_, lean_object* v_x_3715_){
_start:
{
uint8_t v_res_3716_; lean_object* v_r_3717_; 
v_res_3716_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(v_cmp_3712_, v_inst_3713_, v_x_3714_, v_x_3715_);
v_r_3717_ = lean_box(v_res_3716_);
return v_r_3717_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object* v_00_u03b1_3718_, lean_object* v_00_u03b2_3719_, lean_object* v_cmp_3720_, lean_object* v_inst_3721_, lean_object* v_inst_3722_, lean_object* v_inst_3723_, lean_object* v_inst_3724_, lean_object* v_x_3725_, lean_object* v_x_3726_){
_start:
{
uint8_t v___x_3727_; 
v___x_3727_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3720_, v_inst_3723_, v_x_3725_, v_x_3726_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_3728_, lean_object* v_00_u03b2_3729_, lean_object* v_cmp_3730_, lean_object* v_inst_3731_, lean_object* v_inst_3732_, lean_object* v_inst_3733_, lean_object* v_inst_3734_, lean_object* v_x_3735_, lean_object* v_x_3736_){
_start:
{
uint8_t v_res_3737_; lean_object* v_r_3738_; 
v_res_3737_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(v_00_u03b1_3728_, v_00_u03b2_3729_, v_cmp_3730_, v_inst_3731_, v_inst_3732_, v_inst_3733_, v_inst_3734_, v_x_3735_, v_x_3736_);
v_r_3738_ = lean_box(v_res_3737_);
return v_r_3738_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_Const_beq___redArg(lean_object* v_cmp_3739_, lean_object* v_inst_3740_, lean_object* v_m_u2081_3741_, lean_object* v_m_u2082_3742_){
_start:
{
uint8_t v___x_3743_; 
v___x_3743_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3739_, v_inst_3740_, v_m_u2081_3741_, v_m_u2082_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_beq___redArg___boxed(lean_object* v_cmp_3744_, lean_object* v_inst_3745_, lean_object* v_m_u2081_3746_, lean_object* v_m_u2082_3747_){
_start:
{
uint8_t v_res_3748_; lean_object* v_r_3749_; 
v_res_3748_ = l_Std_ExtDTreeMap_Const_beq___redArg(v_cmp_3744_, v_inst_3745_, v_m_u2081_3746_, v_m_u2082_3747_);
v_r_3749_ = lean_box(v_res_3748_);
return v_r_3749_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_Const_beq(lean_object* v_00_u03b1_3750_, lean_object* v_cmp_3751_, lean_object* v_00_u03b2_3752_, lean_object* v_inst_3753_, lean_object* v_inst_3754_, lean_object* v_m_u2081_3755_, lean_object* v_m_u2082_3756_){
_start:
{
uint8_t v___x_3757_; 
v___x_3757_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3751_, v_inst_3754_, v_m_u2081_3755_, v_m_u2082_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_beq___boxed(lean_object* v_00_u03b1_3758_, lean_object* v_cmp_3759_, lean_object* v_00_u03b2_3760_, lean_object* v_inst_3761_, lean_object* v_inst_3762_, lean_object* v_m_u2081_3763_, lean_object* v_m_u2082_3764_){
_start:
{
uint8_t v_res_3765_; lean_object* v_r_3766_; 
v_res_3765_ = l_Std_ExtDTreeMap_Const_beq(v_00_u03b1_3758_, v_cmp_3759_, v_00_u03b2_3760_, v_inst_3761_, v_inst_3762_, v_m_u2081_3763_, v_m_u2082_3764_);
v_r_3766_ = lean_box(v_res_3765_);
return v_r_3766_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_diff___redArg(lean_object* v_cmp_3767_, lean_object* v_m_u2081_3768_, lean_object* v_m_u2082_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_3767_, v_m_u2081_3768_, v_m_u2082_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_diff(lean_object* v_00_u03b1_3771_, lean_object* v_00_u03b2_3772_, lean_object* v_cmp_3773_, lean_object* v_inst_3774_, lean_object* v_m_u2081_3775_, lean_object* v_m_u2082_3776_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_3773_, v_m_u2081_3775_, v_m_u2082_3776_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSDiffOfTransCmp___redArg(lean_object* v_cmp_3778_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_diff), 6, 4);
lean_closure_set(v___x_3779_, 0, lean_box(0));
lean_closure_set(v___x_3779_, 1, lean_box(0));
lean_closure_set(v___x_3779_, 2, v_cmp_3778_);
lean_closure_set(v___x_3779_, 3, lean_box(0));
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSDiffOfTransCmp(lean_object* v_00_u03b1_3780_, lean_object* v_00_u03b2_3781_, lean_object* v_cmp_3782_, lean_object* v_inst_3783_){
_start:
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_diff), 6, 4);
lean_closure_set(v___x_3784_, 0, lean_box(0));
lean_closure_set(v___x_3784_, 1, lean_box(0));
lean_closure_set(v___x_3784_, 2, v_cmp_3782_);
lean_closure_set(v___x_3784_, 3, lean_box(0));
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_3788_, lean_object* v___x_3789_, lean_object* v_m_3790_, lean_object* v_prec_3791_){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3792_ = ((lean_object*)(l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_3793_ = lean_box(0);
v___x_3794_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3795_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3794_, v___f_3788_, v___x_3793_, v_m_3790_);
v___x_3796_ = l_List_repr___redArg(v___x_3789_, v___x_3795_);
v___x_3797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3792_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
v___x_3798_ = l_Repr_addAppParen(v___x_3797_, v_prec_3791_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_3799_, lean_object* v___x_3800_, lean_object* v_m_3801_, lean_object* v_prec_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(v___f_3799_, v___x_3800_, v_m_3801_, v_prec_3802_);
lean_dec(v_prec_3802_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(lean_object* v_inst_3804_, lean_object* v_inst_3805_){
_start:
{
lean_object* v___f_3806_; lean_object* v___x_3807_; lean_object* v___f_3808_; 
v___f_3806_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3807_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_3807_, 0, lean_box(0));
lean_closure_set(v___x_3807_, 1, lean_box(0));
lean_closure_set(v___x_3807_, 2, v_inst_3804_);
lean_closure_set(v___x_3807_, 3, v_inst_3805_);
v___f_3808_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3808_, 0, v___f_3806_);
lean_closure_set(v___f_3808_, 1, v___x_3807_);
return v___f_3808_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp(lean_object* v_00_u03b1_3809_, lean_object* v_00_u03b2_3810_, lean_object* v_cmp_3811_, lean_object* v_inst_3812_, lean_object* v_inst_3813_, lean_object* v_inst_3814_){
_start:
{
lean_object* v___x_3815_; 
v___x_3815_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(v_inst_3813_, v_inst_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_3816_, lean_object* v_00_u03b2_3817_, lean_object* v_cmp_3818_, lean_object* v_inst_3819_, lean_object* v_inst_3820_, lean_object* v_inst_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Std_ExtDTreeMap_instReprOfTransCmp(v_00_u03b1_3816_, v_00_u03b2_3817_, v_cmp_3818_, v_inst_3819_, v_inst_3820_, v_inst_3821_);
lean_dec_ref(v_cmp_3818_);
return v_res_3822_;
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
