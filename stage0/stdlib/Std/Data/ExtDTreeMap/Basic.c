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
lean_object* lean_string_utf8_byte_size(lean_object*);
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
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__15;
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__16;
static const lean_ctor_object l_Std_ExtDTreeMap___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtDTreeMap___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
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
static lean_once_cell_t l_Std_ExtDTreeMap___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDTreeMap___auto__1___closed__26;
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
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__15(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__14));
v___x_34_ = lean_string_utf8_byte_size(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__16(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__15, &l_Std_ExtDTreeMap___auto__1___closed__15_once, _init_l_Std_ExtDTreeMap___auto__1___closed__15);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__14));
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_35_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_41_ = lean_box(0);
v___x_42_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__17));
v___x_43_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__16, &l_Std_ExtDTreeMap___auto__1___closed__16_once, _init_l_Std_ExtDTreeMap___auto__1___closed__16);
v___x_44_ = lean_box(2);
v___x_45_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
lean_ctor_set(v___x_45_, 2, v___x_42_);
lean_ctor_set(v___x_45_, 3, v___x_41_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__18, &l_Std_ExtDTreeMap___auto__1___closed__18_once, _init_l_Std_ExtDTreeMap___auto__1___closed__18);
v___x_47_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__13, &l_Std_ExtDTreeMap___auto__1___closed__13_once, _init_l_Std_ExtDTreeMap___auto__1___closed__13);
v___x_48_ = lean_array_push(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__19, &l_Std_ExtDTreeMap___auto__1___closed__19_once, _init_l_Std_ExtDTreeMap___auto__1___closed__19);
v___x_50_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__11));
v___x_51_ = lean_box(2);
v___x_52_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__21(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__20, &l_Std_ExtDTreeMap___auto__1___closed__20_once, _init_l_Std_ExtDTreeMap___auto__1___closed__20);
v___x_54_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__5));
v___x_55_ = lean_array_push(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__22(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__21, &l_Std_ExtDTreeMap___auto__1___closed__21_once, _init_l_Std_ExtDTreeMap___auto__1___closed__21);
v___x_57_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__9));
v___x_58_ = lean_box(2);
v___x_59_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__23(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__22, &l_Std_ExtDTreeMap___auto__1___closed__22_once, _init_l_Std_ExtDTreeMap___auto__1___closed__22);
v___x_61_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__24(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__23, &l_Std_ExtDTreeMap___auto__1___closed__23_once, _init_l_Std_ExtDTreeMap___auto__1___closed__23);
v___x_64_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__7));
v___x_65_ = lean_box(2);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__25(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__24, &l_Std_ExtDTreeMap___auto__1___closed__24_once, _init_l_Std_ExtDTreeMap___auto__1___closed__24);
v___x_68_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__5));
v___x_69_ = lean_array_push(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1___closed__26(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__25, &l_Std_ExtDTreeMap___auto__1___closed__25_once, _init_l_Std_ExtDTreeMap___auto__1___closed__25);
v___x_71_ = ((lean_object*)(l_Std_ExtDTreeMap___auto__1___closed__4));
v___x_72_ = lean_box(2);
v___x_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_70_);
return v___x_73_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap___auto__1(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mk___redArg(lean_object* v_t_75_){
_start:
{
lean_inc(v_t_75_);
return v_t_75_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mk___redArg___boxed(lean_object* v_t_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_ExtDTreeMap_mk___redArg(v_t_76_);
lean_dec(v_t_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mk(lean_object* v_00_u03b1_78_, lean_object* v_00_u03b2_79_, lean_object* v_cmp_80_, lean_object* v_t_81_){
_start:
{
lean_inc(v_t_81_);
return v_t_81_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mk___boxed(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_cmp_84_, lean_object* v_t_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_ExtDTreeMap_mk(v_00_u03b1_82_, v_00_u03b2_83_, v_cmp_84_, v_t_85_);
lean_dec(v_t_85_);
lean_dec_ref(v_cmp_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift___redArg(lean_object* v_f_87_, lean_object* v_t_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_apply_1(v_f_87_, v_t_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift(lean_object* v_00_u03b1_90_, lean_object* v_00_u03b2_91_, lean_object* v_cmp_92_, lean_object* v_00_u03b3_93_, lean_object* v_f_94_, lean_object* v_h_95_, lean_object* v_t_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_apply_1(v_f_94_, v_t_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift___boxed(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_cmp_100_, lean_object* v_00_u03b3_101_, lean_object* v_f_102_, lean_object* v_h_103_, lean_object* v_t_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_ExtDTreeMap_lift(v_00_u03b1_98_, v_00_u03b2_99_, v_cmp_100_, v_00_u03b3_101_, v_f_102_, v_h_103_, v_t_104_);
lean_dec_ref(v_cmp_100_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift_u2082___redArg(lean_object* v_f_106_, lean_object* v_m_u2081_107_, lean_object* v_m_u2082_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_apply_2(v_f_106_, v_m_u2081_107_, v_m_u2082_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift_u2082(lean_object* v_00_u03b1_110_, lean_object* v_00_u03b2_111_, lean_object* v_cmp_112_, lean_object* v_00_u03b3_113_, lean_object* v_f_114_, lean_object* v_h_115_, lean_object* v_m_u2081_116_, lean_object* v_m_u2082_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_apply_2(v_f_114_, v_m_u2081_116_, v_m_u2082_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_lift_u2082___boxed(lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_cmp_121_, lean_object* v_00_u03b3_122_, lean_object* v_f_123_, lean_object* v_h_124_, lean_object* v_m_u2081_125_, lean_object* v_m_u2082_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_ExtDTreeMap_lift_u2082(v_00_u03b1_119_, v_00_u03b2_120_, v_cmp_121_, v_00_u03b3_122_, v_f_123_, v_h_124_, v_m_u2081_125_, v_m_u2082_126_);
lean_dec_ref(v_cmp_121_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_liftOn_u2082___redArg(lean_object* v_t_u2081_128_, lean_object* v_t_u2082_129_, lean_object* v_f_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_apply_2(v_f_130_, v_t_u2081_128_, v_t_u2082_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_liftOn_u2082(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v_cmp_134_, lean_object* v_00_u03b3_135_, lean_object* v_t_u2081_136_, lean_object* v_t_u2082_137_, lean_object* v_f_138_, lean_object* v_h_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_apply_2(v_f_138_, v_t_u2081_136_, v_t_u2082_137_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_liftOn_u2082___boxed(lean_object* v_00_u03b1_141_, lean_object* v_00_u03b2_142_, lean_object* v_cmp_143_, lean_object* v_00_u03b3_144_, lean_object* v_t_u2081_145_, lean_object* v_t_u2082_146_, lean_object* v_f_147_, lean_object* v_h_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_ExtDTreeMap_liftOn_u2082(v_00_u03b1_141_, v_00_u03b2_142_, v_cmp_143_, v_00_u03b3_144_, v_t_u2081_145_, v_t_u2082_146_, v_f_147_, v_h_148_);
lean_dec_ref(v_cmp_143_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_pliftOn___redArg(lean_object* v_t_150_, lean_object* v_f_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_apply_2(v_f_151_, v_t_150_, lean_box(0));
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_pliftOn(lean_object* v_00_u03b1_153_, lean_object* v_00_u03b2_154_, lean_object* v_cmp_155_, lean_object* v_00_u03b3_156_, lean_object* v_t_157_, lean_object* v_f_158_, lean_object* v_h_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_apply_2(v_f_158_, v_t_157_, lean_box(0));
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_pliftOn___boxed(lean_object* v_00_u03b1_161_, lean_object* v_00_u03b2_162_, lean_object* v_cmp_163_, lean_object* v_00_u03b3_164_, lean_object* v_t_165_, lean_object* v_f_166_, lean_object* v_h_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_ExtDTreeMap_pliftOn(v_00_u03b1_161_, v_00_u03b2_162_, v_cmp_163_, v_00_u03b3_164_, v_t_165_, v_f_166_, v_h_167_);
lean_dec_ref(v_cmp_163_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall___redArg(){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_box(0);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall___redArg___boxed(lean_object* v___dummy_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_ExtDTreeMap_instCoeTypeForall___redArg();
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall(lean_object* v_00_u03b1_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(0);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty___redArg(){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_box(1);
return v___x_176_;
}
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(1);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_ExtDTreeMap_instEmptyCollection___redArg();
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_cmp_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_box(1);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_cmp_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_ExtDTreeMap_instEmptyCollection(v_00_u03b1_195_, v_00_u03b2_196_, v_cmp_197_);
lean_dec_ref(v_cmp_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(1);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited___redArg___boxed(lean_object* v___dummy_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_ExtDTreeMap_instInhabited___redArg();
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited(lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_, lean_object* v_cmp_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(1);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited___boxed(lean_object* v_00_u03b1_207_, lean_object* v_00_u03b2_208_, lean_object* v_cmp_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_ExtDTreeMap_instInhabited(v_00_u03b1_207_, v_00_u03b2_208_, v_cmp_209_);
lean_dec_ref(v_cmp_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insert___redArg(lean_object* v_cmp_211_, lean_object* v_t_212_, lean_object* v_a_213_, lean_object* v_b_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_211_, v_a_213_, v_b_214_, v_t_212_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insert(lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_, lean_object* v_cmp_218_, lean_object* v_inst_219_, lean_object* v_t_220_, lean_object* v_a_221_, lean_object* v_b_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_218_, v_a_221_, v_b_222_, v_t_220_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0(lean_object* v_cmp_224_, lean_object* v_e_225_){
_start:
{
lean_object* v_fst_226_; lean_object* v_snd_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_fst_226_ = lean_ctor_get(v_e_225_, 0);
lean_inc(v_fst_226_);
v_snd_227_ = lean_ctor_get(v_e_225_, 1);
lean_inc(v_snd_227_);
lean_dec_ref(v_e_225_);
v___x_228_ = lean_box(1);
v___x_229_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_224_, v_fst_226_, v_snd_227_, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg(lean_object* v_cmp_230_){
_start:
{
lean_object* v___f_231_; 
v___f_231_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_231_, 0, v_cmp_230_);
return v___f_231_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp(lean_object* v_00_u03b1_232_, lean_object* v_00_u03b2_233_, lean_object* v_cmp_234_, lean_object* v_inst_235_){
_start:
{
lean_object* v___f_236_; 
v___f_236_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_236_, 0, v_cmp_234_);
return v___f_236_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0(lean_object* v_cmp_237_, lean_object* v_e_238_, lean_object* v_s_239_){
_start:
{
lean_object* v_fst_240_; lean_object* v_snd_241_; lean_object* v___x_242_; 
v_fst_240_ = lean_ctor_get(v_e_238_, 0);
lean_inc(v_fst_240_);
v_snd_241_ = lean_ctor_get(v_e_238_, 1);
lean_inc(v_snd_241_);
lean_dec_ref(v_e_238_);
v___x_242_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_237_, v_fst_240_, v_snd_241_, v_s_239_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg(lean_object* v_cmp_243_){
_start:
{
lean_object* v___f_244_; 
v___f_244_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_244_, 0, v_cmp_243_);
return v___f_244_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_cmp_247_, lean_object* v_inst_248_){
_start:
{
lean_object* v___f_249_; 
v___f_249_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_249_, 0, v_cmp_247_);
return v___f_249_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertIfNew___redArg(lean_object* v_cmp_250_, lean_object* v_t_251_, lean_object* v_a_252_, lean_object* v_b_253_){
_start:
{
uint8_t v___x_254_; 
lean_inc(v_t_251_);
lean_inc(v_a_252_);
lean_inc_ref(v_cmp_250_);
v___x_254_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_250_, v_a_252_, v_t_251_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_250_, v_a_252_, v_b_253_, v_t_251_);
return v___x_255_;
}
else
{
lean_dec(v_b_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_cmp_250_);
return v_t_251_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertIfNew(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_cmp_258_, lean_object* v_inst_259_, lean_object* v_t_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
uint8_t v___x_263_; 
lean_inc(v_t_260_);
lean_inc(v_a_261_);
lean_inc_ref(v_cmp_258_);
v___x_263_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_258_, v_a_261_, v_t_260_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
v___x_264_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_258_, v_a_261_, v_b_262_, v_t_260_);
return v___x_264_;
}
else
{
lean_dec(v_b_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_cmp_258_);
return v_t_260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsert___redArg(lean_object* v_cmp_265_, lean_object* v_t_266_, lean_object* v_a_267_, lean_object* v_b_268_){
_start:
{
lean_object* v_sz_269_; lean_object* v_m_270_; lean_object* v___y_272_; 
v_sz_269_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_266_);
v_m_270_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_265_, v_a_267_, v_b_268_, v_t_266_);
if (lean_obj_tag(v_m_270_) == 0)
{
lean_object* v_size_276_; 
v_size_276_ = lean_ctor_get(v_m_270_, 0);
lean_inc(v_size_276_);
v___y_272_ = v_size_276_;
goto v___jp_271_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___y_272_ = v___x_277_;
goto v___jp_271_;
}
v___jp_271_:
{
uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_nat_dec_eq(v_sz_269_, v___y_272_);
lean_dec(v___y_272_);
lean_dec(v_sz_269_);
v___x_274_ = lean_box(v___x_273_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v_m_270_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsert(lean_object* v_00_u03b1_278_, lean_object* v_00_u03b2_279_, lean_object* v_cmp_280_, lean_object* v_inst_281_, lean_object* v_t_282_, lean_object* v_a_283_, lean_object* v_b_284_){
_start:
{
lean_object* v_sz_285_; lean_object* v_m_286_; lean_object* v___y_288_; 
v_sz_285_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_282_);
v_m_286_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_280_, v_a_283_, v_b_284_, v_t_282_);
if (lean_obj_tag(v_m_286_) == 0)
{
lean_object* v_size_292_; 
v_size_292_ = lean_ctor_get(v_m_286_, 0);
lean_inc(v_size_292_);
v___y_288_ = v_size_292_;
goto v___jp_287_;
}
else
{
lean_object* v___x_293_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___y_288_ = v___x_293_;
goto v___jp_287_;
}
v___jp_287_:
{
uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_nat_dec_eq(v_sz_285_, v___y_288_);
lean_dec(v___y_288_);
lean_dec(v_sz_285_);
v___x_290_ = lean_box(v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_m_286_);
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_294_, lean_object* v_t_295_, lean_object* v_a_296_, lean_object* v_b_297_){
_start:
{
uint8_t v___x_298_; 
lean_inc(v_t_295_);
lean_inc(v_a_296_);
lean_inc_ref(v_cmp_294_);
v___x_298_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_294_, v_a_296_, v_t_295_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_294_, v_a_296_, v_b_297_, v_t_295_);
v___x_300_ = lean_box(v___x_298_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_299_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_b_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_cmp_294_);
v___x_302_ = lean_box(v___x_298_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_t_295_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_304_, lean_object* v_00_u03b2_305_, lean_object* v_cmp_306_, lean_object* v_inst_307_, lean_object* v_t_308_, lean_object* v_a_309_, lean_object* v_b_310_){
_start:
{
uint8_t v___x_311_; 
lean_inc(v_t_308_);
lean_inc(v_a_309_);
lean_inc_ref(v_cmp_306_);
v___x_311_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_306_, v_a_309_, v_t_308_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_306_, v_a_309_, v_b_310_, v_t_308_);
v___x_313_ = lean_box(v___x_311_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___x_312_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_b_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_cmp_306_);
v___x_315_ = lean_box(v___x_311_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v_t_308_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_317_, lean_object* v_t_318_, lean_object* v_a_319_, lean_object* v_b_320_){
_start:
{
lean_object* v___x_321_; 
lean_inc(v_a_319_);
lean_inc(v_t_318_);
lean_inc_ref(v_cmp_317_);
v___x_321_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_317_, v_t_318_, v_a_319_);
if (lean_obj_tag(v___x_321_) == 0)
{
uint8_t v___x_322_; 
lean_inc(v_t_318_);
lean_inc(v_a_319_);
lean_inc_ref(v_cmp_317_);
v___x_322_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_317_, v_a_319_, v_t_318_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_317_, v_a_319_, v_b_320_, v_t_318_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_321_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; 
lean_dec(v_b_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_cmp_317_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_321_);
lean_ctor_set(v___x_325_, 1, v_t_318_);
return v___x_325_;
}
}
else
{
lean_object* v___x_326_; 
lean_dec(v_b_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_cmp_317_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_321_);
lean_ctor_set(v___x_326_, 1, v_t_318_);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_327_, lean_object* v_00_u03b2_328_, lean_object* v_cmp_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_t_332_, lean_object* v_a_333_, lean_object* v_b_334_){
_start:
{
lean_object* v___x_335_; 
lean_inc(v_a_333_);
lean_inc(v_t_332_);
lean_inc_ref(v_cmp_329_);
v___x_335_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_329_, v_t_332_, v_a_333_);
if (lean_obj_tag(v___x_335_) == 0)
{
uint8_t v___x_336_; 
lean_inc(v_t_332_);
lean_inc(v_a_333_);
lean_inc_ref(v_cmp_329_);
v___x_336_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_329_, v_a_333_, v_t_332_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_329_, v_a_333_, v_b_334_, v_t_332_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_335_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; 
lean_dec(v_b_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_cmp_329_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_335_);
lean_ctor_set(v___x_339_, 1, v_t_332_);
return v___x_339_;
}
}
else
{
lean_object* v___x_340_; 
lean_dec(v_b_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_cmp_329_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_335_);
lean_ctor_set(v___x_340_, 1, v_t_332_);
return v___x_340_;
}
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_contains___redArg(lean_object* v_cmp_341_, lean_object* v_t_342_, lean_object* v_a_343_){
_start:
{
uint8_t v___x_344_; 
v___x_344_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_341_, v_a_343_, v_t_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_contains___redArg___boxed(lean_object* v_cmp_345_, lean_object* v_t_346_, lean_object* v_a_347_){
_start:
{
uint8_t v_res_348_; lean_object* v_r_349_; 
v_res_348_ = l_Std_ExtDTreeMap_contains___redArg(v_cmp_345_, v_t_346_, v_a_347_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_contains(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_cmp_352_, lean_object* v_inst_353_, lean_object* v_t_354_, lean_object* v_a_355_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_352_, v_a_355_, v_t_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_contains___boxed(lean_object* v_00_u03b1_357_, lean_object* v_00_u03b2_358_, lean_object* v_cmp_359_, lean_object* v_inst_360_, lean_object* v_t_361_, lean_object* v_a_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_Std_ExtDTreeMap_contains(v_00_u03b1_357_, v_00_u03b2_358_, v_cmp_359_, v_inst_360_, v_t_361_, v_a_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg(){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_box(0);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg___boxed(lean_object* v___dummy_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Std_ExtDTreeMap_instMembershipOfTransCmp___redArg();
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp(lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_, lean_object* v_cmp_371_, lean_object* v_inst_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_box(0);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___boxed(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_cmp_376_, lean_object* v_inst_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_ExtDTreeMap_instMembershipOfTransCmp(v_00_u03b1_374_, v_00_u03b2_375_, v_cmp_376_, v_inst_377_);
lean_dec_ref(v_cmp_376_);
return v_res_378_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableMem___redArg(lean_object* v_cmp_379_, lean_object* v_m_380_, lean_object* v_a_381_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_379_, v_a_381_, v_m_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_383_, lean_object* v_m_384_, lean_object* v_a_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_Std_ExtDTreeMap_instDecidableMem___redArg(v_cmp_383_, v_m_384_, v_a_385_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableMem(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_cmp_390_, lean_object* v_inst_391_, lean_object* v_m_392_, lean_object* v_a_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_390_, v_a_393_, v_m_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_395_, lean_object* v_00_u03b2_396_, lean_object* v_cmp_397_, lean_object* v_inst_398_, lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Std_ExtDTreeMap_instDecidableMem(v_00_u03b1_395_, v_00_u03b2_396_, v_cmp_397_, v_inst_398_, v_m_399_, v_a_400_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___redArg(lean_object* v_t_403_){
_start:
{
if (lean_obj_tag(v_t_403_) == 0)
{
lean_object* v_size_404_; 
v_size_404_ = lean_ctor_get(v_t_403_, 0);
lean_inc(v_size_404_);
return v_size_404_;
}
else
{
lean_object* v___x_405_; 
v___x_405_ = lean_unsigned_to_nat(0u);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___redArg___boxed(lean_object* v_t_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Std_ExtDTreeMap_size___redArg(v_t_406_);
lean_dec(v_t_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size(lean_object* v_00_u03b1_408_, lean_object* v_00_u03b2_409_, lean_object* v_cmp_410_, lean_object* v_t_411_){
_start:
{
if (lean_obj_tag(v_t_411_) == 0)
{
lean_object* v_size_412_; 
v_size_412_ = lean_ctor_get(v_t_411_, 0);
lean_inc(v_size_412_);
return v_size_412_;
}
else
{
lean_object* v___x_413_; 
v___x_413_ = lean_unsigned_to_nat(0u);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___boxed(lean_object* v_00_u03b1_414_, lean_object* v_00_u03b2_415_, lean_object* v_cmp_416_, lean_object* v_t_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_ExtDTreeMap_size(v_00_u03b1_414_, v_00_u03b2_415_, v_cmp_416_, v_t_417_);
lean_dec(v_t_417_);
lean_dec_ref(v_cmp_416_);
return v_res_418_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_isEmpty___redArg(lean_object* v_t_419_){
_start:
{
if (lean_obj_tag(v_t_419_) == 0)
{
uint8_t v___x_420_; 
v___x_420_ = 0;
return v___x_420_;
}
else
{
uint8_t v___x_421_; 
v___x_421_ = 1;
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_isEmpty___redArg___boxed(lean_object* v_t_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Std_ExtDTreeMap_isEmpty___redArg(v_t_422_);
lean_dec(v_t_422_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_isEmpty(lean_object* v_00_u03b1_425_, lean_object* v_00_u03b2_426_, lean_object* v_cmp_427_, lean_object* v_t_428_){
_start:
{
if (lean_obj_tag(v_t_428_) == 0)
{
uint8_t v___x_429_; 
v___x_429_ = 0;
return v___x_429_;
}
else
{
uint8_t v___x_430_; 
v___x_430_ = 1;
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_431_, lean_object* v_00_u03b2_432_, lean_object* v_cmp_433_, lean_object* v_t_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Std_ExtDTreeMap_isEmpty(v_00_u03b1_431_, v_00_u03b2_432_, v_cmp_433_, v_t_434_);
lean_dec(v_t_434_);
lean_dec_ref(v_cmp_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_erase___redArg(lean_object* v_cmp_437_, lean_object* v_t_438_, lean_object* v_a_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_437_, v_a_439_, v_t_438_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_erase(lean_object* v_00_u03b1_441_, lean_object* v_00_u03b2_442_, lean_object* v_cmp_443_, lean_object* v_inst_444_, lean_object* v_t_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_443_, v_a_446_, v_t_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x3f___redArg(lean_object* v_cmp_448_, lean_object* v_t_449_, lean_object* v_a_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_448_, v_t_449_, v_a_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x3f(lean_object* v_00_u03b1_452_, lean_object* v_00_u03b2_453_, lean_object* v_cmp_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_t_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_454_, v_t_457_, v_a_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get___redArg(lean_object* v_cmp_460_, lean_object* v_t_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_460_, v_t_461_, v_a_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_cmp_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_t_469_, lean_object* v_a_470_, lean_object* v_h_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_466_, v_t_469_, v_a_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___redArg(lean_object* v_cmp_473_, lean_object* v_t_474_, lean_object* v_a_475_, lean_object* v_inst_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_473_, v_t_474_, v_a_475_, v_inst_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___redArg___boxed(lean_object* v_cmp_478_, lean_object* v_t_479_, lean_object* v_a_480_, lean_object* v_inst_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_ExtDTreeMap_get_x21___redArg(v_cmp_478_, v_t_479_, v_a_480_, v_inst_481_);
lean_dec(v_inst_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21(lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_cmp_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_t_488_, lean_object* v_a_489_, lean_object* v_inst_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_485_, v_t_488_, v_a_489_, v_inst_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___boxed(lean_object* v_00_u03b1_492_, lean_object* v_00_u03b2_493_, lean_object* v_cmp_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_t_497_, lean_object* v_a_498_, lean_object* v_inst_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_ExtDTreeMap_get_x21(v_00_u03b1_492_, v_00_u03b2_493_, v_cmp_494_, v_inst_495_, v_inst_496_, v_t_497_, v_a_498_, v_inst_499_);
lean_dec(v_inst_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg(lean_object* v_cmp_501_, lean_object* v_t_502_, lean_object* v_a_503_, lean_object* v_fallback_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_501_, v_t_502_, v_a_503_, v_fallback_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg___boxed(lean_object* v_cmp_506_, lean_object* v_t_507_, lean_object* v_a_508_, lean_object* v_fallback_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_ExtDTreeMap_getD___redArg(v_cmp_506_, v_t_507_, v_a_508_, v_fallback_509_);
lean_dec(v_fallback_509_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD(lean_object* v_00_u03b1_511_, lean_object* v_00_u03b2_512_, lean_object* v_cmp_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_t_516_, lean_object* v_a_517_, lean_object* v_fallback_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_513_, v_t_516_, v_a_517_, v_fallback_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___boxed(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_cmp_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_t_525_, lean_object* v_a_526_, lean_object* v_fallback_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_ExtDTreeMap_getD(v_00_u03b1_520_, v_00_u03b2_521_, v_cmp_522_, v_inst_523_, v_inst_524_, v_t_525_, v_a_526_, v_fallback_527_);
lean_dec(v_fallback_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f___redArg(lean_object* v_cmp_529_, lean_object* v_t_530_, lean_object* v_a_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_529_, v_t_530_, v_a_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f(lean_object* v_00_u03b1_533_, lean_object* v_00_u03b2_534_, lean_object* v_cmp_535_, lean_object* v_inst_536_, lean_object* v_t_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_535_, v_t_537_, v_a_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey___redArg(lean_object* v_cmp_540_, lean_object* v_t_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_540_, v_t_541_, v_a_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey(lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_, lean_object* v_cmp_546_, lean_object* v_inst_547_, lean_object* v_t_548_, lean_object* v_a_549_, lean_object* v_h_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_546_, v_t_548_, v_a_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___redArg(lean_object* v_cmp_552_, lean_object* v_inst_553_, lean_object* v_t_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_552_, v_t_554_, v_a_555_, v_inst_553_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___redArg___boxed(lean_object* v_cmp_557_, lean_object* v_inst_558_, lean_object* v_t_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_ExtDTreeMap_getKey_x21___redArg(v_cmp_557_, v_inst_558_, v_t_559_, v_a_560_);
lean_dec(v_inst_558_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21(lean_object* v_00_u03b1_562_, lean_object* v_00_u03b2_563_, lean_object* v_cmp_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_t_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_564_, v_t_567_, v_a_568_, v_inst_566_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___boxed(lean_object* v_00_u03b1_570_, lean_object* v_00_u03b2_571_, lean_object* v_cmp_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_t_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_ExtDTreeMap_getKey_x21(v_00_u03b1_570_, v_00_u03b2_571_, v_cmp_572_, v_inst_573_, v_inst_574_, v_t_575_, v_a_576_);
lean_dec(v_inst_574_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___redArg(lean_object* v_cmp_578_, lean_object* v_t_579_, lean_object* v_a_580_, lean_object* v_fallback_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_578_, v_t_579_, v_a_580_, v_fallback_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_583_, lean_object* v_t_584_, lean_object* v_a_585_, lean_object* v_fallback_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_ExtDTreeMap_getKeyD___redArg(v_cmp_583_, v_t_584_, v_a_585_, v_fallback_586_);
lean_dec(v_fallback_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_cmp_590_, lean_object* v_inst_591_, lean_object* v_t_592_, lean_object* v_a_593_, lean_object* v_fallback_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_590_, v_t_592_, v_a_593_, v_fallback_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_596_, lean_object* v_00_u03b2_597_, lean_object* v_cmp_598_, lean_object* v_inst_599_, lean_object* v_t_600_, lean_object* v_a_601_, lean_object* v_fallback_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_ExtDTreeMap_getKeyD(v_00_u03b1_596_, v_00_u03b2_597_, v_cmp_598_, v_inst_599_, v_t_600_, v_a_601_, v_fallback_602_);
lean_dec(v_fallback_602_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___redArg(lean_object* v_t_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_ExtDTreeMap_minEntry_x3f___redArg(v_t_606_);
lean_dec(v_t_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_cmp_610_, lean_object* v_inst_611_, lean_object* v_t_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_614_, lean_object* v_00_u03b2_615_, lean_object* v_cmp_616_, lean_object* v_inst_617_, lean_object* v_t_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_ExtDTreeMap_minEntry_x3f(v_00_u03b1_614_, v_00_u03b2_615_, v_cmp_616_, v_inst_617_, v_t_618_);
lean_dec(v_t_618_);
lean_dec_ref(v_cmp_616_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___redArg(lean_object* v_t_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___redArg___boxed(lean_object* v_t_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_ExtDTreeMap_minEntry___redArg(v_t_622_);
lean_dec(v_t_622_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry(lean_object* v_00_u03b1_624_, lean_object* v_00_u03b2_625_, lean_object* v_cmp_626_, lean_object* v_inst_627_, lean_object* v_t_628_, lean_object* v_h_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___boxed(lean_object* v_00_u03b1_631_, lean_object* v_00_u03b2_632_, lean_object* v_cmp_633_, lean_object* v_inst_634_, lean_object* v_t_635_, lean_object* v_h_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Std_ExtDTreeMap_minEntry(v_00_u03b1_631_, v_00_u03b2_632_, v_cmp_633_, v_inst_634_, v_t_635_, v_h_636_);
lean_dec(v_t_635_);
lean_dec_ref(v_cmp_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___redArg(lean_object* v_inst_638_, lean_object* v_t_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_638_, v_t_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_641_, lean_object* v_t_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_ExtDTreeMap_minEntry_x21___redArg(v_inst_641_, v_t_642_);
lean_dec(v_t_642_);
lean_dec_ref(v_inst_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21(lean_object* v_00_u03b1_644_, lean_object* v_00_u03b2_645_, lean_object* v_cmp_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_t_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_648_, v_t_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_651_, lean_object* v_00_u03b2_652_, lean_object* v_cmp_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_t_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_ExtDTreeMap_minEntry_x21(v_00_u03b1_651_, v_00_u03b2_652_, v_cmp_653_, v_inst_654_, v_inst_655_, v_t_656_);
lean_dec(v_t_656_);
lean_dec_ref(v_inst_655_);
lean_dec_ref(v_cmp_653_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___redArg(lean_object* v_t_658_, lean_object* v_fallback_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_658_, v_fallback_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___redArg___boxed(lean_object* v_t_661_, lean_object* v_fallback_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_ExtDTreeMap_minEntryD___redArg(v_t_661_, v_fallback_662_);
lean_dec_ref(v_fallback_662_);
lean_dec(v_t_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD(lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_cmp_666_, lean_object* v_inst_667_, lean_object* v_t_668_, lean_object* v_fallback_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_668_, v_fallback_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_671_, lean_object* v_00_u03b2_672_, lean_object* v_cmp_673_, lean_object* v_inst_674_, lean_object* v_t_675_, lean_object* v_fallback_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_ExtDTreeMap_minEntryD(v_00_u03b1_671_, v_00_u03b2_672_, v_cmp_673_, v_inst_674_, v_t_675_, v_fallback_676_);
lean_dec_ref(v_fallback_676_);
lean_dec(v_t_675_);
lean_dec_ref(v_cmp_673_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___redArg(lean_object* v_t_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_ExtDTreeMap_maxEntry_x3f___redArg(v_t_680_);
lean_dec(v_t_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_cmp_684_, lean_object* v_inst_685_, lean_object* v_t_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_cmp_690_, lean_object* v_inst_691_, lean_object* v_t_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_ExtDTreeMap_maxEntry_x3f(v_00_u03b1_688_, v_00_u03b2_689_, v_cmp_690_, v_inst_691_, v_t_692_);
lean_dec(v_t_692_);
lean_dec_ref(v_cmp_690_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___redArg(lean_object* v_t_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___redArg___boxed(lean_object* v_t_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_ExtDTreeMap_maxEntry___redArg(v_t_696_);
lean_dec(v_t_696_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_cmp_700_, lean_object* v_inst_701_, lean_object* v_t_702_, lean_object* v_h_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_702_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_705_, lean_object* v_00_u03b2_706_, lean_object* v_cmp_707_, lean_object* v_inst_708_, lean_object* v_t_709_, lean_object* v_h_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_ExtDTreeMap_maxEntry(v_00_u03b1_705_, v_00_u03b2_706_, v_cmp_707_, v_inst_708_, v_t_709_, v_h_710_);
lean_dec(v_t_709_);
lean_dec_ref(v_cmp_707_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___redArg(lean_object* v_inst_712_, lean_object* v_t_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_712_, v_t_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_715_, lean_object* v_t_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_ExtDTreeMap_maxEntry_x21___redArg(v_inst_715_, v_t_716_);
lean_dec(v_t_716_);
lean_dec_ref(v_inst_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21(lean_object* v_00_u03b1_718_, lean_object* v_00_u03b2_719_, lean_object* v_cmp_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_t_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_722_, v_t_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_725_, lean_object* v_00_u03b2_726_, lean_object* v_cmp_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_t_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_ExtDTreeMap_maxEntry_x21(v_00_u03b1_725_, v_00_u03b2_726_, v_cmp_727_, v_inst_728_, v_inst_729_, v_t_730_);
lean_dec(v_t_730_);
lean_dec_ref(v_inst_729_);
lean_dec_ref(v_cmp_727_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___redArg(lean_object* v_t_732_, lean_object* v_fallback_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_732_, v_fallback_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_735_, lean_object* v_fallback_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Std_ExtDTreeMap_maxEntryD___redArg(v_t_735_, v_fallback_736_);
lean_dec_ref(v_fallback_736_);
lean_dec(v_t_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD(lean_object* v_00_u03b1_738_, lean_object* v_00_u03b2_739_, lean_object* v_cmp_740_, lean_object* v_inst_741_, lean_object* v_t_742_, lean_object* v_fallback_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_742_, v_fallback_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_745_, lean_object* v_00_u03b2_746_, lean_object* v_cmp_747_, lean_object* v_inst_748_, lean_object* v_t_749_, lean_object* v_fallback_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_ExtDTreeMap_maxEntryD(v_00_u03b1_745_, v_00_u03b2_746_, v_cmp_747_, v_inst_748_, v_t_749_, v_fallback_750_);
lean_dec_ref(v_fallback_750_);
lean_dec(v_t_749_);
lean_dec_ref(v_cmp_747_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___redArg(lean_object* v_t_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Std_ExtDTreeMap_minKey_x3f___redArg(v_t_754_);
lean_dec(v_t_754_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b2_757_, lean_object* v_cmp_758_, lean_object* v_inst_759_, lean_object* v_t_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_cmp_764_, lean_object* v_inst_765_, lean_object* v_t_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_ExtDTreeMap_minKey_x3f(v_00_u03b1_762_, v_00_u03b2_763_, v_cmp_764_, v_inst_765_, v_t_766_);
lean_dec(v_t_766_);
lean_dec_ref(v_cmp_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___redArg(lean_object* v_t_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___redArg___boxed(lean_object* v_t_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_ExtDTreeMap_minKey___redArg(v_t_770_);
lean_dec(v_t_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_cmp_774_, lean_object* v_inst_775_, lean_object* v_t_776_, lean_object* v_h_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___boxed(lean_object* v_00_u03b1_779_, lean_object* v_00_u03b2_780_, lean_object* v_cmp_781_, lean_object* v_inst_782_, lean_object* v_t_783_, lean_object* v_h_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_ExtDTreeMap_minKey(v_00_u03b1_779_, v_00_u03b2_780_, v_cmp_781_, v_inst_782_, v_t_783_, v_h_784_);
lean_dec(v_t_783_);
lean_dec_ref(v_cmp_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___redArg(lean_object* v_inst_786_, lean_object* v_t_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_786_, v_t_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_789_, lean_object* v_t_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_ExtDTreeMap_minKey_x21___redArg(v_inst_789_, v_t_790_);
lean_dec(v_t_790_);
lean_dec(v_inst_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_cmp_794_, lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_t_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_796_, v_t_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_799_, lean_object* v_00_u03b2_800_, lean_object* v_cmp_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_t_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_ExtDTreeMap_minKey_x21(v_00_u03b1_799_, v_00_u03b2_800_, v_cmp_801_, v_inst_802_, v_inst_803_, v_t_804_);
lean_dec(v_t_804_);
lean_dec(v_inst_803_);
lean_dec_ref(v_cmp_801_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___redArg(lean_object* v_t_806_, lean_object* v_fallback_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_806_, v_fallback_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___redArg___boxed(lean_object* v_t_809_, lean_object* v_fallback_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Std_ExtDTreeMap_minKeyD___redArg(v_t_809_, v_fallback_810_);
lean_dec(v_fallback_810_);
lean_dec(v_t_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD(lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_cmp_814_, lean_object* v_inst_815_, lean_object* v_t_816_, lean_object* v_fallback_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_816_, v_fallback_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_819_, lean_object* v_00_u03b2_820_, lean_object* v_cmp_821_, lean_object* v_inst_822_, lean_object* v_t_823_, lean_object* v_fallback_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_ExtDTreeMap_minKeyD(v_00_u03b1_819_, v_00_u03b2_820_, v_cmp_821_, v_inst_822_, v_t_823_, v_fallback_824_);
lean_dec(v_fallback_824_);
lean_dec(v_t_823_);
lean_dec_ref(v_cmp_821_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___redArg(lean_object* v_t_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_ExtDTreeMap_maxKey_x3f___redArg(v_t_828_);
lean_dec(v_t_828_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f(lean_object* v_00_u03b1_830_, lean_object* v_00_u03b2_831_, lean_object* v_cmp_832_, lean_object* v_inst_833_, lean_object* v_t_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_836_, lean_object* v_00_u03b2_837_, lean_object* v_cmp_838_, lean_object* v_inst_839_, lean_object* v_t_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_ExtDTreeMap_maxKey_x3f(v_00_u03b1_836_, v_00_u03b2_837_, v_cmp_838_, v_inst_839_, v_t_840_);
lean_dec(v_t_840_);
lean_dec_ref(v_cmp_838_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___redArg(lean_object* v_t_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___redArg___boxed(lean_object* v_t_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_ExtDTreeMap_maxKey___redArg(v_t_844_);
lean_dec(v_t_844_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey(lean_object* v_00_u03b1_846_, lean_object* v_00_u03b2_847_, lean_object* v_cmp_848_, lean_object* v_inst_849_, lean_object* v_t_850_, lean_object* v_h_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_850_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___boxed(lean_object* v_00_u03b1_853_, lean_object* v_00_u03b2_854_, lean_object* v_cmp_855_, lean_object* v_inst_856_, lean_object* v_t_857_, lean_object* v_h_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_ExtDTreeMap_maxKey(v_00_u03b1_853_, v_00_u03b2_854_, v_cmp_855_, v_inst_856_, v_t_857_, v_h_858_);
lean_dec(v_t_857_);
lean_dec_ref(v_cmp_855_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___redArg(lean_object* v_inst_860_, lean_object* v_t_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_860_, v_t_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_863_, lean_object* v_t_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_ExtDTreeMap_maxKey_x21___redArg(v_inst_863_, v_t_864_);
lean_dec(v_t_864_);
lean_dec(v_inst_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21(lean_object* v_00_u03b1_866_, lean_object* v_00_u03b2_867_, lean_object* v_cmp_868_, lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_t_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_870_, v_t_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_873_, lean_object* v_00_u03b2_874_, lean_object* v_cmp_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_t_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_ExtDTreeMap_maxKey_x21(v_00_u03b1_873_, v_00_u03b2_874_, v_cmp_875_, v_inst_876_, v_inst_877_, v_t_878_);
lean_dec(v_t_878_);
lean_dec(v_inst_877_);
lean_dec_ref(v_cmp_875_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___redArg(lean_object* v_t_880_, lean_object* v_fallback_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_880_, v_fallback_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_883_, lean_object* v_fallback_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_ExtDTreeMap_maxKeyD___redArg(v_t_883_, v_fallback_884_);
lean_dec(v_fallback_884_);
lean_dec(v_t_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD(lean_object* v_00_u03b1_886_, lean_object* v_00_u03b2_887_, lean_object* v_cmp_888_, lean_object* v_inst_889_, lean_object* v_t_890_, lean_object* v_fallback_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_890_, v_fallback_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_893_, lean_object* v_00_u03b2_894_, lean_object* v_cmp_895_, lean_object* v_inst_896_, lean_object* v_t_897_, lean_object* v_fallback_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_ExtDTreeMap_maxKeyD(v_00_u03b1_893_, v_00_u03b2_894_, v_cmp_895_, v_inst_896_, v_t_897_, v_fallback_898_);
lean_dec(v_fallback_898_);
lean_dec(v_t_897_);
lean_dec_ref(v_cmp_895_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_900_, lean_object* v_n_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_900_, v_n_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_903_, lean_object* v_n_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(v_t_903_, v_n_904_);
lean_dec(v_t_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_906_, lean_object* v_00_u03b2_907_, lean_object* v_cmp_908_, lean_object* v_inst_909_, lean_object* v_t_910_, lean_object* v_n_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_910_, v_n_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_913_, lean_object* v_00_u03b2_914_, lean_object* v_cmp_915_, lean_object* v_inst_916_, lean_object* v_t_917_, lean_object* v_n_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_ExtDTreeMap_entryAtIdx_x3f(v_00_u03b1_913_, v_00_u03b2_914_, v_cmp_915_, v_inst_916_, v_t_917_, v_n_918_);
lean_dec(v_t_917_);
lean_dec_ref(v_cmp_915_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___redArg(lean_object* v_t_920_, lean_object* v_n_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_920_, v_n_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_923_, lean_object* v_n_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_ExtDTreeMap_entryAtIdx___redArg(v_t_923_, v_n_924_);
lean_dec(v_t_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx(lean_object* v_00_u03b1_926_, lean_object* v_00_u03b2_927_, lean_object* v_cmp_928_, lean_object* v_inst_929_, lean_object* v_t_930_, lean_object* v_n_931_, lean_object* v_h_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_930_, v_n_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_934_, lean_object* v_00_u03b2_935_, lean_object* v_cmp_936_, lean_object* v_inst_937_, lean_object* v_t_938_, lean_object* v_n_939_, lean_object* v_h_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_ExtDTreeMap_entryAtIdx(v_00_u03b1_934_, v_00_u03b2_935_, v_cmp_936_, v_inst_937_, v_t_938_, v_n_939_, v_h_940_);
lean_dec(v_t_938_);
lean_dec_ref(v_cmp_936_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_942_, lean_object* v_t_943_, lean_object* v_n_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_942_, v_t_943_, v_n_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_946_, lean_object* v_t_947_, lean_object* v_n_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(v_inst_946_, v_t_947_, v_n_948_);
lean_dec(v_t_947_);
lean_dec_ref(v_inst_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_950_, lean_object* v_00_u03b2_951_, lean_object* v_cmp_952_, lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_t_955_, lean_object* v_n_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_954_, v_t_955_, v_n_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_958_, lean_object* v_00_u03b2_959_, lean_object* v_cmp_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_t_963_, lean_object* v_n_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_ExtDTreeMap_entryAtIdx_x21(v_00_u03b1_958_, v_00_u03b2_959_, v_cmp_960_, v_inst_961_, v_inst_962_, v_t_963_, v_n_964_);
lean_dec(v_t_963_);
lean_dec_ref(v_inst_962_);
lean_dec_ref(v_cmp_960_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___redArg(lean_object* v_t_966_, lean_object* v_n_967_, lean_object* v_fallback_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_966_, v_n_967_, v_fallback_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_970_, lean_object* v_n_971_, lean_object* v_fallback_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_ExtDTreeMap_entryAtIdxD___redArg(v_t_970_, v_n_971_, v_fallback_972_);
lean_dec_ref(v_fallback_972_);
lean_dec(v_t_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD(lean_object* v_00_u03b1_974_, lean_object* v_00_u03b2_975_, lean_object* v_cmp_976_, lean_object* v_inst_977_, lean_object* v_t_978_, lean_object* v_n_979_, lean_object* v_fallback_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_978_, v_n_979_, v_fallback_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_982_, lean_object* v_00_u03b2_983_, lean_object* v_cmp_984_, lean_object* v_inst_985_, lean_object* v_t_986_, lean_object* v_n_987_, lean_object* v_fallback_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_ExtDTreeMap_entryAtIdxD(v_00_u03b1_982_, v_00_u03b2_983_, v_cmp_984_, v_inst_985_, v_t_986_, v_n_987_, v_fallback_988_);
lean_dec_ref(v_fallback_988_);
lean_dec(v_t_986_);
lean_dec_ref(v_cmp_984_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_990_, lean_object* v_n_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_990_, v_n_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_993_, lean_object* v_n_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(v_t_993_, v_n_994_);
lean_dec(v_t_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_996_, lean_object* v_00_u03b2_997_, lean_object* v_cmp_998_, lean_object* v_inst_999_, lean_object* v_t_1000_, lean_object* v_n_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_1000_, v_n_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_1003_, lean_object* v_00_u03b2_1004_, lean_object* v_cmp_1005_, lean_object* v_inst_1006_, lean_object* v_t_1007_, lean_object* v_n_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Std_ExtDTreeMap_keyAtIdx_x3f(v_00_u03b1_1003_, v_00_u03b2_1004_, v_cmp_1005_, v_inst_1006_, v_t_1007_, v_n_1008_);
lean_dec(v_t_1007_);
lean_dec_ref(v_cmp_1005_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___redArg(lean_object* v_t_1010_, lean_object* v_n_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1010_, v_n_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_1013_, lean_object* v_n_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Std_ExtDTreeMap_keyAtIdx___redArg(v_t_1013_, v_n_1014_);
lean_dec(v_t_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03b2_1017_, lean_object* v_cmp_1018_, lean_object* v_inst_1019_, lean_object* v_t_1020_, lean_object* v_n_1021_, lean_object* v_h_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1020_, v_n_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_1024_, lean_object* v_00_u03b2_1025_, lean_object* v_cmp_1026_, lean_object* v_inst_1027_, lean_object* v_t_1028_, lean_object* v_n_1029_, lean_object* v_h_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Std_ExtDTreeMap_keyAtIdx(v_00_u03b1_1024_, v_00_u03b2_1025_, v_cmp_1026_, v_inst_1027_, v_t_1028_, v_n_1029_, v_h_1030_);
lean_dec(v_t_1028_);
lean_dec_ref(v_cmp_1026_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_1032_, lean_object* v_t_1033_, lean_object* v_n_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1032_, v_t_1033_, v_n_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_1036_, lean_object* v_t_1037_, lean_object* v_n_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(v_inst_1036_, v_t_1037_, v_n_1038_);
lean_dec(v_t_1037_);
lean_dec(v_inst_1036_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_1040_, lean_object* v_00_u03b2_1041_, lean_object* v_cmp_1042_, lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_t_1045_, lean_object* v_n_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1044_, v_t_1045_, v_n_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_cmp_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_t_1053_, lean_object* v_n_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Std_ExtDTreeMap_keyAtIdx_x21(v_00_u03b1_1048_, v_00_u03b2_1049_, v_cmp_1050_, v_inst_1051_, v_inst_1052_, v_t_1053_, v_n_1054_);
lean_dec(v_t_1053_);
lean_dec(v_inst_1052_);
lean_dec_ref(v_cmp_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___redArg(lean_object* v_t_1056_, lean_object* v_n_1057_, lean_object* v_fallback_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1056_, v_n_1057_, v_fallback_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_1060_, lean_object* v_n_1061_, lean_object* v_fallback_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Std_ExtDTreeMap_keyAtIdxD___redArg(v_t_1060_, v_n_1061_, v_fallback_1062_);
lean_dec(v_fallback_1062_);
lean_dec(v_t_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD(lean_object* v_00_u03b1_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_cmp_1066_, lean_object* v_inst_1067_, lean_object* v_t_1068_, lean_object* v_n_1069_, lean_object* v_fallback_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1068_, v_n_1069_, v_fallback_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_1072_, lean_object* v_00_u03b2_1073_, lean_object* v_cmp_1074_, lean_object* v_inst_1075_, lean_object* v_t_1076_, lean_object* v_n_1077_, lean_object* v_fallback_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Std_ExtDTreeMap_keyAtIdxD(v_00_u03b1_1072_, v_00_u03b2_1073_, v_cmp_1074_, v_inst_1075_, v_t_1076_, v_n_1077_, v_fallback_1078_);
lean_dec(v_fallback_1078_);
lean_dec(v_t_1076_);
lean_dec_ref(v_cmp_1074_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1080_, lean_object* v_t_1081_, lean_object* v_k_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_box(0);
v___x_1084_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1080_, v_k_1082_, v___x_1083_, v_t_1081_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1085_, lean_object* v_00_u03b2_1086_, lean_object* v_cmp_1087_, lean_object* v_inst_1088_, lean_object* v_t_1089_, lean_object* v_k_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_box(0);
v___x_1092_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1087_, v_k_1090_, v___x_1091_, v_t_1089_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1093_, lean_object* v_t_1094_, lean_object* v_k_1095_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_box(0);
v___x_1097_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1093_, v_k_1095_, v___x_1096_, v_t_1094_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1098_, lean_object* v_00_u03b2_1099_, lean_object* v_cmp_1100_, lean_object* v_inst_1101_, lean_object* v_t_1102_, lean_object* v_k_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_box(0);
v___x_1105_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1100_, v_k_1103_, v___x_1104_, v_t_1102_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1106_, lean_object* v_t_1107_, lean_object* v_k_1108_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_box(0);
v___x_1110_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1106_, v_k_1108_, v___x_1109_, v_t_1107_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1111_, lean_object* v_00_u03b2_1112_, lean_object* v_cmp_1113_, lean_object* v_inst_1114_, lean_object* v_t_1115_, lean_object* v_k_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_box(0);
v___x_1118_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1113_, v_k_1116_, v___x_1117_, v_t_1115_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1119_, lean_object* v_t_1120_, lean_object* v_k_1121_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_box(0);
v___x_1123_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1119_, v_k_1121_, v___x_1122_, v_t_1120_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1124_, lean_object* v_00_u03b2_1125_, lean_object* v_cmp_1126_, lean_object* v_inst_1127_, lean_object* v_t_1128_, lean_object* v_k_1129_){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_box(0);
v___x_1131_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1126_, v_k_1129_, v___x_1130_, v_t_1128_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE___redArg(lean_object* v_cmp_1132_, lean_object* v_t_1133_, lean_object* v_k_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_1132_, v_k_1134_, v_t_1133_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE(lean_object* v_00_u03b1_1136_, lean_object* v_00_u03b2_1137_, lean_object* v_cmp_1138_, lean_object* v_inst_1139_, lean_object* v_t_1140_, lean_object* v_k_1141_, lean_object* v_h_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_1138_, v_k_1141_, v_t_1140_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT___redArg(lean_object* v_cmp_1144_, lean_object* v_t_1145_, lean_object* v_k_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_1144_, v_k_1146_, v_t_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT(lean_object* v_00_u03b1_1148_, lean_object* v_00_u03b2_1149_, lean_object* v_cmp_1150_, lean_object* v_inst_1151_, lean_object* v_t_1152_, lean_object* v_k_1153_, lean_object* v_h_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_1150_, v_k_1153_, v_t_1152_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE___redArg(lean_object* v_cmp_1156_, lean_object* v_t_1157_, lean_object* v_k_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_1156_, v_k_1158_, v_t_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE(lean_object* v_00_u03b1_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_cmp_1162_, lean_object* v_inst_1163_, lean_object* v_t_1164_, lean_object* v_k_1165_, lean_object* v_h_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_1162_, v_k_1165_, v_t_1164_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT___redArg(lean_object* v_cmp_1168_, lean_object* v_t_1169_, lean_object* v_k_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_1168_, v_k_1170_, v_t_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT(lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_cmp_1174_, lean_object* v_inst_1175_, lean_object* v_t_1176_, lean_object* v_k_1177_, lean_object* v_h_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_1174_, v_k_1177_, v_t_1176_);
return v___x_1179_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1183_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1184_ = lean_unsigned_to_nat(14u);
v___x_1185_ = lean_unsigned_to_nat(22u);
v___x_1186_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1187_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1188_ = l_mkPanicMessageWithDecl(v___x_1187_, v___x_1186_, v___x_1185_, v___x_1184_, v___x_1183_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1189_, lean_object* v_inst_1190_, lean_object* v_t_1191_, lean_object* v_k_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_box(0);
v___x_1194_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1189_, v_k_1192_, v___x_1193_, v_t_1191_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1196_ = l_panic___redArg(v_inst_1190_, v___x_1195_);
return v___x_1196_;
}
else
{
lean_object* v_val_1197_; 
v_val_1197_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_val_1197_);
lean_dec_ref_known(v___x_1194_, 1);
return v_val_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1198_, lean_object* v_inst_1199_, lean_object* v_t_1200_, lean_object* v_k_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Std_ExtDTreeMap_getEntryGE_x21___redArg(v_cmp_1198_, v_inst_1199_, v_t_1200_, v_k_1201_);
lean_dec_ref(v_inst_1199_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1203_, lean_object* v_00_u03b2_1204_, lean_object* v_cmp_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_t_1208_, lean_object* v_k_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_box(0);
v___x_1211_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1205_, v_k_1209_, v___x_1210_, v_t_1208_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1213_ = l_panic___redArg(v_inst_1207_, v___x_1212_);
return v___x_1213_;
}
else
{
lean_object* v_val_1214_; 
v_val_1214_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_val_1214_);
lean_dec_ref_known(v___x_1211_, 1);
return v_val_1214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1215_, lean_object* v_00_u03b2_1216_, lean_object* v_cmp_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_t_1220_, lean_object* v_k_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Std_ExtDTreeMap_getEntryGE_x21(v_00_u03b1_1215_, v_00_u03b2_1216_, v_cmp_1217_, v_inst_1218_, v_inst_1219_, v_t_1220_, v_k_1221_);
lean_dec_ref(v_inst_1219_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1223_, lean_object* v_inst_1224_, lean_object* v_t_1225_, lean_object* v_k_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_box(0);
v___x_1228_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1223_, v_k_1226_, v___x_1227_, v_t_1225_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1230_ = l_panic___redArg(v_inst_1224_, v___x_1229_);
return v___x_1230_;
}
else
{
lean_object* v_val_1231_; 
v_val_1231_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_val_1231_);
lean_dec_ref_known(v___x_1228_, 1);
return v_val_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1232_, lean_object* v_inst_1233_, lean_object* v_t_1234_, lean_object* v_k_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_ExtDTreeMap_getEntryGT_x21___redArg(v_cmp_1232_, v_inst_1233_, v_t_1234_, v_k_1235_);
lean_dec_ref(v_inst_1233_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1237_, lean_object* v_00_u03b2_1238_, lean_object* v_cmp_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_t_1242_, lean_object* v_k_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_box(0);
v___x_1245_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1239_, v_k_1243_, v___x_1244_, v_t_1242_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1247_ = l_panic___redArg(v_inst_1241_, v___x_1246_);
return v___x_1247_;
}
else
{
lean_object* v_val_1248_; 
v_val_1248_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_val_1248_);
lean_dec_ref_known(v___x_1245_, 1);
return v_val_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_00_u03b2_1250_, lean_object* v_cmp_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_t_1254_, lean_object* v_k_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_ExtDTreeMap_getEntryGT_x21(v_00_u03b1_1249_, v_00_u03b2_1250_, v_cmp_1251_, v_inst_1252_, v_inst_1253_, v_t_1254_, v_k_1255_);
lean_dec_ref(v_inst_1253_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1257_, lean_object* v_inst_1258_, lean_object* v_t_1259_, lean_object* v_k_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1257_, v_k_1260_, v___x_1261_, v_t_1259_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1264_ = l_panic___redArg(v_inst_1258_, v___x_1263_);
return v___x_1264_;
}
else
{
lean_object* v_val_1265_; 
v_val_1265_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v___x_1262_, 1);
return v_val_1265_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1266_, lean_object* v_inst_1267_, lean_object* v_t_1268_, lean_object* v_k_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Std_ExtDTreeMap_getEntryLE_x21___redArg(v_cmp_1266_, v_inst_1267_, v_t_1268_, v_k_1269_);
lean_dec_ref(v_inst_1267_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1271_, lean_object* v_00_u03b2_1272_, lean_object* v_cmp_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_t_1276_, lean_object* v_k_1277_){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_box(0);
v___x_1279_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1273_, v_k_1277_, v___x_1278_, v_t_1276_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1281_ = l_panic___redArg(v_inst_1275_, v___x_1280_);
return v___x_1281_;
}
else
{
lean_object* v_val_1282_; 
v_val_1282_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_val_1282_);
lean_dec_ref_known(v___x_1279_, 1);
return v_val_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_00_u03b2_1284_, lean_object* v_cmp_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_t_1288_, lean_object* v_k_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Std_ExtDTreeMap_getEntryLE_x21(v_00_u03b1_1283_, v_00_u03b2_1284_, v_cmp_1285_, v_inst_1286_, v_inst_1287_, v_t_1288_, v_k_1289_);
lean_dec_ref(v_inst_1287_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1291_, lean_object* v_inst_1292_, lean_object* v_t_1293_, lean_object* v_k_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_box(0);
v___x_1296_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1291_, v_k_1294_, v___x_1295_, v_t_1293_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1298_ = l_panic___redArg(v_inst_1292_, v___x_1297_);
return v___x_1298_;
}
else
{
lean_object* v_val_1299_; 
v_val_1299_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v___x_1296_, 1);
return v_val_1299_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1300_, lean_object* v_inst_1301_, lean_object* v_t_1302_, lean_object* v_k_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Std_ExtDTreeMap_getEntryLT_x21___redArg(v_cmp_1300_, v_inst_1301_, v_t_1302_, v_k_1303_);
lean_dec_ref(v_inst_1301_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1305_, lean_object* v_00_u03b2_1306_, lean_object* v_cmp_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_t_1310_, lean_object* v_k_1311_){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_box(0);
v___x_1313_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1307_, v_k_1311_, v___x_1312_, v_t_1310_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1315_ = l_panic___redArg(v_inst_1309_, v___x_1314_);
return v___x_1315_;
}
else
{
lean_object* v_val_1316_; 
v_val_1316_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_val_1316_);
lean_dec_ref_known(v___x_1313_, 1);
return v_val_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_00_u03b2_1318_, lean_object* v_cmp_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_t_1322_, lean_object* v_k_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Std_ExtDTreeMap_getEntryLT_x21(v_00_u03b1_1317_, v_00_u03b2_1318_, v_cmp_1319_, v_inst_1320_, v_inst_1321_, v_t_1322_, v_k_1323_);
lean_dec_ref(v_inst_1321_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___redArg(lean_object* v_cmp_1325_, lean_object* v_t_1326_, lean_object* v_k_1327_, lean_object* v_fallback_1328_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_box(0);
v___x_1330_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1325_, v_k_1327_, v___x_1329_, v_t_1326_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_inc_ref(v_fallback_1328_);
return v_fallback_1328_;
}
else
{
lean_object* v_val_1331_; 
v_val_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v___x_1330_, 1);
return v_val_1331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1332_, lean_object* v_t_1333_, lean_object* v_k_1334_, lean_object* v_fallback_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_ExtDTreeMap_getEntryGED___redArg(v_cmp_1332_, v_t_1333_, v_k_1334_, v_fallback_1335_);
lean_dec_ref(v_fallback_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED(lean_object* v_00_u03b1_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_cmp_1339_, lean_object* v_inst_1340_, lean_object* v_t_1341_, lean_object* v_k_1342_, lean_object* v_fallback_1343_){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_box(0);
v___x_1345_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1339_, v_k_1342_, v___x_1344_, v_t_1341_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_inc_ref(v_fallback_1343_);
return v_fallback_1343_;
}
else
{
lean_object* v_val_1346_; 
v_val_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_val_1346_);
lean_dec_ref_known(v___x_1345_, 1);
return v_val_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1347_, lean_object* v_00_u03b2_1348_, lean_object* v_cmp_1349_, lean_object* v_inst_1350_, lean_object* v_t_1351_, lean_object* v_k_1352_, lean_object* v_fallback_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Std_ExtDTreeMap_getEntryGED(v_00_u03b1_1347_, v_00_u03b2_1348_, v_cmp_1349_, v_inst_1350_, v_t_1351_, v_k_1352_, v_fallback_1353_);
lean_dec_ref(v_fallback_1353_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1355_, lean_object* v_t_1356_, lean_object* v_k_1357_, lean_object* v_fallback_1358_){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_box(0);
v___x_1360_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1355_, v_k_1357_, v___x_1359_, v_t_1356_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_inc_ref(v_fallback_1358_);
return v_fallback_1358_;
}
else
{
lean_object* v_val_1361_; 
v_val_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_val_1361_);
lean_dec_ref_known(v___x_1360_, 1);
return v_val_1361_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1362_, lean_object* v_t_1363_, lean_object* v_k_1364_, lean_object* v_fallback_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Std_ExtDTreeMap_getEntryGTD___redArg(v_cmp_1362_, v_t_1363_, v_k_1364_, v_fallback_1365_);
lean_dec_ref(v_fallback_1365_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD(lean_object* v_00_u03b1_1367_, lean_object* v_00_u03b2_1368_, lean_object* v_cmp_1369_, lean_object* v_inst_1370_, lean_object* v_t_1371_, lean_object* v_k_1372_, lean_object* v_fallback_1373_){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1369_, v_k_1372_, v___x_1374_, v_t_1371_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_inc_ref(v_fallback_1373_);
return v_fallback_1373_;
}
else
{
lean_object* v_val_1376_; 
v_val_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_val_1376_);
lean_dec_ref_known(v___x_1375_, 1);
return v_val_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_00_u03b2_1378_, lean_object* v_cmp_1379_, lean_object* v_inst_1380_, lean_object* v_t_1381_, lean_object* v_k_1382_, lean_object* v_fallback_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Std_ExtDTreeMap_getEntryGTD(v_00_u03b1_1377_, v_00_u03b2_1378_, v_cmp_1379_, v_inst_1380_, v_t_1381_, v_k_1382_, v_fallback_1383_);
lean_dec_ref(v_fallback_1383_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___redArg(lean_object* v_cmp_1385_, lean_object* v_t_1386_, lean_object* v_k_1387_, lean_object* v_fallback_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1385_, v_k_1387_, v___x_1389_, v_t_1386_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_inc_ref(v_fallback_1388_);
return v_fallback_1388_;
}
else
{
lean_object* v_val_1391_; 
v_val_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_val_1391_);
lean_dec_ref_known(v___x_1390_, 1);
return v_val_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1392_, lean_object* v_t_1393_, lean_object* v_k_1394_, lean_object* v_fallback_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Std_ExtDTreeMap_getEntryLED___redArg(v_cmp_1392_, v_t_1393_, v_k_1394_, v_fallback_1395_);
lean_dec_ref(v_fallback_1395_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED(lean_object* v_00_u03b1_1397_, lean_object* v_00_u03b2_1398_, lean_object* v_cmp_1399_, lean_object* v_inst_1400_, lean_object* v_t_1401_, lean_object* v_k_1402_, lean_object* v_fallback_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_box(0);
v___x_1405_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1399_, v_k_1402_, v___x_1404_, v_t_1401_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_inc_ref(v_fallback_1403_);
return v_fallback_1403_;
}
else
{
lean_object* v_val_1406_; 
v_val_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_val_1406_);
lean_dec_ref_known(v___x_1405_, 1);
return v_val_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1407_, lean_object* v_00_u03b2_1408_, lean_object* v_cmp_1409_, lean_object* v_inst_1410_, lean_object* v_t_1411_, lean_object* v_k_1412_, lean_object* v_fallback_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Std_ExtDTreeMap_getEntryLED(v_00_u03b1_1407_, v_00_u03b2_1408_, v_cmp_1409_, v_inst_1410_, v_t_1411_, v_k_1412_, v_fallback_1413_);
lean_dec_ref(v_fallback_1413_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1415_, lean_object* v_t_1416_, lean_object* v_k_1417_, lean_object* v_fallback_1418_){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_box(0);
v___x_1420_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1415_, v_k_1417_, v___x_1419_, v_t_1416_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_inc_ref(v_fallback_1418_);
return v_fallback_1418_;
}
else
{
lean_object* v_val_1421_; 
v_val_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_val_1421_);
lean_dec_ref_known(v___x_1420_, 1);
return v_val_1421_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1422_, lean_object* v_t_1423_, lean_object* v_k_1424_, lean_object* v_fallback_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Std_ExtDTreeMap_getEntryLTD___redArg(v_cmp_1422_, v_t_1423_, v_k_1424_, v_fallback_1425_);
lean_dec_ref(v_fallback_1425_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD(lean_object* v_00_u03b1_1427_, lean_object* v_00_u03b2_1428_, lean_object* v_cmp_1429_, lean_object* v_inst_1430_, lean_object* v_t_1431_, lean_object* v_k_1432_, lean_object* v_fallback_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1429_, v_k_1432_, v___x_1434_, v_t_1431_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_inc_ref(v_fallback_1433_);
return v_fallback_1433_;
}
else
{
lean_object* v_val_1436_; 
v_val_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1436_);
lean_dec_ref_known(v___x_1435_, 1);
return v_val_1436_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_00_u03b2_1438_, lean_object* v_cmp_1439_, lean_object* v_inst_1440_, lean_object* v_t_1441_, lean_object* v_k_1442_, lean_object* v_fallback_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Std_ExtDTreeMap_getEntryLTD(v_00_u03b1_1437_, v_00_u03b2_1438_, v_cmp_1439_, v_inst_1440_, v_t_1441_, v_k_1442_, v_fallback_1443_);
lean_dec_ref(v_fallback_1443_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1445_, lean_object* v_t_1446_, lean_object* v_k_1447_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1445_, v_k_1447_, v___x_1448_, v_t_1446_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_cmp_1452_, lean_object* v_inst_1453_, lean_object* v_t_1454_, lean_object* v_k_1455_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_box(0);
v___x_1457_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1452_, v_k_1455_, v___x_1456_, v_t_1454_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1458_, lean_object* v_t_1459_, lean_object* v_k_1460_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_box(0);
v___x_1462_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1458_, v_k_1460_, v___x_1461_, v_t_1459_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1463_, lean_object* v_00_u03b2_1464_, lean_object* v_cmp_1465_, lean_object* v_inst_1466_, lean_object* v_t_1467_, lean_object* v_k_1468_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_box(0);
v___x_1470_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1465_, v_k_1468_, v___x_1469_, v_t_1467_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1471_, lean_object* v_t_1472_, lean_object* v_k_1473_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_box(0);
v___x_1475_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1471_, v_k_1473_, v___x_1474_, v_t_1472_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1476_, lean_object* v_00_u03b2_1477_, lean_object* v_cmp_1478_, lean_object* v_inst_1479_, lean_object* v_t_1480_, lean_object* v_k_1481_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_box(0);
v___x_1483_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1478_, v_k_1481_, v___x_1482_, v_t_1480_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1484_, lean_object* v_t_1485_, lean_object* v_k_1486_){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_box(0);
v___x_1488_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1484_, v_k_1486_, v___x_1487_, v_t_1485_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1489_, lean_object* v_00_u03b2_1490_, lean_object* v_cmp_1491_, lean_object* v_inst_1492_, lean_object* v_t_1493_, lean_object* v_k_1494_){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_box(0);
v___x_1496_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1491_, v_k_1494_, v___x_1495_, v_t_1493_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE___redArg(lean_object* v_cmp_1497_, lean_object* v_t_1498_, lean_object* v_k_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1497_, v_k_1499_, v_t_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE(lean_object* v_00_u03b1_1501_, lean_object* v_00_u03b2_1502_, lean_object* v_cmp_1503_, lean_object* v_inst_1504_, lean_object* v_t_1505_, lean_object* v_k_1506_, lean_object* v_h_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1503_, v_k_1506_, v_t_1505_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT___redArg(lean_object* v_cmp_1509_, lean_object* v_t_1510_, lean_object* v_k_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1509_, v_k_1511_, v_t_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT(lean_object* v_00_u03b1_1513_, lean_object* v_00_u03b2_1514_, lean_object* v_cmp_1515_, lean_object* v_inst_1516_, lean_object* v_t_1517_, lean_object* v_k_1518_, lean_object* v_h_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1515_, v_k_1518_, v_t_1517_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE___redArg(lean_object* v_cmp_1521_, lean_object* v_t_1522_, lean_object* v_k_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1521_, v_k_1523_, v_t_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE(lean_object* v_00_u03b1_1525_, lean_object* v_00_u03b2_1526_, lean_object* v_cmp_1527_, lean_object* v_inst_1528_, lean_object* v_t_1529_, lean_object* v_k_1530_, lean_object* v_h_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1527_, v_k_1530_, v_t_1529_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT___redArg(lean_object* v_cmp_1533_, lean_object* v_t_1534_, lean_object* v_k_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1533_, v_k_1535_, v_t_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT(lean_object* v_00_u03b1_1537_, lean_object* v_00_u03b2_1538_, lean_object* v_cmp_1539_, lean_object* v_inst_1540_, lean_object* v_t_1541_, lean_object* v_k_1542_, lean_object* v_h_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1539_, v_k_1542_, v_t_1541_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1545_, lean_object* v_inst_1546_, lean_object* v_t_1547_, lean_object* v_k_1548_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_box(0);
v___x_1550_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1545_, v_k_1548_, v___x_1549_, v_t_1547_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1552_ = l_panic___redArg(v_inst_1546_, v___x_1551_);
return v___x_1552_;
}
else
{
lean_object* v_val_1553_; 
v_val_1553_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1553_);
lean_dec_ref_known(v___x_1550_, 1);
return v_val_1553_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1554_, lean_object* v_inst_1555_, lean_object* v_t_1556_, lean_object* v_k_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Std_ExtDTreeMap_getKeyGE_x21___redArg(v_cmp_1554_, v_inst_1555_, v_t_1556_, v_k_1557_);
lean_dec(v_inst_1555_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1559_, lean_object* v_00_u03b2_1560_, lean_object* v_cmp_1561_, lean_object* v_inst_1562_, lean_object* v_inst_1563_, lean_object* v_t_1564_, lean_object* v_k_1565_){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = lean_box(0);
v___x_1567_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1561_, v_k_1565_, v___x_1566_, v_t_1564_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1569_ = l_panic___redArg(v_inst_1563_, v___x_1568_);
return v___x_1569_;
}
else
{
lean_object* v_val_1570_; 
v_val_1570_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_val_1570_);
lean_dec_ref_known(v___x_1567_, 1);
return v_val_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1571_, lean_object* v_00_u03b2_1572_, lean_object* v_cmp_1573_, lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_t_1576_, lean_object* v_k_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Std_ExtDTreeMap_getKeyGE_x21(v_00_u03b1_1571_, v_00_u03b2_1572_, v_cmp_1573_, v_inst_1574_, v_inst_1575_, v_t_1576_, v_k_1577_);
lean_dec(v_inst_1575_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1579_, lean_object* v_inst_1580_, lean_object* v_t_1581_, lean_object* v_k_1582_){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_box(0);
v___x_1584_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1579_, v_k_1582_, v___x_1583_, v_t_1581_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1586_ = l_panic___redArg(v_inst_1580_, v___x_1585_);
return v___x_1586_;
}
else
{
lean_object* v_val_1587_; 
v_val_1587_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_val_1587_);
lean_dec_ref_known(v___x_1584_, 1);
return v_val_1587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1588_, lean_object* v_inst_1589_, lean_object* v_t_1590_, lean_object* v_k_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Std_ExtDTreeMap_getKeyGT_x21___redArg(v_cmp_1588_, v_inst_1589_, v_t_1590_, v_k_1591_);
lean_dec(v_inst_1589_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1593_, lean_object* v_00_u03b2_1594_, lean_object* v_cmp_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_t_1598_, lean_object* v_k_1599_){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = lean_box(0);
v___x_1601_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1595_, v_k_1599_, v___x_1600_, v_t_1598_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1603_ = l_panic___redArg(v_inst_1597_, v___x_1602_);
return v___x_1603_;
}
else
{
lean_object* v_val_1604_; 
v_val_1604_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v___x_1601_, 1);
return v_val_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1605_, lean_object* v_00_u03b2_1606_, lean_object* v_cmp_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_t_1610_, lean_object* v_k_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Std_ExtDTreeMap_getKeyGT_x21(v_00_u03b1_1605_, v_00_u03b2_1606_, v_cmp_1607_, v_inst_1608_, v_inst_1609_, v_t_1610_, v_k_1611_);
lean_dec(v_inst_1609_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1613_, lean_object* v_inst_1614_, lean_object* v_t_1615_, lean_object* v_k_1616_){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_box(0);
v___x_1618_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1613_, v_k_1616_, v___x_1617_, v_t_1615_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1620_ = l_panic___redArg(v_inst_1614_, v___x_1619_);
return v___x_1620_;
}
else
{
lean_object* v_val_1621_; 
v_val_1621_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_val_1621_);
lean_dec_ref_known(v___x_1618_, 1);
return v_val_1621_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1622_, lean_object* v_inst_1623_, lean_object* v_t_1624_, lean_object* v_k_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Std_ExtDTreeMap_getKeyLE_x21___redArg(v_cmp_1622_, v_inst_1623_, v_t_1624_, v_k_1625_);
lean_dec(v_inst_1623_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1627_, lean_object* v_00_u03b2_1628_, lean_object* v_cmp_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_t_1632_, lean_object* v_k_1633_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_box(0);
v___x_1635_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1629_, v_k_1633_, v___x_1634_, v_t_1632_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1637_ = l_panic___redArg(v_inst_1631_, v___x_1636_);
return v___x_1637_;
}
else
{
lean_object* v_val_1638_; 
v_val_1638_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_val_1638_);
lean_dec_ref_known(v___x_1635_, 1);
return v_val_1638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_cmp_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_t_1644_, lean_object* v_k_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Std_ExtDTreeMap_getKeyLE_x21(v_00_u03b1_1639_, v_00_u03b2_1640_, v_cmp_1641_, v_inst_1642_, v_inst_1643_, v_t_1644_, v_k_1645_);
lean_dec(v_inst_1643_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1647_, lean_object* v_inst_1648_, lean_object* v_t_1649_, lean_object* v_k_1650_){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_box(0);
v___x_1652_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1647_, v_k_1650_, v___x_1651_, v_t_1649_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1654_ = l_panic___redArg(v_inst_1648_, v___x_1653_);
return v___x_1654_;
}
else
{
lean_object* v_val_1655_; 
v_val_1655_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_val_1655_);
lean_dec_ref_known(v___x_1652_, 1);
return v_val_1655_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1656_, lean_object* v_inst_1657_, lean_object* v_t_1658_, lean_object* v_k_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Std_ExtDTreeMap_getKeyLT_x21___redArg(v_cmp_1656_, v_inst_1657_, v_t_1658_, v_k_1659_);
lean_dec(v_inst_1657_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1661_, lean_object* v_00_u03b2_1662_, lean_object* v_cmp_1663_, lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_t_1666_, lean_object* v_k_1667_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = lean_box(0);
v___x_1669_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1663_, v_k_1667_, v___x_1668_, v_t_1666_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1671_ = l_panic___redArg(v_inst_1665_, v___x_1670_);
return v___x_1671_;
}
else
{
lean_object* v_val_1672_; 
v_val_1672_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_val_1672_);
lean_dec_ref_known(v___x_1669_, 1);
return v_val_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1673_, lean_object* v_00_u03b2_1674_, lean_object* v_cmp_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_t_1678_, lean_object* v_k_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Std_ExtDTreeMap_getKeyLT_x21(v_00_u03b1_1673_, v_00_u03b2_1674_, v_cmp_1675_, v_inst_1676_, v_inst_1677_, v_t_1678_, v_k_1679_);
lean_dec(v_inst_1677_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___redArg(lean_object* v_cmp_1681_, lean_object* v_t_1682_, lean_object* v_k_1683_, lean_object* v_fallback_1684_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = lean_box(0);
v___x_1686_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1681_, v_k_1683_, v___x_1685_, v_t_1682_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_inc(v_fallback_1684_);
return v_fallback_1684_;
}
else
{
lean_object* v_val_1687_; 
v_val_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_val_1687_);
lean_dec_ref_known(v___x_1686_, 1);
return v_val_1687_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1688_, lean_object* v_t_1689_, lean_object* v_k_1690_, lean_object* v_fallback_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Std_ExtDTreeMap_getKeyGED___redArg(v_cmp_1688_, v_t_1689_, v_k_1690_, v_fallback_1691_);
lean_dec(v_fallback_1691_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED(lean_object* v_00_u03b1_1693_, lean_object* v_00_u03b2_1694_, lean_object* v_cmp_1695_, lean_object* v_inst_1696_, lean_object* v_t_1697_, lean_object* v_k_1698_, lean_object* v_fallback_1699_){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = lean_box(0);
v___x_1701_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1695_, v_k_1698_, v___x_1700_, v_t_1697_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_inc(v_fallback_1699_);
return v_fallback_1699_;
}
else
{
lean_object* v_val_1702_; 
v_val_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_val_1702_);
lean_dec_ref_known(v___x_1701_, 1);
return v_val_1702_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_00_u03b2_1704_, lean_object* v_cmp_1705_, lean_object* v_inst_1706_, lean_object* v_t_1707_, lean_object* v_k_1708_, lean_object* v_fallback_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Std_ExtDTreeMap_getKeyGED(v_00_u03b1_1703_, v_00_u03b2_1704_, v_cmp_1705_, v_inst_1706_, v_t_1707_, v_k_1708_, v_fallback_1709_);
lean_dec(v_fallback_1709_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1711_, lean_object* v_t_1712_, lean_object* v_k_1713_, lean_object* v_fallback_1714_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_box(0);
v___x_1716_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1711_, v_k_1713_, v___x_1715_, v_t_1712_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_inc(v_fallback_1714_);
return v_fallback_1714_;
}
else
{
lean_object* v_val_1717_; 
v_val_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_val_1717_);
lean_dec_ref_known(v___x_1716_, 1);
return v_val_1717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1718_, lean_object* v_t_1719_, lean_object* v_k_1720_, lean_object* v_fallback_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Std_ExtDTreeMap_getKeyGTD___redArg(v_cmp_1718_, v_t_1719_, v_k_1720_, v_fallback_1721_);
lean_dec(v_fallback_1721_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD(lean_object* v_00_u03b1_1723_, lean_object* v_00_u03b2_1724_, lean_object* v_cmp_1725_, lean_object* v_inst_1726_, lean_object* v_t_1727_, lean_object* v_k_1728_, lean_object* v_fallback_1729_){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_box(0);
v___x_1731_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1725_, v_k_1728_, v___x_1730_, v_t_1727_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_inc(v_fallback_1729_);
return v_fallback_1729_;
}
else
{
lean_object* v_val_1732_; 
v_val_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_val_1732_);
lean_dec_ref_known(v___x_1731_, 1);
return v_val_1732_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1733_, lean_object* v_00_u03b2_1734_, lean_object* v_cmp_1735_, lean_object* v_inst_1736_, lean_object* v_t_1737_, lean_object* v_k_1738_, lean_object* v_fallback_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Std_ExtDTreeMap_getKeyGTD(v_00_u03b1_1733_, v_00_u03b2_1734_, v_cmp_1735_, v_inst_1736_, v_t_1737_, v_k_1738_, v_fallback_1739_);
lean_dec(v_fallback_1739_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___redArg(lean_object* v_cmp_1741_, lean_object* v_t_1742_, lean_object* v_k_1743_, lean_object* v_fallback_1744_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_box(0);
v___x_1746_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1741_, v_k_1743_, v___x_1745_, v_t_1742_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_inc(v_fallback_1744_);
return v_fallback_1744_;
}
else
{
lean_object* v_val_1747_; 
v_val_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_val_1747_);
lean_dec_ref_known(v___x_1746_, 1);
return v_val_1747_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1748_, lean_object* v_t_1749_, lean_object* v_k_1750_, lean_object* v_fallback_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Std_ExtDTreeMap_getKeyLED___redArg(v_cmp_1748_, v_t_1749_, v_k_1750_, v_fallback_1751_);
lean_dec(v_fallback_1751_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED(lean_object* v_00_u03b1_1753_, lean_object* v_00_u03b2_1754_, lean_object* v_cmp_1755_, lean_object* v_inst_1756_, lean_object* v_t_1757_, lean_object* v_k_1758_, lean_object* v_fallback_1759_){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_box(0);
v___x_1761_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1755_, v_k_1758_, v___x_1760_, v_t_1757_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_inc(v_fallback_1759_);
return v_fallback_1759_;
}
else
{
lean_object* v_val_1762_; 
v_val_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_val_1762_);
lean_dec_ref_known(v___x_1761_, 1);
return v_val_1762_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1763_, lean_object* v_00_u03b2_1764_, lean_object* v_cmp_1765_, lean_object* v_inst_1766_, lean_object* v_t_1767_, lean_object* v_k_1768_, lean_object* v_fallback_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Std_ExtDTreeMap_getKeyLED(v_00_u03b1_1763_, v_00_u03b2_1764_, v_cmp_1765_, v_inst_1766_, v_t_1767_, v_k_1768_, v_fallback_1769_);
lean_dec(v_fallback_1769_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1771_, lean_object* v_t_1772_, lean_object* v_k_1773_, lean_object* v_fallback_1774_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = lean_box(0);
v___x_1776_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1771_, v_k_1773_, v___x_1775_, v_t_1772_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_inc(v_fallback_1774_);
return v_fallback_1774_;
}
else
{
lean_object* v_val_1777_; 
v_val_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_val_1777_);
lean_dec_ref_known(v___x_1776_, 1);
return v_val_1777_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1778_, lean_object* v_t_1779_, lean_object* v_k_1780_, lean_object* v_fallback_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Std_ExtDTreeMap_getKeyLTD___redArg(v_cmp_1778_, v_t_1779_, v_k_1780_, v_fallback_1781_);
lean_dec(v_fallback_1781_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD(lean_object* v_00_u03b1_1783_, lean_object* v_00_u03b2_1784_, lean_object* v_cmp_1785_, lean_object* v_inst_1786_, lean_object* v_t_1787_, lean_object* v_k_1788_, lean_object* v_fallback_1789_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_box(0);
v___x_1791_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1785_, v_k_1788_, v___x_1790_, v_t_1787_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_inc(v_fallback_1789_);
return v_fallback_1789_;
}
else
{
lean_object* v_val_1792_; 
v_val_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_val_1792_);
lean_dec_ref_known(v___x_1791_, 1);
return v_val_1792_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1793_, lean_object* v_00_u03b2_1794_, lean_object* v_cmp_1795_, lean_object* v_inst_1796_, lean_object* v_t_1797_, lean_object* v_k_1798_, lean_object* v_fallback_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Std_ExtDTreeMap_getKeyLTD(v_00_u03b1_1793_, v_00_u03b2_1794_, v_cmp_1795_, v_inst_1796_, v_t_1797_, v_k_1798_, v_fallback_1799_);
lean_dec(v_fallback_1799_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1801_, lean_object* v_t_1802_, lean_object* v_a_1803_, lean_object* v_b_1804_){
_start:
{
lean_object* v___x_1805_; 
lean_inc(v_a_1803_);
lean_inc(v_t_1802_);
lean_inc_ref(v_cmp_1801_);
v___x_1805_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1801_, v_t_1802_, v_a_1803_);
if (lean_obj_tag(v___x_1805_) == 0)
{
uint8_t v___x_1806_; 
lean_inc(v_t_1802_);
lean_inc(v_a_1803_);
lean_inc_ref(v_cmp_1801_);
v___x_1806_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1801_, v_a_1803_, v_t_1802_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1801_, v_a_1803_, v_b_1804_, v_t_1802_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1805_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
return v___x_1808_;
}
else
{
lean_object* v___x_1809_; 
lean_dec(v_b_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_cmp_1801_);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1805_);
lean_ctor_set(v___x_1809_, 1, v_t_1802_);
return v___x_1809_;
}
}
else
{
lean_object* v___x_1810_; 
lean_dec(v_b_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_cmp_1801_);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1805_);
lean_ctor_set(v___x_1810_, 1, v_t_1802_);
return v___x_1810_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1811_, lean_object* v_cmp_1812_, lean_object* v_00_u03b2_1813_, lean_object* v_inst_1814_, lean_object* v_t_1815_, lean_object* v_a_1816_, lean_object* v_b_1817_){
_start:
{
lean_object* v___x_1818_; 
lean_inc(v_a_1816_);
lean_inc(v_t_1815_);
lean_inc_ref(v_cmp_1812_);
v___x_1818_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1812_, v_t_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1818_) == 0)
{
uint8_t v___x_1819_; 
lean_inc(v_t_1815_);
lean_inc(v_a_1816_);
lean_inc_ref(v_cmp_1812_);
v___x_1819_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1812_, v_a_1816_, v_t_1815_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1812_, v_a_1816_, v_b_1817_, v_t_1815_);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1818_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; 
lean_dec(v_b_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_cmp_1812_);
v___x_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1818_);
lean_ctor_set(v___x_1822_, 1, v_t_1815_);
return v___x_1822_;
}
}
else
{
lean_object* v___x_1823_; 
lean_dec(v_b_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_cmp_1812_);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1818_);
lean_ctor_set(v___x_1823_, 1, v_t_1815_);
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x3f___redArg(lean_object* v_cmp_1824_, lean_object* v_t_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1824_, v_t_1825_, v_a_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x3f(lean_object* v_00_u03b1_1828_, lean_object* v_cmp_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_inst_1831_, lean_object* v_t_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1829_, v_t_1832_, v_a_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get___redArg(lean_object* v_cmp_1835_, lean_object* v_t_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1835_, v_t_1836_, v_a_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get(lean_object* v_00_u03b1_1839_, lean_object* v_cmp_1840_, lean_object* v_00_u03b2_1841_, lean_object* v_inst_1842_, lean_object* v_t_1843_, lean_object* v_a_1844_, lean_object* v_h_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1840_, v_t_1843_, v_a_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___redArg(lean_object* v_cmp_1847_, lean_object* v_inst_1848_, lean_object* v_t_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1847_, v_inst_1848_, v_t_1849_, v_a_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___redArg___boxed(lean_object* v_cmp_1852_, lean_object* v_inst_1853_, lean_object* v_t_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Std_ExtDTreeMap_Const_get_x21___redArg(v_cmp_1852_, v_inst_1853_, v_t_1854_, v_a_1855_);
lean_dec(v_inst_1853_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21(lean_object* v_00_u03b1_1857_, lean_object* v_cmp_1858_, lean_object* v_00_u03b2_1859_, lean_object* v_inst_1860_, lean_object* v_inst_1861_, lean_object* v_t_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1858_, v_inst_1861_, v_t_1862_, v_a_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___boxed(lean_object* v_00_u03b1_1865_, lean_object* v_cmp_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_t_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Std_ExtDTreeMap_Const_get_x21(v_00_u03b1_1865_, v_cmp_1866_, v_00_u03b2_1867_, v_inst_1868_, v_inst_1869_, v_t_1870_, v_a_1871_);
lean_dec(v_inst_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___redArg(lean_object* v_cmp_1873_, lean_object* v_t_1874_, lean_object* v_a_1875_, lean_object* v_fallback_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1873_, v_t_1874_, v_a_1875_, v_fallback_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___redArg___boxed(lean_object* v_cmp_1878_, lean_object* v_t_1879_, lean_object* v_a_1880_, lean_object* v_fallback_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Std_ExtDTreeMap_Const_getD___redArg(v_cmp_1878_, v_t_1879_, v_a_1880_, v_fallback_1881_);
lean_dec(v_fallback_1881_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD(lean_object* v_00_u03b1_1883_, lean_object* v_cmp_1884_, lean_object* v_00_u03b2_1885_, lean_object* v_inst_1886_, lean_object* v_t_1887_, lean_object* v_a_1888_, lean_object* v_fallback_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1884_, v_t_1887_, v_a_1888_, v_fallback_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___boxed(lean_object* v_00_u03b1_1891_, lean_object* v_cmp_1892_, lean_object* v_00_u03b2_1893_, lean_object* v_inst_1894_, lean_object* v_t_1895_, lean_object* v_a_1896_, lean_object* v_fallback_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Std_ExtDTreeMap_Const_getD(v_00_u03b1_1891_, v_cmp_1892_, v_00_u03b2_1893_, v_inst_1894_, v_t_1895_, v_a_1896_, v_fallback_1897_);
lean_dec(v_fallback_1897_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(lean_object* v_t_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(v_t_1901_);
lean_dec(v_t_1901_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f(lean_object* v_00_u03b1_1903_, lean_object* v_cmp_1904_, lean_object* v_00_u03b2_1905_, lean_object* v_inst_1906_, lean_object* v_t_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1909_, lean_object* v_cmp_1910_, lean_object* v_00_u03b2_1911_, lean_object* v_inst_1912_, lean_object* v_t_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Std_ExtDTreeMap_Const_minEntry_x3f(v_00_u03b1_1909_, v_cmp_1910_, v_00_u03b2_1911_, v_inst_1912_, v_t_1913_);
lean_dec(v_t_1913_);
lean_dec_ref(v_cmp_1910_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___redArg(lean_object* v_t_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___redArg___boxed(lean_object* v_t_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Std_ExtDTreeMap_Const_minEntry___redArg(v_t_1917_);
lean_dec(v_t_1917_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry(lean_object* v_00_u03b1_1919_, lean_object* v_cmp_1920_, lean_object* v_00_u03b2_1921_, lean_object* v_inst_1922_, lean_object* v_t_1923_, lean_object* v_h_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1923_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___boxed(lean_object* v_00_u03b1_1926_, lean_object* v_cmp_1927_, lean_object* v_00_u03b2_1928_, lean_object* v_inst_1929_, lean_object* v_t_1930_, lean_object* v_h_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Std_ExtDTreeMap_Const_minEntry(v_00_u03b1_1926_, v_cmp_1927_, v_00_u03b2_1928_, v_inst_1929_, v_t_1930_, v_h_1931_);
lean_dec(v_t_1930_);
lean_dec_ref(v_cmp_1927_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(lean_object* v_inst_1933_, lean_object* v_t_1934_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1933_, v_t_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1936_, lean_object* v_t_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(v_inst_1936_, v_t_1937_);
lean_dec(v_t_1937_);
lean_dec_ref(v_inst_1936_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21(lean_object* v_00_u03b1_1939_, lean_object* v_cmp_1940_, lean_object* v_00_u03b2_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_t_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1943_, v_t_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_cmp_1947_, lean_object* v_00_u03b2_1948_, lean_object* v_inst_1949_, lean_object* v_inst_1950_, lean_object* v_t_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Std_ExtDTreeMap_Const_minEntry_x21(v_00_u03b1_1946_, v_cmp_1947_, v_00_u03b2_1948_, v_inst_1949_, v_inst_1950_, v_t_1951_);
lean_dec(v_t_1951_);
lean_dec_ref(v_inst_1950_);
lean_dec_ref(v_cmp_1947_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___redArg(lean_object* v_t_1953_, lean_object* v_fallback_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1953_, v_fallback_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___redArg___boxed(lean_object* v_t_1956_, lean_object* v_fallback_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Std_ExtDTreeMap_Const_minEntryD___redArg(v_t_1956_, v_fallback_1957_);
lean_dec_ref(v_fallback_1957_);
lean_dec(v_t_1956_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD(lean_object* v_00_u03b1_1959_, lean_object* v_cmp_1960_, lean_object* v_00_u03b2_1961_, lean_object* v_inst_1962_, lean_object* v_t_1963_, lean_object* v_fallback_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1963_, v_fallback_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___boxed(lean_object* v_00_u03b1_1966_, lean_object* v_cmp_1967_, lean_object* v_00_u03b2_1968_, lean_object* v_inst_1969_, lean_object* v_t_1970_, lean_object* v_fallback_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Std_ExtDTreeMap_Const_minEntryD(v_00_u03b1_1966_, v_cmp_1967_, v_00_u03b2_1968_, v_inst_1969_, v_t_1970_, v_fallback_1971_);
lean_dec_ref(v_fallback_1971_);
lean_dec(v_t_1970_);
lean_dec_ref(v_cmp_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(lean_object* v_t_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(v_t_1975_);
lean_dec(v_t_1975_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f(lean_object* v_00_u03b1_1977_, lean_object* v_cmp_1978_, lean_object* v_00_u03b2_1979_, lean_object* v_inst_1980_, lean_object* v_t_1981_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1983_, lean_object* v_cmp_1984_, lean_object* v_00_u03b2_1985_, lean_object* v_inst_1986_, lean_object* v_t_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Std_ExtDTreeMap_Const_maxEntry_x3f(v_00_u03b1_1983_, v_cmp_1984_, v_00_u03b2_1985_, v_inst_1986_, v_t_1987_);
lean_dec(v_t_1987_);
lean_dec_ref(v_cmp_1984_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___redArg(lean_object* v_t_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___redArg___boxed(lean_object* v_t_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Std_ExtDTreeMap_Const_maxEntry___redArg(v_t_1991_);
lean_dec(v_t_1991_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry(lean_object* v_00_u03b1_1993_, lean_object* v_cmp_1994_, lean_object* v_00_u03b2_1995_, lean_object* v_inst_1996_, lean_object* v_t_1997_, lean_object* v_h_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1997_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___boxed(lean_object* v_00_u03b1_2000_, lean_object* v_cmp_2001_, lean_object* v_00_u03b2_2002_, lean_object* v_inst_2003_, lean_object* v_t_2004_, lean_object* v_h_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Std_ExtDTreeMap_Const_maxEntry(v_00_u03b1_2000_, v_cmp_2001_, v_00_u03b2_2002_, v_inst_2003_, v_t_2004_, v_h_2005_);
lean_dec(v_t_2004_);
lean_dec_ref(v_cmp_2001_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(lean_object* v_inst_2007_, lean_object* v_t_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_2007_, v_t_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_2010_, lean_object* v_t_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(v_inst_2010_, v_t_2011_);
lean_dec(v_t_2011_);
lean_dec_ref(v_inst_2010_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21(lean_object* v_00_u03b1_2013_, lean_object* v_cmp_2014_, lean_object* v_00_u03b2_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_t_2018_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_2017_, v_t_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_2020_, lean_object* v_cmp_2021_, lean_object* v_00_u03b2_2022_, lean_object* v_inst_2023_, lean_object* v_inst_2024_, lean_object* v_t_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Std_ExtDTreeMap_Const_maxEntry_x21(v_00_u03b1_2020_, v_cmp_2021_, v_00_u03b2_2022_, v_inst_2023_, v_inst_2024_, v_t_2025_);
lean_dec(v_t_2025_);
lean_dec_ref(v_inst_2024_);
lean_dec_ref(v_cmp_2021_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___redArg(lean_object* v_t_2027_, lean_object* v_fallback_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_2027_, v_fallback_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___redArg___boxed(lean_object* v_t_2030_, lean_object* v_fallback_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Std_ExtDTreeMap_Const_maxEntryD___redArg(v_t_2030_, v_fallback_2031_);
lean_dec_ref(v_fallback_2031_);
lean_dec(v_t_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD(lean_object* v_00_u03b1_2033_, lean_object* v_cmp_2034_, lean_object* v_00_u03b2_2035_, lean_object* v_inst_2036_, lean_object* v_t_2037_, lean_object* v_fallback_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_2037_, v_fallback_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___boxed(lean_object* v_00_u03b1_2040_, lean_object* v_cmp_2041_, lean_object* v_00_u03b2_2042_, lean_object* v_inst_2043_, lean_object* v_t_2044_, lean_object* v_fallback_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Std_ExtDTreeMap_Const_maxEntryD(v_00_u03b1_2040_, v_cmp_2041_, v_00_u03b2_2042_, v_inst_2043_, v_t_2044_, v_fallback_2045_);
lean_dec_ref(v_fallback_2045_);
lean_dec(v_t_2044_);
lean_dec_ref(v_cmp_2041_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(lean_object* v_t_2047_, lean_object* v_n_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_2047_, v_n_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_2050_, lean_object* v_n_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(v_t_2050_, v_n_2051_);
lean_dec(v_t_2050_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_2053_, lean_object* v_cmp_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_inst_2056_, lean_object* v_t_2057_, lean_object* v_n_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_2057_, v_n_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_2060_, lean_object* v_cmp_2061_, lean_object* v_00_u03b2_2062_, lean_object* v_inst_2063_, lean_object* v_t_2064_, lean_object* v_n_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(v_00_u03b1_2060_, v_cmp_2061_, v_00_u03b2_2062_, v_inst_2063_, v_t_2064_, v_n_2065_);
lean_dec(v_t_2064_);
lean_dec_ref(v_cmp_2061_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(lean_object* v_t_2067_, lean_object* v_n_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_2067_, v_n_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___redArg___boxed(lean_object* v_t_2070_, lean_object* v_n_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(v_t_2070_, v_n_2071_);
lean_dec(v_t_2070_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx(lean_object* v_00_u03b1_2073_, lean_object* v_cmp_2074_, lean_object* v_00_u03b2_2075_, lean_object* v_inst_2076_, lean_object* v_t_2077_, lean_object* v_n_2078_, lean_object* v_h_2079_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_2077_, v_n_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_2081_, lean_object* v_cmp_2082_, lean_object* v_00_u03b2_2083_, lean_object* v_inst_2084_, lean_object* v_t_2085_, lean_object* v_n_2086_, lean_object* v_h_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Std_ExtDTreeMap_Const_entryAtIdx(v_00_u03b1_2081_, v_cmp_2082_, v_00_u03b2_2083_, v_inst_2084_, v_t_2085_, v_n_2086_, v_h_2087_);
lean_dec(v_t_2085_);
lean_dec_ref(v_cmp_2082_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(lean_object* v_inst_2089_, lean_object* v_t_2090_, lean_object* v_n_2091_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_2089_, v_t_2090_, v_n_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_2093_, lean_object* v_t_2094_, lean_object* v_n_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(v_inst_2093_, v_t_2094_, v_n_2095_);
lean_dec(v_t_2094_);
lean_dec_ref(v_inst_2093_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21(lean_object* v_00_u03b1_2097_, lean_object* v_cmp_2098_, lean_object* v_00_u03b2_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_t_2102_, lean_object* v_n_2103_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_2101_, v_t_2102_, v_n_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_2105_, lean_object* v_cmp_2106_, lean_object* v_00_u03b2_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_t_2110_, lean_object* v_n_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x21(v_00_u03b1_2105_, v_cmp_2106_, v_00_u03b2_2107_, v_inst_2108_, v_inst_2109_, v_t_2110_, v_n_2111_);
lean_dec(v_t_2110_);
lean_dec_ref(v_inst_2109_);
lean_dec_ref(v_cmp_2106_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(lean_object* v_t_2113_, lean_object* v_n_2114_, lean_object* v_fallback_2115_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_2113_, v_n_2114_, v_fallback_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_2117_, lean_object* v_n_2118_, lean_object* v_fallback_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(v_t_2117_, v_n_2118_, v_fallback_2119_);
lean_dec_ref(v_fallback_2119_);
lean_dec(v_t_2117_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD(lean_object* v_00_u03b1_2121_, lean_object* v_cmp_2122_, lean_object* v_00_u03b2_2123_, lean_object* v_inst_2124_, lean_object* v_t_2125_, lean_object* v_n_2126_, lean_object* v_fallback_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_2125_, v_n_2126_, v_fallback_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_2129_, lean_object* v_cmp_2130_, lean_object* v_00_u03b2_2131_, lean_object* v_inst_2132_, lean_object* v_t_2133_, lean_object* v_n_2134_, lean_object* v_fallback_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Std_ExtDTreeMap_Const_entryAtIdxD(v_00_u03b1_2129_, v_cmp_2130_, v_00_u03b2_2131_, v_inst_2132_, v_t_2133_, v_n_2134_, v_fallback_2135_);
lean_dec_ref(v_fallback_2135_);
lean_dec(v_t_2133_);
lean_dec_ref(v_cmp_2130_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_2137_, lean_object* v_t_2138_, lean_object* v_k_2139_){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_box(0);
v___x_2141_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2137_, v_k_2139_, v___x_2140_, v_t_2138_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x3f(lean_object* v_00_u03b1_2142_, lean_object* v_cmp_2143_, lean_object* v_00_u03b2_2144_, lean_object* v_inst_2145_, lean_object* v_t_2146_, lean_object* v_k_2147_){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_box(0);
v___x_2149_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2143_, v_k_2147_, v___x_2148_, v_t_2146_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_2150_, lean_object* v_t_2151_, lean_object* v_k_2152_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_box(0);
v___x_2154_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2150_, v_k_2152_, v___x_2153_, v_t_2151_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x3f(lean_object* v_00_u03b1_2155_, lean_object* v_cmp_2156_, lean_object* v_00_u03b2_2157_, lean_object* v_inst_2158_, lean_object* v_t_2159_, lean_object* v_k_2160_){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_box(0);
v___x_2162_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2156_, v_k_2160_, v___x_2161_, v_t_2159_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_2163_, lean_object* v_t_2164_, lean_object* v_k_2165_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_box(0);
v___x_2167_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2163_, v_k_2165_, v___x_2166_, v_t_2164_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x3f(lean_object* v_00_u03b1_2168_, lean_object* v_cmp_2169_, lean_object* v_00_u03b2_2170_, lean_object* v_inst_2171_, lean_object* v_t_2172_, lean_object* v_k_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = lean_box(0);
v___x_2175_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2169_, v_k_2173_, v___x_2174_, v_t_2172_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_2176_, lean_object* v_t_2177_, lean_object* v_k_2178_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_box(0);
v___x_2180_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2176_, v_k_2178_, v___x_2179_, v_t_2177_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x3f(lean_object* v_00_u03b1_2181_, lean_object* v_cmp_2182_, lean_object* v_00_u03b2_2183_, lean_object* v_inst_2184_, lean_object* v_t_2185_, lean_object* v_k_2186_){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = lean_box(0);
v___x_2188_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2182_, v_k_2186_, v___x_2187_, v_t_2185_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE___redArg(lean_object* v_cmp_2189_, lean_object* v_t_2190_, lean_object* v_k_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_2189_, v_k_2191_, v_t_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE(lean_object* v_00_u03b1_2193_, lean_object* v_cmp_2194_, lean_object* v_00_u03b2_2195_, lean_object* v_inst_2196_, lean_object* v_t_2197_, lean_object* v_k_2198_, lean_object* v_h_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_2194_, v_k_2198_, v_t_2197_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT___redArg(lean_object* v_cmp_2201_, lean_object* v_t_2202_, lean_object* v_k_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_2201_, v_k_2203_, v_t_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT(lean_object* v_00_u03b1_2205_, lean_object* v_cmp_2206_, lean_object* v_00_u03b2_2207_, lean_object* v_inst_2208_, lean_object* v_t_2209_, lean_object* v_k_2210_, lean_object* v_h_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_2206_, v_k_2210_, v_t_2209_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE___redArg(lean_object* v_cmp_2213_, lean_object* v_t_2214_, lean_object* v_k_2215_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_2213_, v_k_2215_, v_t_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE(lean_object* v_00_u03b1_2217_, lean_object* v_cmp_2218_, lean_object* v_00_u03b2_2219_, lean_object* v_inst_2220_, lean_object* v_t_2221_, lean_object* v_k_2222_, lean_object* v_h_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_2218_, v_k_2222_, v_t_2221_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT___redArg(lean_object* v_cmp_2225_, lean_object* v_t_2226_, lean_object* v_k_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_2225_, v_k_2227_, v_t_2226_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT(lean_object* v_00_u03b1_2229_, lean_object* v_cmp_2230_, lean_object* v_00_u03b2_2231_, lean_object* v_inst_2232_, lean_object* v_t_2233_, lean_object* v_k_2234_, lean_object* v_h_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_2230_, v_k_2234_, v_t_2233_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg(lean_object* v_cmp_2237_, lean_object* v_inst_2238_, lean_object* v_t_2239_, lean_object* v_k_2240_){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_box(0);
v___x_2242_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2237_, v_k_2240_, v___x_2241_, v_t_2239_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2244_ = l_panic___redArg(v_inst_2238_, v___x_2243_);
return v___x_2244_;
}
else
{
lean_object* v_val_2245_; 
v_val_2245_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_val_2245_);
lean_dec_ref_known(v___x_2242_, 1);
return v_val_2245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_2246_, lean_object* v_inst_2247_, lean_object* v_t_2248_, lean_object* v_k_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg(v_cmp_2246_, v_inst_2247_, v_t_2248_, v_k_2249_);
lean_dec_ref(v_inst_2247_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21(lean_object* v_00_u03b1_2251_, lean_object* v_cmp_2252_, lean_object* v_00_u03b2_2253_, lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_t_2256_, lean_object* v_k_2257_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_box(0);
v___x_2259_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2252_, v_k_2257_, v___x_2258_, v_t_2256_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2261_ = l_panic___redArg(v_inst_2255_, v___x_2260_);
return v___x_2261_;
}
else
{
lean_object* v_val_2262_; 
v_val_2262_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_val_2262_);
lean_dec_ref_known(v___x_2259_, 1);
return v_val_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_2263_, lean_object* v_cmp_2264_, lean_object* v_00_u03b2_2265_, lean_object* v_inst_2266_, lean_object* v_inst_2267_, lean_object* v_t_2268_, lean_object* v_k_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Std_ExtDTreeMap_Const_getEntryGE_x21(v_00_u03b1_2263_, v_cmp_2264_, v_00_u03b2_2265_, v_inst_2266_, v_inst_2267_, v_t_2268_, v_k_2269_);
lean_dec_ref(v_inst_2267_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(lean_object* v_cmp_2271_, lean_object* v_inst_2272_, lean_object* v_t_2273_, lean_object* v_k_2274_){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2271_, v_k_2274_, v___x_2275_, v_t_2273_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2278_ = l_panic___redArg(v_inst_2272_, v___x_2277_);
return v___x_2278_;
}
else
{
lean_object* v_val_2279_; 
v_val_2279_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_val_2279_);
lean_dec_ref_known(v___x_2276_, 1);
return v_val_2279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_2280_, lean_object* v_inst_2281_, lean_object* v_t_2282_, lean_object* v_k_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(v_cmp_2280_, v_inst_2281_, v_t_2282_, v_k_2283_);
lean_dec_ref(v_inst_2281_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21(lean_object* v_00_u03b1_2285_, lean_object* v_cmp_2286_, lean_object* v_00_u03b2_2287_, lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v_t_2290_, lean_object* v_k_2291_){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_box(0);
v___x_2293_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2286_, v_k_2291_, v___x_2292_, v_t_2290_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2295_ = l_panic___redArg(v_inst_2289_, v___x_2294_);
return v___x_2295_;
}
else
{
lean_object* v_val_2296_; 
v_val_2296_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_val_2296_);
lean_dec_ref_known(v___x_2293_, 1);
return v_val_2296_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_2297_, lean_object* v_cmp_2298_, lean_object* v_00_u03b2_2299_, lean_object* v_inst_2300_, lean_object* v_inst_2301_, lean_object* v_t_2302_, lean_object* v_k_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Std_ExtDTreeMap_Const_getEntryGT_x21(v_00_u03b1_2297_, v_cmp_2298_, v_00_u03b2_2299_, v_inst_2300_, v_inst_2301_, v_t_2302_, v_k_2303_);
lean_dec_ref(v_inst_2301_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(lean_object* v_cmp_2305_, lean_object* v_inst_2306_, lean_object* v_t_2307_, lean_object* v_k_2308_){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_box(0);
v___x_2310_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2305_, v_k_2308_, v___x_2309_, v_t_2307_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2312_ = l_panic___redArg(v_inst_2306_, v___x_2311_);
return v___x_2312_;
}
else
{
lean_object* v_val_2313_; 
v_val_2313_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_val_2313_);
lean_dec_ref_known(v___x_2310_, 1);
return v_val_2313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_2314_, lean_object* v_inst_2315_, lean_object* v_t_2316_, lean_object* v_k_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(v_cmp_2314_, v_inst_2315_, v_t_2316_, v_k_2317_);
lean_dec_ref(v_inst_2315_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21(lean_object* v_00_u03b1_2319_, lean_object* v_cmp_2320_, lean_object* v_00_u03b2_2321_, lean_object* v_inst_2322_, lean_object* v_inst_2323_, lean_object* v_t_2324_, lean_object* v_k_2325_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_box(0);
v___x_2327_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2320_, v_k_2325_, v___x_2326_, v_t_2324_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2329_ = l_panic___redArg(v_inst_2323_, v___x_2328_);
return v___x_2329_;
}
else
{
lean_object* v_val_2330_; 
v_val_2330_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_val_2330_);
lean_dec_ref_known(v___x_2327_, 1);
return v_val_2330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2331_, lean_object* v_cmp_2332_, lean_object* v_00_u03b2_2333_, lean_object* v_inst_2334_, lean_object* v_inst_2335_, lean_object* v_t_2336_, lean_object* v_k_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Std_ExtDTreeMap_Const_getEntryLE_x21(v_00_u03b1_2331_, v_cmp_2332_, v_00_u03b2_2333_, v_inst_2334_, v_inst_2335_, v_t_2336_, v_k_2337_);
lean_dec_ref(v_inst_2335_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(lean_object* v_cmp_2339_, lean_object* v_inst_2340_, lean_object* v_t_2341_, lean_object* v_k_2342_){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_box(0);
v___x_2344_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2339_, v_k_2342_, v___x_2343_, v_t_2341_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2346_ = l_panic___redArg(v_inst_2340_, v___x_2345_);
return v___x_2346_;
}
else
{
lean_object* v_val_2347_; 
v_val_2347_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_val_2347_);
lean_dec_ref_known(v___x_2344_, 1);
return v_val_2347_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_2348_, lean_object* v_inst_2349_, lean_object* v_t_2350_, lean_object* v_k_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(v_cmp_2348_, v_inst_2349_, v_t_2350_, v_k_2351_);
lean_dec_ref(v_inst_2349_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21(lean_object* v_00_u03b1_2353_, lean_object* v_cmp_2354_, lean_object* v_00_u03b2_2355_, lean_object* v_inst_2356_, lean_object* v_inst_2357_, lean_object* v_t_2358_, lean_object* v_k_2359_){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_box(0);
v___x_2361_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2354_, v_k_2359_, v___x_2360_, v_t_2358_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2363_ = l_panic___redArg(v_inst_2357_, v___x_2362_);
return v___x_2363_;
}
else
{
lean_object* v_val_2364_; 
v_val_2364_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_val_2364_);
lean_dec_ref_known(v___x_2361_, 1);
return v_val_2364_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2365_, lean_object* v_cmp_2366_, lean_object* v_00_u03b2_2367_, lean_object* v_inst_2368_, lean_object* v_inst_2369_, lean_object* v_t_2370_, lean_object* v_k_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Std_ExtDTreeMap_Const_getEntryLT_x21(v_00_u03b1_2365_, v_cmp_2366_, v_00_u03b2_2367_, v_inst_2368_, v_inst_2369_, v_t_2370_, v_k_2371_);
lean_dec_ref(v_inst_2369_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___redArg(lean_object* v_cmp_2373_, lean_object* v_t_2374_, lean_object* v_k_2375_, lean_object* v_fallback_2376_){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_box(0);
v___x_2378_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2373_, v_k_2375_, v___x_2377_, v_t_2374_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_inc_ref(v_fallback_2376_);
return v_fallback_2376_;
}
else
{
lean_object* v_val_2379_; 
v_val_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_val_2379_);
lean_dec_ref_known(v___x_2378_, 1);
return v_val_2379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2380_, lean_object* v_t_2381_, lean_object* v_k_2382_, lean_object* v_fallback_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Std_ExtDTreeMap_Const_getEntryGED___redArg(v_cmp_2380_, v_t_2381_, v_k_2382_, v_fallback_2383_);
lean_dec_ref(v_fallback_2383_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED(lean_object* v_00_u03b1_2385_, lean_object* v_cmp_2386_, lean_object* v_00_u03b2_2387_, lean_object* v_inst_2388_, lean_object* v_t_2389_, lean_object* v_k_2390_, lean_object* v_fallback_2391_){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = lean_box(0);
v___x_2393_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2386_, v_k_2390_, v___x_2392_, v_t_2389_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_inc_ref(v_fallback_2391_);
return v_fallback_2391_;
}
else
{
lean_object* v_val_2394_; 
v_val_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_val_2394_);
lean_dec_ref_known(v___x_2393_, 1);
return v_val_2394_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2395_, lean_object* v_cmp_2396_, lean_object* v_00_u03b2_2397_, lean_object* v_inst_2398_, lean_object* v_t_2399_, lean_object* v_k_2400_, lean_object* v_fallback_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Std_ExtDTreeMap_Const_getEntryGED(v_00_u03b1_2395_, v_cmp_2396_, v_00_u03b2_2397_, v_inst_2398_, v_t_2399_, v_k_2400_, v_fallback_2401_);
lean_dec_ref(v_fallback_2401_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(lean_object* v_cmp_2403_, lean_object* v_t_2404_, lean_object* v_k_2405_, lean_object* v_fallback_2406_){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_box(0);
v___x_2408_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2403_, v_k_2405_, v___x_2407_, v_t_2404_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_inc_ref(v_fallback_2406_);
return v_fallback_2406_;
}
else
{
lean_object* v_val_2409_; 
v_val_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_val_2409_);
lean_dec_ref_known(v___x_2408_, 1);
return v_val_2409_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2410_, lean_object* v_t_2411_, lean_object* v_k_2412_, lean_object* v_fallback_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(v_cmp_2410_, v_t_2411_, v_k_2412_, v_fallback_2413_);
lean_dec_ref(v_fallback_2413_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD(lean_object* v_00_u03b1_2415_, lean_object* v_cmp_2416_, lean_object* v_00_u03b2_2417_, lean_object* v_inst_2418_, lean_object* v_t_2419_, lean_object* v_k_2420_, lean_object* v_fallback_2421_){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = lean_box(0);
v___x_2423_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2416_, v_k_2420_, v___x_2422_, v_t_2419_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_inc_ref(v_fallback_2421_);
return v_fallback_2421_;
}
else
{
lean_object* v_val_2424_; 
v_val_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_val_2424_);
lean_dec_ref_known(v___x_2423_, 1);
return v_val_2424_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2425_, lean_object* v_cmp_2426_, lean_object* v_00_u03b2_2427_, lean_object* v_inst_2428_, lean_object* v_t_2429_, lean_object* v_k_2430_, lean_object* v_fallback_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Std_ExtDTreeMap_Const_getEntryGTD(v_00_u03b1_2425_, v_cmp_2426_, v_00_u03b2_2427_, v_inst_2428_, v_t_2429_, v_k_2430_, v_fallback_2431_);
lean_dec_ref(v_fallback_2431_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___redArg(lean_object* v_cmp_2433_, lean_object* v_t_2434_, lean_object* v_k_2435_, lean_object* v_fallback_2436_){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_box(0);
v___x_2438_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2433_, v_k_2435_, v___x_2437_, v_t_2434_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_inc_ref(v_fallback_2436_);
return v_fallback_2436_;
}
else
{
lean_object* v_val_2439_; 
v_val_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_val_2439_);
lean_dec_ref_known(v___x_2438_, 1);
return v_val_2439_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2440_, lean_object* v_t_2441_, lean_object* v_k_2442_, lean_object* v_fallback_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Std_ExtDTreeMap_Const_getEntryLED___redArg(v_cmp_2440_, v_t_2441_, v_k_2442_, v_fallback_2443_);
lean_dec_ref(v_fallback_2443_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED(lean_object* v_00_u03b1_2445_, lean_object* v_cmp_2446_, lean_object* v_00_u03b2_2447_, lean_object* v_inst_2448_, lean_object* v_t_2449_, lean_object* v_k_2450_, lean_object* v_fallback_2451_){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_box(0);
v___x_2453_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2446_, v_k_2450_, v___x_2452_, v_t_2449_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_inc_ref(v_fallback_2451_);
return v_fallback_2451_;
}
else
{
lean_object* v_val_2454_; 
v_val_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_val_2454_);
lean_dec_ref_known(v___x_2453_, 1);
return v_val_2454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2455_, lean_object* v_cmp_2456_, lean_object* v_00_u03b2_2457_, lean_object* v_inst_2458_, lean_object* v_t_2459_, lean_object* v_k_2460_, lean_object* v_fallback_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Std_ExtDTreeMap_Const_getEntryLED(v_00_u03b1_2455_, v_cmp_2456_, v_00_u03b2_2457_, v_inst_2458_, v_t_2459_, v_k_2460_, v_fallback_2461_);
lean_dec_ref(v_fallback_2461_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(lean_object* v_cmp_2463_, lean_object* v_t_2464_, lean_object* v_k_2465_, lean_object* v_fallback_2466_){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_box(0);
v___x_2468_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2463_, v_k_2465_, v___x_2467_, v_t_2464_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_inc_ref(v_fallback_2466_);
return v_fallback_2466_;
}
else
{
lean_object* v_val_2469_; 
v_val_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_val_2469_);
lean_dec_ref_known(v___x_2468_, 1);
return v_val_2469_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2470_, lean_object* v_t_2471_, lean_object* v_k_2472_, lean_object* v_fallback_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(v_cmp_2470_, v_t_2471_, v_k_2472_, v_fallback_2473_);
lean_dec_ref(v_fallback_2473_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD(lean_object* v_00_u03b1_2475_, lean_object* v_cmp_2476_, lean_object* v_00_u03b2_2477_, lean_object* v_inst_2478_, lean_object* v_t_2479_, lean_object* v_k_2480_, lean_object* v_fallback_2481_){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = lean_box(0);
v___x_2483_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2476_, v_k_2480_, v___x_2482_, v_t_2479_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_inc_ref(v_fallback_2481_);
return v_fallback_2481_;
}
else
{
lean_object* v_val_2484_; 
v_val_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_val_2484_);
lean_dec_ref_known(v___x_2483_, 1);
return v_val_2484_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2485_, lean_object* v_cmp_2486_, lean_object* v_00_u03b2_2487_, lean_object* v_inst_2488_, lean_object* v_t_2489_, lean_object* v_k_2490_, lean_object* v_fallback_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Std_ExtDTreeMap_Const_getEntryLTD(v_00_u03b1_2485_, v_cmp_2486_, v_00_u03b2_2487_, v_inst_2488_, v_t_2489_, v_k_2490_, v_fallback_2491_);
lean_dec_ref(v_fallback_2491_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter___redArg(lean_object* v_f_2493_, lean_object* v_t_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2493_, v_t_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter(lean_object* v_00_u03b1_2496_, lean_object* v_00_u03b2_2497_, lean_object* v_cmp_2498_, lean_object* v_f_2499_, lean_object* v_t_2500_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2499_, v_t_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter___boxed(lean_object* v_00_u03b1_2502_, lean_object* v_00_u03b2_2503_, lean_object* v_cmp_2504_, lean_object* v_f_2505_, lean_object* v_t_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Std_ExtDTreeMap_filter(v_00_u03b1_2502_, v_00_u03b2_2503_, v_cmp_2504_, v_f_2505_, v_t_2506_);
lean_dec_ref(v_cmp_2504_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap___redArg(lean_object* v_f_2508_, lean_object* v_t_2509_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_2508_, v_t_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap(lean_object* v_00_u03b1_2511_, lean_object* v_00_u03b2_2512_, lean_object* v_00_u03b3_2513_, lean_object* v_cmp_2514_, lean_object* v_f_2515_, lean_object* v_t_2516_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_2515_, v_t_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap___boxed(lean_object* v_00_u03b1_2518_, lean_object* v_00_u03b2_2519_, lean_object* v_00_u03b3_2520_, lean_object* v_cmp_2521_, lean_object* v_f_2522_, lean_object* v_t_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Std_ExtDTreeMap_filterMap(v_00_u03b1_2518_, v_00_u03b2_2519_, v_00_u03b3_2520_, v_cmp_2521_, v_f_2522_, v_t_2523_);
lean_dec_ref(v_cmp_2521_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map___redArg(lean_object* v_f_2525_, lean_object* v_t_2526_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_2525_, v_t_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map(lean_object* v_00_u03b1_2528_, lean_object* v_00_u03b2_2529_, lean_object* v_00_u03b3_2530_, lean_object* v_cmp_2531_, lean_object* v_f_2532_, lean_object* v_t_2533_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_2532_, v_t_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map___boxed(lean_object* v_00_u03b1_2535_, lean_object* v_00_u03b2_2536_, lean_object* v_00_u03b3_2537_, lean_object* v_cmp_2538_, lean_object* v_f_2539_, lean_object* v_t_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Std_ExtDTreeMap_map(v_00_u03b1_2535_, v_00_u03b2_2536_, v_00_u03b3_2537_, v_cmp_2538_, v_f_2539_, v_t_2540_);
lean_dec_ref(v_cmp_2538_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM___redArg(lean_object* v_inst_2542_, lean_object* v_f_2543_, lean_object* v_init_2544_, lean_object* v_t_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2542_, v_f_2543_, v_init_2544_, v_t_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM(lean_object* v_00_u03b1_2547_, lean_object* v_00_u03b2_2548_, lean_object* v_cmp_2549_, lean_object* v_00_u03b4_2550_, lean_object* v_m_2551_, lean_object* v_inst_2552_, lean_object* v_inst_2553_, lean_object* v_inst_2554_, lean_object* v_f_2555_, lean_object* v_init_2556_, lean_object* v_t_2557_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2552_, v_f_2555_, v_init_2556_, v_t_2557_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM___boxed(lean_object* v_00_u03b1_2559_, lean_object* v_00_u03b2_2560_, lean_object* v_cmp_2561_, lean_object* v_00_u03b4_2562_, lean_object* v_m_2563_, lean_object* v_inst_2564_, lean_object* v_inst_2565_, lean_object* v_inst_2566_, lean_object* v_f_2567_, lean_object* v_init_2568_, lean_object* v_t_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Std_ExtDTreeMap_foldlM(v_00_u03b1_2559_, v_00_u03b2_2560_, v_cmp_2561_, v_00_u03b4_2562_, v_m_2563_, v_inst_2564_, v_inst_2565_, v_inst_2566_, v_f_2567_, v_init_2568_, v_t_2569_);
lean_dec_ref(v_cmp_2561_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl___redArg(lean_object* v_f_2571_, lean_object* v_init_2572_, lean_object* v_t_2573_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2571_, v_init_2572_, v_t_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl(lean_object* v_00_u03b1_2575_, lean_object* v_00_u03b2_2576_, lean_object* v_cmp_2577_, lean_object* v_00_u03b4_2578_, lean_object* v_inst_2579_, lean_object* v_f_2580_, lean_object* v_init_2581_, lean_object* v_t_2582_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2580_, v_init_2581_, v_t_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl___boxed(lean_object* v_00_u03b1_2584_, lean_object* v_00_u03b2_2585_, lean_object* v_cmp_2586_, lean_object* v_00_u03b4_2587_, lean_object* v_inst_2588_, lean_object* v_f_2589_, lean_object* v_init_2590_, lean_object* v_t_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Std_ExtDTreeMap_foldl(v_00_u03b1_2584_, v_00_u03b2_2585_, v_cmp_2586_, v_00_u03b4_2587_, v_inst_2588_, v_f_2589_, v_init_2590_, v_t_2591_);
lean_dec_ref(v_cmp_2586_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM___redArg(lean_object* v_inst_2593_, lean_object* v_f_2594_, lean_object* v_init_2595_, lean_object* v_t_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2593_, v_f_2594_, v_init_2595_, v_t_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM(lean_object* v_00_u03b1_2598_, lean_object* v_00_u03b2_2599_, lean_object* v_cmp_2600_, lean_object* v_00_u03b4_2601_, lean_object* v_m_2602_, lean_object* v_inst_2603_, lean_object* v_inst_2604_, lean_object* v_inst_2605_, lean_object* v_f_2606_, lean_object* v_init_2607_, lean_object* v_t_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2603_, v_f_2606_, v_init_2607_, v_t_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM___boxed(lean_object* v_00_u03b1_2610_, lean_object* v_00_u03b2_2611_, lean_object* v_cmp_2612_, lean_object* v_00_u03b4_2613_, lean_object* v_m_2614_, lean_object* v_inst_2615_, lean_object* v_inst_2616_, lean_object* v_inst_2617_, lean_object* v_f_2618_, lean_object* v_init_2619_, lean_object* v_t_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Std_ExtDTreeMap_foldrM(v_00_u03b1_2610_, v_00_u03b2_2611_, v_cmp_2612_, v_00_u03b4_2613_, v_m_2614_, v_inst_2615_, v_inst_2616_, v_inst_2617_, v_f_2618_, v_init_2619_, v_t_2620_);
lean_dec_ref(v_cmp_2612_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___redArg___lam__0(lean_object* v_f_2622_, lean_object* v_x1_2623_, lean_object* v_x2_2624_, lean_object* v_x3_2625_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_apply_3(v_f_2622_, v_x1_2623_, v_x2_2624_, v_x3_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___redArg(lean_object* v_f_2646_, lean_object* v_init_2647_, lean_object* v_t_2648_){
_start:
{
lean_object* v___f_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___f_2649_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2649_, 0, v_f_2646_);
v___x_2650_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2651_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2650_, v___f_2649_, v_init_2647_, v_t_2648_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr(lean_object* v_00_u03b1_2652_, lean_object* v_00_u03b2_2653_, lean_object* v_cmp_2654_, lean_object* v_00_u03b4_2655_, lean_object* v_inst_2656_, lean_object* v_f_2657_, lean_object* v_init_2658_, lean_object* v_t_2659_){
_start:
{
lean_object* v___f_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___f_2660_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2660_, 0, v_f_2657_);
v___x_2661_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2662_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2661_, v___f_2660_, v_init_2658_, v_t_2659_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___boxed(lean_object* v_00_u03b1_2663_, lean_object* v_00_u03b2_2664_, lean_object* v_cmp_2665_, lean_object* v_00_u03b4_2666_, lean_object* v_inst_2667_, lean_object* v_f_2668_, lean_object* v_init_2669_, lean_object* v_t_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Std_ExtDTreeMap_foldr(v_00_u03b1_2663_, v_00_u03b2_2664_, v_cmp_2665_, v_00_u03b4_2666_, v_inst_2667_, v_f_2668_, v_init_2669_, v_t_2670_);
lean_dec_ref(v_cmp_2665_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition___redArg___lam__0(lean_object* v_f_2672_, lean_object* v_cmp_2673_, lean_object* v_x_2674_, lean_object* v_a_2675_, lean_object* v_b_2676_){
_start:
{
lean_object* v_fst_2677_; lean_object* v_snd_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2692_; 
v_fst_2677_ = lean_ctor_get(v_x_2674_, 0);
v_snd_2678_ = lean_ctor_get(v_x_2674_, 1);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_x_2674_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2680_ = v_x_2674_;
v_isShared_2681_ = v_isSharedCheck_2692_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_snd_2678_);
lean_inc(v_fst_2677_);
lean_dec(v_x_2674_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2692_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; uint8_t v___x_2683_; 
lean_inc(v_b_2676_);
lean_inc(v_a_2675_);
v___x_2682_ = lean_apply_2(v_f_2672_, v_a_2675_, v_b_2676_);
v___x_2683_ = lean_unbox(v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2686_; 
v___x_2684_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2673_, v_a_2675_, v_b_2676_, v_snd_2678_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 1, v___x_2684_);
v___x_2686_ = v___x_2680_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_fst_2677_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2688_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2673_, v_a_2675_, v_b_2676_, v_fst_2677_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2688_);
v___x_2690_ = v___x_2680_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_snd_2678_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition___redArg(lean_object* v_cmp_2695_, lean_object* v_f_2696_, lean_object* v_t_2697_){
_start:
{
lean_object* v___f_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___f_2698_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2698_, 0, v_f_2696_);
lean_closure_set(v___f_2698_, 1, v_cmp_2695_);
v___x_2699_ = ((lean_object*)(l_Std_ExtDTreeMap_partition___redArg___closed__0));
v___x_2700_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2698_, v___x_2699_, v_t_2697_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition(lean_object* v_00_u03b1_2701_, lean_object* v_00_u03b2_2702_, lean_object* v_cmp_2703_, lean_object* v_inst_2704_, lean_object* v_f_2705_, lean_object* v_t_2706_){
_start:
{
lean_object* v___f_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___f_2707_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2707_, 0, v_f_2705_);
lean_closure_set(v___f_2707_, 1, v_cmp_2703_);
v___x_2708_ = ((lean_object*)(l_Std_ExtDTreeMap_partition___redArg___closed__0));
v___x_2709_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2707_, v___x_2708_, v_t_2706_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___redArg___lam__0(lean_object* v_f_2710_, lean_object* v_x_2711_, lean_object* v_k_2712_, lean_object* v_v_2713_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_apply_2(v_f_2710_, v_k_2712_, v_v_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___redArg(lean_object* v_inst_2715_, lean_object* v_f_2716_, lean_object* v_t_2717_){
_start:
{
lean_object* v___f_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___f_2718_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2718_, 0, v_f_2716_);
v___x_2719_ = lean_box(0);
v___x_2720_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2715_, v___f_2718_, v___x_2719_, v_t_2717_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM(lean_object* v_00_u03b1_2721_, lean_object* v_00_u03b2_2722_, lean_object* v_cmp_2723_, lean_object* v_m_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v_f_2728_, lean_object* v_t_2729_){
_start:
{
lean_object* v___f_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___f_2730_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2730_, 0, v_f_2728_);
v___x_2731_ = lean_box(0);
v___x_2732_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2725_, v___f_2730_, v___x_2731_, v_t_2729_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___boxed(lean_object* v_00_u03b1_2733_, lean_object* v_00_u03b2_2734_, lean_object* v_cmp_2735_, lean_object* v_m_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v_inst_2739_, lean_object* v_f_2740_, lean_object* v_t_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Std_ExtDTreeMap_forM(v_00_u03b1_2733_, v_00_u03b2_2734_, v_cmp_2735_, v_m_2736_, v_inst_2737_, v_inst_2738_, v_inst_2739_, v_f_2740_, v_t_2741_);
lean_dec_ref(v_cmp_2735_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___redArg___lam__0(lean_object* v_toPure_2743_, lean_object* v_____do__lift_2744_){
_start:
{
lean_object* v_a_2745_; lean_object* v___x_2746_; 
v_a_2745_ = lean_ctor_get(v_____do__lift_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref(v_____do__lift_2744_);
v___x_2746_ = lean_apply_2(v_toPure_2743_, lean_box(0), v_a_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___redArg(lean_object* v_inst_2747_, lean_object* v_f_2748_, lean_object* v_init_2749_, lean_object* v_t_2750_){
_start:
{
lean_object* v_toApplicative_2751_; lean_object* v_toBind_2752_; lean_object* v_toPure_2753_; lean_object* v___x_2754_; lean_object* v___f_2755_; lean_object* v___x_2756_; 
v_toApplicative_2751_ = lean_ctor_get(v_inst_2747_, 0);
v_toBind_2752_ = lean_ctor_get(v_inst_2747_, 1);
lean_inc(v_toBind_2752_);
v_toPure_2753_ = lean_ctor_get(v_toApplicative_2751_, 1);
lean_inc(v_toPure_2753_);
v___x_2754_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2747_, v_f_2748_, v_init_2749_, v_t_2750_);
v___f_2755_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2755_, 0, v_toPure_2753_);
v___x_2756_ = lean_apply_4(v_toBind_2752_, lean_box(0), lean_box(0), v___x_2754_, v___f_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn(lean_object* v_00_u03b1_2757_, lean_object* v_00_u03b2_2758_, lean_object* v_cmp_2759_, lean_object* v_00_u03b4_2760_, lean_object* v_m_2761_, lean_object* v_inst_2762_, lean_object* v_inst_2763_, lean_object* v_inst_2764_, lean_object* v_f_2765_, lean_object* v_init_2766_, lean_object* v_t_2767_){
_start:
{
lean_object* v_toApplicative_2768_; lean_object* v_toBind_2769_; lean_object* v_toPure_2770_; lean_object* v___x_2771_; lean_object* v___f_2772_; lean_object* v___x_2773_; 
v_toApplicative_2768_ = lean_ctor_get(v_inst_2762_, 0);
v_toBind_2769_ = lean_ctor_get(v_inst_2762_, 1);
lean_inc(v_toBind_2769_);
v_toPure_2770_ = lean_ctor_get(v_toApplicative_2768_, 1);
lean_inc(v_toPure_2770_);
v___x_2771_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2762_, v_f_2765_, v_init_2766_, v_t_2767_);
v___f_2772_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2772_, 0, v_toPure_2770_);
v___x_2773_ = lean_apply_4(v_toBind_2769_, lean_box(0), lean_box(0), v___x_2771_, v___f_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___boxed(lean_object* v_00_u03b1_2774_, lean_object* v_00_u03b2_2775_, lean_object* v_cmp_2776_, lean_object* v_00_u03b4_2777_, lean_object* v_m_2778_, lean_object* v_inst_2779_, lean_object* v_inst_2780_, lean_object* v_inst_2781_, lean_object* v_f_2782_, lean_object* v_init_2783_, lean_object* v_t_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Std_ExtDTreeMap_forIn(v_00_u03b1_2774_, v_00_u03b2_2775_, v_cmp_2776_, v_00_u03b4_2777_, v_m_2778_, v_inst_2779_, v_inst_2780_, v_inst_2781_, v_f_2782_, v_init_2783_, v_t_2784_);
lean_dec_ref(v_cmp_2776_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2786_, lean_object* v_x_2787_, lean_object* v_k_2788_, lean_object* v_v_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v_k_2788_);
lean_ctor_set(v___x_2790_, 1, v_v_2789_);
v___x_2791_ = lean_apply_1(v_f_2786_, v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_2792_, lean_object* v_t_2793_, lean_object* v_f_2794_){
_start:
{
lean_object* v___f_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___f_2795_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2795_, 0, v_f_2794_);
v___x_2796_ = lean_box(0);
v___x_2797_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2792_, v___f_2795_, v___x_2796_, v_t_2793_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2798_){
_start:
{
lean_object* v___f_2799_; 
v___f_2799_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2799_, 0, v_inst_2798_);
return v___f_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2800_, lean_object* v_00_u03b2_2801_, lean_object* v_cmp_2802_, lean_object* v_m_2803_, lean_object* v_inst_2804_, lean_object* v_inst_2805_, lean_object* v_inst_2806_){
_start:
{
lean_object* v___f_2807_; 
v___f_2807_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2807_, 0, v_inst_2805_);
return v___f_2807_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2808_, lean_object* v_00_u03b2_2809_, lean_object* v_cmp_2810_, lean_object* v_m_2811_, lean_object* v_inst_2812_, lean_object* v_inst_2813_, lean_object* v_inst_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(v_00_u03b1_2808_, v_00_u03b2_2809_, v_cmp_2810_, v_m_2811_, v_inst_2812_, v_inst_2813_, v_inst_2814_);
lean_dec_ref(v_cmp_2810_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2816_, lean_object* v_a_2817_, lean_object* v_b_2818_, lean_object* v_acc_2819_){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2820_, 0, v_a_2817_);
lean_ctor_set(v___x_2820_, 1, v_b_2818_);
v___x_2821_ = lean_apply_2(v_f_2816_, v___x_2820_, v_acc_2819_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_2822_, lean_object* v_00_u03b2_2823_, lean_object* v_m_2824_, lean_object* v_init_2825_, lean_object* v_f_2826_){
_start:
{
lean_object* v_toApplicative_2827_; lean_object* v_toBind_2828_; lean_object* v_toPure_2829_; lean_object* v___f_2830_; lean_object* v___x_2831_; lean_object* v___f_2832_; lean_object* v___x_2833_; 
v_toApplicative_2827_ = lean_ctor_get(v_inst_2822_, 0);
v_toBind_2828_ = lean_ctor_get(v_inst_2822_, 1);
lean_inc(v_toBind_2828_);
v_toPure_2829_ = lean_ctor_get(v_toApplicative_2827_, 1);
lean_inc(v_toPure_2829_);
v___f_2830_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2830_, 0, v_f_2826_);
v___x_2831_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2822_, v___f_2830_, v_init_2825_, v_m_2824_);
v___f_2832_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2832_, 0, v_toPure_2829_);
v___x_2833_ = lean_apply_4(v_toBind_2828_, lean_box(0), lean_box(0), v___x_2831_, v___f_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2834_){
_start:
{
lean_object* v___f_2835_; 
v___f_2835_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2835_, 0, v_inst_2834_);
return v___f_2835_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2836_, lean_object* v_00_u03b2_2837_, lean_object* v_cmp_2838_, lean_object* v_m_2839_, lean_object* v_inst_2840_, lean_object* v_inst_2841_, lean_object* v_inst_2842_){
_start:
{
lean_object* v___f_2843_; 
v___f_2843_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2843_, 0, v_inst_2841_);
return v___f_2843_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2844_, lean_object* v_00_u03b2_2845_, lean_object* v_cmp_2846_, lean_object* v_m_2847_, lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_inst_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(v_00_u03b1_2844_, v_00_u03b2_2845_, v_cmp_2846_, v_m_2847_, v_inst_2848_, v_inst_2849_, v_inst_2850_);
lean_dec_ref(v_cmp_2846_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2852_, lean_object* v_x_2853_, lean_object* v_k_2854_, lean_object* v_v_2855_){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v_k_2854_);
lean_ctor_set(v___x_2856_, 1, v_v_2855_);
v___x_2857_ = lean_apply_1(v_f_2852_, v___x_2856_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___redArg(lean_object* v_inst_2858_, lean_object* v_f_2859_, lean_object* v_t_2860_){
_start:
{
lean_object* v___f_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___f_2861_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2861_, 0, v_f_2859_);
v___x_2862_ = lean_box(0);
v___x_2863_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2858_, v___f_2861_, v___x_2862_, v_t_2860_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried(lean_object* v_00_u03b1_2864_, lean_object* v_cmp_2865_, lean_object* v_m_2866_, lean_object* v_inst_2867_, lean_object* v_inst_2868_, lean_object* v_00_u03b2_2869_, lean_object* v_inst_2870_, lean_object* v_f_2871_, lean_object* v_t_2872_){
_start:
{
lean_object* v___f_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___f_2873_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2873_, 0, v_f_2871_);
v___x_2874_ = lean_box(0);
v___x_2875_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2867_, v___f_2873_, v___x_2874_, v_t_2872_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2876_, lean_object* v_cmp_2877_, lean_object* v_m_2878_, lean_object* v_inst_2879_, lean_object* v_inst_2880_, lean_object* v_00_u03b2_2881_, lean_object* v_inst_2882_, lean_object* v_f_2883_, lean_object* v_t_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Std_ExtDTreeMap_Const_forMUncurried(v_00_u03b1_2876_, v_cmp_2877_, v_m_2878_, v_inst_2879_, v_inst_2880_, v_00_u03b2_2881_, v_inst_2882_, v_f_2883_, v_t_2884_);
lean_dec_ref(v_cmp_2877_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2886_, lean_object* v_a_2887_, lean_object* v_b_2888_, lean_object* v_acc_2889_){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v_a_2887_);
lean_ctor_set(v___x_2890_, 1, v_b_2888_);
v___x_2891_ = lean_apply_2(v_f_2886_, v___x_2890_, v_acc_2889_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___redArg(lean_object* v_inst_2892_, lean_object* v_f_2893_, lean_object* v_init_2894_, lean_object* v_t_2895_){
_start:
{
lean_object* v_toApplicative_2896_; lean_object* v_toBind_2897_; lean_object* v_toPure_2898_; lean_object* v___f_2899_; lean_object* v___x_2900_; lean_object* v___f_2901_; lean_object* v___x_2902_; 
v_toApplicative_2896_ = lean_ctor_get(v_inst_2892_, 0);
v_toBind_2897_ = lean_ctor_get(v_inst_2892_, 1);
lean_inc(v_toBind_2897_);
v_toPure_2898_ = lean_ctor_get(v_toApplicative_2896_, 1);
lean_inc(v_toPure_2898_);
v___f_2899_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2899_, 0, v_f_2893_);
v___x_2900_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2892_, v___f_2899_, v_init_2894_, v_t_2895_);
v___f_2901_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2901_, 0, v_toPure_2898_);
v___x_2902_ = lean_apply_4(v_toBind_2897_, lean_box(0), lean_box(0), v___x_2900_, v___f_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried(lean_object* v_00_u03b1_2903_, lean_object* v_cmp_2904_, lean_object* v_00_u03b4_2905_, lean_object* v_m_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_00_u03b2_2909_, lean_object* v_inst_2910_, lean_object* v_f_2911_, lean_object* v_init_2912_, lean_object* v_t_2913_){
_start:
{
lean_object* v_toApplicative_2914_; lean_object* v_toBind_2915_; lean_object* v_toPure_2916_; lean_object* v___f_2917_; lean_object* v___x_2918_; lean_object* v___f_2919_; lean_object* v___x_2920_; 
v_toApplicative_2914_ = lean_ctor_get(v_inst_2907_, 0);
v_toBind_2915_ = lean_ctor_get(v_inst_2907_, 1);
lean_inc(v_toBind_2915_);
v_toPure_2916_ = lean_ctor_get(v_toApplicative_2914_, 1);
lean_inc(v_toPure_2916_);
v___f_2917_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2917_, 0, v_f_2911_);
v___x_2918_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2907_, v___f_2917_, v_init_2912_, v_t_2913_);
v___f_2919_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2919_, 0, v_toPure_2916_);
v___x_2920_ = lean_apply_4(v_toBind_2915_, lean_box(0), lean_box(0), v___x_2918_, v___f_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2921_, lean_object* v_cmp_2922_, lean_object* v_00_u03b4_2923_, lean_object* v_m_2924_, lean_object* v_inst_2925_, lean_object* v_inst_2926_, lean_object* v_00_u03b2_2927_, lean_object* v_inst_2928_, lean_object* v_f_2929_, lean_object* v_init_2930_, lean_object* v_t_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Std_ExtDTreeMap_Const_forInUncurried(v_00_u03b1_2921_, v_cmp_2922_, v_00_u03b4_2923_, v_m_2924_, v_inst_2925_, v_inst_2926_, v_00_u03b2_2927_, v_inst_2928_, v_f_2929_, v_init_2930_, v_t_2931_);
lean_dec_ref(v_cmp_2922_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___lam__0(lean_object* v_p_2933_, lean_object* v___x_2934_, lean_object* v___x_2935_, lean_object* v_a_2936_, lean_object* v_b_2937_, lean_object* v_acc_2938_){
_start:
{
lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2939_ = lean_apply_2(v_p_2933_, v_a_2936_, v_b_2937_);
v___x_2940_ = lean_unbox(v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; 
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2934_);
return v___x_2941_;
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
lean_dec_ref(v___x_2934_);
v___x_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2939_);
v___x_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
lean_ctor_set(v___x_2943_, 1, v___x_2935_);
v___x_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
return v___x_2944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2945_, lean_object* v___x_2946_, lean_object* v___x_2947_, lean_object* v_a_2948_, lean_object* v_b_2949_, lean_object* v_acc_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Std_ExtDTreeMap_any___redArg___lam__0(v_p_2945_, v___x_2946_, v___x_2947_, v_a_2948_, v_b_2949_, v_acc_2950_);
lean_dec_ref(v_acc_2950_);
return v_res_2951_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_any___redArg(lean_object* v_t_2955_, lean_object* v_p_2956_){
_start:
{
lean_object* v___y_2958_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___f_2966_; lean_object* v___x_2967_; lean_object* v_a_2968_; 
v___x_2963_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2964_ = lean_box(0);
v___x_2965_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_2966_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2966_, 0, v_p_2956_);
lean_closure_set(v___f_2966_, 1, v___x_2965_);
lean_closure_set(v___f_2966_, 2, v___x_2964_);
v___x_2967_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2963_, v___f_2966_, v___x_2965_, v_t_2955_);
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___y_2958_ = v_a_2968_;
goto v___jp_2957_;
v___jp_2957_:
{
lean_object* v_fst_2959_; 
v_fst_2959_ = lean_ctor_get(v___y_2958_, 0);
lean_inc(v_fst_2959_);
lean_dec_ref(v___y_2958_);
if (lean_obj_tag(v_fst_2959_) == 0)
{
uint8_t v___x_2960_; 
v___x_2960_ = 0;
return v___x_2960_;
}
else
{
lean_object* v_val_2961_; uint8_t v___x_2962_; 
v_val_2961_ = lean_ctor_get(v_fst_2959_, 0);
lean_inc(v_val_2961_);
lean_dec_ref_known(v_fst_2959_, 1);
v___x_2962_ = lean_unbox(v_val_2961_);
lean_dec(v_val_2961_);
return v___x_2962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___boxed(lean_object* v_t_2969_, lean_object* v_p_2970_){
_start:
{
uint8_t v_res_2971_; lean_object* v_r_2972_; 
v_res_2971_ = l_Std_ExtDTreeMap_any___redArg(v_t_2969_, v_p_2970_);
v_r_2972_ = lean_box(v_res_2971_);
return v_r_2972_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_any(lean_object* v_00_u03b1_2973_, lean_object* v_00_u03b2_2974_, lean_object* v_cmp_2975_, lean_object* v_inst_2976_, lean_object* v_t_2977_, lean_object* v_p_2978_){
_start:
{
lean_object* v___y_2980_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___f_2988_; lean_object* v___x_2989_; lean_object* v_a_2990_; 
v___x_2985_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2986_ = lean_box(0);
v___x_2987_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_2988_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2988_, 0, v_p_2978_);
lean_closure_set(v___f_2988_, 1, v___x_2987_);
lean_closure_set(v___f_2988_, 2, v___x_2986_);
v___x_2989_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2985_, v___f_2988_, v___x_2987_, v_t_2977_);
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___y_2980_ = v_a_2990_;
goto v___jp_2979_;
v___jp_2979_:
{
lean_object* v_fst_2981_; 
v_fst_2981_ = lean_ctor_get(v___y_2980_, 0);
lean_inc(v_fst_2981_);
lean_dec_ref(v___y_2980_);
if (lean_obj_tag(v_fst_2981_) == 0)
{
uint8_t v___x_2982_; 
v___x_2982_ = 0;
return v___x_2982_;
}
else
{
lean_object* v_val_2983_; uint8_t v___x_2984_; 
v_val_2983_ = lean_ctor_get(v_fst_2981_, 0);
lean_inc(v_val_2983_);
lean_dec_ref_known(v_fst_2981_, 1);
v___x_2984_ = lean_unbox(v_val_2983_);
lean_dec(v_val_2983_);
return v___x_2984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___boxed(lean_object* v_00_u03b1_2991_, lean_object* v_00_u03b2_2992_, lean_object* v_cmp_2993_, lean_object* v_inst_2994_, lean_object* v_t_2995_, lean_object* v_p_2996_){
_start:
{
uint8_t v_res_2997_; lean_object* v_r_2998_; 
v_res_2997_ = l_Std_ExtDTreeMap_any(v_00_u03b1_2991_, v_00_u03b2_2992_, v_cmp_2993_, v_inst_2994_, v_t_2995_, v_p_2996_);
lean_dec_ref(v_cmp_2993_);
v_r_2998_ = lean_box(v_res_2997_);
return v_r_2998_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___lam__0(lean_object* v_p_2999_, lean_object* v___x_3000_, lean_object* v___x_3001_, lean_object* v_a_3002_, lean_object* v_b_3003_, lean_object* v_acc_3004_){
_start:
{
lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = lean_apply_2(v_p_2999_, v_a_3002_, v_b_3003_);
v___x_3006_ = lean_unbox(v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec_ref(v___x_3001_);
v___x_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v___x_3000_);
v___x_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
return v___x_3009_;
}
else
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3001_);
return v___x_3010_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_3011_, lean_object* v___x_3012_, lean_object* v___x_3013_, lean_object* v_a_3014_, lean_object* v_b_3015_, lean_object* v_acc_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Std_ExtDTreeMap_all___redArg___lam__0(v_p_3011_, v___x_3012_, v___x_3013_, v_a_3014_, v_b_3015_, v_acc_3016_);
lean_dec_ref(v_acc_3016_);
return v_res_3017_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_all___redArg(lean_object* v_t_3018_, lean_object* v_p_3019_){
_start:
{
lean_object* v___y_3021_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___f_3029_; lean_object* v___x_3030_; lean_object* v_a_3031_; 
v___x_3026_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3027_ = lean_box(0);
v___x_3028_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_3029_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3029_, 0, v_p_3019_);
lean_closure_set(v___f_3029_, 1, v___x_3027_);
lean_closure_set(v___f_3029_, 2, v___x_3028_);
v___x_3030_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_3026_, v___f_3029_, v___x_3028_, v_t_3018_);
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___y_3021_ = v_a_3031_;
goto v___jp_3020_;
v___jp_3020_:
{
lean_object* v_fst_3022_; 
v_fst_3022_ = lean_ctor_get(v___y_3021_, 0);
lean_inc(v_fst_3022_);
lean_dec_ref(v___y_3021_);
if (lean_obj_tag(v_fst_3022_) == 0)
{
uint8_t v___x_3023_; 
v___x_3023_ = 1;
return v___x_3023_;
}
else
{
lean_object* v_val_3024_; uint8_t v___x_3025_; 
v_val_3024_ = lean_ctor_get(v_fst_3022_, 0);
lean_inc(v_val_3024_);
lean_dec_ref_known(v_fst_3022_, 1);
v___x_3025_ = lean_unbox(v_val_3024_);
lean_dec(v_val_3024_);
return v___x_3025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___boxed(lean_object* v_t_3032_, lean_object* v_p_3033_){
_start:
{
uint8_t v_res_3034_; lean_object* v_r_3035_; 
v_res_3034_ = l_Std_ExtDTreeMap_all___redArg(v_t_3032_, v_p_3033_);
v_r_3035_ = lean_box(v_res_3034_);
return v_r_3035_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_all(lean_object* v_00_u03b1_3036_, lean_object* v_00_u03b2_3037_, lean_object* v_cmp_3038_, lean_object* v_inst_3039_, lean_object* v_t_3040_, lean_object* v_p_3041_){
_start:
{
lean_object* v___y_3043_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___f_3051_; lean_object* v___x_3052_; lean_object* v_a_3053_; 
v___x_3048_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3049_ = lean_box(0);
v___x_3050_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_3051_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3051_, 0, v_p_3041_);
lean_closure_set(v___f_3051_, 1, v___x_3049_);
lean_closure_set(v___f_3051_, 2, v___x_3050_);
v___x_3052_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_3048_, v___f_3051_, v___x_3050_, v_t_3040_);
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec(v___x_3052_);
v___y_3043_ = v_a_3053_;
goto v___jp_3042_;
v___jp_3042_:
{
lean_object* v_fst_3044_; 
v_fst_3044_ = lean_ctor_get(v___y_3043_, 0);
lean_inc(v_fst_3044_);
lean_dec_ref(v___y_3043_);
if (lean_obj_tag(v_fst_3044_) == 0)
{
uint8_t v___x_3045_; 
v___x_3045_ = 1;
return v___x_3045_;
}
else
{
lean_object* v_val_3046_; uint8_t v___x_3047_; 
v_val_3046_ = lean_ctor_get(v_fst_3044_, 0);
lean_inc(v_val_3046_);
lean_dec_ref_known(v_fst_3044_, 1);
v___x_3047_ = lean_unbox(v_val_3046_);
lean_dec(v_val_3046_);
return v___x_3047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___boxed(lean_object* v_00_u03b1_3054_, lean_object* v_00_u03b2_3055_, lean_object* v_cmp_3056_, lean_object* v_inst_3057_, lean_object* v_t_3058_, lean_object* v_p_3059_){
_start:
{
uint8_t v_res_3060_; lean_object* v_r_3061_; 
v_res_3060_ = l_Std_ExtDTreeMap_all(v_00_u03b1_3054_, v_00_u03b2_3055_, v_cmp_3056_, v_inst_3057_, v_t_3058_, v_p_3059_);
lean_dec_ref(v_cmp_3056_);
v_r_3061_ = lean_box(v_res_3060_);
return v_r_3061_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg___lam__0(lean_object* v_x1_3062_, lean_object* v_x2_3063_, lean_object* v_x3_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_x1_3062_);
lean_ctor_set(v___x_3065_, 1, v_x3_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_3066_, lean_object* v_x2_3067_, lean_object* v_x3_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_Std_ExtDTreeMap_keys___redArg___lam__0(v_x1_3066_, v_x2_3067_, v_x3_3068_);
lean_dec(v_x2_3067_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg(lean_object* v_t_3071_){
_start:
{
lean_object* v___f_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___f_3072_ = ((lean_object*)(l_Std_ExtDTreeMap_keys___redArg___closed__0));
v___x_3073_ = lean_box(0);
v___x_3074_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3075_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3074_, v___f_3072_, v___x_3073_, v_t_3071_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys(lean_object* v_00_u03b1_3076_, lean_object* v_00_u03b2_3077_, lean_object* v_cmp_3078_, lean_object* v_inst_3079_, lean_object* v_t_3080_){
_start:
{
lean_object* v___f_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___f_3081_ = ((lean_object*)(l_Std_ExtDTreeMap_keys___redArg___closed__0));
v___x_3082_ = lean_box(0);
v___x_3083_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3084_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3083_, v___f_3081_, v___x_3082_, v_t_3080_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___boxed(lean_object* v_00_u03b1_3085_, lean_object* v_00_u03b2_3086_, lean_object* v_cmp_3087_, lean_object* v_inst_3088_, lean_object* v_t_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Std_ExtDTreeMap_keys(v_00_u03b1_3085_, v_00_u03b2_3086_, v_cmp_3087_, v_inst_3088_, v_t_3089_);
lean_dec_ref(v_cmp_3087_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg___lam__0(lean_object* v_l_3091_, lean_object* v_k_3092_, lean_object* v_x_3093_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = lean_array_push(v_l_3091_, v_k_3092_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_3095_, lean_object* v_k_3096_, lean_object* v_x_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Std_ExtDTreeMap_keysArray___redArg___lam__0(v_l_3095_, v_k_3096_, v_x_3097_);
lean_dec(v_x_3097_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg(lean_object* v_t_3100_){
_start:
{
lean_object* v___f_3101_; lean_object* v___y_3103_; 
v___f_3101_ = ((lean_object*)(l_Std_ExtDTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_3100_) == 0)
{
lean_object* v_size_3106_; 
v_size_3106_ = lean_ctor_get(v_t_3100_, 0);
lean_inc(v_size_3106_);
v___y_3103_ = v_size_3106_;
goto v___jp_3102_;
}
else
{
lean_object* v___x_3107_; 
v___x_3107_ = lean_unsigned_to_nat(0u);
v___y_3103_ = v___x_3107_;
goto v___jp_3102_;
}
v___jp_3102_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_mk_empty_array_with_capacity(v___y_3103_);
lean_dec(v___y_3103_);
v___x_3105_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3101_, v___x_3104_, v_t_3100_);
return v___x_3105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray(lean_object* v_00_u03b1_3108_, lean_object* v_00_u03b2_3109_, lean_object* v_cmp_3110_, lean_object* v_inst_3111_, lean_object* v_t_3112_){
_start:
{
lean_object* v___f_3113_; lean_object* v___y_3115_; 
v___f_3113_ = ((lean_object*)(l_Std_ExtDTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_3112_) == 0)
{
lean_object* v_size_3118_; 
v_size_3118_ = lean_ctor_get(v_t_3112_, 0);
lean_inc(v_size_3118_);
v___y_3115_ = v_size_3118_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_unsigned_to_nat(0u);
v___y_3115_ = v___x_3119_;
goto v___jp_3114_;
}
v___jp_3114_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_mk_empty_array_with_capacity(v___y_3115_);
lean_dec(v___y_3115_);
v___x_3117_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3113_, v___x_3116_, v_t_3112_);
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___boxed(lean_object* v_00_u03b1_3120_, lean_object* v_00_u03b2_3121_, lean_object* v_cmp_3122_, lean_object* v_inst_3123_, lean_object* v_t_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Std_ExtDTreeMap_keysArray(v_00_u03b1_3120_, v_00_u03b2_3121_, v_cmp_3122_, v_inst_3123_, v_t_3124_);
lean_dec_ref(v_cmp_3122_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg___lam__0(lean_object* v_x1_3126_, lean_object* v_x2_3127_, lean_object* v_x3_3128_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3129_, 0, v_x2_3127_);
lean_ctor_set(v___x_3129_, 1, v_x3_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_3130_, lean_object* v_x2_3131_, lean_object* v_x3_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Std_ExtDTreeMap_values___redArg___lam__0(v_x1_3130_, v_x2_3131_, v_x3_3132_);
lean_dec(v_x1_3130_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg(lean_object* v_t_3135_){
_start:
{
lean_object* v___f_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___f_3136_ = ((lean_object*)(l_Std_ExtDTreeMap_values___redArg___closed__0));
v___x_3137_ = lean_box(0);
v___x_3138_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3139_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3138_, v___f_3136_, v___x_3137_, v_t_3135_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values(lean_object* v_00_u03b1_3140_, lean_object* v_cmp_3141_, lean_object* v_inst_3142_, lean_object* v_00_u03b2_3143_, lean_object* v_t_3144_){
_start:
{
lean_object* v___f_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___f_3145_ = ((lean_object*)(l_Std_ExtDTreeMap_values___redArg___closed__0));
v___x_3146_ = lean_box(0);
v___x_3147_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3148_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3147_, v___f_3145_, v___x_3146_, v_t_3144_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___boxed(lean_object* v_00_u03b1_3149_, lean_object* v_cmp_3150_, lean_object* v_inst_3151_, lean_object* v_00_u03b2_3152_, lean_object* v_t_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Std_ExtDTreeMap_values(v_00_u03b1_3149_, v_cmp_3150_, v_inst_3151_, v_00_u03b2_3152_, v_t_3153_);
lean_dec_ref(v_cmp_3150_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_3155_, lean_object* v_x_3156_, lean_object* v_v_3157_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = lean_array_push(v_l_3155_, v_v_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_3159_, lean_object* v_x_3160_, lean_object* v_v_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(v_l_3159_, v_x_3160_, v_v_3161_);
lean_dec(v_x_3160_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg(lean_object* v_t_3164_){
_start:
{
lean_object* v___f_3165_; lean_object* v___y_3167_; 
v___f_3165_ = ((lean_object*)(l_Std_ExtDTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_3164_) == 0)
{
lean_object* v_size_3170_; 
v_size_3170_ = lean_ctor_get(v_t_3164_, 0);
lean_inc(v_size_3170_);
v___y_3167_ = v_size_3170_;
goto v___jp_3166_;
}
else
{
lean_object* v___x_3171_; 
v___x_3171_ = lean_unsigned_to_nat(0u);
v___y_3167_ = v___x_3171_;
goto v___jp_3166_;
}
v___jp_3166_:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = lean_mk_empty_array_with_capacity(v___y_3167_);
lean_dec(v___y_3167_);
v___x_3169_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3165_, v___x_3168_, v_t_3164_);
return v___x_3169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray(lean_object* v_00_u03b1_3172_, lean_object* v_cmp_3173_, lean_object* v_inst_3174_, lean_object* v_00_u03b2_3175_, lean_object* v_t_3176_){
_start:
{
lean_object* v___f_3177_; lean_object* v___y_3179_; 
v___f_3177_ = ((lean_object*)(l_Std_ExtDTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_3176_) == 0)
{
lean_object* v_size_3182_; 
v_size_3182_ = lean_ctor_get(v_t_3176_, 0);
lean_inc(v_size_3182_);
v___y_3179_ = v_size_3182_;
goto v___jp_3178_;
}
else
{
lean_object* v___x_3183_; 
v___x_3183_ = lean_unsigned_to_nat(0u);
v___y_3179_ = v___x_3183_;
goto v___jp_3178_;
}
v___jp_3178_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = lean_mk_empty_array_with_capacity(v___y_3179_);
lean_dec(v___y_3179_);
v___x_3181_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3177_, v___x_3180_, v_t_3176_);
return v___x_3181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_3184_, lean_object* v_cmp_3185_, lean_object* v_inst_3186_, lean_object* v_00_u03b2_3187_, lean_object* v_t_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Std_ExtDTreeMap_valuesArray(v_00_u03b1_3184_, v_cmp_3185_, v_inst_3186_, v_00_u03b2_3187_, v_t_3188_);
lean_dec_ref(v_cmp_3185_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___redArg___lam__0(lean_object* v_x1_3190_, lean_object* v_x2_3191_, lean_object* v_x3_3192_){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3193_, 0, v_x1_3190_);
lean_ctor_set(v___x_3193_, 1, v_x2_3191_);
v___x_3194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
lean_ctor_set(v___x_3194_, 1, v_x3_3192_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___redArg(lean_object* v_t_3196_){
_start:
{
lean_object* v___f_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___f_3197_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3198_ = lean_box(0);
v___x_3199_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3200_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3199_, v___f_3197_, v___x_3198_, v_t_3196_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList(lean_object* v_00_u03b1_3201_, lean_object* v_00_u03b2_3202_, lean_object* v_cmp_3203_, lean_object* v_inst_3204_, lean_object* v_t_3205_){
_start:
{
lean_object* v___f_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___f_3206_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3207_ = lean_box(0);
v___x_3208_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3209_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3208_, v___f_3206_, v___x_3207_, v_t_3205_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___boxed(lean_object* v_00_u03b1_3210_, lean_object* v_00_u03b2_3211_, lean_object* v_cmp_3212_, lean_object* v_inst_3213_, lean_object* v_t_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Std_ExtDTreeMap_toList(v_00_u03b1_3210_, v_00_u03b2_3211_, v_cmp_3212_, v_inst_3213_, v_t_3214_);
lean_dec_ref(v_cmp_3212_);
return v_res_3215_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_3217_, lean_object* v_a_3218_, lean_object* v_x_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_fst_3221_; lean_object* v_snd_3222_; lean_object* v_r_3223_; lean_object* v___x_3224_; 
v_fst_3221_ = lean_ctor_get(v_a_3218_, 0);
lean_inc(v_fst_3221_);
v_snd_3222_ = lean_ctor_get(v_a_3218_, 1);
lean_inc(v_snd_3222_);
lean_dec_ref(v_a_3218_);
v_r_3223_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3217_, v_fst_3221_, v_snd_3222_, v___y_3220_);
v___x_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3224_, 0, v_r_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg(lean_object* v_l_3225_, lean_object* v_cmp_3226_){
_start:
{
lean_object* v___f_3227_; lean_object* v___x_3228_; lean_object* v_r_3229_; lean_object* v___x_3230_; 
v___f_3227_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3227_, 0, v_cmp_3226_);
v___x_3228_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3229_ = lean_box(1);
v___x_3230_ = l_List_forIn_x27_loop___redArg(v___x_3228_, v___f_3227_, v_l_3225_, v_r_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg___boxed(lean_object* v_l_3231_, lean_object* v_cmp_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Std_ExtDTreeMap_ofList___redArg(v_l_3231_, v_cmp_3232_);
lean_dec(v_l_3231_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList(lean_object* v_00_u03b1_3234_, lean_object* v_00_u03b2_3235_, lean_object* v_l_3236_, lean_object* v_cmp_3237_){
_start:
{
lean_object* v___f_3238_; lean_object* v___x_3239_; lean_object* v_r_3240_; lean_object* v___x_3241_; 
v___f_3238_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3238_, 0, v_cmp_3237_);
v___x_3239_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3240_ = lean_box(1);
v___x_3241_ = l_List_forIn_x27_loop___redArg(v___x_3239_, v___f_3238_, v_l_3236_, v_r_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___boxed(lean_object* v_00_u03b1_3242_, lean_object* v_00_u03b2_3243_, lean_object* v_l_3244_, lean_object* v_cmp_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Std_ExtDTreeMap_ofList(v_00_u03b1_3242_, v_00_u03b2_3243_, v_l_3244_, v_cmp_3245_);
lean_dec(v_l_3244_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___redArg___lam__0(lean_object* v_l_3247_, lean_object* v_k_3248_, lean_object* v_v_3249_){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v_k_3248_);
lean_ctor_set(v___x_3250_, 1, v_v_3249_);
v___x_3251_ = lean_array_push(v_l_3247_, v___x_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___redArg(lean_object* v_t_3253_){
_start:
{
lean_object* v___f_3254_; lean_object* v___y_3256_; 
v___f_3254_ = ((lean_object*)(l_Std_ExtDTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3253_) == 0)
{
lean_object* v_size_3259_; 
v_size_3259_ = lean_ctor_get(v_t_3253_, 0);
lean_inc(v_size_3259_);
v___y_3256_ = v_size_3259_;
goto v___jp_3255_;
}
else
{
lean_object* v___x_3260_; 
v___x_3260_ = lean_unsigned_to_nat(0u);
v___y_3256_ = v___x_3260_;
goto v___jp_3255_;
}
v___jp_3255_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3257_ = lean_mk_empty_array_with_capacity(v___y_3256_);
lean_dec(v___y_3256_);
v___x_3258_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3254_, v___x_3257_, v_t_3253_);
return v___x_3258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray(lean_object* v_00_u03b1_3261_, lean_object* v_00_u03b2_3262_, lean_object* v_cmp_3263_, lean_object* v_inst_3264_, lean_object* v_t_3265_){
_start:
{
lean_object* v___f_3266_; lean_object* v___y_3268_; 
v___f_3266_ = ((lean_object*)(l_Std_ExtDTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3265_) == 0)
{
lean_object* v_size_3271_; 
v_size_3271_ = lean_ctor_get(v_t_3265_, 0);
lean_inc(v_size_3271_);
v___y_3268_ = v_size_3271_;
goto v___jp_3267_;
}
else
{
lean_object* v___x_3272_; 
v___x_3272_ = lean_unsigned_to_nat(0u);
v___y_3268_ = v___x_3272_;
goto v___jp_3267_;
}
v___jp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = lean_mk_empty_array_with_capacity(v___y_3268_);
lean_dec(v___y_3268_);
v___x_3270_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3266_, v___x_3269_, v_t_3265_);
return v___x_3270_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___boxed(lean_object* v_00_u03b1_3273_, lean_object* v_00_u03b2_3274_, lean_object* v_cmp_3275_, lean_object* v_inst_3276_, lean_object* v_t_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Std_ExtDTreeMap_toArray(v_00_u03b1_3273_, v_00_u03b2_3274_, v_cmp_3275_, v_inst_3276_, v_t_3277_);
lean_dec_ref(v_cmp_3275_);
return v_res_3278_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray___redArg(lean_object* v_a_3280_, lean_object* v_cmp_3281_){
_start:
{
lean_object* v___f_3282_; lean_object* v___x_3283_; lean_object* v_r_3284_; size_t v_sz_3285_; size_t v___x_3286_; lean_object* v___x_3287_; 
v___f_3282_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3282_, 0, v_cmp_3281_);
v___x_3283_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3284_ = lean_box(1);
v_sz_3285_ = lean_array_size(v_a_3280_);
v___x_3286_ = ((size_t)0ULL);
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3283_, v_a_3280_, v___f_3282_, v_sz_3285_, v___x_3286_, v_r_3284_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray(lean_object* v_00_u03b1_3288_, lean_object* v_00_u03b2_3289_, lean_object* v_a_3290_, lean_object* v_cmp_3291_){
_start:
{
lean_object* v___f_3292_; lean_object* v___x_3293_; lean_object* v_r_3294_; size_t v_sz_3295_; size_t v___x_3296_; lean_object* v___x_3297_; 
v___f_3292_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3292_, 0, v_cmp_3291_);
v___x_3293_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3294_ = lean_box(1);
v_sz_3295_ = lean_array_size(v_a_3290_);
v___x_3296_ = ((size_t)0ULL);
v___x_3297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3293_, v_a_3290_, v___f_3292_, v_sz_3295_, v___x_3296_, v_r_3294_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_modify___redArg(lean_object* v_cmp_3298_, lean_object* v_t_3299_, lean_object* v_a_3300_, lean_object* v_f_3301_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3298_, v_a_3300_, v_f_3301_, v_t_3299_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_modify(lean_object* v_00_u03b1_3303_, lean_object* v_00_u03b2_3304_, lean_object* v_cmp_3305_, lean_object* v_inst_3306_, lean_object* v_inst_3307_, lean_object* v_t_3308_, lean_object* v_a_3309_, lean_object* v_f_3310_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3305_, v_a_3309_, v_f_3310_, v_t_3308_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_alter___redArg(lean_object* v_cmp_3312_, lean_object* v_t_3313_, lean_object* v_a_3314_, lean_object* v_f_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3312_, v_a_3314_, v_f_3315_, v_t_3313_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_alter(lean_object* v_00_u03b1_3317_, lean_object* v_00_u03b2_3318_, lean_object* v_cmp_3319_, lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_t_3322_, lean_object* v_a_3323_, lean_object* v_f_3324_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3319_, v_a_3323_, v_f_3324_, v_t_3322_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_3326_, lean_object* v_mergeFn_3327_, lean_object* v_a_3328_, lean_object* v_x_3329_){
_start:
{
if (lean_obj_tag(v_x_3329_) == 0)
{
lean_object* v___x_3330_; 
lean_dec(v_a_3328_);
lean_dec(v_mergeFn_3327_);
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_b_u2082_3326_);
return v___x_3330_;
}
else
{
lean_object* v_val_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3339_; 
v_val_3331_ = lean_ctor_get(v_x_3329_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_x_3329_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3333_ = v_x_3329_;
v_isShared_3334_ = v_isSharedCheck_3339_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_val_3331_);
lean_dec(v_x_3329_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3339_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3335_ = lean_apply_3(v_mergeFn_3327_, v_a_3328_, v_val_3331_, v_b_u2082_3326_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v___x_3335_);
v___x_3337_ = v___x_3333_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3340_, lean_object* v_cmp_3341_, lean_object* v_t_3342_, lean_object* v_a_3343_, lean_object* v_b_u2082_3344_){
_start:
{
lean_object* v___f_3345_; lean_object* v___x_3346_; 
lean_inc(v_a_3343_);
v___f_3345_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3345_, 0, v_b_u2082_3344_);
lean_closure_set(v___f_3345_, 1, v_mergeFn_3340_);
lean_closure_set(v___f_3345_, 2, v_a_3343_);
v___x_3346_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3341_, v_a_3343_, v___f_3345_, v_t_3342_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg(lean_object* v_cmp_3347_, lean_object* v_mergeFn_3348_, lean_object* v_t_u2081_3349_, lean_object* v_t_u2082_3350_){
_start:
{
lean_object* v___f_3351_; lean_object* v___x_3352_; 
v___f_3351_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3351_, 0, v_mergeFn_3348_);
lean_closure_set(v___f_3351_, 1, v_cmp_3347_);
v___x_3352_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3351_, v_t_u2081_3349_, v_t_u2082_3350_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith(lean_object* v_00_u03b1_3353_, lean_object* v_00_u03b2_3354_, lean_object* v_cmp_3355_, lean_object* v_inst_3356_, lean_object* v_inst_3357_, lean_object* v_mergeFn_3358_, lean_object* v_t_u2081_3359_, lean_object* v_t_u2082_3360_){
_start:
{
lean_object* v___f_3361_; lean_object* v___x_3362_; 
v___f_3361_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3361_, 0, v_mergeFn_3358_);
lean_closure_set(v___f_3361_, 1, v_cmp_3355_);
v___x_3362_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3361_, v_t_u2081_3359_, v_t_u2082_3360_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___redArg___lam__0(lean_object* v_x1_3363_, lean_object* v_x2_3364_, lean_object* v_x3_3365_){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_x1_3363_);
lean_ctor_set(v___x_3366_, 1, v_x2_3364_);
v___x_3367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
lean_ctor_set(v___x_3367_, 1, v_x3_3365_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___redArg(lean_object* v_t_3369_){
_start:
{
lean_object* v___f_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___f_3370_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toList___redArg___closed__0));
v___x_3371_ = lean_box(0);
v___x_3372_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3373_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3372_, v___f_3370_, v___x_3371_, v_t_3369_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList(lean_object* v_00_u03b1_3374_, lean_object* v_cmp_3375_, lean_object* v_00_u03b2_3376_, lean_object* v_inst_3377_, lean_object* v_t_3378_){
_start:
{
lean_object* v___f_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___f_3379_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toList___redArg___closed__0));
v___x_3380_ = lean_box(0);
v___x_3381_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3382_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3381_, v___f_3379_, v___x_3380_, v_t_3378_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___boxed(lean_object* v_00_u03b1_3383_, lean_object* v_cmp_3384_, lean_object* v_00_u03b2_3385_, lean_object* v_inst_3386_, lean_object* v_t_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Std_ExtDTreeMap_Const_toList(v_00_u03b1_3383_, v_cmp_3384_, v_00_u03b2_3385_, v_inst_3386_, v_t_3387_);
lean_dec_ref(v_cmp_3384_);
return v_res_3388_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_3389_; 
v___x_3389_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0(lean_object* v_cmp_3390_, lean_object* v_a_3391_, lean_object* v_x_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_fst_3394_; lean_object* v_snd_3395_; lean_object* v_r_3396_; lean_object* v___x_3397_; 
v_fst_3394_ = lean_ctor_get(v_a_3391_, 0);
lean_inc(v_fst_3394_);
v_snd_3395_ = lean_ctor_get(v_a_3391_, 1);
lean_inc(v_snd_3395_);
lean_dec_ref(v_a_3391_);
v_r_3396_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3390_, v_fst_3394_, v_snd_3395_, v___y_3393_);
v___x_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3397_, 0, v_r_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg(lean_object* v_l_3398_, lean_object* v_cmp_3399_){
_start:
{
lean_object* v___f_3400_; lean_object* v___x_3401_; lean_object* v_r_3402_; lean_object* v___x_3403_; 
v___f_3400_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3400_, 0, v_cmp_3399_);
v___x_3401_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3402_ = lean_box(1);
v___x_3403_ = l_List_forIn_x27_loop___redArg(v___x_3401_, v___f_3400_, v_l_3398_, v_r_3402_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg___boxed(lean_object* v_l_3404_, lean_object* v_cmp_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Std_ExtDTreeMap_Const_ofList___redArg(v_l_3404_, v_cmp_3405_);
lean_dec(v_l_3404_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList(lean_object* v_00_u03b1_3407_, lean_object* v_00_u03b2_3408_, lean_object* v_l_3409_, lean_object* v_cmp_3410_){
_start:
{
lean_object* v___f_3411_; lean_object* v___x_3412_; lean_object* v_r_3413_; lean_object* v___x_3414_; 
v___f_3411_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3411_, 0, v_cmp_3410_);
v___x_3412_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3413_ = lean_box(1);
v___x_3414_ = l_List_forIn_x27_loop___redArg(v___x_3412_, v___f_3411_, v_l_3409_, v_r_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___boxed(lean_object* v_00_u03b1_3415_, lean_object* v_00_u03b2_3416_, lean_object* v_l_3417_, lean_object* v_cmp_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Std_ExtDTreeMap_Const_ofList(v_00_u03b1_3415_, v_00_u03b2_3416_, v_l_3417_, v_cmp_3418_);
lean_dec(v_l_3417_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg___lam__0(lean_object* v_acc_3420_, lean_object* v_k_3421_, lean_object* v_v_3422_){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3423_, 0, v_k_3421_);
lean_ctor_set(v___x_3423_, 1, v_v_3422_);
v___x_3424_ = lean_array_push(v_acc_3420_, v___x_3423_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg(lean_object* v_t_3428_){
_start:
{
lean_object* v___f_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___f_3429_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0));
v___x_3430_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1));
v___x_3431_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3429_, v___x_3430_, v_t_3428_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray(lean_object* v_00_u03b1_3432_, lean_object* v_cmp_3433_, lean_object* v_00_u03b2_3434_, lean_object* v_inst_3435_, lean_object* v_t_3436_){
_start:
{
lean_object* v___f_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___f_3437_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0));
v___x_3438_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1));
v___x_3439_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3437_, v___x_3438_, v_t_3436_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___boxed(lean_object* v_00_u03b1_3440_, lean_object* v_cmp_3441_, lean_object* v_00_u03b2_3442_, lean_object* v_inst_3443_, lean_object* v_t_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Std_ExtDTreeMap_Const_toArray(v_00_u03b1_3440_, v_cmp_3441_, v_00_u03b2_3442_, v_inst_3443_, v_t_3444_);
lean_dec_ref(v_cmp_3441_);
return v_res_3445_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray___redArg(lean_object* v_a_3447_, lean_object* v_cmp_3448_){
_start:
{
lean_object* v___f_3449_; lean_object* v___x_3450_; lean_object* v_r_3451_; size_t v_sz_3452_; size_t v___x_3453_; lean_object* v___x_3454_; 
v___f_3449_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3449_, 0, v_cmp_3448_);
v___x_3450_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3451_ = lean_box(1);
v_sz_3452_ = lean_array_size(v_a_3447_);
v___x_3453_ = ((size_t)0ULL);
v___x_3454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3450_, v_a_3447_, v___f_3449_, v_sz_3452_, v___x_3453_, v_r_3451_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray(lean_object* v_00_u03b1_3455_, lean_object* v_00_u03b2_3456_, lean_object* v_a_3457_, lean_object* v_cmp_3458_){
_start:
{
lean_object* v___f_3459_; lean_object* v___x_3460_; lean_object* v_r_3461_; size_t v_sz_3462_; size_t v___x_3463_; lean_object* v___x_3464_; 
v___f_3459_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3459_, 0, v_cmp_3458_);
v___x_3460_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3461_ = lean_box(1);
v_sz_3462_ = lean_array_size(v_a_3457_);
v___x_3463_ = ((size_t)0ULL);
v___x_3464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3460_, v_a_3457_, v___f_3459_, v_sz_3462_, v___x_3463_, v_r_3461_);
return v___x_3464_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_3465_; 
v___x_3465_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_3466_, lean_object* v_a_3467_, lean_object* v_x_3468_, lean_object* v___y_3469_){
_start:
{
uint8_t v___x_3470_; 
lean_inc(v___y_3469_);
lean_inc(v_a_3467_);
lean_inc_ref(v_cmp_3466_);
v___x_3470_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3466_, v_a_3467_, v___y_3469_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = lean_box(0);
v___x_3472_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3466_, v_a_3467_, v___x_3471_, v___y_3469_);
v___x_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
return v___x_3473_;
}
else
{
lean_object* v___x_3474_; 
lean_dec(v_a_3467_);
lean_dec_ref(v_cmp_3466_);
v___x_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3474_, 0, v___y_3469_);
return v___x_3474_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg(lean_object* v_l_3475_, lean_object* v_cmp_3476_){
_start:
{
lean_object* v___f_3477_; lean_object* v___x_3478_; lean_object* v_r_3479_; lean_object* v___x_3480_; 
v___f_3477_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3477_, 0, v_cmp_3476_);
v___x_3478_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3479_ = lean_box(1);
v___x_3480_ = l_List_forIn_x27_loop___redArg(v___x_3478_, v___f_3477_, v_l_3475_, v_r_3479_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg___boxed(lean_object* v_l_3481_, lean_object* v_cmp_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Std_ExtDTreeMap_Const_unitOfList___redArg(v_l_3481_, v_cmp_3482_);
lean_dec(v_l_3481_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList(lean_object* v_00_u03b1_3484_, lean_object* v_l_3485_, lean_object* v_cmp_3486_){
_start:
{
lean_object* v___f_3487_; lean_object* v___x_3488_; lean_object* v_r_3489_; lean_object* v___x_3490_; 
v___f_3487_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3487_, 0, v_cmp_3486_);
v___x_3488_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3489_ = lean_box(1);
v___x_3490_ = l_List_forIn_x27_loop___redArg(v___x_3488_, v___f_3487_, v_l_3485_, v_r_3489_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___boxed(lean_object* v_00_u03b1_3491_, lean_object* v_l_3492_, lean_object* v_cmp_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Std_ExtDTreeMap_Const_unitOfList(v_00_u03b1_3491_, v_l_3492_, v_cmp_3493_);
lean_dec(v_l_3492_);
return v_res_3494_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray___redArg(lean_object* v_a_3496_, lean_object* v_cmp_3497_){
_start:
{
lean_object* v___f_3498_; lean_object* v___x_3499_; lean_object* v_r_3500_; size_t v_sz_3501_; size_t v___x_3502_; lean_object* v___x_3503_; 
v___f_3498_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3498_, 0, v_cmp_3497_);
v___x_3499_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3500_ = lean_box(1);
v_sz_3501_ = lean_array_size(v_a_3496_);
v___x_3502_ = ((size_t)0ULL);
v___x_3503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3499_, v_a_3496_, v___f_3498_, v_sz_3501_, v___x_3502_, v_r_3500_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray(lean_object* v_00_u03b1_3504_, lean_object* v_a_3505_, lean_object* v_cmp_3506_){
_start:
{
lean_object* v___f_3507_; lean_object* v___x_3508_; lean_object* v_r_3509_; size_t v_sz_3510_; size_t v___x_3511_; lean_object* v___x_3512_; 
v___f_3507_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3507_, 0, v_cmp_3506_);
v___x_3508_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3509_ = lean_box(1);
v_sz_3510_ = lean_array_size(v_a_3505_);
v___x_3511_ = ((size_t)0ULL);
v___x_3512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3508_, v_a_3505_, v___f_3507_, v_sz_3510_, v___x_3511_, v_r_3509_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_modify___redArg(lean_object* v_cmp_3513_, lean_object* v_t_3514_, lean_object* v_a_3515_, lean_object* v_f_3516_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3513_, v_a_3515_, v_f_3516_, v_t_3514_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_modify(lean_object* v_00_u03b1_3518_, lean_object* v_cmp_3519_, lean_object* v_00_u03b2_3520_, lean_object* v_inst_3521_, lean_object* v_t_3522_, lean_object* v_a_3523_, lean_object* v_f_3524_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3519_, v_a_3523_, v_f_3524_, v_t_3522_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_alter___redArg(lean_object* v_cmp_3526_, lean_object* v_t_3527_, lean_object* v_a_3528_, lean_object* v_f_3529_){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3526_, v_a_3528_, v_f_3529_, v_t_3527_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_alter(lean_object* v_00_u03b1_3531_, lean_object* v_cmp_3532_, lean_object* v_00_u03b2_3533_, lean_object* v_inst_3534_, lean_object* v_t_3535_, lean_object* v_a_3536_, lean_object* v_f_3537_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3532_, v_a_3536_, v_f_3537_, v_t_3535_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3539_, lean_object* v_cmp_3540_, lean_object* v_t_3541_, lean_object* v_a_3542_, lean_object* v_b_u2082_3543_){
_start:
{
lean_object* v___f_3544_; lean_object* v___x_3545_; 
lean_inc(v_a_3542_);
v___f_3544_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3544_, 0, v_b_u2082_3543_);
lean_closure_set(v___f_3544_, 1, v_mergeFn_3539_);
lean_closure_set(v___f_3544_, 2, v_a_3542_);
v___x_3545_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3540_, v_a_3542_, v___f_3544_, v_t_3541_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith___redArg(lean_object* v_cmp_3546_, lean_object* v_mergeFn_3547_, lean_object* v_t_u2081_3548_, lean_object* v_t_u2082_3549_){
_start:
{
lean_object* v___f_3550_; lean_object* v___x_3551_; 
v___f_3550_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3550_, 0, v_mergeFn_3547_);
lean_closure_set(v___f_3550_, 1, v_cmp_3546_);
v___x_3551_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3550_, v_t_u2081_3548_, v_t_u2082_3549_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith(lean_object* v_00_u03b1_3552_, lean_object* v_cmp_3553_, lean_object* v_00_u03b2_3554_, lean_object* v_inst_3555_, lean_object* v_mergeFn_3556_, lean_object* v_t_u2081_3557_, lean_object* v_t_u2082_3558_){
_start:
{
lean_object* v___f_3559_; lean_object* v___x_3560_; 
v___f_3559_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3559_, 0, v_mergeFn_3556_);
lean_closure_set(v___f_3559_, 1, v_cmp_3553_);
v___x_3560_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3559_, v_t_u2081_3557_, v_t_u2082_3558_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_3561_, lean_object* v_x_3562_, lean_object* v_____s_3563_){
_start:
{
lean_object* v_fst_3564_; lean_object* v_snd_3565_; lean_object* v_acc_3566_; lean_object* v___x_3567_; 
v_fst_3564_ = lean_ctor_get(v_x_3562_, 0);
lean_inc(v_fst_3564_);
v_snd_3565_ = lean_ctor_get(v_x_3562_, 1);
lean_inc(v_snd_3565_);
lean_dec_ref(v_x_3562_);
v_acc_3566_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3561_, v_fst_3564_, v_snd_3565_, v_____s_3563_);
v___x_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3567_, 0, v_acc_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany___redArg(lean_object* v_cmp_3568_, lean_object* v_inst_3569_, lean_object* v_t_3570_, lean_object* v_l_3571_){
_start:
{
lean_object* v___f_3572_; lean_object* v___x_3573_; 
v___f_3572_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3572_, 0, v_cmp_3568_);
v___x_3573_ = lean_apply_4(v_inst_3569_, lean_box(0), v_l_3571_, v_t_3570_, v___f_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany(lean_object* v_00_u03b1_3574_, lean_object* v_00_u03b2_3575_, lean_object* v_cmp_3576_, lean_object* v_inst_3577_, lean_object* v_00_u03c1_3578_, lean_object* v_inst_3579_, lean_object* v_t_3580_, lean_object* v_l_3581_){
_start:
{
lean_object* v___f_3582_; lean_object* v___x_3583_; 
v___f_3582_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3582_, 0, v_cmp_3576_);
v___x_3583_ = lean_apply_4(v_inst_3579_, lean_box(0), v_l_3581_, v_t_3580_, v___f_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_3584_, lean_object* v_a_3585_, lean_object* v_____s_3586_){
_start:
{
lean_object* v_acc_3587_; lean_object* v___x_3588_; 
v_acc_3587_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_3584_, v_a_3585_, v_____s_3586_);
v___x_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3588_, 0, v_acc_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany___redArg(lean_object* v_cmp_3589_, lean_object* v_inst_3590_, lean_object* v_t_3591_, lean_object* v_l_3592_){
_start:
{
lean_object* v___f_3593_; lean_object* v___x_3594_; 
v___f_3593_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3593_, 0, v_cmp_3589_);
v___x_3594_ = lean_apply_4(v_inst_3590_, lean_box(0), v_l_3592_, v_t_3591_, v___f_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany(lean_object* v_00_u03b1_3595_, lean_object* v_00_u03b2_3596_, lean_object* v_cmp_3597_, lean_object* v_inst_3598_, lean_object* v_00_u03c1_3599_, lean_object* v_inst_3600_, lean_object* v_t_3601_, lean_object* v_l_3602_){
_start:
{
lean_object* v___f_3603_; lean_object* v___x_3604_; 
v___f_3603_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3603_, 0, v_cmp_3597_);
v___x_3604_ = lean_apply_4(v_inst_3600_, lean_box(0), v_l_3602_, v_t_3601_, v___f_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0(lean_object* v_cmp_3605_, lean_object* v_x_3606_, lean_object* v_____s_3607_){
_start:
{
lean_object* v_fst_3608_; lean_object* v_snd_3609_; lean_object* v_acc_3610_; lean_object* v___x_3611_; 
v_fst_3608_ = lean_ctor_get(v_x_3606_, 0);
lean_inc(v_fst_3608_);
v_snd_3609_ = lean_ctor_get(v_x_3606_, 1);
lean_inc(v_snd_3609_);
lean_dec_ref(v_x_3606_);
v_acc_3610_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3605_, v_fst_3608_, v_snd_3609_, v_____s_3607_);
v___x_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3611_, 0, v_acc_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany___redArg(lean_object* v_cmp_3612_, lean_object* v_inst_3613_, lean_object* v_t_3614_, lean_object* v_l_3615_){
_start:
{
lean_object* v___f_3616_; lean_object* v___x_3617_; 
v___f_3616_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3616_, 0, v_cmp_3612_);
v___x_3617_ = lean_apply_4(v_inst_3613_, lean_box(0), v_l_3615_, v_t_3614_, v___f_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany(lean_object* v_00_u03b1_3618_, lean_object* v_cmp_3619_, lean_object* v_00_u03b2_3620_, lean_object* v_inst_3621_, lean_object* v_00_u03c1_3622_, lean_object* v_inst_3623_, lean_object* v_t_3624_, lean_object* v_l_3625_){
_start:
{
lean_object* v___f_3626_; lean_object* v___x_3627_; 
v___f_3626_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3626_, 0, v_cmp_3619_);
v___x_3627_ = lean_apply_4(v_inst_3623_, lean_box(0), v_l_3625_, v_t_3624_, v___f_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_3628_, lean_object* v_a_3629_, lean_object* v_____s_3630_){
_start:
{
uint8_t v___x_3631_; 
lean_inc(v_____s_3630_);
lean_inc(v_a_3629_);
lean_inc_ref(v_cmp_3628_);
v___x_3631_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3628_, v_a_3629_, v_____s_3630_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3632_ = lean_box(0);
v___x_3633_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3628_, v_a_3629_, v___x_3632_, v_____s_3630_);
v___x_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
return v___x_3634_;
}
else
{
lean_object* v___x_3635_; 
lean_dec(v_a_3629_);
lean_dec_ref(v_cmp_3628_);
v___x_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3635_, 0, v_____s_3630_);
return v___x_3635_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_3636_, lean_object* v_inst_3637_, lean_object* v_t_3638_, lean_object* v_l_3639_){
_start:
{
lean_object* v___f_3640_; lean_object* v___x_3641_; 
v___f_3640_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3640_, 0, v_cmp_3636_);
v___x_3641_ = lean_apply_4(v_inst_3637_, lean_box(0), v_l_3639_, v_t_3638_, v___f_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_3642_, lean_object* v_cmp_3643_, lean_object* v_inst_3644_, lean_object* v_00_u03c1_3645_, lean_object* v_inst_3646_, lean_object* v_t_3647_, lean_object* v_l_3648_){
_start:
{
lean_object* v___f_3649_; lean_object* v___x_3650_; 
v___f_3649_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3649_, 0, v_cmp_3643_);
v___x_3650_ = lean_apply_4(v_inst_3646_, lean_box(0), v_l_3648_, v_t_3647_, v___f_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_union___redArg(lean_object* v_cmp_3651_, lean_object* v_m_u2081_3652_, lean_object* v_m_u2082_3653_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3651_, v_m_u2081_3652_, v_m_u2082_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_union(lean_object* v_00_u03b1_3655_, lean_object* v_00_u03b2_3656_, lean_object* v_cmp_3657_, lean_object* v_inst_3658_, lean_object* v_m_u2081_3659_, lean_object* v_m_u2082_3660_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3657_, v_m_u2081_3659_, v_m_u2082_3660_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instUnionOfTransCmp___redArg(lean_object* v_cmp_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_union), 6, 4);
lean_closure_set(v___x_3663_, 0, lean_box(0));
lean_closure_set(v___x_3663_, 1, lean_box(0));
lean_closure_set(v___x_3663_, 2, v_cmp_3662_);
lean_closure_set(v___x_3663_, 3, lean_box(0));
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instUnionOfTransCmp(lean_object* v_00_u03b1_3664_, lean_object* v_00_u03b2_3665_, lean_object* v_cmp_3666_, lean_object* v_inst_3667_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_union), 6, 4);
lean_closure_set(v___x_3668_, 0, lean_box(0));
lean_closure_set(v___x_3668_, 1, lean_box(0));
lean_closure_set(v___x_3668_, 2, v_cmp_3666_);
lean_closure_set(v___x_3668_, 3, lean_box(0));
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_inter___redArg(lean_object* v_cmp_3669_, lean_object* v_m_u2081_3670_, lean_object* v_m_u2082_3671_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3669_, v_m_u2081_3670_, v_m_u2082_3671_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_inter(lean_object* v_00_u03b1_3673_, lean_object* v_00_u03b2_3674_, lean_object* v_cmp_3675_, lean_object* v_inst_3676_, lean_object* v_m_u2081_3677_, lean_object* v_m_u2082_3678_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3675_, v_m_u2081_3677_, v_m_u2082_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInterOfTransCmp___redArg(lean_object* v_cmp_3680_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_inter), 6, 4);
lean_closure_set(v___x_3681_, 0, lean_box(0));
lean_closure_set(v___x_3681_, 1, lean_box(0));
lean_closure_set(v___x_3681_, 2, v_cmp_3680_);
lean_closure_set(v___x_3681_, 3, lean_box(0));
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInterOfTransCmp(lean_object* v_00_u03b1_3682_, lean_object* v_00_u03b2_3683_, lean_object* v_cmp_3684_, lean_object* v_inst_3685_){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_inter), 6, 4);
lean_closure_set(v___x_3686_, 0, lean_box(0));
lean_closure_set(v___x_3686_, 1, lean_box(0));
lean_closure_set(v___x_3686_, 2, v_cmp_3684_);
lean_closure_set(v___x_3686_, 3, lean_box(0));
return v___x_3686_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(lean_object* v_cmp_3687_, lean_object* v_inst_3688_, lean_object* v_x_3689_, lean_object* v_y_3690_){
_start:
{
uint8_t v___x_3691_; 
v___x_3691_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3687_, v_inst_3688_, v_x_3689_, v_y_3690_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_3692_, lean_object* v_inst_3693_, lean_object* v_x_3694_, lean_object* v_y_3695_){
_start:
{
uint8_t v_res_3696_; lean_object* v_r_3697_; 
v_res_3696_ = l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(v_cmp_3692_, v_inst_3693_, v_x_3694_, v_y_3695_);
v_r_3697_ = lean_box(v_res_3696_);
return v_r_3697_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(lean_object* v_cmp_3698_, lean_object* v_inst_3699_){
_start:
{
lean_object* v___f_3700_; lean_object* v___x_3701_; 
lean_inc_ref(v_cmp_3698_);
v___f_3700_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3700_, 0, v_cmp_3698_);
lean_closure_set(v___f_3700_, 1, v_inst_3699_);
v___x_3701_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_lift_u2082___boxed), 8, 6);
lean_closure_set(v___x_3701_, 0, lean_box(0));
lean_closure_set(v___x_3701_, 1, lean_box(0));
lean_closure_set(v___x_3701_, 2, v_cmp_3698_);
lean_closure_set(v___x_3701_, 3, lean_box(0));
lean_closure_set(v___x_3701_, 4, v___f_3700_);
lean_closure_set(v___x_3701_, 5, lean_box(0));
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp(lean_object* v_00_u03b1_3702_, lean_object* v_00_u03b2_3703_, lean_object* v_cmp_3704_, lean_object* v_inst_3705_, lean_object* v_inst_3706_, lean_object* v_inst_3707_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_3704_, v_inst_3707_);
return v___x_3708_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object* v_cmp_3709_, lean_object* v_inst_3710_, lean_object* v_x_3711_, lean_object* v_x_3712_){
_start:
{
uint8_t v___x_3713_; 
v___x_3713_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3709_, v_inst_3710_, v_x_3711_, v_x_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_3714_, lean_object* v_inst_3715_, lean_object* v_x_3716_, lean_object* v_x_3717_){
_start:
{
uint8_t v_res_3718_; lean_object* v_r_3719_; 
v_res_3718_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(v_cmp_3714_, v_inst_3715_, v_x_3716_, v_x_3717_);
v_r_3719_ = lean_box(v_res_3718_);
return v_r_3719_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object* v_00_u03b1_3720_, lean_object* v_00_u03b2_3721_, lean_object* v_cmp_3722_, lean_object* v_inst_3723_, lean_object* v_inst_3724_, lean_object* v_inst_3725_, lean_object* v_inst_3726_, lean_object* v_x_3727_, lean_object* v_x_3728_){
_start:
{
uint8_t v___x_3729_; 
v___x_3729_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3722_, v_inst_3725_, v_x_3727_, v_x_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_3730_, lean_object* v_00_u03b2_3731_, lean_object* v_cmp_3732_, lean_object* v_inst_3733_, lean_object* v_inst_3734_, lean_object* v_inst_3735_, lean_object* v_inst_3736_, lean_object* v_x_3737_, lean_object* v_x_3738_){
_start:
{
uint8_t v_res_3739_; lean_object* v_r_3740_; 
v_res_3739_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(v_00_u03b1_3730_, v_00_u03b2_3731_, v_cmp_3732_, v_inst_3733_, v_inst_3734_, v_inst_3735_, v_inst_3736_, v_x_3737_, v_x_3738_);
v_r_3740_ = lean_box(v_res_3739_);
return v_r_3740_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_Const_beq___redArg(lean_object* v_cmp_3741_, lean_object* v_inst_3742_, lean_object* v_m_u2081_3743_, lean_object* v_m_u2082_3744_){
_start:
{
uint8_t v___x_3745_; 
v___x_3745_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3741_, v_inst_3742_, v_m_u2081_3743_, v_m_u2082_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_beq___redArg___boxed(lean_object* v_cmp_3746_, lean_object* v_inst_3747_, lean_object* v_m_u2081_3748_, lean_object* v_m_u2082_3749_){
_start:
{
uint8_t v_res_3750_; lean_object* v_r_3751_; 
v_res_3750_ = l_Std_ExtDTreeMap_Const_beq___redArg(v_cmp_3746_, v_inst_3747_, v_m_u2081_3748_, v_m_u2082_3749_);
v_r_3751_ = lean_box(v_res_3750_);
return v_r_3751_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_Const_beq(lean_object* v_00_u03b1_3752_, lean_object* v_cmp_3753_, lean_object* v_00_u03b2_3754_, lean_object* v_inst_3755_, lean_object* v_inst_3756_, lean_object* v_m_u2081_3757_, lean_object* v_m_u2082_3758_){
_start:
{
uint8_t v___x_3759_; 
v___x_3759_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3753_, v_inst_3756_, v_m_u2081_3757_, v_m_u2082_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_beq___boxed(lean_object* v_00_u03b1_3760_, lean_object* v_cmp_3761_, lean_object* v_00_u03b2_3762_, lean_object* v_inst_3763_, lean_object* v_inst_3764_, lean_object* v_m_u2081_3765_, lean_object* v_m_u2082_3766_){
_start:
{
uint8_t v_res_3767_; lean_object* v_r_3768_; 
v_res_3767_ = l_Std_ExtDTreeMap_Const_beq(v_00_u03b1_3760_, v_cmp_3761_, v_00_u03b2_3762_, v_inst_3763_, v_inst_3764_, v_m_u2081_3765_, v_m_u2082_3766_);
v_r_3768_ = lean_box(v_res_3767_);
return v_r_3768_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_diff___redArg(lean_object* v_cmp_3769_, lean_object* v_m_u2081_3770_, lean_object* v_m_u2082_3771_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_3769_, v_m_u2081_3770_, v_m_u2082_3771_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_diff(lean_object* v_00_u03b1_3773_, lean_object* v_00_u03b2_3774_, lean_object* v_cmp_3775_, lean_object* v_inst_3776_, lean_object* v_m_u2081_3777_, lean_object* v_m_u2082_3778_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_3775_, v_m_u2081_3777_, v_m_u2082_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSDiffOfTransCmp___redArg(lean_object* v_cmp_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_diff), 6, 4);
lean_closure_set(v___x_3781_, 0, lean_box(0));
lean_closure_set(v___x_3781_, 1, lean_box(0));
lean_closure_set(v___x_3781_, 2, v_cmp_3780_);
lean_closure_set(v___x_3781_, 3, lean_box(0));
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSDiffOfTransCmp(lean_object* v_00_u03b1_3782_, lean_object* v_00_u03b2_3783_, lean_object* v_cmp_3784_, lean_object* v_inst_3785_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_diff), 6, 4);
lean_closure_set(v___x_3786_, 0, lean_box(0));
lean_closure_set(v___x_3786_, 1, lean_box(0));
lean_closure_set(v___x_3786_, 2, v_cmp_3784_);
lean_closure_set(v___x_3786_, 3, lean_box(0));
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_3790_, lean_object* v___x_3791_, lean_object* v_m_3792_, lean_object* v_prec_3793_){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3794_ = ((lean_object*)(l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_3795_ = lean_box(0);
v___x_3796_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3797_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3796_, v___f_3790_, v___x_3795_, v_m_3792_);
v___x_3798_ = l_List_repr___redArg(v___x_3791_, v___x_3797_);
v___x_3799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3794_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v___x_3800_ = l_Repr_addAppParen(v___x_3799_, v_prec_3793_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_3801_, lean_object* v___x_3802_, lean_object* v_m_3803_, lean_object* v_prec_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(v___f_3801_, v___x_3802_, v_m_3803_, v_prec_3804_);
lean_dec(v_prec_3804_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(lean_object* v_inst_3806_, lean_object* v_inst_3807_){
_start:
{
lean_object* v___f_3808_; lean_object* v___x_3809_; lean_object* v___f_3810_; 
v___f_3808_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3809_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_3809_, 0, lean_box(0));
lean_closure_set(v___x_3809_, 1, lean_box(0));
lean_closure_set(v___x_3809_, 2, v_inst_3806_);
lean_closure_set(v___x_3809_, 3, v_inst_3807_);
v___f_3810_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3810_, 0, v___f_3808_);
lean_closure_set(v___f_3810_, 1, v___x_3809_);
return v___f_3810_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp(lean_object* v_00_u03b1_3811_, lean_object* v_00_u03b2_3812_, lean_object* v_cmp_3813_, lean_object* v_inst_3814_, lean_object* v_inst_3815_, lean_object* v_inst_3816_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(v_inst_3815_, v_inst_3816_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_3818_, lean_object* v_00_u03b2_3819_, lean_object* v_cmp_3820_, lean_object* v_inst_3821_, lean_object* v_inst_3822_, lean_object* v_inst_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l_Std_ExtDTreeMap_instReprOfTransCmp(v_00_u03b1_3818_, v_00_u03b2_3819_, v_cmp_3820_, v_inst_3821_, v_inst_3822_, v_inst_3823_);
lean_dec_ref(v_cmp_3820_);
return v_res_3824_;
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
