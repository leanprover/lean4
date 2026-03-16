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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instCoeTypeForall(lean_object* v_00_u03b1_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_box(0);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty(lean_object* v_00_u03b1_171_, lean_object* v_00_u03b2_172_, lean_object* v_cmp_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(1);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_empty___boxed(lean_object* v_00_u03b1_175_, lean_object* v_00_u03b2_176_, lean_object* v_cmp_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_ExtDTreeMap_empty(v_00_u03b1_175_, v_00_u03b2_176_, v_cmp_177_);
lean_dec_ref(v_cmp_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_cmp_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_box(1);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_cmp_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_ExtDTreeMap_instEmptyCollection(v_00_u03b1_183_, v_00_u03b2_184_, v_cmp_185_);
lean_dec_ref(v_cmp_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited(lean_object* v_00_u03b1_187_, lean_object* v_00_u03b2_188_, lean_object* v_cmp_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_box(1);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInhabited___boxed(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_cmp_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_ExtDTreeMap_instInhabited(v_00_u03b1_191_, v_00_u03b2_192_, v_cmp_193_);
lean_dec_ref(v_cmp_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insert___redArg(lean_object* v_cmp_195_, lean_object* v_t_196_, lean_object* v_a_197_, lean_object* v_b_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_195_, v_a_197_, v_b_198_, v_t_196_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insert(lean_object* v_00_u03b1_200_, lean_object* v_00_u03b2_201_, lean_object* v_cmp_202_, lean_object* v_inst_203_, lean_object* v_t_204_, lean_object* v_a_205_, lean_object* v_b_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_202_, v_a_205_, v_b_206_, v_t_204_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0(lean_object* v_cmp_208_, lean_object* v_e_209_){
_start:
{
lean_object* v_fst_210_; lean_object* v_snd_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_fst_210_ = lean_ctor_get(v_e_209_, 0);
lean_inc(v_fst_210_);
v_snd_211_ = lean_ctor_get(v_e_209_, 1);
lean_inc(v_snd_211_);
lean_dec_ref(v_e_209_);
v___x_212_ = lean_box(1);
v___x_213_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_208_, v_fst_210_, v_snd_211_, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg(lean_object* v_cmp_214_){
_start:
{
lean_object* v___f_215_; 
v___f_215_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_215_, 0, v_cmp_214_);
return v___f_215_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp(lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_, lean_object* v_cmp_218_, lean_object* v_inst_219_){
_start:
{
lean_object* v___f_220_; 
v___f_220_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_220_, 0, v_cmp_218_);
return v___f_220_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0(lean_object* v_cmp_221_, lean_object* v_e_222_, lean_object* v_s_223_){
_start:
{
lean_object* v_fst_224_; lean_object* v_snd_225_; lean_object* v___x_226_; 
v_fst_224_ = lean_ctor_get(v_e_222_, 0);
lean_inc(v_fst_224_);
v_snd_225_ = lean_ctor_get(v_e_222_, 1);
lean_inc(v_snd_225_);
lean_dec_ref(v_e_222_);
v___x_226_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_221_, v_fst_224_, v_snd_225_, v_s_223_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg(lean_object* v_cmp_227_){
_start:
{
lean_object* v___f_228_; 
v___f_228_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_228_, 0, v_cmp_227_);
return v___f_228_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp(lean_object* v_00_u03b1_229_, lean_object* v_00_u03b2_230_, lean_object* v_cmp_231_, lean_object* v_inst_232_){
_start:
{
lean_object* v___f_233_; 
v___f_233_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_233_, 0, v_cmp_231_);
return v___f_233_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertIfNew___redArg(lean_object* v_cmp_234_, lean_object* v_t_235_, lean_object* v_a_236_, lean_object* v_b_237_){
_start:
{
uint8_t v___x_238_; 
lean_inc(v_t_235_);
lean_inc(v_a_236_);
lean_inc_ref(v_cmp_234_);
v___x_238_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_234_, v_a_236_, v_t_235_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
v___x_239_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_234_, v_a_236_, v_b_237_, v_t_235_);
return v___x_239_;
}
else
{
lean_dec(v_b_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_cmp_234_);
return v_t_235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertIfNew(lean_object* v_00_u03b1_240_, lean_object* v_00_u03b2_241_, lean_object* v_cmp_242_, lean_object* v_inst_243_, lean_object* v_t_244_, lean_object* v_a_245_, lean_object* v_b_246_){
_start:
{
uint8_t v___x_247_; 
lean_inc(v_t_244_);
lean_inc(v_a_245_);
lean_inc_ref(v_cmp_242_);
v___x_247_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_242_, v_a_245_, v_t_244_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
v___x_248_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_242_, v_a_245_, v_b_246_, v_t_244_);
return v___x_248_;
}
else
{
lean_dec(v_b_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_cmp_242_);
return v_t_244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsert___redArg(lean_object* v_cmp_249_, lean_object* v_t_250_, lean_object* v_a_251_, lean_object* v_b_252_){
_start:
{
lean_object* v_sz_253_; lean_object* v_m_254_; lean_object* v___y_256_; 
v_sz_253_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_250_);
v_m_254_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_249_, v_a_251_, v_b_252_, v_t_250_);
if (lean_obj_tag(v_m_254_) == 0)
{
lean_object* v_size_260_; 
v_size_260_ = lean_ctor_get(v_m_254_, 0);
lean_inc(v_size_260_);
v___y_256_ = v_size_260_;
goto v___jp_255_;
}
else
{
lean_object* v___x_261_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___y_256_ = v___x_261_;
goto v___jp_255_;
}
v___jp_255_:
{
uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_nat_dec_eq(v_sz_253_, v___y_256_);
lean_dec(v___y_256_);
lean_dec(v_sz_253_);
v___x_258_ = lean_box(v___x_257_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v_m_254_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsert(lean_object* v_00_u03b1_262_, lean_object* v_00_u03b2_263_, lean_object* v_cmp_264_, lean_object* v_inst_265_, lean_object* v_t_266_, lean_object* v_a_267_, lean_object* v_b_268_){
_start:
{
lean_object* v_sz_269_; lean_object* v_m_270_; lean_object* v___y_272_; 
v_sz_269_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_266_);
v_m_270_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_264_, v_a_267_, v_b_268_, v_t_266_);
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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_278_, lean_object* v_t_279_, lean_object* v_a_280_, lean_object* v_b_281_){
_start:
{
uint8_t v___x_282_; 
lean_inc(v_t_279_);
lean_inc(v_a_280_);
lean_inc_ref(v_cmp_278_);
v___x_282_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_278_, v_a_280_, v_t_279_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_278_, v_a_280_, v_b_281_, v_t_279_);
v___x_284_ = lean_box(v___x_282_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
return v___x_285_;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v_b_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_cmp_278_);
v___x_286_ = lean_box(v___x_282_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v_t_279_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_288_, lean_object* v_00_u03b2_289_, lean_object* v_cmp_290_, lean_object* v_inst_291_, lean_object* v_t_292_, lean_object* v_a_293_, lean_object* v_b_294_){
_start:
{
uint8_t v___x_295_; 
lean_inc(v_t_292_);
lean_inc(v_a_293_);
lean_inc_ref(v_cmp_290_);
v___x_295_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_290_, v_a_293_, v_t_292_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_290_, v_a_293_, v_b_294_, v_t_292_);
v___x_297_ = lean_box(v___x_295_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v_b_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_cmp_290_);
v___x_299_ = lean_box(v___x_295_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v_t_292_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_301_, lean_object* v_t_302_, lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
lean_object* v___x_305_; 
lean_inc(v_a_303_);
lean_inc(v_t_302_);
lean_inc_ref(v_cmp_301_);
v___x_305_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_301_, v_t_302_, v_a_303_);
if (lean_obj_tag(v___x_305_) == 0)
{
uint8_t v___x_306_; 
lean_inc(v_t_302_);
lean_inc(v_a_303_);
lean_inc_ref(v_cmp_301_);
v___x_306_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_301_, v_a_303_, v_t_302_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_301_, v_a_303_, v_b_304_, v_t_302_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_305_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; 
lean_dec(v_b_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_cmp_301_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_305_);
lean_ctor_set(v___x_309_, 1, v_t_302_);
return v___x_309_;
}
}
else
{
lean_object* v___x_310_; 
lean_dec(v_b_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_cmp_301_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_305_);
lean_ctor_set(v___x_310_, 1, v_t_302_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_311_, lean_object* v_00_u03b2_312_, lean_object* v_cmp_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_t_316_, lean_object* v_a_317_, lean_object* v_b_318_){
_start:
{
lean_object* v___x_319_; 
lean_inc(v_a_317_);
lean_inc(v_t_316_);
lean_inc_ref(v_cmp_313_);
v___x_319_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_313_, v_t_316_, v_a_317_);
if (lean_obj_tag(v___x_319_) == 0)
{
uint8_t v___x_320_; 
lean_inc(v_t_316_);
lean_inc(v_a_317_);
lean_inc_ref(v_cmp_313_);
v___x_320_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_313_, v_a_317_, v_t_316_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_313_, v_a_317_, v_b_318_, v_t_316_);
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
lean_dec_ref(v_cmp_313_);
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
lean_dec_ref(v_cmp_313_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_319_);
lean_ctor_set(v___x_324_, 1, v_t_316_);
return v___x_324_;
}
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_contains___redArg(lean_object* v_cmp_325_, lean_object* v_t_326_, lean_object* v_a_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_325_, v_a_327_, v_t_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_contains___redArg___boxed(lean_object* v_cmp_329_, lean_object* v_t_330_, lean_object* v_a_331_){
_start:
{
uint8_t v_res_332_; lean_object* v_r_333_; 
v_res_332_ = l_Std_ExtDTreeMap_contains___redArg(v_cmp_329_, v_t_330_, v_a_331_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_contains(lean_object* v_00_u03b1_334_, lean_object* v_00_u03b2_335_, lean_object* v_cmp_336_, lean_object* v_inst_337_, lean_object* v_t_338_, lean_object* v_a_339_){
_start:
{
uint8_t v___x_340_; 
v___x_340_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_336_, v_a_339_, v_t_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_contains___boxed(lean_object* v_00_u03b1_341_, lean_object* v_00_u03b2_342_, lean_object* v_cmp_343_, lean_object* v_inst_344_, lean_object* v_t_345_, lean_object* v_a_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Std_ExtDTreeMap_contains(v_00_u03b1_341_, v_00_u03b2_342_, v_cmp_343_, v_inst_344_, v_t_345_, v_a_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp(lean_object* v_00_u03b1_349_, lean_object* v_00_u03b2_350_, lean_object* v_cmp_351_, lean_object* v_inst_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = lean_box(0);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instMembershipOfTransCmp___boxed(lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_cmp_356_, lean_object* v_inst_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_ExtDTreeMap_instMembershipOfTransCmp(v_00_u03b1_354_, v_00_u03b2_355_, v_cmp_356_, v_inst_357_);
lean_dec_ref(v_cmp_356_);
return v_res_358_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableMem___redArg(lean_object* v_cmp_359_, lean_object* v_m_360_, lean_object* v_a_361_){
_start:
{
uint8_t v___x_362_; 
v___x_362_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_359_, v_a_361_, v_m_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_363_, lean_object* v_m_364_, lean_object* v_a_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Std_ExtDTreeMap_instDecidableMem___redArg(v_cmp_363_, v_m_364_, v_a_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableMem(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_cmp_370_, lean_object* v_inst_371_, lean_object* v_m_372_, lean_object* v_a_373_){
_start:
{
uint8_t v___x_374_; 
v___x_374_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_370_, v_a_373_, v_m_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_375_, lean_object* v_00_u03b2_376_, lean_object* v_cmp_377_, lean_object* v_inst_378_, lean_object* v_m_379_, lean_object* v_a_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l_Std_ExtDTreeMap_instDecidableMem(v_00_u03b1_375_, v_00_u03b2_376_, v_cmp_377_, v_inst_378_, v_m_379_, v_a_380_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___redArg(lean_object* v_t_383_){
_start:
{
if (lean_obj_tag(v_t_383_) == 0)
{
lean_object* v_size_384_; 
v_size_384_ = lean_ctor_get(v_t_383_, 0);
lean_inc(v_size_384_);
return v_size_384_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_unsigned_to_nat(0u);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___redArg___boxed(lean_object* v_t_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_ExtDTreeMap_size___redArg(v_t_386_);
lean_dec(v_t_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_cmp_390_, lean_object* v_t_391_){
_start:
{
if (lean_obj_tag(v_t_391_) == 0)
{
lean_object* v_size_392_; 
v_size_392_ = lean_ctor_get(v_t_391_, 0);
lean_inc(v_size_392_);
return v_size_392_;
}
else
{
lean_object* v___x_393_; 
v___x_393_ = lean_unsigned_to_nat(0u);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_size___boxed(lean_object* v_00_u03b1_394_, lean_object* v_00_u03b2_395_, lean_object* v_cmp_396_, lean_object* v_t_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_ExtDTreeMap_size(v_00_u03b1_394_, v_00_u03b2_395_, v_cmp_396_, v_t_397_);
lean_dec(v_t_397_);
lean_dec_ref(v_cmp_396_);
return v_res_398_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_isEmpty___redArg(lean_object* v_t_399_){
_start:
{
if (lean_obj_tag(v_t_399_) == 0)
{
uint8_t v___x_400_; 
v___x_400_ = 0;
return v___x_400_;
}
else
{
uint8_t v___x_401_; 
v___x_401_ = 1;
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_isEmpty___redArg___boxed(lean_object* v_t_402_){
_start:
{
uint8_t v_res_403_; lean_object* v_r_404_; 
v_res_403_ = l_Std_ExtDTreeMap_isEmpty___redArg(v_t_402_);
lean_dec(v_t_402_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_isEmpty(lean_object* v_00_u03b1_405_, lean_object* v_00_u03b2_406_, lean_object* v_cmp_407_, lean_object* v_t_408_){
_start:
{
if (lean_obj_tag(v_t_408_) == 0)
{
uint8_t v___x_409_; 
v___x_409_ = 0;
return v___x_409_;
}
else
{
uint8_t v___x_410_; 
v___x_410_ = 1;
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_411_, lean_object* v_00_u03b2_412_, lean_object* v_cmp_413_, lean_object* v_t_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Std_ExtDTreeMap_isEmpty(v_00_u03b1_411_, v_00_u03b2_412_, v_cmp_413_, v_t_414_);
lean_dec(v_t_414_);
lean_dec_ref(v_cmp_413_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_erase___redArg(lean_object* v_cmp_417_, lean_object* v_t_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_417_, v_a_419_, v_t_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_erase(lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_cmp_423_, lean_object* v_inst_424_, lean_object* v_t_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_423_, v_a_426_, v_t_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x3f___redArg(lean_object* v_cmp_428_, lean_object* v_t_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_428_, v_t_429_, v_a_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x3f(lean_object* v_00_u03b1_432_, lean_object* v_00_u03b2_433_, lean_object* v_cmp_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_t_437_, lean_object* v_a_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_434_, v_t_437_, v_a_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get___redArg(lean_object* v_cmp_440_, lean_object* v_t_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_440_, v_t_441_, v_a_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get(lean_object* v_00_u03b1_444_, lean_object* v_00_u03b2_445_, lean_object* v_cmp_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_t_449_, lean_object* v_a_450_, lean_object* v_h_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_446_, v_t_449_, v_a_450_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___redArg(lean_object* v_cmp_453_, lean_object* v_t_454_, lean_object* v_a_455_, lean_object* v_inst_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_453_, v_t_454_, v_a_455_, v_inst_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21(lean_object* v_00_u03b1_458_, lean_object* v_00_u03b2_459_, lean_object* v_cmp_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_t_463_, lean_object* v_a_464_, lean_object* v_inst_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_460_, v_t_463_, v_a_464_, v_inst_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg(lean_object* v_cmp_467_, lean_object* v_t_468_, lean_object* v_a_469_, lean_object* v_fallback_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_467_, v_t_468_, v_a_469_, v_fallback_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg___boxed(lean_object* v_cmp_472_, lean_object* v_t_473_, lean_object* v_a_474_, lean_object* v_fallback_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_ExtDTreeMap_getD___redArg(v_cmp_472_, v_t_473_, v_a_474_, v_fallback_475_);
lean_dec(v_fallback_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD(lean_object* v_00_u03b1_477_, lean_object* v_00_u03b2_478_, lean_object* v_cmp_479_, lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_t_482_, lean_object* v_a_483_, lean_object* v_fallback_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_479_, v_t_482_, v_a_483_, v_fallback_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___boxed(lean_object* v_00_u03b1_486_, lean_object* v_00_u03b2_487_, lean_object* v_cmp_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_t_491_, lean_object* v_a_492_, lean_object* v_fallback_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_ExtDTreeMap_getD(v_00_u03b1_486_, v_00_u03b2_487_, v_cmp_488_, v_inst_489_, v_inst_490_, v_t_491_, v_a_492_, v_fallback_493_);
lean_dec(v_fallback_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f___redArg(lean_object* v_cmp_495_, lean_object* v_t_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_495_, v_t_496_, v_a_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f(lean_object* v_00_u03b1_499_, lean_object* v_00_u03b2_500_, lean_object* v_cmp_501_, lean_object* v_inst_502_, lean_object* v_t_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_501_, v_t_503_, v_a_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey___redArg(lean_object* v_cmp_506_, lean_object* v_t_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_506_, v_t_507_, v_a_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey(lean_object* v_00_u03b1_510_, lean_object* v_00_u03b2_511_, lean_object* v_cmp_512_, lean_object* v_inst_513_, lean_object* v_t_514_, lean_object* v_a_515_, lean_object* v_h_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_512_, v_t_514_, v_a_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___redArg(lean_object* v_cmp_518_, lean_object* v_inst_519_, lean_object* v_t_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_518_, v_t_520_, v_a_521_, v_inst_519_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21(lean_object* v_00_u03b1_523_, lean_object* v_00_u03b2_524_, lean_object* v_cmp_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_t_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_525_, v_t_528_, v_a_529_, v_inst_527_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___redArg(lean_object* v_cmp_531_, lean_object* v_t_532_, lean_object* v_a_533_, lean_object* v_fallback_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_531_, v_t_532_, v_a_533_, v_fallback_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_536_, lean_object* v_t_537_, lean_object* v_a_538_, lean_object* v_fallback_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_ExtDTreeMap_getKeyD___redArg(v_cmp_536_, v_t_537_, v_a_538_, v_fallback_539_);
lean_dec(v_fallback_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD(lean_object* v_00_u03b1_541_, lean_object* v_00_u03b2_542_, lean_object* v_cmp_543_, lean_object* v_inst_544_, lean_object* v_t_545_, lean_object* v_a_546_, lean_object* v_fallback_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_543_, v_t_545_, v_a_546_, v_fallback_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_549_, lean_object* v_00_u03b2_550_, lean_object* v_cmp_551_, lean_object* v_inst_552_, lean_object* v_t_553_, lean_object* v_a_554_, lean_object* v_fallback_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_ExtDTreeMap_getKeyD(v_00_u03b1_549_, v_00_u03b2_550_, v_cmp_551_, v_inst_552_, v_t_553_, v_a_554_, v_fallback_555_);
lean_dec(v_fallback_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___redArg(lean_object* v_t_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_ExtDTreeMap_minEntry_x3f___redArg(v_t_559_);
lean_dec(v_t_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f(lean_object* v_00_u03b1_561_, lean_object* v_00_u03b2_562_, lean_object* v_cmp_563_, lean_object* v_inst_564_, lean_object* v_t_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_567_, lean_object* v_00_u03b2_568_, lean_object* v_cmp_569_, lean_object* v_inst_570_, lean_object* v_t_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_ExtDTreeMap_minEntry_x3f(v_00_u03b1_567_, v_00_u03b2_568_, v_cmp_569_, v_inst_570_, v_t_571_);
lean_dec(v_t_571_);
lean_dec_ref(v_cmp_569_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___redArg(lean_object* v_t_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___redArg___boxed(lean_object* v_t_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_ExtDTreeMap_minEntry___redArg(v_t_575_);
lean_dec(v_t_575_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry(lean_object* v_00_u03b1_577_, lean_object* v_00_u03b2_578_, lean_object* v_cmp_579_, lean_object* v_inst_580_, lean_object* v_t_581_, lean_object* v_h_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___boxed(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_cmp_586_, lean_object* v_inst_587_, lean_object* v_t_588_, lean_object* v_h_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_ExtDTreeMap_minEntry(v_00_u03b1_584_, v_00_u03b2_585_, v_cmp_586_, v_inst_587_, v_t_588_, v_h_589_);
lean_dec(v_t_588_);
lean_dec_ref(v_cmp_586_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___redArg(lean_object* v_inst_591_, lean_object* v_t_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_591_, v_t_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_594_, lean_object* v_t_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_ExtDTreeMap_minEntry_x21___redArg(v_inst_594_, v_t_595_);
lean_dec(v_t_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21(lean_object* v_00_u03b1_597_, lean_object* v_00_u03b2_598_, lean_object* v_cmp_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_t_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_601_, v_t_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_604_, lean_object* v_00_u03b2_605_, lean_object* v_cmp_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_t_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_ExtDTreeMap_minEntry_x21(v_00_u03b1_604_, v_00_u03b2_605_, v_cmp_606_, v_inst_607_, v_inst_608_, v_t_609_);
lean_dec(v_t_609_);
lean_dec_ref(v_cmp_606_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___redArg(lean_object* v_t_611_, lean_object* v_fallback_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_611_, v_fallback_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___redArg___boxed(lean_object* v_t_614_, lean_object* v_fallback_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_ExtDTreeMap_minEntryD___redArg(v_t_614_, v_fallback_615_);
lean_dec_ref(v_fallback_615_);
lean_dec(v_t_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_cmp_619_, lean_object* v_inst_620_, lean_object* v_t_621_, lean_object* v_fallback_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_621_, v_fallback_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_624_, lean_object* v_00_u03b2_625_, lean_object* v_cmp_626_, lean_object* v_inst_627_, lean_object* v_t_628_, lean_object* v_fallback_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_ExtDTreeMap_minEntryD(v_00_u03b1_624_, v_00_u03b2_625_, v_cmp_626_, v_inst_627_, v_t_628_, v_fallback_629_);
lean_dec_ref(v_fallback_629_);
lean_dec(v_t_628_);
lean_dec_ref(v_cmp_626_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___redArg(lean_object* v_t_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_ExtDTreeMap_maxEntry_x3f___redArg(v_t_633_);
lean_dec(v_t_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_635_, lean_object* v_00_u03b2_636_, lean_object* v_cmp_637_, lean_object* v_inst_638_, lean_object* v_t_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_641_, lean_object* v_00_u03b2_642_, lean_object* v_cmp_643_, lean_object* v_inst_644_, lean_object* v_t_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_ExtDTreeMap_maxEntry_x3f(v_00_u03b1_641_, v_00_u03b2_642_, v_cmp_643_, v_inst_644_, v_t_645_);
lean_dec(v_t_645_);
lean_dec_ref(v_cmp_643_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___redArg(lean_object* v_t_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___redArg___boxed(lean_object* v_t_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_ExtDTreeMap_maxEntry___redArg(v_t_649_);
lean_dec(v_t_649_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry(lean_object* v_00_u03b1_651_, lean_object* v_00_u03b2_652_, lean_object* v_cmp_653_, lean_object* v_inst_654_, lean_object* v_t_655_, lean_object* v_h_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_658_, lean_object* v_00_u03b2_659_, lean_object* v_cmp_660_, lean_object* v_inst_661_, lean_object* v_t_662_, lean_object* v_h_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Std_ExtDTreeMap_maxEntry(v_00_u03b1_658_, v_00_u03b2_659_, v_cmp_660_, v_inst_661_, v_t_662_, v_h_663_);
lean_dec(v_t_662_);
lean_dec_ref(v_cmp_660_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___redArg(lean_object* v_inst_665_, lean_object* v_t_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_665_, v_t_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_668_, lean_object* v_t_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Std_ExtDTreeMap_maxEntry_x21___redArg(v_inst_668_, v_t_669_);
lean_dec(v_t_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21(lean_object* v_00_u03b1_671_, lean_object* v_00_u03b2_672_, lean_object* v_cmp_673_, lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_t_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_675_, v_t_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_cmp_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_t_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_ExtDTreeMap_maxEntry_x21(v_00_u03b1_678_, v_00_u03b2_679_, v_cmp_680_, v_inst_681_, v_inst_682_, v_t_683_);
lean_dec(v_t_683_);
lean_dec_ref(v_cmp_680_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___redArg(lean_object* v_t_685_, lean_object* v_fallback_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_685_, v_fallback_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_688_, lean_object* v_fallback_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_ExtDTreeMap_maxEntryD___redArg(v_t_688_, v_fallback_689_);
lean_dec_ref(v_fallback_689_);
lean_dec(v_t_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD(lean_object* v_00_u03b1_691_, lean_object* v_00_u03b2_692_, lean_object* v_cmp_693_, lean_object* v_inst_694_, lean_object* v_t_695_, lean_object* v_fallback_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_695_, v_fallback_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_cmp_700_, lean_object* v_inst_701_, lean_object* v_t_702_, lean_object* v_fallback_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_ExtDTreeMap_maxEntryD(v_00_u03b1_698_, v_00_u03b2_699_, v_cmp_700_, v_inst_701_, v_t_702_, v_fallback_703_);
lean_dec_ref(v_fallback_703_);
lean_dec(v_t_702_);
lean_dec_ref(v_cmp_700_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___redArg(lean_object* v_t_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Std_ExtDTreeMap_minKey_x3f___redArg(v_t_707_);
lean_dec(v_t_707_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f(lean_object* v_00_u03b1_709_, lean_object* v_00_u03b2_710_, lean_object* v_cmp_711_, lean_object* v_inst_712_, lean_object* v_t_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_715_, lean_object* v_00_u03b2_716_, lean_object* v_cmp_717_, lean_object* v_inst_718_, lean_object* v_t_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_ExtDTreeMap_minKey_x3f(v_00_u03b1_715_, v_00_u03b2_716_, v_cmp_717_, v_inst_718_, v_t_719_);
lean_dec(v_t_719_);
lean_dec_ref(v_cmp_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___redArg(lean_object* v_t_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___redArg___boxed(lean_object* v_t_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Std_ExtDTreeMap_minKey___redArg(v_t_723_);
lean_dec(v_t_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey(lean_object* v_00_u03b1_725_, lean_object* v_00_u03b2_726_, lean_object* v_cmp_727_, lean_object* v_inst_728_, lean_object* v_t_729_, lean_object* v_h_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___boxed(lean_object* v_00_u03b1_732_, lean_object* v_00_u03b2_733_, lean_object* v_cmp_734_, lean_object* v_inst_735_, lean_object* v_t_736_, lean_object* v_h_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_ExtDTreeMap_minKey(v_00_u03b1_732_, v_00_u03b2_733_, v_cmp_734_, v_inst_735_, v_t_736_, v_h_737_);
lean_dec(v_t_736_);
lean_dec_ref(v_cmp_734_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___redArg(lean_object* v_inst_739_, lean_object* v_t_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_739_, v_t_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_742_, lean_object* v_t_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_ExtDTreeMap_minKey_x21___redArg(v_inst_742_, v_t_743_);
lean_dec(v_t_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21(lean_object* v_00_u03b1_745_, lean_object* v_00_u03b2_746_, lean_object* v_cmp_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_t_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_749_, v_t_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_752_, lean_object* v_00_u03b2_753_, lean_object* v_cmp_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_t_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_ExtDTreeMap_minKey_x21(v_00_u03b1_752_, v_00_u03b2_753_, v_cmp_754_, v_inst_755_, v_inst_756_, v_t_757_);
lean_dec(v_t_757_);
lean_dec_ref(v_cmp_754_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___redArg(lean_object* v_t_759_, lean_object* v_fallback_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_759_, v_fallback_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___redArg___boxed(lean_object* v_t_762_, lean_object* v_fallback_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_ExtDTreeMap_minKeyD___redArg(v_t_762_, v_fallback_763_);
lean_dec(v_fallback_763_);
lean_dec(v_t_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD(lean_object* v_00_u03b1_765_, lean_object* v_00_u03b2_766_, lean_object* v_cmp_767_, lean_object* v_inst_768_, lean_object* v_t_769_, lean_object* v_fallback_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_769_, v_fallback_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_cmp_774_, lean_object* v_inst_775_, lean_object* v_t_776_, lean_object* v_fallback_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_ExtDTreeMap_minKeyD(v_00_u03b1_772_, v_00_u03b2_773_, v_cmp_774_, v_inst_775_, v_t_776_, v_fallback_777_);
lean_dec(v_fallback_777_);
lean_dec(v_t_776_);
lean_dec_ref(v_cmp_774_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___redArg(lean_object* v_t_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Std_ExtDTreeMap_maxKey_x3f___redArg(v_t_781_);
lean_dec(v_t_781_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f(lean_object* v_00_u03b1_783_, lean_object* v_00_u03b2_784_, lean_object* v_cmp_785_, lean_object* v_inst_786_, lean_object* v_t_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_789_, lean_object* v_00_u03b2_790_, lean_object* v_cmp_791_, lean_object* v_inst_792_, lean_object* v_t_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_ExtDTreeMap_maxKey_x3f(v_00_u03b1_789_, v_00_u03b2_790_, v_cmp_791_, v_inst_792_, v_t_793_);
lean_dec(v_t_793_);
lean_dec_ref(v_cmp_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___redArg(lean_object* v_t_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___redArg___boxed(lean_object* v_t_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_ExtDTreeMap_maxKey___redArg(v_t_797_);
lean_dec(v_t_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey(lean_object* v_00_u03b1_799_, lean_object* v_00_u03b2_800_, lean_object* v_cmp_801_, lean_object* v_inst_802_, lean_object* v_t_803_, lean_object* v_h_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___boxed(lean_object* v_00_u03b1_806_, lean_object* v_00_u03b2_807_, lean_object* v_cmp_808_, lean_object* v_inst_809_, lean_object* v_t_810_, lean_object* v_h_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_ExtDTreeMap_maxKey(v_00_u03b1_806_, v_00_u03b2_807_, v_cmp_808_, v_inst_809_, v_t_810_, v_h_811_);
lean_dec(v_t_810_);
lean_dec_ref(v_cmp_808_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___redArg(lean_object* v_inst_813_, lean_object* v_t_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_813_, v_t_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_816_, lean_object* v_t_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_ExtDTreeMap_maxKey_x21___redArg(v_inst_816_, v_t_817_);
lean_dec(v_t_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21(lean_object* v_00_u03b1_819_, lean_object* v_00_u03b2_820_, lean_object* v_cmp_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_t_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_823_, v_t_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_cmp_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_t_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_ExtDTreeMap_maxKey_x21(v_00_u03b1_826_, v_00_u03b2_827_, v_cmp_828_, v_inst_829_, v_inst_830_, v_t_831_);
lean_dec(v_t_831_);
lean_dec_ref(v_cmp_828_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___redArg(lean_object* v_t_833_, lean_object* v_fallback_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_833_, v_fallback_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_836_, lean_object* v_fallback_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_ExtDTreeMap_maxKeyD___redArg(v_t_836_, v_fallback_837_);
lean_dec(v_fallback_837_);
lean_dec(v_t_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD(lean_object* v_00_u03b1_839_, lean_object* v_00_u03b2_840_, lean_object* v_cmp_841_, lean_object* v_inst_842_, lean_object* v_t_843_, lean_object* v_fallback_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_843_, v_fallback_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_846_, lean_object* v_00_u03b2_847_, lean_object* v_cmp_848_, lean_object* v_inst_849_, lean_object* v_t_850_, lean_object* v_fallback_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_ExtDTreeMap_maxKeyD(v_00_u03b1_846_, v_00_u03b2_847_, v_cmp_848_, v_inst_849_, v_t_850_, v_fallback_851_);
lean_dec(v_fallback_851_);
lean_dec(v_t_850_);
lean_dec_ref(v_cmp_848_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_853_, lean_object* v_n_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_853_, v_n_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_856_, lean_object* v_n_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(v_t_856_, v_n_857_);
lean_dec(v_t_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_859_, lean_object* v_00_u03b2_860_, lean_object* v_cmp_861_, lean_object* v_inst_862_, lean_object* v_t_863_, lean_object* v_n_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_863_, v_n_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_866_, lean_object* v_00_u03b2_867_, lean_object* v_cmp_868_, lean_object* v_inst_869_, lean_object* v_t_870_, lean_object* v_n_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_ExtDTreeMap_entryAtIdx_x3f(v_00_u03b1_866_, v_00_u03b2_867_, v_cmp_868_, v_inst_869_, v_t_870_, v_n_871_);
lean_dec(v_t_870_);
lean_dec_ref(v_cmp_868_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___redArg(lean_object* v_t_873_, lean_object* v_n_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_873_, v_n_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_876_, lean_object* v_n_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Std_ExtDTreeMap_entryAtIdx___redArg(v_t_876_, v_n_877_);
lean_dec(v_t_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx(lean_object* v_00_u03b1_879_, lean_object* v_00_u03b2_880_, lean_object* v_cmp_881_, lean_object* v_inst_882_, lean_object* v_t_883_, lean_object* v_n_884_, lean_object* v_h_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_883_, v_n_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_887_, lean_object* v_00_u03b2_888_, lean_object* v_cmp_889_, lean_object* v_inst_890_, lean_object* v_t_891_, lean_object* v_n_892_, lean_object* v_h_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Std_ExtDTreeMap_entryAtIdx(v_00_u03b1_887_, v_00_u03b2_888_, v_cmp_889_, v_inst_890_, v_t_891_, v_n_892_, v_h_893_);
lean_dec(v_t_891_);
lean_dec_ref(v_cmp_889_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_895_, lean_object* v_t_896_, lean_object* v_n_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_895_, v_t_896_, v_n_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_899_, lean_object* v_t_900_, lean_object* v_n_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(v_inst_899_, v_t_900_, v_n_901_);
lean_dec(v_t_900_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_903_, lean_object* v_00_u03b2_904_, lean_object* v_cmp_905_, lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v_t_908_, lean_object* v_n_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_907_, v_t_908_, v_n_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_911_, lean_object* v_00_u03b2_912_, lean_object* v_cmp_913_, lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_t_916_, lean_object* v_n_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Std_ExtDTreeMap_entryAtIdx_x21(v_00_u03b1_911_, v_00_u03b2_912_, v_cmp_913_, v_inst_914_, v_inst_915_, v_t_916_, v_n_917_);
lean_dec(v_t_916_);
lean_dec_ref(v_cmp_913_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___redArg(lean_object* v_t_919_, lean_object* v_n_920_, lean_object* v_fallback_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_919_, v_n_920_, v_fallback_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_923_, lean_object* v_n_924_, lean_object* v_fallback_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Std_ExtDTreeMap_entryAtIdxD___redArg(v_t_923_, v_n_924_, v_fallback_925_);
lean_dec_ref(v_fallback_925_);
lean_dec(v_t_923_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD(lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v_cmp_929_, lean_object* v_inst_930_, lean_object* v_t_931_, lean_object* v_n_932_, lean_object* v_fallback_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_931_, v_n_932_, v_fallback_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_cmp_937_, lean_object* v_inst_938_, lean_object* v_t_939_, lean_object* v_n_940_, lean_object* v_fallback_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_ExtDTreeMap_entryAtIdxD(v_00_u03b1_935_, v_00_u03b2_936_, v_cmp_937_, v_inst_938_, v_t_939_, v_n_940_, v_fallback_941_);
lean_dec_ref(v_fallback_941_);
lean_dec(v_t_939_);
lean_dec_ref(v_cmp_937_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_943_, lean_object* v_n_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_943_, v_n_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_946_, lean_object* v_n_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(v_t_946_, v_n_947_);
lean_dec(v_t_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_949_, lean_object* v_00_u03b2_950_, lean_object* v_cmp_951_, lean_object* v_inst_952_, lean_object* v_t_953_, lean_object* v_n_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_953_, v_n_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_956_, lean_object* v_00_u03b2_957_, lean_object* v_cmp_958_, lean_object* v_inst_959_, lean_object* v_t_960_, lean_object* v_n_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Std_ExtDTreeMap_keyAtIdx_x3f(v_00_u03b1_956_, v_00_u03b2_957_, v_cmp_958_, v_inst_959_, v_t_960_, v_n_961_);
lean_dec(v_t_960_);
lean_dec_ref(v_cmp_958_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___redArg(lean_object* v_t_963_, lean_object* v_n_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_963_, v_n_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_966_, lean_object* v_n_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Std_ExtDTreeMap_keyAtIdx___redArg(v_t_966_, v_n_967_);
lean_dec(v_t_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_cmp_971_, lean_object* v_inst_972_, lean_object* v_t_973_, lean_object* v_n_974_, lean_object* v_h_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_973_, v_n_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_977_, lean_object* v_00_u03b2_978_, lean_object* v_cmp_979_, lean_object* v_inst_980_, lean_object* v_t_981_, lean_object* v_n_982_, lean_object* v_h_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Std_ExtDTreeMap_keyAtIdx(v_00_u03b1_977_, v_00_u03b2_978_, v_cmp_979_, v_inst_980_, v_t_981_, v_n_982_, v_h_983_);
lean_dec(v_t_981_);
lean_dec_ref(v_cmp_979_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_985_, lean_object* v_t_986_, lean_object* v_n_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_985_, v_t_986_, v_n_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_989_, lean_object* v_t_990_, lean_object* v_n_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(v_inst_989_, v_t_990_, v_n_991_);
lean_dec(v_t_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_993_, lean_object* v_00_u03b2_994_, lean_object* v_cmp_995_, lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_t_998_, lean_object* v_n_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_997_, v_t_998_, v_n_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_1001_, lean_object* v_00_u03b2_1002_, lean_object* v_cmp_1003_, lean_object* v_inst_1004_, lean_object* v_inst_1005_, lean_object* v_t_1006_, lean_object* v_n_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Std_ExtDTreeMap_keyAtIdx_x21(v_00_u03b1_1001_, v_00_u03b2_1002_, v_cmp_1003_, v_inst_1004_, v_inst_1005_, v_t_1006_, v_n_1007_);
lean_dec(v_t_1006_);
lean_dec_ref(v_cmp_1003_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___redArg(lean_object* v_t_1009_, lean_object* v_n_1010_, lean_object* v_fallback_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1009_, v_n_1010_, v_fallback_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_1013_, lean_object* v_n_1014_, lean_object* v_fallback_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Std_ExtDTreeMap_keyAtIdxD___redArg(v_t_1013_, v_n_1014_, v_fallback_1015_);
lean_dec(v_fallback_1015_);
lean_dec(v_t_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD(lean_object* v_00_u03b1_1017_, lean_object* v_00_u03b2_1018_, lean_object* v_cmp_1019_, lean_object* v_inst_1020_, lean_object* v_t_1021_, lean_object* v_n_1022_, lean_object* v_fallback_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1021_, v_n_1022_, v_fallback_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_cmp_1027_, lean_object* v_inst_1028_, lean_object* v_t_1029_, lean_object* v_n_1030_, lean_object* v_fallback_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Std_ExtDTreeMap_keyAtIdxD(v_00_u03b1_1025_, v_00_u03b2_1026_, v_cmp_1027_, v_inst_1028_, v_t_1029_, v_n_1030_, v_fallback_1031_);
lean_dec(v_fallback_1031_);
lean_dec(v_t_1029_);
lean_dec_ref(v_cmp_1027_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1033_, lean_object* v_t_1034_, lean_object* v_k_1035_){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_box(0);
v___x_1037_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1033_, v_k_1035_, v___x_1036_, v_t_1034_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1038_, lean_object* v_00_u03b2_1039_, lean_object* v_cmp_1040_, lean_object* v_inst_1041_, lean_object* v_t_1042_, lean_object* v_k_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1040_, v_k_1043_, v___x_1044_, v_t_1042_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1046_, lean_object* v_t_1047_, lean_object* v_k_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1046_, v_k_1048_, v___x_1049_, v_t_1047_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1051_, lean_object* v_00_u03b2_1052_, lean_object* v_cmp_1053_, lean_object* v_inst_1054_, lean_object* v_t_1055_, lean_object* v_k_1056_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1053_, v_k_1056_, v___x_1057_, v_t_1055_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1059_, lean_object* v_t_1060_, lean_object* v_k_1061_){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_box(0);
v___x_1063_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1059_, v_k_1061_, v___x_1062_, v_t_1060_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_cmp_1066_, lean_object* v_inst_1067_, lean_object* v_t_1068_, lean_object* v_k_1069_){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_box(0);
v___x_1071_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1066_, v_k_1069_, v___x_1070_, v_t_1068_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1072_, lean_object* v_t_1073_, lean_object* v_k_1074_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_box(0);
v___x_1076_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1072_, v_k_1074_, v___x_1075_, v_t_1073_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1077_, lean_object* v_00_u03b2_1078_, lean_object* v_cmp_1079_, lean_object* v_inst_1080_, lean_object* v_t_1081_, lean_object* v_k_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_box(0);
v___x_1084_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1079_, v_k_1082_, v___x_1083_, v_t_1081_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE___redArg(lean_object* v_cmp_1085_, lean_object* v_t_1086_, lean_object* v_k_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_1085_, v_k_1087_, v_t_1086_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE(lean_object* v_00_u03b1_1089_, lean_object* v_00_u03b2_1090_, lean_object* v_cmp_1091_, lean_object* v_inst_1092_, lean_object* v_t_1093_, lean_object* v_k_1094_, lean_object* v_h_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_1091_, v_k_1094_, v_t_1093_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT___redArg(lean_object* v_cmp_1097_, lean_object* v_t_1098_, lean_object* v_k_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_1097_, v_k_1099_, v_t_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT(lean_object* v_00_u03b1_1101_, lean_object* v_00_u03b2_1102_, lean_object* v_cmp_1103_, lean_object* v_inst_1104_, lean_object* v_t_1105_, lean_object* v_k_1106_, lean_object* v_h_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_1103_, v_k_1106_, v_t_1105_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE___redArg(lean_object* v_cmp_1109_, lean_object* v_t_1110_, lean_object* v_k_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_1109_, v_k_1111_, v_t_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE(lean_object* v_00_u03b1_1113_, lean_object* v_00_u03b2_1114_, lean_object* v_cmp_1115_, lean_object* v_inst_1116_, lean_object* v_t_1117_, lean_object* v_k_1118_, lean_object* v_h_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_1115_, v_k_1118_, v_t_1117_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT___redArg(lean_object* v_cmp_1121_, lean_object* v_t_1122_, lean_object* v_k_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_1121_, v_k_1123_, v_t_1122_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT(lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_cmp_1127_, lean_object* v_inst_1128_, lean_object* v_t_1129_, lean_object* v_k_1130_, lean_object* v_h_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_1127_, v_k_1130_, v_t_1129_);
return v___x_1132_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1136_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1137_ = lean_unsigned_to_nat(14u);
v___x_1138_ = lean_unsigned_to_nat(22u);
v___x_1139_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1140_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1141_ = l_mkPanicMessageWithDecl(v___x_1140_, v___x_1139_, v___x_1138_, v___x_1137_, v___x_1136_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1142_, lean_object* v_inst_1143_, lean_object* v_t_1144_, lean_object* v_k_1145_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_box(0);
v___x_1147_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1142_, v_k_1145_, v___x_1146_, v_t_1144_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1149_ = l_panic___redArg(v_inst_1143_, v___x_1148_);
return v___x_1149_;
}
else
{
lean_object* v_val_1150_; 
lean_dec_ref(v_inst_1143_);
v_val_1150_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_val_1150_);
lean_dec_ref(v___x_1147_);
return v_val_1150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1151_, lean_object* v_00_u03b2_1152_, lean_object* v_cmp_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_t_1156_, lean_object* v_k_1157_){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_box(0);
v___x_1159_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1153_, v_k_1157_, v___x_1158_, v_t_1156_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1161_ = l_panic___redArg(v_inst_1155_, v___x_1160_);
return v___x_1161_;
}
else
{
lean_object* v_val_1162_; 
lean_dec_ref(v_inst_1155_);
v_val_1162_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_val_1162_);
lean_dec_ref(v___x_1159_);
return v_val_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1163_, lean_object* v_inst_1164_, lean_object* v_t_1165_, lean_object* v_k_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1163_, v_k_1166_, v___x_1167_, v_t_1165_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1170_ = l_panic___redArg(v_inst_1164_, v___x_1169_);
return v___x_1170_;
}
else
{
lean_object* v_val_1171_; 
lean_dec_ref(v_inst_1164_);
v_val_1171_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_val_1171_);
lean_dec_ref(v___x_1168_);
return v_val_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_cmp_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_t_1177_, lean_object* v_k_1178_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_box(0);
v___x_1180_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1174_, v_k_1178_, v___x_1179_, v_t_1177_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1182_ = l_panic___redArg(v_inst_1176_, v___x_1181_);
return v___x_1182_;
}
else
{
lean_object* v_val_1183_; 
lean_dec_ref(v_inst_1176_);
v_val_1183_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_val_1183_);
lean_dec_ref(v___x_1180_);
return v_val_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1184_, lean_object* v_inst_1185_, lean_object* v_t_1186_, lean_object* v_k_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_box(0);
v___x_1189_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1184_, v_k_1187_, v___x_1188_, v_t_1186_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1191_ = l_panic___redArg(v_inst_1185_, v___x_1190_);
return v___x_1191_;
}
else
{
lean_object* v_val_1192_; 
lean_dec_ref(v_inst_1185_);
v_val_1192_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_val_1192_);
lean_dec_ref(v___x_1189_);
return v_val_1192_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1193_, lean_object* v_00_u03b2_1194_, lean_object* v_cmp_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_t_1198_, lean_object* v_k_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_box(0);
v___x_1201_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1195_, v_k_1199_, v___x_1200_, v_t_1198_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1203_ = l_panic___redArg(v_inst_1197_, v___x_1202_);
return v___x_1203_;
}
else
{
lean_object* v_val_1204_; 
lean_dec_ref(v_inst_1197_);
v_val_1204_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_val_1204_);
lean_dec_ref(v___x_1201_);
return v_val_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1205_, lean_object* v_inst_1206_, lean_object* v_t_1207_, lean_object* v_k_1208_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_box(0);
v___x_1210_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1205_, v_k_1208_, v___x_1209_, v_t_1207_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1212_ = l_panic___redArg(v_inst_1206_, v___x_1211_);
return v___x_1212_;
}
else
{
lean_object* v_val_1213_; 
lean_dec_ref(v_inst_1206_);
v_val_1213_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_val_1213_);
lean_dec_ref(v___x_1210_);
return v_val_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1214_, lean_object* v_00_u03b2_1215_, lean_object* v_cmp_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_t_1219_, lean_object* v_k_1220_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1216_, v_k_1220_, v___x_1221_, v_t_1219_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1224_ = l_panic___redArg(v_inst_1218_, v___x_1223_);
return v___x_1224_;
}
else
{
lean_object* v_val_1225_; 
lean_dec_ref(v_inst_1218_);
v_val_1225_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_val_1225_);
lean_dec_ref(v___x_1222_);
return v_val_1225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___redArg(lean_object* v_cmp_1226_, lean_object* v_t_1227_, lean_object* v_k_1228_, lean_object* v_fallback_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_box(0);
v___x_1231_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1226_, v_k_1228_, v___x_1230_, v_t_1227_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_inc_ref(v_fallback_1229_);
return v_fallback_1229_;
}
else
{
lean_object* v_val_1232_; 
v_val_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_val_1232_);
lean_dec_ref(v___x_1231_);
return v_val_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1233_, lean_object* v_t_1234_, lean_object* v_k_1235_, lean_object* v_fallback_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Std_ExtDTreeMap_getEntryGED___redArg(v_cmp_1233_, v_t_1234_, v_k_1235_, v_fallback_1236_);
lean_dec_ref(v_fallback_1236_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED(lean_object* v_00_u03b1_1238_, lean_object* v_00_u03b2_1239_, lean_object* v_cmp_1240_, lean_object* v_inst_1241_, lean_object* v_t_1242_, lean_object* v_k_1243_, lean_object* v_fallback_1244_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_box(0);
v___x_1246_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1240_, v_k_1243_, v___x_1245_, v_t_1242_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_inc_ref(v_fallback_1244_);
return v_fallback_1244_;
}
else
{
lean_object* v_val_1247_; 
v_val_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_val_1247_);
lean_dec_ref(v___x_1246_);
return v_val_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_00_u03b2_1249_, lean_object* v_cmp_1250_, lean_object* v_inst_1251_, lean_object* v_t_1252_, lean_object* v_k_1253_, lean_object* v_fallback_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Std_ExtDTreeMap_getEntryGED(v_00_u03b1_1248_, v_00_u03b2_1249_, v_cmp_1250_, v_inst_1251_, v_t_1252_, v_k_1253_, v_fallback_1254_);
lean_dec_ref(v_fallback_1254_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1256_, lean_object* v_t_1257_, lean_object* v_k_1258_, lean_object* v_fallback_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_box(0);
v___x_1261_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1256_, v_k_1258_, v___x_1260_, v_t_1257_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_inc_ref(v_fallback_1259_);
return v_fallback_1259_;
}
else
{
lean_object* v_val_1262_; 
v_val_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_val_1262_);
lean_dec_ref(v___x_1261_);
return v_val_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1263_, lean_object* v_t_1264_, lean_object* v_k_1265_, lean_object* v_fallback_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_ExtDTreeMap_getEntryGTD___redArg(v_cmp_1263_, v_t_1264_, v_k_1265_, v_fallback_1266_);
lean_dec_ref(v_fallback_1266_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD(lean_object* v_00_u03b1_1268_, lean_object* v_00_u03b2_1269_, lean_object* v_cmp_1270_, lean_object* v_inst_1271_, lean_object* v_t_1272_, lean_object* v_k_1273_, lean_object* v_fallback_1274_){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_box(0);
v___x_1276_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1270_, v_k_1273_, v___x_1275_, v_t_1272_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_inc_ref(v_fallback_1274_);
return v_fallback_1274_;
}
else
{
lean_object* v_val_1277_; 
v_val_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_val_1277_);
lean_dec_ref(v___x_1276_);
return v_val_1277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1278_, lean_object* v_00_u03b2_1279_, lean_object* v_cmp_1280_, lean_object* v_inst_1281_, lean_object* v_t_1282_, lean_object* v_k_1283_, lean_object* v_fallback_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Std_ExtDTreeMap_getEntryGTD(v_00_u03b1_1278_, v_00_u03b2_1279_, v_cmp_1280_, v_inst_1281_, v_t_1282_, v_k_1283_, v_fallback_1284_);
lean_dec_ref(v_fallback_1284_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___redArg(lean_object* v_cmp_1286_, lean_object* v_t_1287_, lean_object* v_k_1288_, lean_object* v_fallback_1289_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_box(0);
v___x_1291_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1286_, v_k_1288_, v___x_1290_, v_t_1287_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_inc_ref(v_fallback_1289_);
return v_fallback_1289_;
}
else
{
lean_object* v_val_1292_; 
v_val_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_val_1292_);
lean_dec_ref(v___x_1291_);
return v_val_1292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1293_, lean_object* v_t_1294_, lean_object* v_k_1295_, lean_object* v_fallback_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Std_ExtDTreeMap_getEntryLED___redArg(v_cmp_1293_, v_t_1294_, v_k_1295_, v_fallback_1296_);
lean_dec_ref(v_fallback_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED(lean_object* v_00_u03b1_1298_, lean_object* v_00_u03b2_1299_, lean_object* v_cmp_1300_, lean_object* v_inst_1301_, lean_object* v_t_1302_, lean_object* v_k_1303_, lean_object* v_fallback_1304_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_box(0);
v___x_1306_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1300_, v_k_1303_, v___x_1305_, v_t_1302_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_inc_ref(v_fallback_1304_);
return v_fallback_1304_;
}
else
{
lean_object* v_val_1307_; 
v_val_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_val_1307_);
lean_dec_ref(v___x_1306_);
return v_val_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1308_, lean_object* v_00_u03b2_1309_, lean_object* v_cmp_1310_, lean_object* v_inst_1311_, lean_object* v_t_1312_, lean_object* v_k_1313_, lean_object* v_fallback_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Std_ExtDTreeMap_getEntryLED(v_00_u03b1_1308_, v_00_u03b2_1309_, v_cmp_1310_, v_inst_1311_, v_t_1312_, v_k_1313_, v_fallback_1314_);
lean_dec_ref(v_fallback_1314_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1316_, lean_object* v_t_1317_, lean_object* v_k_1318_, lean_object* v_fallback_1319_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_box(0);
v___x_1321_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1316_, v_k_1318_, v___x_1320_, v_t_1317_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_inc_ref(v_fallback_1319_);
return v_fallback_1319_;
}
else
{
lean_object* v_val_1322_; 
v_val_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_val_1322_);
lean_dec_ref(v___x_1321_);
return v_val_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1323_, lean_object* v_t_1324_, lean_object* v_k_1325_, lean_object* v_fallback_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Std_ExtDTreeMap_getEntryLTD___redArg(v_cmp_1323_, v_t_1324_, v_k_1325_, v_fallback_1326_);
lean_dec_ref(v_fallback_1326_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD(lean_object* v_00_u03b1_1328_, lean_object* v_00_u03b2_1329_, lean_object* v_cmp_1330_, lean_object* v_inst_1331_, lean_object* v_t_1332_, lean_object* v_k_1333_, lean_object* v_fallback_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_box(0);
v___x_1336_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1330_, v_k_1333_, v___x_1335_, v_t_1332_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_inc_ref(v_fallback_1334_);
return v_fallback_1334_;
}
else
{
lean_object* v_val_1337_; 
v_val_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_val_1337_);
lean_dec_ref(v___x_1336_);
return v_val_1337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1338_, lean_object* v_00_u03b2_1339_, lean_object* v_cmp_1340_, lean_object* v_inst_1341_, lean_object* v_t_1342_, lean_object* v_k_1343_, lean_object* v_fallback_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Std_ExtDTreeMap_getEntryLTD(v_00_u03b1_1338_, v_00_u03b2_1339_, v_cmp_1340_, v_inst_1341_, v_t_1342_, v_k_1343_, v_fallback_1344_);
lean_dec_ref(v_fallback_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1346_, lean_object* v_t_1347_, lean_object* v_k_1348_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_box(0);
v___x_1350_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1346_, v_k_1348_, v___x_1349_, v_t_1347_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1351_, lean_object* v_00_u03b2_1352_, lean_object* v_cmp_1353_, lean_object* v_inst_1354_, lean_object* v_t_1355_, lean_object* v_k_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_box(0);
v___x_1358_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1353_, v_k_1356_, v___x_1357_, v_t_1355_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1359_, lean_object* v_t_1360_, lean_object* v_k_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1359_, v_k_1361_, v___x_1362_, v_t_1360_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1364_, lean_object* v_00_u03b2_1365_, lean_object* v_cmp_1366_, lean_object* v_inst_1367_, lean_object* v_t_1368_, lean_object* v_k_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_box(0);
v___x_1371_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1366_, v_k_1369_, v___x_1370_, v_t_1368_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1372_, lean_object* v_t_1373_, lean_object* v_k_1374_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1372_, v_k_1374_, v___x_1375_, v_t_1373_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1377_, lean_object* v_00_u03b2_1378_, lean_object* v_cmp_1379_, lean_object* v_inst_1380_, lean_object* v_t_1381_, lean_object* v_k_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1379_, v_k_1382_, v___x_1383_, v_t_1381_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1385_, lean_object* v_t_1386_, lean_object* v_k_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_box(0);
v___x_1389_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1385_, v_k_1387_, v___x_1388_, v_t_1386_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1390_, lean_object* v_00_u03b2_1391_, lean_object* v_cmp_1392_, lean_object* v_inst_1393_, lean_object* v_t_1394_, lean_object* v_k_1395_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_box(0);
v___x_1397_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1392_, v_k_1395_, v___x_1396_, v_t_1394_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE___redArg(lean_object* v_cmp_1398_, lean_object* v_t_1399_, lean_object* v_k_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1398_, v_k_1400_, v_t_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE(lean_object* v_00_u03b1_1402_, lean_object* v_00_u03b2_1403_, lean_object* v_cmp_1404_, lean_object* v_inst_1405_, lean_object* v_t_1406_, lean_object* v_k_1407_, lean_object* v_h_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1404_, v_k_1407_, v_t_1406_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT___redArg(lean_object* v_cmp_1410_, lean_object* v_t_1411_, lean_object* v_k_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1410_, v_k_1412_, v_t_1411_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT(lean_object* v_00_u03b1_1414_, lean_object* v_00_u03b2_1415_, lean_object* v_cmp_1416_, lean_object* v_inst_1417_, lean_object* v_t_1418_, lean_object* v_k_1419_, lean_object* v_h_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1416_, v_k_1419_, v_t_1418_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE___redArg(lean_object* v_cmp_1422_, lean_object* v_t_1423_, lean_object* v_k_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1422_, v_k_1424_, v_t_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE(lean_object* v_00_u03b1_1426_, lean_object* v_00_u03b2_1427_, lean_object* v_cmp_1428_, lean_object* v_inst_1429_, lean_object* v_t_1430_, lean_object* v_k_1431_, lean_object* v_h_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1428_, v_k_1431_, v_t_1430_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT___redArg(lean_object* v_cmp_1434_, lean_object* v_t_1435_, lean_object* v_k_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1434_, v_k_1436_, v_t_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT(lean_object* v_00_u03b1_1438_, lean_object* v_00_u03b2_1439_, lean_object* v_cmp_1440_, lean_object* v_inst_1441_, lean_object* v_t_1442_, lean_object* v_k_1443_, lean_object* v_h_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1440_, v_k_1443_, v_t_1442_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1446_, lean_object* v_inst_1447_, lean_object* v_t_1448_, lean_object* v_k_1449_){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_box(0);
v___x_1451_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1446_, v_k_1449_, v___x_1450_, v_t_1448_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1453_ = l_panic___redArg(v_inst_1447_, v___x_1452_);
return v___x_1453_;
}
else
{
lean_object* v_val_1454_; 
lean_dec(v_inst_1447_);
v_val_1454_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_val_1454_);
lean_dec_ref(v___x_1451_);
return v_val_1454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1455_, lean_object* v_00_u03b2_1456_, lean_object* v_cmp_1457_, lean_object* v_inst_1458_, lean_object* v_inst_1459_, lean_object* v_t_1460_, lean_object* v_k_1461_){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_box(0);
v___x_1463_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1457_, v_k_1461_, v___x_1462_, v_t_1460_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1465_ = l_panic___redArg(v_inst_1459_, v___x_1464_);
return v___x_1465_;
}
else
{
lean_object* v_val_1466_; 
lean_dec(v_inst_1459_);
v_val_1466_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_val_1466_);
lean_dec_ref(v___x_1463_);
return v_val_1466_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1467_, lean_object* v_inst_1468_, lean_object* v_t_1469_, lean_object* v_k_1470_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1467_, v_k_1470_, v___x_1471_, v_t_1469_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1474_ = l_panic___redArg(v_inst_1468_, v___x_1473_);
return v___x_1474_;
}
else
{
lean_object* v_val_1475_; 
lean_dec(v_inst_1468_);
v_val_1475_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_val_1475_);
lean_dec_ref(v___x_1472_);
return v_val_1475_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1476_, lean_object* v_00_u03b2_1477_, lean_object* v_cmp_1478_, lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_t_1481_, lean_object* v_k_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_box(0);
v___x_1484_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1478_, v_k_1482_, v___x_1483_, v_t_1481_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1486_ = l_panic___redArg(v_inst_1480_, v___x_1485_);
return v___x_1486_;
}
else
{
lean_object* v_val_1487_; 
lean_dec(v_inst_1480_);
v_val_1487_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_val_1487_);
lean_dec_ref(v___x_1484_);
return v_val_1487_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1488_, lean_object* v_inst_1489_, lean_object* v_t_1490_, lean_object* v_k_1491_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = lean_box(0);
v___x_1493_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1488_, v_k_1491_, v___x_1492_, v_t_1490_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1495_ = l_panic___redArg(v_inst_1489_, v___x_1494_);
return v___x_1495_;
}
else
{
lean_object* v_val_1496_; 
lean_dec(v_inst_1489_);
v_val_1496_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_val_1496_);
lean_dec_ref(v___x_1493_);
return v_val_1496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1497_, lean_object* v_00_u03b2_1498_, lean_object* v_cmp_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_t_1502_, lean_object* v_k_1503_){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_box(0);
v___x_1505_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1499_, v_k_1503_, v___x_1504_, v_t_1502_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1507_ = l_panic___redArg(v_inst_1501_, v___x_1506_);
return v___x_1507_;
}
else
{
lean_object* v_val_1508_; 
lean_dec(v_inst_1501_);
v_val_1508_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_val_1508_);
lean_dec_ref(v___x_1505_);
return v_val_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1509_, lean_object* v_inst_1510_, lean_object* v_t_1511_, lean_object* v_k_1512_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_box(0);
v___x_1514_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1509_, v_k_1512_, v___x_1513_, v_t_1511_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1516_ = l_panic___redArg(v_inst_1510_, v___x_1515_);
return v___x_1516_;
}
else
{
lean_object* v_val_1517_; 
lean_dec(v_inst_1510_);
v_val_1517_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_val_1517_);
lean_dec_ref(v___x_1514_);
return v_val_1517_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1518_, lean_object* v_00_u03b2_1519_, lean_object* v_cmp_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_t_1523_, lean_object* v_k_1524_){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_box(0);
v___x_1526_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1520_, v_k_1524_, v___x_1525_, v_t_1523_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1528_ = l_panic___redArg(v_inst_1522_, v___x_1527_);
return v___x_1528_;
}
else
{
lean_object* v_val_1529_; 
lean_dec(v_inst_1522_);
v_val_1529_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_val_1529_);
lean_dec_ref(v___x_1526_);
return v_val_1529_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___redArg(lean_object* v_cmp_1530_, lean_object* v_t_1531_, lean_object* v_k_1532_, lean_object* v_fallback_1533_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_box(0);
v___x_1535_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1530_, v_k_1532_, v___x_1534_, v_t_1531_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_inc(v_fallback_1533_);
return v_fallback_1533_;
}
else
{
lean_object* v_val_1536_; 
v_val_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_val_1536_);
lean_dec_ref(v___x_1535_);
return v_val_1536_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1537_, lean_object* v_t_1538_, lean_object* v_k_1539_, lean_object* v_fallback_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Std_ExtDTreeMap_getKeyGED___redArg(v_cmp_1537_, v_t_1538_, v_k_1539_, v_fallback_1540_);
lean_dec(v_fallback_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED(lean_object* v_00_u03b1_1542_, lean_object* v_00_u03b2_1543_, lean_object* v_cmp_1544_, lean_object* v_inst_1545_, lean_object* v_t_1546_, lean_object* v_k_1547_, lean_object* v_fallback_1548_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_box(0);
v___x_1550_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1544_, v_k_1547_, v___x_1549_, v_t_1546_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_inc(v_fallback_1548_);
return v_fallback_1548_;
}
else
{
lean_object* v_val_1551_; 
v_val_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1551_);
lean_dec_ref(v___x_1550_);
return v_val_1551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1552_, lean_object* v_00_u03b2_1553_, lean_object* v_cmp_1554_, lean_object* v_inst_1555_, lean_object* v_t_1556_, lean_object* v_k_1557_, lean_object* v_fallback_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Std_ExtDTreeMap_getKeyGED(v_00_u03b1_1552_, v_00_u03b2_1553_, v_cmp_1554_, v_inst_1555_, v_t_1556_, v_k_1557_, v_fallback_1558_);
lean_dec(v_fallback_1558_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1560_, lean_object* v_t_1561_, lean_object* v_k_1562_, lean_object* v_fallback_1563_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_box(0);
v___x_1565_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1560_, v_k_1562_, v___x_1564_, v_t_1561_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_inc(v_fallback_1563_);
return v_fallback_1563_;
}
else
{
lean_object* v_val_1566_; 
v_val_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_val_1566_);
lean_dec_ref(v___x_1565_);
return v_val_1566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1567_, lean_object* v_t_1568_, lean_object* v_k_1569_, lean_object* v_fallback_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Std_ExtDTreeMap_getKeyGTD___redArg(v_cmp_1567_, v_t_1568_, v_k_1569_, v_fallback_1570_);
lean_dec(v_fallback_1570_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD(lean_object* v_00_u03b1_1572_, lean_object* v_00_u03b2_1573_, lean_object* v_cmp_1574_, lean_object* v_inst_1575_, lean_object* v_t_1576_, lean_object* v_k_1577_, lean_object* v_fallback_1578_){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1574_, v_k_1577_, v___x_1579_, v_t_1576_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_inc(v_fallback_1578_);
return v_fallback_1578_;
}
else
{
lean_object* v_val_1581_; 
v_val_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_val_1581_);
lean_dec_ref(v___x_1580_);
return v_val_1581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1582_, lean_object* v_00_u03b2_1583_, lean_object* v_cmp_1584_, lean_object* v_inst_1585_, lean_object* v_t_1586_, lean_object* v_k_1587_, lean_object* v_fallback_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Std_ExtDTreeMap_getKeyGTD(v_00_u03b1_1582_, v_00_u03b2_1583_, v_cmp_1584_, v_inst_1585_, v_t_1586_, v_k_1587_, v_fallback_1588_);
lean_dec(v_fallback_1588_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___redArg(lean_object* v_cmp_1590_, lean_object* v_t_1591_, lean_object* v_k_1592_, lean_object* v_fallback_1593_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_box(0);
v___x_1595_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1590_, v_k_1592_, v___x_1594_, v_t_1591_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_inc(v_fallback_1593_);
return v_fallback_1593_;
}
else
{
lean_object* v_val_1596_; 
v_val_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_val_1596_);
lean_dec_ref(v___x_1595_);
return v_val_1596_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1597_, lean_object* v_t_1598_, lean_object* v_k_1599_, lean_object* v_fallback_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Std_ExtDTreeMap_getKeyLED___redArg(v_cmp_1597_, v_t_1598_, v_k_1599_, v_fallback_1600_);
lean_dec(v_fallback_1600_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED(lean_object* v_00_u03b1_1602_, lean_object* v_00_u03b2_1603_, lean_object* v_cmp_1604_, lean_object* v_inst_1605_, lean_object* v_t_1606_, lean_object* v_k_1607_, lean_object* v_fallback_1608_){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_box(0);
v___x_1610_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1604_, v_k_1607_, v___x_1609_, v_t_1606_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_inc(v_fallback_1608_);
return v_fallback_1608_;
}
else
{
lean_object* v_val_1611_; 
v_val_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_val_1611_);
lean_dec_ref(v___x_1610_);
return v_val_1611_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1612_, lean_object* v_00_u03b2_1613_, lean_object* v_cmp_1614_, lean_object* v_inst_1615_, lean_object* v_t_1616_, lean_object* v_k_1617_, lean_object* v_fallback_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Std_ExtDTreeMap_getKeyLED(v_00_u03b1_1612_, v_00_u03b2_1613_, v_cmp_1614_, v_inst_1615_, v_t_1616_, v_k_1617_, v_fallback_1618_);
lean_dec(v_fallback_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1620_, lean_object* v_t_1621_, lean_object* v_k_1622_, lean_object* v_fallback_1623_){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_box(0);
v___x_1625_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1620_, v_k_1622_, v___x_1624_, v_t_1621_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_inc(v_fallback_1623_);
return v_fallback_1623_;
}
else
{
lean_object* v_val_1626_; 
v_val_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_val_1626_);
lean_dec_ref(v___x_1625_);
return v_val_1626_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1627_, lean_object* v_t_1628_, lean_object* v_k_1629_, lean_object* v_fallback_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Std_ExtDTreeMap_getKeyLTD___redArg(v_cmp_1627_, v_t_1628_, v_k_1629_, v_fallback_1630_);
lean_dec(v_fallback_1630_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD(lean_object* v_00_u03b1_1632_, lean_object* v_00_u03b2_1633_, lean_object* v_cmp_1634_, lean_object* v_inst_1635_, lean_object* v_t_1636_, lean_object* v_k_1637_, lean_object* v_fallback_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = lean_box(0);
v___x_1640_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1634_, v_k_1637_, v___x_1639_, v_t_1636_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_inc(v_fallback_1638_);
return v_fallback_1638_;
}
else
{
lean_object* v_val_1641_; 
v_val_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_val_1641_);
lean_dec_ref(v___x_1640_);
return v_val_1641_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1642_, lean_object* v_00_u03b2_1643_, lean_object* v_cmp_1644_, lean_object* v_inst_1645_, lean_object* v_t_1646_, lean_object* v_k_1647_, lean_object* v_fallback_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Std_ExtDTreeMap_getKeyLTD(v_00_u03b1_1642_, v_00_u03b2_1643_, v_cmp_1644_, v_inst_1645_, v_t_1646_, v_k_1647_, v_fallback_1648_);
lean_dec(v_fallback_1648_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1650_, lean_object* v_t_1651_, lean_object* v_a_1652_, lean_object* v_b_1653_){
_start:
{
lean_object* v___x_1654_; 
lean_inc(v_a_1652_);
lean_inc(v_t_1651_);
lean_inc_ref(v_cmp_1650_);
v___x_1654_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1650_, v_t_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1654_) == 0)
{
uint8_t v___x_1655_; 
lean_inc(v_t_1651_);
lean_inc(v_a_1652_);
lean_inc_ref(v_cmp_1650_);
v___x_1655_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1650_, v_a_1652_, v_t_1651_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1650_, v_a_1652_, v_b_1653_, v_t_1651_);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1654_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
return v___x_1657_;
}
else
{
lean_object* v___x_1658_; 
lean_dec(v_b_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_cmp_1650_);
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1654_);
lean_ctor_set(v___x_1658_, 1, v_t_1651_);
return v___x_1658_;
}
}
else
{
lean_object* v___x_1659_; 
lean_dec(v_b_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_cmp_1650_);
v___x_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1654_);
lean_ctor_set(v___x_1659_, 1, v_t_1651_);
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1660_, lean_object* v_cmp_1661_, lean_object* v_00_u03b2_1662_, lean_object* v_inst_1663_, lean_object* v_t_1664_, lean_object* v_a_1665_, lean_object* v_b_1666_){
_start:
{
lean_object* v___x_1667_; 
lean_inc(v_a_1665_);
lean_inc(v_t_1664_);
lean_inc_ref(v_cmp_1661_);
v___x_1667_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1661_, v_t_1664_, v_a_1665_);
if (lean_obj_tag(v___x_1667_) == 0)
{
uint8_t v___x_1668_; 
lean_inc(v_t_1664_);
lean_inc(v_a_1665_);
lean_inc_ref(v_cmp_1661_);
v___x_1668_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1661_, v_a_1665_, v_t_1664_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1661_, v_a_1665_, v_b_1666_, v_t_1664_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1667_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
return v___x_1670_;
}
else
{
lean_object* v___x_1671_; 
lean_dec(v_b_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_cmp_1661_);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1667_);
lean_ctor_set(v___x_1671_, 1, v_t_1664_);
return v___x_1671_;
}
}
else
{
lean_object* v___x_1672_; 
lean_dec(v_b_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_cmp_1661_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1667_);
lean_ctor_set(v___x_1672_, 1, v_t_1664_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x3f___redArg(lean_object* v_cmp_1673_, lean_object* v_t_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1673_, v_t_1674_, v_a_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x3f(lean_object* v_00_u03b1_1677_, lean_object* v_cmp_1678_, lean_object* v_00_u03b2_1679_, lean_object* v_inst_1680_, lean_object* v_t_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1678_, v_t_1681_, v_a_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get___redArg(lean_object* v_cmp_1684_, lean_object* v_t_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1684_, v_t_1685_, v_a_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get(lean_object* v_00_u03b1_1688_, lean_object* v_cmp_1689_, lean_object* v_00_u03b2_1690_, lean_object* v_inst_1691_, lean_object* v_t_1692_, lean_object* v_a_1693_, lean_object* v_h_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1689_, v_t_1692_, v_a_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___redArg(lean_object* v_cmp_1696_, lean_object* v_inst_1697_, lean_object* v_t_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1696_, v_inst_1697_, v_t_1698_, v_a_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21(lean_object* v_00_u03b1_1701_, lean_object* v_cmp_1702_, lean_object* v_00_u03b2_1703_, lean_object* v_inst_1704_, lean_object* v_inst_1705_, lean_object* v_t_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1702_, v_inst_1705_, v_t_1706_, v_a_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___redArg(lean_object* v_cmp_1709_, lean_object* v_t_1710_, lean_object* v_a_1711_, lean_object* v_fallback_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1709_, v_t_1710_, v_a_1711_, v_fallback_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___redArg___boxed(lean_object* v_cmp_1714_, lean_object* v_t_1715_, lean_object* v_a_1716_, lean_object* v_fallback_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Std_ExtDTreeMap_Const_getD___redArg(v_cmp_1714_, v_t_1715_, v_a_1716_, v_fallback_1717_);
lean_dec(v_fallback_1717_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD(lean_object* v_00_u03b1_1719_, lean_object* v_cmp_1720_, lean_object* v_00_u03b2_1721_, lean_object* v_inst_1722_, lean_object* v_t_1723_, lean_object* v_a_1724_, lean_object* v_fallback_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1720_, v_t_1723_, v_a_1724_, v_fallback_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___boxed(lean_object* v_00_u03b1_1727_, lean_object* v_cmp_1728_, lean_object* v_00_u03b2_1729_, lean_object* v_inst_1730_, lean_object* v_t_1731_, lean_object* v_a_1732_, lean_object* v_fallback_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Std_ExtDTreeMap_Const_getD(v_00_u03b1_1727_, v_cmp_1728_, v_00_u03b2_1729_, v_inst_1730_, v_t_1731_, v_a_1732_, v_fallback_1733_);
lean_dec(v_fallback_1733_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(lean_object* v_t_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(v_t_1737_);
lean_dec(v_t_1737_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f(lean_object* v_00_u03b1_1739_, lean_object* v_cmp_1740_, lean_object* v_00_u03b2_1741_, lean_object* v_inst_1742_, lean_object* v_t_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_cmp_1746_, lean_object* v_00_u03b2_1747_, lean_object* v_inst_1748_, lean_object* v_t_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Std_ExtDTreeMap_Const_minEntry_x3f(v_00_u03b1_1745_, v_cmp_1746_, v_00_u03b2_1747_, v_inst_1748_, v_t_1749_);
lean_dec(v_t_1749_);
lean_dec_ref(v_cmp_1746_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___redArg(lean_object* v_t_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___redArg___boxed(lean_object* v_t_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Std_ExtDTreeMap_Const_minEntry___redArg(v_t_1753_);
lean_dec(v_t_1753_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry(lean_object* v_00_u03b1_1755_, lean_object* v_cmp_1756_, lean_object* v_00_u03b2_1757_, lean_object* v_inst_1758_, lean_object* v_t_1759_, lean_object* v_h_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___boxed(lean_object* v_00_u03b1_1762_, lean_object* v_cmp_1763_, lean_object* v_00_u03b2_1764_, lean_object* v_inst_1765_, lean_object* v_t_1766_, lean_object* v_h_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Std_ExtDTreeMap_Const_minEntry(v_00_u03b1_1762_, v_cmp_1763_, v_00_u03b2_1764_, v_inst_1765_, v_t_1766_, v_h_1767_);
lean_dec(v_t_1766_);
lean_dec_ref(v_cmp_1763_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(lean_object* v_inst_1769_, lean_object* v_t_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1769_, v_t_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1772_, lean_object* v_t_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(v_inst_1772_, v_t_1773_);
lean_dec(v_t_1773_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21(lean_object* v_00_u03b1_1775_, lean_object* v_cmp_1776_, lean_object* v_00_u03b2_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_t_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1779_, v_t_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1782_, lean_object* v_cmp_1783_, lean_object* v_00_u03b2_1784_, lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_t_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Std_ExtDTreeMap_Const_minEntry_x21(v_00_u03b1_1782_, v_cmp_1783_, v_00_u03b2_1784_, v_inst_1785_, v_inst_1786_, v_t_1787_);
lean_dec(v_t_1787_);
lean_dec_ref(v_cmp_1783_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___redArg(lean_object* v_t_1789_, lean_object* v_fallback_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1789_, v_fallback_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___redArg___boxed(lean_object* v_t_1792_, lean_object* v_fallback_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_ExtDTreeMap_Const_minEntryD___redArg(v_t_1792_, v_fallback_1793_);
lean_dec_ref(v_fallback_1793_);
lean_dec(v_t_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD(lean_object* v_00_u03b1_1795_, lean_object* v_cmp_1796_, lean_object* v_00_u03b2_1797_, lean_object* v_inst_1798_, lean_object* v_t_1799_, lean_object* v_fallback_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1799_, v_fallback_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___boxed(lean_object* v_00_u03b1_1802_, lean_object* v_cmp_1803_, lean_object* v_00_u03b2_1804_, lean_object* v_inst_1805_, lean_object* v_t_1806_, lean_object* v_fallback_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_ExtDTreeMap_Const_minEntryD(v_00_u03b1_1802_, v_cmp_1803_, v_00_u03b2_1804_, v_inst_1805_, v_t_1806_, v_fallback_1807_);
lean_dec_ref(v_fallback_1807_);
lean_dec(v_t_1806_);
lean_dec_ref(v_cmp_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(lean_object* v_t_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(v_t_1811_);
lean_dec(v_t_1811_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f(lean_object* v_00_u03b1_1813_, lean_object* v_cmp_1814_, lean_object* v_00_u03b2_1815_, lean_object* v_inst_1816_, lean_object* v_t_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_cmp_1820_, lean_object* v_00_u03b2_1821_, lean_object* v_inst_1822_, lean_object* v_t_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Std_ExtDTreeMap_Const_maxEntry_x3f(v_00_u03b1_1819_, v_cmp_1820_, v_00_u03b2_1821_, v_inst_1822_, v_t_1823_);
lean_dec(v_t_1823_);
lean_dec_ref(v_cmp_1820_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___redArg(lean_object* v_t_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___redArg___boxed(lean_object* v_t_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Std_ExtDTreeMap_Const_maxEntry___redArg(v_t_1827_);
lean_dec(v_t_1827_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry(lean_object* v_00_u03b1_1829_, lean_object* v_cmp_1830_, lean_object* v_00_u03b2_1831_, lean_object* v_inst_1832_, lean_object* v_t_1833_, lean_object* v_h_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1833_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___boxed(lean_object* v_00_u03b1_1836_, lean_object* v_cmp_1837_, lean_object* v_00_u03b2_1838_, lean_object* v_inst_1839_, lean_object* v_t_1840_, lean_object* v_h_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Std_ExtDTreeMap_Const_maxEntry(v_00_u03b1_1836_, v_cmp_1837_, v_00_u03b2_1838_, v_inst_1839_, v_t_1840_, v_h_1841_);
lean_dec(v_t_1840_);
lean_dec_ref(v_cmp_1837_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(lean_object* v_inst_1843_, lean_object* v_t_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1843_, v_t_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_1846_, lean_object* v_t_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(v_inst_1846_, v_t_1847_);
lean_dec(v_t_1847_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21(lean_object* v_00_u03b1_1849_, lean_object* v_cmp_1850_, lean_object* v_00_u03b2_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_t_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1853_, v_t_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_1856_, lean_object* v_cmp_1857_, lean_object* v_00_u03b2_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_t_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Std_ExtDTreeMap_Const_maxEntry_x21(v_00_u03b1_1856_, v_cmp_1857_, v_00_u03b2_1858_, v_inst_1859_, v_inst_1860_, v_t_1861_);
lean_dec(v_t_1861_);
lean_dec_ref(v_cmp_1857_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___redArg(lean_object* v_t_1863_, lean_object* v_fallback_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1863_, v_fallback_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___redArg___boxed(lean_object* v_t_1866_, lean_object* v_fallback_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Std_ExtDTreeMap_Const_maxEntryD___redArg(v_t_1866_, v_fallback_1867_);
lean_dec_ref(v_fallback_1867_);
lean_dec(v_t_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD(lean_object* v_00_u03b1_1869_, lean_object* v_cmp_1870_, lean_object* v_00_u03b2_1871_, lean_object* v_inst_1872_, lean_object* v_t_1873_, lean_object* v_fallback_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1873_, v_fallback_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___boxed(lean_object* v_00_u03b1_1876_, lean_object* v_cmp_1877_, lean_object* v_00_u03b2_1878_, lean_object* v_inst_1879_, lean_object* v_t_1880_, lean_object* v_fallback_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Std_ExtDTreeMap_Const_maxEntryD(v_00_u03b1_1876_, v_cmp_1877_, v_00_u03b2_1878_, v_inst_1879_, v_t_1880_, v_fallback_1881_);
lean_dec_ref(v_fallback_1881_);
lean_dec(v_t_1880_);
lean_dec_ref(v_cmp_1877_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(lean_object* v_t_1883_, lean_object* v_n_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1883_, v_n_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_1886_, lean_object* v_n_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(v_t_1886_, v_n_1887_);
lean_dec(v_t_1886_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_1889_, lean_object* v_cmp_1890_, lean_object* v_00_u03b2_1891_, lean_object* v_inst_1892_, lean_object* v_t_1893_, lean_object* v_n_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1893_, v_n_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1896_, lean_object* v_cmp_1897_, lean_object* v_00_u03b2_1898_, lean_object* v_inst_1899_, lean_object* v_t_1900_, lean_object* v_n_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(v_00_u03b1_1896_, v_cmp_1897_, v_00_u03b2_1898_, v_inst_1899_, v_t_1900_, v_n_1901_);
lean_dec(v_t_1900_);
lean_dec_ref(v_cmp_1897_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(lean_object* v_t_1903_, lean_object* v_n_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_1903_, v_n_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___redArg___boxed(lean_object* v_t_1906_, lean_object* v_n_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(v_t_1906_, v_n_1907_);
lean_dec(v_t_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx(lean_object* v_00_u03b1_1909_, lean_object* v_cmp_1910_, lean_object* v_00_u03b2_1911_, lean_object* v_inst_1912_, lean_object* v_t_1913_, lean_object* v_n_1914_, lean_object* v_h_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_1913_, v_n_1914_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_1917_, lean_object* v_cmp_1918_, lean_object* v_00_u03b2_1919_, lean_object* v_inst_1920_, lean_object* v_t_1921_, lean_object* v_n_1922_, lean_object* v_h_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Std_ExtDTreeMap_Const_entryAtIdx(v_00_u03b1_1917_, v_cmp_1918_, v_00_u03b2_1919_, v_inst_1920_, v_t_1921_, v_n_1922_, v_h_1923_);
lean_dec(v_t_1921_);
lean_dec_ref(v_cmp_1918_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(lean_object* v_inst_1925_, lean_object* v_t_1926_, lean_object* v_n_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1925_, v_t_1926_, v_n_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_1929_, lean_object* v_t_1930_, lean_object* v_n_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(v_inst_1929_, v_t_1930_, v_n_1931_);
lean_dec(v_t_1930_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21(lean_object* v_00_u03b1_1933_, lean_object* v_cmp_1934_, lean_object* v_00_u03b2_1935_, lean_object* v_inst_1936_, lean_object* v_inst_1937_, lean_object* v_t_1938_, lean_object* v_n_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1937_, v_t_1938_, v_n_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_1941_, lean_object* v_cmp_1942_, lean_object* v_00_u03b2_1943_, lean_object* v_inst_1944_, lean_object* v_inst_1945_, lean_object* v_t_1946_, lean_object* v_n_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x21(v_00_u03b1_1941_, v_cmp_1942_, v_00_u03b2_1943_, v_inst_1944_, v_inst_1945_, v_t_1946_, v_n_1947_);
lean_dec(v_t_1946_);
lean_dec_ref(v_cmp_1942_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(lean_object* v_t_1949_, lean_object* v_n_1950_, lean_object* v_fallback_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1949_, v_n_1950_, v_fallback_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_1953_, lean_object* v_n_1954_, lean_object* v_fallback_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(v_t_1953_, v_n_1954_, v_fallback_1955_);
lean_dec_ref(v_fallback_1955_);
lean_dec(v_t_1953_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD(lean_object* v_00_u03b1_1957_, lean_object* v_cmp_1958_, lean_object* v_00_u03b2_1959_, lean_object* v_inst_1960_, lean_object* v_t_1961_, lean_object* v_n_1962_, lean_object* v_fallback_1963_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1961_, v_n_1962_, v_fallback_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_1965_, lean_object* v_cmp_1966_, lean_object* v_00_u03b2_1967_, lean_object* v_inst_1968_, lean_object* v_t_1969_, lean_object* v_n_1970_, lean_object* v_fallback_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Std_ExtDTreeMap_Const_entryAtIdxD(v_00_u03b1_1965_, v_cmp_1966_, v_00_u03b2_1967_, v_inst_1968_, v_t_1969_, v_n_1970_, v_fallback_1971_);
lean_dec_ref(v_fallback_1971_);
lean_dec(v_t_1969_);
lean_dec_ref(v_cmp_1966_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_1973_, lean_object* v_t_1974_, lean_object* v_k_1975_){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_box(0);
v___x_1977_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1973_, v_k_1975_, v___x_1976_, v_t_1974_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x3f(lean_object* v_00_u03b1_1978_, lean_object* v_cmp_1979_, lean_object* v_00_u03b2_1980_, lean_object* v_inst_1981_, lean_object* v_t_1982_, lean_object* v_k_1983_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_box(0);
v___x_1985_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1979_, v_k_1983_, v___x_1984_, v_t_1982_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_1986_, lean_object* v_t_1987_, lean_object* v_k_1988_){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_box(0);
v___x_1990_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1986_, v_k_1988_, v___x_1989_, v_t_1987_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x3f(lean_object* v_00_u03b1_1991_, lean_object* v_cmp_1992_, lean_object* v_00_u03b2_1993_, lean_object* v_inst_1994_, lean_object* v_t_1995_, lean_object* v_k_1996_){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_box(0);
v___x_1998_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1992_, v_k_1996_, v___x_1997_, v_t_1995_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_1999_, lean_object* v_t_2000_, lean_object* v_k_2001_){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_box(0);
v___x_2003_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1999_, v_k_2001_, v___x_2002_, v_t_2000_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x3f(lean_object* v_00_u03b1_2004_, lean_object* v_cmp_2005_, lean_object* v_00_u03b2_2006_, lean_object* v_inst_2007_, lean_object* v_t_2008_, lean_object* v_k_2009_){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_box(0);
v___x_2011_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2005_, v_k_2009_, v___x_2010_, v_t_2008_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_2012_, lean_object* v_t_2013_, lean_object* v_k_2014_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_box(0);
v___x_2016_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2012_, v_k_2014_, v___x_2015_, v_t_2013_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x3f(lean_object* v_00_u03b1_2017_, lean_object* v_cmp_2018_, lean_object* v_00_u03b2_2019_, lean_object* v_inst_2020_, lean_object* v_t_2021_, lean_object* v_k_2022_){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = lean_box(0);
v___x_2024_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2018_, v_k_2022_, v___x_2023_, v_t_2021_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE___redArg(lean_object* v_cmp_2025_, lean_object* v_t_2026_, lean_object* v_k_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_2025_, v_k_2027_, v_t_2026_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE(lean_object* v_00_u03b1_2029_, lean_object* v_cmp_2030_, lean_object* v_00_u03b2_2031_, lean_object* v_inst_2032_, lean_object* v_t_2033_, lean_object* v_k_2034_, lean_object* v_h_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_2030_, v_k_2034_, v_t_2033_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT___redArg(lean_object* v_cmp_2037_, lean_object* v_t_2038_, lean_object* v_k_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_2037_, v_k_2039_, v_t_2038_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT(lean_object* v_00_u03b1_2041_, lean_object* v_cmp_2042_, lean_object* v_00_u03b2_2043_, lean_object* v_inst_2044_, lean_object* v_t_2045_, lean_object* v_k_2046_, lean_object* v_h_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_2042_, v_k_2046_, v_t_2045_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE___redArg(lean_object* v_cmp_2049_, lean_object* v_t_2050_, lean_object* v_k_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_2049_, v_k_2051_, v_t_2050_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE(lean_object* v_00_u03b1_2053_, lean_object* v_cmp_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_inst_2056_, lean_object* v_t_2057_, lean_object* v_k_2058_, lean_object* v_h_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_2054_, v_k_2058_, v_t_2057_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT___redArg(lean_object* v_cmp_2061_, lean_object* v_t_2062_, lean_object* v_k_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_2061_, v_k_2063_, v_t_2062_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT(lean_object* v_00_u03b1_2065_, lean_object* v_cmp_2066_, lean_object* v_00_u03b2_2067_, lean_object* v_inst_2068_, lean_object* v_t_2069_, lean_object* v_k_2070_, lean_object* v_h_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_2066_, v_k_2070_, v_t_2069_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg(lean_object* v_cmp_2073_, lean_object* v_inst_2074_, lean_object* v_t_2075_, lean_object* v_k_2076_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_box(0);
v___x_2078_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2073_, v_k_2076_, v___x_2077_, v_t_2075_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2080_ = l_panic___redArg(v_inst_2074_, v___x_2079_);
return v___x_2080_;
}
else
{
lean_object* v_val_2081_; 
lean_dec_ref(v_inst_2074_);
v_val_2081_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_val_2081_);
lean_dec_ref(v___x_2078_);
return v_val_2081_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21(lean_object* v_00_u03b1_2082_, lean_object* v_cmp_2083_, lean_object* v_00_u03b2_2084_, lean_object* v_inst_2085_, lean_object* v_inst_2086_, lean_object* v_t_2087_, lean_object* v_k_2088_){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_box(0);
v___x_2090_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2083_, v_k_2088_, v___x_2089_, v_t_2087_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2092_ = l_panic___redArg(v_inst_2086_, v___x_2091_);
return v___x_2092_;
}
else
{
lean_object* v_val_2093_; 
lean_dec_ref(v_inst_2086_);
v_val_2093_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_val_2093_);
lean_dec_ref(v___x_2090_);
return v_val_2093_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(lean_object* v_cmp_2094_, lean_object* v_inst_2095_, lean_object* v_t_2096_, lean_object* v_k_2097_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_box(0);
v___x_2099_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2094_, v_k_2097_, v___x_2098_, v_t_2096_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2101_ = l_panic___redArg(v_inst_2095_, v___x_2100_);
return v___x_2101_;
}
else
{
lean_object* v_val_2102_; 
lean_dec_ref(v_inst_2095_);
v_val_2102_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_val_2102_);
lean_dec_ref(v___x_2099_);
return v_val_2102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21(lean_object* v_00_u03b1_2103_, lean_object* v_cmp_2104_, lean_object* v_00_u03b2_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_t_2108_, lean_object* v_k_2109_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_box(0);
v___x_2111_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2104_, v_k_2109_, v___x_2110_, v_t_2108_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2113_ = l_panic___redArg(v_inst_2107_, v___x_2112_);
return v___x_2113_;
}
else
{
lean_object* v_val_2114_; 
lean_dec_ref(v_inst_2107_);
v_val_2114_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_val_2114_);
lean_dec_ref(v___x_2111_);
return v_val_2114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(lean_object* v_cmp_2115_, lean_object* v_inst_2116_, lean_object* v_t_2117_, lean_object* v_k_2118_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_box(0);
v___x_2120_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2115_, v_k_2118_, v___x_2119_, v_t_2117_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2122_ = l_panic___redArg(v_inst_2116_, v___x_2121_);
return v___x_2122_;
}
else
{
lean_object* v_val_2123_; 
lean_dec_ref(v_inst_2116_);
v_val_2123_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_val_2123_);
lean_dec_ref(v___x_2120_);
return v_val_2123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21(lean_object* v_00_u03b1_2124_, lean_object* v_cmp_2125_, lean_object* v_00_u03b2_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_t_2129_, lean_object* v_k_2130_){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_box(0);
v___x_2132_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2125_, v_k_2130_, v___x_2131_, v_t_2129_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2134_ = l_panic___redArg(v_inst_2128_, v___x_2133_);
return v___x_2134_;
}
else
{
lean_object* v_val_2135_; 
lean_dec_ref(v_inst_2128_);
v_val_2135_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_val_2135_);
lean_dec_ref(v___x_2132_);
return v_val_2135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(lean_object* v_cmp_2136_, lean_object* v_inst_2137_, lean_object* v_t_2138_, lean_object* v_k_2139_){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_box(0);
v___x_2141_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2136_, v_k_2139_, v___x_2140_, v_t_2138_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2143_ = l_panic___redArg(v_inst_2137_, v___x_2142_);
return v___x_2143_;
}
else
{
lean_object* v_val_2144_; 
lean_dec_ref(v_inst_2137_);
v_val_2144_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_val_2144_);
lean_dec_ref(v___x_2141_);
return v_val_2144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21(lean_object* v_00_u03b1_2145_, lean_object* v_cmp_2146_, lean_object* v_00_u03b2_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_t_2150_, lean_object* v_k_2151_){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = lean_box(0);
v___x_2153_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2146_, v_k_2151_, v___x_2152_, v_t_2150_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2155_ = l_panic___redArg(v_inst_2149_, v___x_2154_);
return v___x_2155_;
}
else
{
lean_object* v_val_2156_; 
lean_dec_ref(v_inst_2149_);
v_val_2156_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_val_2156_);
lean_dec_ref(v___x_2153_);
return v_val_2156_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___redArg(lean_object* v_cmp_2157_, lean_object* v_t_2158_, lean_object* v_k_2159_, lean_object* v_fallback_2160_){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_box(0);
v___x_2162_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2157_, v_k_2159_, v___x_2161_, v_t_2158_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_inc_ref(v_fallback_2160_);
return v_fallback_2160_;
}
else
{
lean_object* v_val_2163_; 
v_val_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_val_2163_);
lean_dec_ref(v___x_2162_);
return v_val_2163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2164_, lean_object* v_t_2165_, lean_object* v_k_2166_, lean_object* v_fallback_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Std_ExtDTreeMap_Const_getEntryGED___redArg(v_cmp_2164_, v_t_2165_, v_k_2166_, v_fallback_2167_);
lean_dec_ref(v_fallback_2167_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED(lean_object* v_00_u03b1_2169_, lean_object* v_cmp_2170_, lean_object* v_00_u03b2_2171_, lean_object* v_inst_2172_, lean_object* v_t_2173_, lean_object* v_k_2174_, lean_object* v_fallback_2175_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_box(0);
v___x_2177_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2170_, v_k_2174_, v___x_2176_, v_t_2173_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_inc_ref(v_fallback_2175_);
return v_fallback_2175_;
}
else
{
lean_object* v_val_2178_; 
v_val_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_val_2178_);
lean_dec_ref(v___x_2177_);
return v_val_2178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2179_, lean_object* v_cmp_2180_, lean_object* v_00_u03b2_2181_, lean_object* v_inst_2182_, lean_object* v_t_2183_, lean_object* v_k_2184_, lean_object* v_fallback_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Std_ExtDTreeMap_Const_getEntryGED(v_00_u03b1_2179_, v_cmp_2180_, v_00_u03b2_2181_, v_inst_2182_, v_t_2183_, v_k_2184_, v_fallback_2185_);
lean_dec_ref(v_fallback_2185_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(lean_object* v_cmp_2187_, lean_object* v_t_2188_, lean_object* v_k_2189_, lean_object* v_fallback_2190_){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = lean_box(0);
v___x_2192_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2187_, v_k_2189_, v___x_2191_, v_t_2188_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_inc_ref(v_fallback_2190_);
return v_fallback_2190_;
}
else
{
lean_object* v_val_2193_; 
v_val_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_val_2193_);
lean_dec_ref(v___x_2192_);
return v_val_2193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2194_, lean_object* v_t_2195_, lean_object* v_k_2196_, lean_object* v_fallback_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(v_cmp_2194_, v_t_2195_, v_k_2196_, v_fallback_2197_);
lean_dec_ref(v_fallback_2197_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD(lean_object* v_00_u03b1_2199_, lean_object* v_cmp_2200_, lean_object* v_00_u03b2_2201_, lean_object* v_inst_2202_, lean_object* v_t_2203_, lean_object* v_k_2204_, lean_object* v_fallback_2205_){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = lean_box(0);
v___x_2207_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2200_, v_k_2204_, v___x_2206_, v_t_2203_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_inc_ref(v_fallback_2205_);
return v_fallback_2205_;
}
else
{
lean_object* v_val_2208_; 
v_val_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_val_2208_);
lean_dec_ref(v___x_2207_);
return v_val_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2209_, lean_object* v_cmp_2210_, lean_object* v_00_u03b2_2211_, lean_object* v_inst_2212_, lean_object* v_t_2213_, lean_object* v_k_2214_, lean_object* v_fallback_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Std_ExtDTreeMap_Const_getEntryGTD(v_00_u03b1_2209_, v_cmp_2210_, v_00_u03b2_2211_, v_inst_2212_, v_t_2213_, v_k_2214_, v_fallback_2215_);
lean_dec_ref(v_fallback_2215_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___redArg(lean_object* v_cmp_2217_, lean_object* v_t_2218_, lean_object* v_k_2219_, lean_object* v_fallback_2220_){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_box(0);
v___x_2222_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2217_, v_k_2219_, v___x_2221_, v_t_2218_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_inc_ref(v_fallback_2220_);
return v_fallback_2220_;
}
else
{
lean_object* v_val_2223_; 
v_val_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_val_2223_);
lean_dec_ref(v___x_2222_);
return v_val_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2224_, lean_object* v_t_2225_, lean_object* v_k_2226_, lean_object* v_fallback_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Std_ExtDTreeMap_Const_getEntryLED___redArg(v_cmp_2224_, v_t_2225_, v_k_2226_, v_fallback_2227_);
lean_dec_ref(v_fallback_2227_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED(lean_object* v_00_u03b1_2229_, lean_object* v_cmp_2230_, lean_object* v_00_u03b2_2231_, lean_object* v_inst_2232_, lean_object* v_t_2233_, lean_object* v_k_2234_, lean_object* v_fallback_2235_){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = lean_box(0);
v___x_2237_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2230_, v_k_2234_, v___x_2236_, v_t_2233_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_inc_ref(v_fallback_2235_);
return v_fallback_2235_;
}
else
{
lean_object* v_val_2238_; 
v_val_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_val_2238_);
lean_dec_ref(v___x_2237_);
return v_val_2238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2239_, lean_object* v_cmp_2240_, lean_object* v_00_u03b2_2241_, lean_object* v_inst_2242_, lean_object* v_t_2243_, lean_object* v_k_2244_, lean_object* v_fallback_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Std_ExtDTreeMap_Const_getEntryLED(v_00_u03b1_2239_, v_cmp_2240_, v_00_u03b2_2241_, v_inst_2242_, v_t_2243_, v_k_2244_, v_fallback_2245_);
lean_dec_ref(v_fallback_2245_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(lean_object* v_cmp_2247_, lean_object* v_t_2248_, lean_object* v_k_2249_, lean_object* v_fallback_2250_){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_box(0);
v___x_2252_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2247_, v_k_2249_, v___x_2251_, v_t_2248_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_inc_ref(v_fallback_2250_);
return v_fallback_2250_;
}
else
{
lean_object* v_val_2253_; 
v_val_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_val_2253_);
lean_dec_ref(v___x_2252_);
return v_val_2253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2254_, lean_object* v_t_2255_, lean_object* v_k_2256_, lean_object* v_fallback_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(v_cmp_2254_, v_t_2255_, v_k_2256_, v_fallback_2257_);
lean_dec_ref(v_fallback_2257_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD(lean_object* v_00_u03b1_2259_, lean_object* v_cmp_2260_, lean_object* v_00_u03b2_2261_, lean_object* v_inst_2262_, lean_object* v_t_2263_, lean_object* v_k_2264_, lean_object* v_fallback_2265_){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2260_, v_k_2264_, v___x_2266_, v_t_2263_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_inc_ref(v_fallback_2265_);
return v_fallback_2265_;
}
else
{
lean_object* v_val_2268_; 
v_val_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_val_2268_);
lean_dec_ref(v___x_2267_);
return v_val_2268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2269_, lean_object* v_cmp_2270_, lean_object* v_00_u03b2_2271_, lean_object* v_inst_2272_, lean_object* v_t_2273_, lean_object* v_k_2274_, lean_object* v_fallback_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Std_ExtDTreeMap_Const_getEntryLTD(v_00_u03b1_2269_, v_cmp_2270_, v_00_u03b2_2271_, v_inst_2272_, v_t_2273_, v_k_2274_, v_fallback_2275_);
lean_dec_ref(v_fallback_2275_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter___redArg(lean_object* v_f_2277_, lean_object* v_t_2278_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2277_, v_t_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter(lean_object* v_00_u03b1_2280_, lean_object* v_00_u03b2_2281_, lean_object* v_cmp_2282_, lean_object* v_f_2283_, lean_object* v_t_2284_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2283_, v_t_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter___boxed(lean_object* v_00_u03b1_2286_, lean_object* v_00_u03b2_2287_, lean_object* v_cmp_2288_, lean_object* v_f_2289_, lean_object* v_t_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Std_ExtDTreeMap_filter(v_00_u03b1_2286_, v_00_u03b2_2287_, v_cmp_2288_, v_f_2289_, v_t_2290_);
lean_dec_ref(v_cmp_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap___redArg(lean_object* v_f_2292_, lean_object* v_t_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_2292_, v_t_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap(lean_object* v_00_u03b1_2295_, lean_object* v_00_u03b2_2296_, lean_object* v_00_u03b3_2297_, lean_object* v_cmp_2298_, lean_object* v_f_2299_, lean_object* v_t_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_2299_, v_t_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap___boxed(lean_object* v_00_u03b1_2302_, lean_object* v_00_u03b2_2303_, lean_object* v_00_u03b3_2304_, lean_object* v_cmp_2305_, lean_object* v_f_2306_, lean_object* v_t_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Std_ExtDTreeMap_filterMap(v_00_u03b1_2302_, v_00_u03b2_2303_, v_00_u03b3_2304_, v_cmp_2305_, v_f_2306_, v_t_2307_);
lean_dec_ref(v_cmp_2305_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map___redArg(lean_object* v_f_2309_, lean_object* v_t_2310_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_2309_, v_t_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map(lean_object* v_00_u03b1_2312_, lean_object* v_00_u03b2_2313_, lean_object* v_00_u03b3_2314_, lean_object* v_cmp_2315_, lean_object* v_f_2316_, lean_object* v_t_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_2316_, v_t_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map___boxed(lean_object* v_00_u03b1_2319_, lean_object* v_00_u03b2_2320_, lean_object* v_00_u03b3_2321_, lean_object* v_cmp_2322_, lean_object* v_f_2323_, lean_object* v_t_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Std_ExtDTreeMap_map(v_00_u03b1_2319_, v_00_u03b2_2320_, v_00_u03b3_2321_, v_cmp_2322_, v_f_2323_, v_t_2324_);
lean_dec_ref(v_cmp_2322_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM___redArg(lean_object* v_inst_2326_, lean_object* v_f_2327_, lean_object* v_init_2328_, lean_object* v_t_2329_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2326_, v_f_2327_, v_init_2328_, v_t_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM(lean_object* v_00_u03b1_2331_, lean_object* v_00_u03b2_2332_, lean_object* v_cmp_2333_, lean_object* v_00_u03b4_2334_, lean_object* v_m_2335_, lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_f_2339_, lean_object* v_init_2340_, lean_object* v_t_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2336_, v_f_2339_, v_init_2340_, v_t_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM___boxed(lean_object* v_00_u03b1_2343_, lean_object* v_00_u03b2_2344_, lean_object* v_cmp_2345_, lean_object* v_00_u03b4_2346_, lean_object* v_m_2347_, lean_object* v_inst_2348_, lean_object* v_inst_2349_, lean_object* v_inst_2350_, lean_object* v_f_2351_, lean_object* v_init_2352_, lean_object* v_t_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Std_ExtDTreeMap_foldlM(v_00_u03b1_2343_, v_00_u03b2_2344_, v_cmp_2345_, v_00_u03b4_2346_, v_m_2347_, v_inst_2348_, v_inst_2349_, v_inst_2350_, v_f_2351_, v_init_2352_, v_t_2353_);
lean_dec_ref(v_cmp_2345_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl___redArg(lean_object* v_f_2355_, lean_object* v_init_2356_, lean_object* v_t_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2355_, v_init_2356_, v_t_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl(lean_object* v_00_u03b1_2359_, lean_object* v_00_u03b2_2360_, lean_object* v_cmp_2361_, lean_object* v_00_u03b4_2362_, lean_object* v_inst_2363_, lean_object* v_f_2364_, lean_object* v_init_2365_, lean_object* v_t_2366_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2364_, v_init_2365_, v_t_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl___boxed(lean_object* v_00_u03b1_2368_, lean_object* v_00_u03b2_2369_, lean_object* v_cmp_2370_, lean_object* v_00_u03b4_2371_, lean_object* v_inst_2372_, lean_object* v_f_2373_, lean_object* v_init_2374_, lean_object* v_t_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Std_ExtDTreeMap_foldl(v_00_u03b1_2368_, v_00_u03b2_2369_, v_cmp_2370_, v_00_u03b4_2371_, v_inst_2372_, v_f_2373_, v_init_2374_, v_t_2375_);
lean_dec_ref(v_cmp_2370_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM___redArg(lean_object* v_inst_2377_, lean_object* v_f_2378_, lean_object* v_init_2379_, lean_object* v_t_2380_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2377_, v_f_2378_, v_init_2379_, v_t_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM(lean_object* v_00_u03b1_2382_, lean_object* v_00_u03b2_2383_, lean_object* v_cmp_2384_, lean_object* v_00_u03b4_2385_, lean_object* v_m_2386_, lean_object* v_inst_2387_, lean_object* v_inst_2388_, lean_object* v_inst_2389_, lean_object* v_f_2390_, lean_object* v_init_2391_, lean_object* v_t_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2387_, v_f_2390_, v_init_2391_, v_t_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM___boxed(lean_object* v_00_u03b1_2394_, lean_object* v_00_u03b2_2395_, lean_object* v_cmp_2396_, lean_object* v_00_u03b4_2397_, lean_object* v_m_2398_, lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_f_2402_, lean_object* v_init_2403_, lean_object* v_t_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Std_ExtDTreeMap_foldrM(v_00_u03b1_2394_, v_00_u03b2_2395_, v_cmp_2396_, v_00_u03b4_2397_, v_m_2398_, v_inst_2399_, v_inst_2400_, v_inst_2401_, v_f_2402_, v_init_2403_, v_t_2404_);
lean_dec_ref(v_cmp_2396_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___redArg___lam__0(lean_object* v_f_2406_, lean_object* v_x1_2407_, lean_object* v_x2_2408_, lean_object* v_x3_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_apply_3(v_f_2406_, v_x1_2407_, v_x2_2408_, v_x3_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___redArg(lean_object* v_f_2430_, lean_object* v_init_2431_, lean_object* v_t_2432_){
_start:
{
lean_object* v___f_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___f_2433_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2433_, 0, v_f_2430_);
v___x_2434_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2435_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2434_, v___f_2433_, v_init_2431_, v_t_2432_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr(lean_object* v_00_u03b1_2436_, lean_object* v_00_u03b2_2437_, lean_object* v_cmp_2438_, lean_object* v_00_u03b4_2439_, lean_object* v_inst_2440_, lean_object* v_f_2441_, lean_object* v_init_2442_, lean_object* v_t_2443_){
_start:
{
lean_object* v___f_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___f_2444_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2444_, 0, v_f_2441_);
v___x_2445_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2446_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2445_, v___f_2444_, v_init_2442_, v_t_2443_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___boxed(lean_object* v_00_u03b1_2447_, lean_object* v_00_u03b2_2448_, lean_object* v_cmp_2449_, lean_object* v_00_u03b4_2450_, lean_object* v_inst_2451_, lean_object* v_f_2452_, lean_object* v_init_2453_, lean_object* v_t_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Std_ExtDTreeMap_foldr(v_00_u03b1_2447_, v_00_u03b2_2448_, v_cmp_2449_, v_00_u03b4_2450_, v_inst_2451_, v_f_2452_, v_init_2453_, v_t_2454_);
lean_dec_ref(v_cmp_2449_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition___redArg___lam__0(lean_object* v_f_2456_, lean_object* v_cmp_2457_, lean_object* v_x_2458_, lean_object* v_a_2459_, lean_object* v_b_2460_){
_start:
{
lean_object* v_fst_2461_; lean_object* v_snd_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2476_; 
v_fst_2461_ = lean_ctor_get(v_x_2458_, 0);
v_snd_2462_ = lean_ctor_get(v_x_2458_, 1);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_x_2458_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2464_ = v_x_2458_;
v_isShared_2465_ = v_isSharedCheck_2476_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_snd_2462_);
lean_inc(v_fst_2461_);
lean_dec(v_x_2458_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2476_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
lean_inc(v_b_2460_);
lean_inc(v_a_2459_);
v___x_2466_ = lean_apply_2(v_f_2456_, v_a_2459_, v_b_2460_);
v___x_2467_ = lean_unbox(v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2468_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2457_, v_a_2459_, v_b_2460_, v_snd_2462_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 1, v___x_2468_);
v___x_2470_ = v___x_2464_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_fst_2461_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2472_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2457_, v_a_2459_, v_b_2460_, v_fst_2461_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2472_);
v___x_2474_ = v___x_2464_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_snd_2462_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition___redArg(lean_object* v_cmp_2479_, lean_object* v_f_2480_, lean_object* v_t_2481_){
_start:
{
lean_object* v___f_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___f_2482_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2482_, 0, v_f_2480_);
lean_closure_set(v___f_2482_, 1, v_cmp_2479_);
v___x_2483_ = ((lean_object*)(l_Std_ExtDTreeMap_partition___redArg___closed__0));
v___x_2484_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2482_, v___x_2483_, v_t_2481_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition(lean_object* v_00_u03b1_2485_, lean_object* v_00_u03b2_2486_, lean_object* v_cmp_2487_, lean_object* v_inst_2488_, lean_object* v_f_2489_, lean_object* v_t_2490_){
_start:
{
lean_object* v___f_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___f_2491_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2491_, 0, v_f_2489_);
lean_closure_set(v___f_2491_, 1, v_cmp_2487_);
v___x_2492_ = ((lean_object*)(l_Std_ExtDTreeMap_partition___redArg___closed__0));
v___x_2493_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2491_, v___x_2492_, v_t_2490_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___redArg___lam__0(lean_object* v_f_2494_, lean_object* v_x_2495_, lean_object* v_k_2496_, lean_object* v_v_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_apply_2(v_f_2494_, v_k_2496_, v_v_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___redArg(lean_object* v_inst_2499_, lean_object* v_f_2500_, lean_object* v_t_2501_){
_start:
{
lean_object* v___f_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___f_2502_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2502_, 0, v_f_2500_);
v___x_2503_ = lean_box(0);
v___x_2504_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2499_, v___f_2502_, v___x_2503_, v_t_2501_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM(lean_object* v_00_u03b1_2505_, lean_object* v_00_u03b2_2506_, lean_object* v_cmp_2507_, lean_object* v_m_2508_, lean_object* v_inst_2509_, lean_object* v_inst_2510_, lean_object* v_inst_2511_, lean_object* v_f_2512_, lean_object* v_t_2513_){
_start:
{
lean_object* v___f_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___f_2514_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2514_, 0, v_f_2512_);
v___x_2515_ = lean_box(0);
v___x_2516_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2509_, v___f_2514_, v___x_2515_, v_t_2513_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___boxed(lean_object* v_00_u03b1_2517_, lean_object* v_00_u03b2_2518_, lean_object* v_cmp_2519_, lean_object* v_m_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_inst_2523_, lean_object* v_f_2524_, lean_object* v_t_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Std_ExtDTreeMap_forM(v_00_u03b1_2517_, v_00_u03b2_2518_, v_cmp_2519_, v_m_2520_, v_inst_2521_, v_inst_2522_, v_inst_2523_, v_f_2524_, v_t_2525_);
lean_dec_ref(v_cmp_2519_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___redArg___lam__0(lean_object* v_toPure_2527_, lean_object* v_____do__lift_2528_){
_start:
{
lean_object* v_a_2529_; lean_object* v___x_2530_; 
v_a_2529_ = lean_ctor_get(v_____do__lift_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref(v_____do__lift_2528_);
v___x_2530_ = lean_apply_2(v_toPure_2527_, lean_box(0), v_a_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___redArg(lean_object* v_inst_2531_, lean_object* v_f_2532_, lean_object* v_init_2533_, lean_object* v_t_2534_){
_start:
{
lean_object* v_toApplicative_2535_; lean_object* v_toBind_2536_; lean_object* v_toPure_2537_; lean_object* v___x_2538_; lean_object* v___f_2539_; lean_object* v___x_2540_; 
v_toApplicative_2535_ = lean_ctor_get(v_inst_2531_, 0);
v_toBind_2536_ = lean_ctor_get(v_inst_2531_, 1);
lean_inc(v_toBind_2536_);
v_toPure_2537_ = lean_ctor_get(v_toApplicative_2535_, 1);
lean_inc(v_toPure_2537_);
v___x_2538_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2531_, v_f_2532_, v_init_2533_, v_t_2534_);
v___f_2539_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2539_, 0, v_toPure_2537_);
v___x_2540_ = lean_apply_4(v_toBind_2536_, lean_box(0), lean_box(0), v___x_2538_, v___f_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn(lean_object* v_00_u03b1_2541_, lean_object* v_00_u03b2_2542_, lean_object* v_cmp_2543_, lean_object* v_00_u03b4_2544_, lean_object* v_m_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_inst_2548_, lean_object* v_f_2549_, lean_object* v_init_2550_, lean_object* v_t_2551_){
_start:
{
lean_object* v_toApplicative_2552_; lean_object* v_toBind_2553_; lean_object* v_toPure_2554_; lean_object* v___x_2555_; lean_object* v___f_2556_; lean_object* v___x_2557_; 
v_toApplicative_2552_ = lean_ctor_get(v_inst_2546_, 0);
v_toBind_2553_ = lean_ctor_get(v_inst_2546_, 1);
lean_inc(v_toBind_2553_);
v_toPure_2554_ = lean_ctor_get(v_toApplicative_2552_, 1);
lean_inc(v_toPure_2554_);
v___x_2555_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2546_, v_f_2549_, v_init_2550_, v_t_2551_);
v___f_2556_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2556_, 0, v_toPure_2554_);
v___x_2557_ = lean_apply_4(v_toBind_2553_, lean_box(0), lean_box(0), v___x_2555_, v___f_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___boxed(lean_object* v_00_u03b1_2558_, lean_object* v_00_u03b2_2559_, lean_object* v_cmp_2560_, lean_object* v_00_u03b4_2561_, lean_object* v_m_2562_, lean_object* v_inst_2563_, lean_object* v_inst_2564_, lean_object* v_inst_2565_, lean_object* v_f_2566_, lean_object* v_init_2567_, lean_object* v_t_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Std_ExtDTreeMap_forIn(v_00_u03b1_2558_, v_00_u03b2_2559_, v_cmp_2560_, v_00_u03b4_2561_, v_m_2562_, v_inst_2563_, v_inst_2564_, v_inst_2565_, v_f_2566_, v_init_2567_, v_t_2568_);
lean_dec_ref(v_cmp_2560_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2570_, lean_object* v_x_2571_, lean_object* v_k_2572_, lean_object* v_v_2573_){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_k_2572_);
lean_ctor_set(v___x_2574_, 1, v_v_2573_);
v___x_2575_ = lean_apply_1(v_f_2570_, v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_2576_, lean_object* v_t_2577_, lean_object* v_f_2578_){
_start:
{
lean_object* v___f_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___f_2579_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2579_, 0, v_f_2578_);
v___x_2580_ = lean_box(0);
v___x_2581_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2576_, v___f_2579_, v___x_2580_, v_t_2577_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2582_){
_start:
{
lean_object* v___f_2583_; 
v___f_2583_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2583_, 0, v_inst_2582_);
return v___f_2583_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2584_, lean_object* v_00_u03b2_2585_, lean_object* v_cmp_2586_, lean_object* v_m_2587_, lean_object* v_inst_2588_, lean_object* v_inst_2589_, lean_object* v_inst_2590_){
_start:
{
lean_object* v___f_2591_; 
v___f_2591_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2591_, 0, v_inst_2589_);
return v___f_2591_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2592_, lean_object* v_00_u03b2_2593_, lean_object* v_cmp_2594_, lean_object* v_m_2595_, lean_object* v_inst_2596_, lean_object* v_inst_2597_, lean_object* v_inst_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(v_00_u03b1_2592_, v_00_u03b2_2593_, v_cmp_2594_, v_m_2595_, v_inst_2596_, v_inst_2597_, v_inst_2598_);
lean_dec_ref(v_cmp_2594_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2600_, lean_object* v_a_2601_, lean_object* v_b_2602_, lean_object* v_acc_2603_){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v_a_2601_);
lean_ctor_set(v___x_2604_, 1, v_b_2602_);
v___x_2605_ = lean_apply_2(v_f_2600_, v___x_2604_, v_acc_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_2606_, lean_object* v_00_u03b2_2607_, lean_object* v_m_2608_, lean_object* v_init_2609_, lean_object* v_f_2610_){
_start:
{
lean_object* v_toApplicative_2611_; lean_object* v_toBind_2612_; lean_object* v_toPure_2613_; lean_object* v___f_2614_; lean_object* v___x_2615_; lean_object* v___f_2616_; lean_object* v___x_2617_; 
v_toApplicative_2611_ = lean_ctor_get(v_inst_2606_, 0);
v_toBind_2612_ = lean_ctor_get(v_inst_2606_, 1);
lean_inc(v_toBind_2612_);
v_toPure_2613_ = lean_ctor_get(v_toApplicative_2611_, 1);
lean_inc(v_toPure_2613_);
v___f_2614_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2614_, 0, v_f_2610_);
v___x_2615_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2606_, v___f_2614_, v_init_2609_, v_m_2608_);
v___f_2616_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2616_, 0, v_toPure_2613_);
v___x_2617_ = lean_apply_4(v_toBind_2612_, lean_box(0), lean_box(0), v___x_2615_, v___f_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2618_){
_start:
{
lean_object* v___f_2619_; 
v___f_2619_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2619_, 0, v_inst_2618_);
return v___f_2619_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2620_, lean_object* v_00_u03b2_2621_, lean_object* v_cmp_2622_, lean_object* v_m_2623_, lean_object* v_inst_2624_, lean_object* v_inst_2625_, lean_object* v_inst_2626_){
_start:
{
lean_object* v___f_2627_; 
v___f_2627_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2627_, 0, v_inst_2625_);
return v___f_2627_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2628_, lean_object* v_00_u03b2_2629_, lean_object* v_cmp_2630_, lean_object* v_m_2631_, lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(v_00_u03b1_2628_, v_00_u03b2_2629_, v_cmp_2630_, v_m_2631_, v_inst_2632_, v_inst_2633_, v_inst_2634_);
lean_dec_ref(v_cmp_2630_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2636_, lean_object* v_x_2637_, lean_object* v_k_2638_, lean_object* v_v_2639_){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2640_, 0, v_k_2638_);
lean_ctor_set(v___x_2640_, 1, v_v_2639_);
v___x_2641_ = lean_apply_1(v_f_2636_, v___x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___redArg(lean_object* v_inst_2642_, lean_object* v_f_2643_, lean_object* v_t_2644_){
_start:
{
lean_object* v___f_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___f_2645_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2645_, 0, v_f_2643_);
v___x_2646_ = lean_box(0);
v___x_2647_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2642_, v___f_2645_, v___x_2646_, v_t_2644_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried(lean_object* v_00_u03b1_2648_, lean_object* v_cmp_2649_, lean_object* v_m_2650_, lean_object* v_inst_2651_, lean_object* v_inst_2652_, lean_object* v_00_u03b2_2653_, lean_object* v_inst_2654_, lean_object* v_f_2655_, lean_object* v_t_2656_){
_start:
{
lean_object* v___f_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___f_2657_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2657_, 0, v_f_2655_);
v___x_2658_ = lean_box(0);
v___x_2659_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2651_, v___f_2657_, v___x_2658_, v_t_2656_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2660_, lean_object* v_cmp_2661_, lean_object* v_m_2662_, lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_00_u03b2_2665_, lean_object* v_inst_2666_, lean_object* v_f_2667_, lean_object* v_t_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Std_ExtDTreeMap_Const_forMUncurried(v_00_u03b1_2660_, v_cmp_2661_, v_m_2662_, v_inst_2663_, v_inst_2664_, v_00_u03b2_2665_, v_inst_2666_, v_f_2667_, v_t_2668_);
lean_dec_ref(v_cmp_2661_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2670_, lean_object* v_a_2671_, lean_object* v_b_2672_, lean_object* v_acc_2673_){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v_a_2671_);
lean_ctor_set(v___x_2674_, 1, v_b_2672_);
v___x_2675_ = lean_apply_2(v_f_2670_, v___x_2674_, v_acc_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___redArg(lean_object* v_inst_2676_, lean_object* v_f_2677_, lean_object* v_init_2678_, lean_object* v_t_2679_){
_start:
{
lean_object* v_toApplicative_2680_; lean_object* v_toBind_2681_; lean_object* v_toPure_2682_; lean_object* v___f_2683_; lean_object* v___x_2684_; lean_object* v___f_2685_; lean_object* v___x_2686_; 
v_toApplicative_2680_ = lean_ctor_get(v_inst_2676_, 0);
v_toBind_2681_ = lean_ctor_get(v_inst_2676_, 1);
lean_inc(v_toBind_2681_);
v_toPure_2682_ = lean_ctor_get(v_toApplicative_2680_, 1);
lean_inc(v_toPure_2682_);
v___f_2683_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2683_, 0, v_f_2677_);
v___x_2684_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2676_, v___f_2683_, v_init_2678_, v_t_2679_);
v___f_2685_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2685_, 0, v_toPure_2682_);
v___x_2686_ = lean_apply_4(v_toBind_2681_, lean_box(0), lean_box(0), v___x_2684_, v___f_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried(lean_object* v_00_u03b1_2687_, lean_object* v_cmp_2688_, lean_object* v_00_u03b4_2689_, lean_object* v_m_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_00_u03b2_2693_, lean_object* v_inst_2694_, lean_object* v_f_2695_, lean_object* v_init_2696_, lean_object* v_t_2697_){
_start:
{
lean_object* v_toApplicative_2698_; lean_object* v_toBind_2699_; lean_object* v_toPure_2700_; lean_object* v___f_2701_; lean_object* v___x_2702_; lean_object* v___f_2703_; lean_object* v___x_2704_; 
v_toApplicative_2698_ = lean_ctor_get(v_inst_2691_, 0);
v_toBind_2699_ = lean_ctor_get(v_inst_2691_, 1);
lean_inc(v_toBind_2699_);
v_toPure_2700_ = lean_ctor_get(v_toApplicative_2698_, 1);
lean_inc(v_toPure_2700_);
v___f_2701_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2701_, 0, v_f_2695_);
v___x_2702_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2691_, v___f_2701_, v_init_2696_, v_t_2697_);
v___f_2703_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2703_, 0, v_toPure_2700_);
v___x_2704_ = lean_apply_4(v_toBind_2699_, lean_box(0), lean_box(0), v___x_2702_, v___f_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2705_, lean_object* v_cmp_2706_, lean_object* v_00_u03b4_2707_, lean_object* v_m_2708_, lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_00_u03b2_2711_, lean_object* v_inst_2712_, lean_object* v_f_2713_, lean_object* v_init_2714_, lean_object* v_t_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Std_ExtDTreeMap_Const_forInUncurried(v_00_u03b1_2705_, v_cmp_2706_, v_00_u03b4_2707_, v_m_2708_, v_inst_2709_, v_inst_2710_, v_00_u03b2_2711_, v_inst_2712_, v_f_2713_, v_init_2714_, v_t_2715_);
lean_dec_ref(v_cmp_2706_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___lam__0(lean_object* v_p_2717_, lean_object* v___x_2718_, lean_object* v___x_2719_, lean_object* v_a_2720_, lean_object* v_b_2721_, lean_object* v_acc_2722_){
_start:
{
lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = lean_apply_2(v_p_2717_, v_a_2720_, v_b_2721_);
v___x_2724_ = lean_unbox(v___x_2723_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; 
v___x_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2718_);
return v___x_2725_;
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_dec_ref(v___x_2718_);
v___x_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2723_);
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
lean_ctor_set(v___x_2727_, 1, v___x_2719_);
v___x_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
return v___x_2728_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2729_, lean_object* v___x_2730_, lean_object* v___x_2731_, lean_object* v_a_2732_, lean_object* v_b_2733_, lean_object* v_acc_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Std_ExtDTreeMap_any___redArg___lam__0(v_p_2729_, v___x_2730_, v___x_2731_, v_a_2732_, v_b_2733_, v_acc_2734_);
lean_dec_ref(v_acc_2734_);
return v_res_2735_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_any___redArg(lean_object* v_t_2739_, lean_object* v_p_2740_){
_start:
{
lean_object* v___y_2742_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___f_2750_; lean_object* v___x_2751_; lean_object* v_a_2752_; 
v___x_2747_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2748_ = lean_box(0);
v___x_2749_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_2750_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2750_, 0, v_p_2740_);
lean_closure_set(v___f_2750_, 1, v___x_2749_);
lean_closure_set(v___f_2750_, 2, v___x_2748_);
v___x_2751_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2747_, v___f_2750_, v___x_2749_, v_t_2739_);
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___y_2742_ = v_a_2752_;
goto v___jp_2741_;
v___jp_2741_:
{
lean_object* v_fst_2743_; 
v_fst_2743_ = lean_ctor_get(v___y_2742_, 0);
lean_inc(v_fst_2743_);
lean_dec_ref(v___y_2742_);
if (lean_obj_tag(v_fst_2743_) == 0)
{
uint8_t v___x_2744_; 
v___x_2744_ = 0;
return v___x_2744_;
}
else
{
lean_object* v_val_2745_; uint8_t v___x_2746_; 
v_val_2745_ = lean_ctor_get(v_fst_2743_, 0);
lean_inc(v_val_2745_);
lean_dec_ref(v_fst_2743_);
v___x_2746_ = lean_unbox(v_val_2745_);
lean_dec(v_val_2745_);
return v___x_2746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___boxed(lean_object* v_t_2753_, lean_object* v_p_2754_){
_start:
{
uint8_t v_res_2755_; lean_object* v_r_2756_; 
v_res_2755_ = l_Std_ExtDTreeMap_any___redArg(v_t_2753_, v_p_2754_);
v_r_2756_ = lean_box(v_res_2755_);
return v_r_2756_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_any(lean_object* v_00_u03b1_2757_, lean_object* v_00_u03b2_2758_, lean_object* v_cmp_2759_, lean_object* v_inst_2760_, lean_object* v_t_2761_, lean_object* v_p_2762_){
_start:
{
lean_object* v___y_2764_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___f_2772_; lean_object* v___x_2773_; lean_object* v_a_2774_; 
v___x_2769_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2770_ = lean_box(0);
v___x_2771_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_2772_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2772_, 0, v_p_2762_);
lean_closure_set(v___f_2772_, 1, v___x_2771_);
lean_closure_set(v___f_2772_, 2, v___x_2770_);
v___x_2773_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2769_, v___f_2772_, v___x_2771_, v_t_2761_);
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___y_2764_ = v_a_2774_;
goto v___jp_2763_;
v___jp_2763_:
{
lean_object* v_fst_2765_; 
v_fst_2765_ = lean_ctor_get(v___y_2764_, 0);
lean_inc(v_fst_2765_);
lean_dec_ref(v___y_2764_);
if (lean_obj_tag(v_fst_2765_) == 0)
{
uint8_t v___x_2766_; 
v___x_2766_ = 0;
return v___x_2766_;
}
else
{
lean_object* v_val_2767_; uint8_t v___x_2768_; 
v_val_2767_ = lean_ctor_get(v_fst_2765_, 0);
lean_inc(v_val_2767_);
lean_dec_ref(v_fst_2765_);
v___x_2768_ = lean_unbox(v_val_2767_);
lean_dec(v_val_2767_);
return v___x_2768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___boxed(lean_object* v_00_u03b1_2775_, lean_object* v_00_u03b2_2776_, lean_object* v_cmp_2777_, lean_object* v_inst_2778_, lean_object* v_t_2779_, lean_object* v_p_2780_){
_start:
{
uint8_t v_res_2781_; lean_object* v_r_2782_; 
v_res_2781_ = l_Std_ExtDTreeMap_any(v_00_u03b1_2775_, v_00_u03b2_2776_, v_cmp_2777_, v_inst_2778_, v_t_2779_, v_p_2780_);
lean_dec_ref(v_cmp_2777_);
v_r_2782_ = lean_box(v_res_2781_);
return v_r_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___lam__0(lean_object* v_p_2783_, lean_object* v___x_2784_, lean_object* v___x_2785_, lean_object* v_a_2786_, lean_object* v_b_2787_, lean_object* v_acc_2788_){
_start:
{
lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2789_ = lean_apply_2(v_p_2783_, v_a_2786_, v_b_2787_);
v___x_2790_ = lean_unbox(v___x_2789_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
lean_dec_ref(v___x_2785_);
v___x_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v___x_2784_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
else
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2785_);
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_2795_, lean_object* v___x_2796_, lean_object* v___x_2797_, lean_object* v_a_2798_, lean_object* v_b_2799_, lean_object* v_acc_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Std_ExtDTreeMap_all___redArg___lam__0(v_p_2795_, v___x_2796_, v___x_2797_, v_a_2798_, v_b_2799_, v_acc_2800_);
lean_dec_ref(v_acc_2800_);
return v_res_2801_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_all___redArg(lean_object* v_t_2802_, lean_object* v_p_2803_){
_start:
{
lean_object* v___y_2805_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___f_2813_; lean_object* v___x_2814_; lean_object* v_a_2815_; 
v___x_2810_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2811_ = lean_box(0);
v___x_2812_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_2813_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2813_, 0, v_p_2803_);
lean_closure_set(v___f_2813_, 1, v___x_2811_);
lean_closure_set(v___f_2813_, 2, v___x_2812_);
v___x_2814_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2810_, v___f_2813_, v___x_2812_, v_t_2802_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___y_2805_ = v_a_2815_;
goto v___jp_2804_;
v___jp_2804_:
{
lean_object* v_fst_2806_; 
v_fst_2806_ = lean_ctor_get(v___y_2805_, 0);
lean_inc(v_fst_2806_);
lean_dec_ref(v___y_2805_);
if (lean_obj_tag(v_fst_2806_) == 0)
{
uint8_t v___x_2807_; 
v___x_2807_ = 1;
return v___x_2807_;
}
else
{
lean_object* v_val_2808_; uint8_t v___x_2809_; 
v_val_2808_ = lean_ctor_get(v_fst_2806_, 0);
lean_inc(v_val_2808_);
lean_dec_ref(v_fst_2806_);
v___x_2809_ = lean_unbox(v_val_2808_);
lean_dec(v_val_2808_);
return v___x_2809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___boxed(lean_object* v_t_2816_, lean_object* v_p_2817_){
_start:
{
uint8_t v_res_2818_; lean_object* v_r_2819_; 
v_res_2818_ = l_Std_ExtDTreeMap_all___redArg(v_t_2816_, v_p_2817_);
v_r_2819_ = lean_box(v_res_2818_);
return v_r_2819_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_all(lean_object* v_00_u03b1_2820_, lean_object* v_00_u03b2_2821_, lean_object* v_cmp_2822_, lean_object* v_inst_2823_, lean_object* v_t_2824_, lean_object* v_p_2825_){
_start:
{
lean_object* v___y_2827_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___f_2835_; lean_object* v___x_2836_; lean_object* v_a_2837_; 
v___x_2832_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2833_ = lean_box(0);
v___x_2834_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_2835_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2835_, 0, v_p_2825_);
lean_closure_set(v___f_2835_, 1, v___x_2833_);
lean_closure_set(v___f_2835_, 2, v___x_2834_);
v___x_2836_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2832_, v___f_2835_, v___x_2834_, v_t_2824_);
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec(v___x_2836_);
v___y_2827_ = v_a_2837_;
goto v___jp_2826_;
v___jp_2826_:
{
lean_object* v_fst_2828_; 
v_fst_2828_ = lean_ctor_get(v___y_2827_, 0);
lean_inc(v_fst_2828_);
lean_dec_ref(v___y_2827_);
if (lean_obj_tag(v_fst_2828_) == 0)
{
uint8_t v___x_2829_; 
v___x_2829_ = 1;
return v___x_2829_;
}
else
{
lean_object* v_val_2830_; uint8_t v___x_2831_; 
v_val_2830_ = lean_ctor_get(v_fst_2828_, 0);
lean_inc(v_val_2830_);
lean_dec_ref(v_fst_2828_);
v___x_2831_ = lean_unbox(v_val_2830_);
lean_dec(v_val_2830_);
return v___x_2831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___boxed(lean_object* v_00_u03b1_2838_, lean_object* v_00_u03b2_2839_, lean_object* v_cmp_2840_, lean_object* v_inst_2841_, lean_object* v_t_2842_, lean_object* v_p_2843_){
_start:
{
uint8_t v_res_2844_; lean_object* v_r_2845_; 
v_res_2844_ = l_Std_ExtDTreeMap_all(v_00_u03b1_2838_, v_00_u03b2_2839_, v_cmp_2840_, v_inst_2841_, v_t_2842_, v_p_2843_);
lean_dec_ref(v_cmp_2840_);
v_r_2845_ = lean_box(v_res_2844_);
return v_r_2845_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg___lam__0(lean_object* v_x1_2846_, lean_object* v_x2_2847_, lean_object* v_x3_2848_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2849_, 0, v_x1_2846_);
lean_ctor_set(v___x_2849_, 1, v_x3_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_2850_, lean_object* v_x2_2851_, lean_object* v_x3_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Std_ExtDTreeMap_keys___redArg___lam__0(v_x1_2850_, v_x2_2851_, v_x3_2852_);
lean_dec(v_x2_2851_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg(lean_object* v_t_2855_){
_start:
{
lean_object* v___f_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___f_2856_ = ((lean_object*)(l_Std_ExtDTreeMap_keys___redArg___closed__0));
v___x_2857_ = lean_box(0);
v___x_2858_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2859_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2858_, v___f_2856_, v___x_2857_, v_t_2855_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys(lean_object* v_00_u03b1_2860_, lean_object* v_00_u03b2_2861_, lean_object* v_cmp_2862_, lean_object* v_inst_2863_, lean_object* v_t_2864_){
_start:
{
lean_object* v___f_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___f_2865_ = ((lean_object*)(l_Std_ExtDTreeMap_keys___redArg___closed__0));
v___x_2866_ = lean_box(0);
v___x_2867_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2868_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2867_, v___f_2865_, v___x_2866_, v_t_2864_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___boxed(lean_object* v_00_u03b1_2869_, lean_object* v_00_u03b2_2870_, lean_object* v_cmp_2871_, lean_object* v_inst_2872_, lean_object* v_t_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Std_ExtDTreeMap_keys(v_00_u03b1_2869_, v_00_u03b2_2870_, v_cmp_2871_, v_inst_2872_, v_t_2873_);
lean_dec_ref(v_cmp_2871_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg___lam__0(lean_object* v_l_2875_, lean_object* v_k_2876_, lean_object* v_x_2877_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = lean_array_push(v_l_2875_, v_k_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_2879_, lean_object* v_k_2880_, lean_object* v_x_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Std_ExtDTreeMap_keysArray___redArg___lam__0(v_l_2879_, v_k_2880_, v_x_2881_);
lean_dec(v_x_2881_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg(lean_object* v_t_2884_){
_start:
{
lean_object* v___f_2885_; lean_object* v___y_2887_; 
v___f_2885_ = ((lean_object*)(l_Std_ExtDTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2884_) == 0)
{
lean_object* v_size_2890_; 
v_size_2890_ = lean_ctor_get(v_t_2884_, 0);
lean_inc(v_size_2890_);
v___y_2887_ = v_size_2890_;
goto v___jp_2886_;
}
else
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_unsigned_to_nat(0u);
v___y_2887_ = v___x_2891_;
goto v___jp_2886_;
}
v___jp_2886_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_mk_empty_array_with_capacity(v___y_2887_);
lean_dec(v___y_2887_);
v___x_2889_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2885_, v___x_2888_, v_t_2884_);
return v___x_2889_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray(lean_object* v_00_u03b1_2892_, lean_object* v_00_u03b2_2893_, lean_object* v_cmp_2894_, lean_object* v_inst_2895_, lean_object* v_t_2896_){
_start:
{
lean_object* v___f_2897_; lean_object* v___y_2899_; 
v___f_2897_ = ((lean_object*)(l_Std_ExtDTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2896_) == 0)
{
lean_object* v_size_2902_; 
v_size_2902_ = lean_ctor_get(v_t_2896_, 0);
lean_inc(v_size_2902_);
v___y_2899_ = v_size_2902_;
goto v___jp_2898_;
}
else
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_unsigned_to_nat(0u);
v___y_2899_ = v___x_2903_;
goto v___jp_2898_;
}
v___jp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = lean_mk_empty_array_with_capacity(v___y_2899_);
lean_dec(v___y_2899_);
v___x_2901_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2897_, v___x_2900_, v_t_2896_);
return v___x_2901_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___boxed(lean_object* v_00_u03b1_2904_, lean_object* v_00_u03b2_2905_, lean_object* v_cmp_2906_, lean_object* v_inst_2907_, lean_object* v_t_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Std_ExtDTreeMap_keysArray(v_00_u03b1_2904_, v_00_u03b2_2905_, v_cmp_2906_, v_inst_2907_, v_t_2908_);
lean_dec_ref(v_cmp_2906_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg___lam__0(lean_object* v_x1_2910_, lean_object* v_x2_2911_, lean_object* v_x3_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2913_, 0, v_x2_2911_);
lean_ctor_set(v___x_2913_, 1, v_x3_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_2914_, lean_object* v_x2_2915_, lean_object* v_x3_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Std_ExtDTreeMap_values___redArg___lam__0(v_x1_2914_, v_x2_2915_, v_x3_2916_);
lean_dec(v_x1_2914_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg(lean_object* v_t_2919_){
_start:
{
lean_object* v___f_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___f_2920_ = ((lean_object*)(l_Std_ExtDTreeMap_values___redArg___closed__0));
v___x_2921_ = lean_box(0);
v___x_2922_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2923_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2922_, v___f_2920_, v___x_2921_, v_t_2919_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values(lean_object* v_00_u03b1_2924_, lean_object* v_cmp_2925_, lean_object* v_inst_2926_, lean_object* v_00_u03b2_2927_, lean_object* v_t_2928_){
_start:
{
lean_object* v___f_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___f_2929_ = ((lean_object*)(l_Std_ExtDTreeMap_values___redArg___closed__0));
v___x_2930_ = lean_box(0);
v___x_2931_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2932_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2931_, v___f_2929_, v___x_2930_, v_t_2928_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___boxed(lean_object* v_00_u03b1_2933_, lean_object* v_cmp_2934_, lean_object* v_inst_2935_, lean_object* v_00_u03b2_2936_, lean_object* v_t_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Std_ExtDTreeMap_values(v_00_u03b1_2933_, v_cmp_2934_, v_inst_2935_, v_00_u03b2_2936_, v_t_2937_);
lean_dec_ref(v_cmp_2934_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_2939_, lean_object* v_x_2940_, lean_object* v_v_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_array_push(v_l_2939_, v_v_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2943_, lean_object* v_x_2944_, lean_object* v_v_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(v_l_2943_, v_x_2944_, v_v_2945_);
lean_dec(v_x_2944_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg(lean_object* v_t_2948_){
_start:
{
lean_object* v___f_2949_; lean_object* v___y_2951_; 
v___f_2949_ = ((lean_object*)(l_Std_ExtDTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2948_) == 0)
{
lean_object* v_size_2954_; 
v_size_2954_ = lean_ctor_get(v_t_2948_, 0);
lean_inc(v_size_2954_);
v___y_2951_ = v_size_2954_;
goto v___jp_2950_;
}
else
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_unsigned_to_nat(0u);
v___y_2951_ = v___x_2955_;
goto v___jp_2950_;
}
v___jp_2950_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = lean_mk_empty_array_with_capacity(v___y_2951_);
lean_dec(v___y_2951_);
v___x_2953_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2949_, v___x_2952_, v_t_2948_);
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray(lean_object* v_00_u03b1_2956_, lean_object* v_cmp_2957_, lean_object* v_inst_2958_, lean_object* v_00_u03b2_2959_, lean_object* v_t_2960_){
_start:
{
lean_object* v___f_2961_; lean_object* v___y_2963_; 
v___f_2961_ = ((lean_object*)(l_Std_ExtDTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2960_) == 0)
{
lean_object* v_size_2966_; 
v_size_2966_ = lean_ctor_get(v_t_2960_, 0);
lean_inc(v_size_2966_);
v___y_2963_ = v_size_2966_;
goto v___jp_2962_;
}
else
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_unsigned_to_nat(0u);
v___y_2963_ = v___x_2967_;
goto v___jp_2962_;
}
v___jp_2962_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = lean_mk_empty_array_with_capacity(v___y_2963_);
lean_dec(v___y_2963_);
v___x_2965_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2961_, v___x_2964_, v_t_2960_);
return v___x_2965_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_2968_, lean_object* v_cmp_2969_, lean_object* v_inst_2970_, lean_object* v_00_u03b2_2971_, lean_object* v_t_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Std_ExtDTreeMap_valuesArray(v_00_u03b1_2968_, v_cmp_2969_, v_inst_2970_, v_00_u03b2_2971_, v_t_2972_);
lean_dec_ref(v_cmp_2969_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___redArg___lam__0(lean_object* v_x1_2974_, lean_object* v_x2_2975_, lean_object* v_x3_2976_){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v_x1_2974_);
lean_ctor_set(v___x_2977_, 1, v_x2_2975_);
v___x_2978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
lean_ctor_set(v___x_2978_, 1, v_x3_2976_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___redArg(lean_object* v_t_2980_){
_start:
{
lean_object* v___f_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___f_2981_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_2982_ = lean_box(0);
v___x_2983_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2984_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2983_, v___f_2981_, v___x_2982_, v_t_2980_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList(lean_object* v_00_u03b1_2985_, lean_object* v_00_u03b2_2986_, lean_object* v_cmp_2987_, lean_object* v_inst_2988_, lean_object* v_t_2989_){
_start:
{
lean_object* v___f_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___f_2990_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_2991_ = lean_box(0);
v___x_2992_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2993_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2992_, v___f_2990_, v___x_2991_, v_t_2989_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___boxed(lean_object* v_00_u03b1_2994_, lean_object* v_00_u03b2_2995_, lean_object* v_cmp_2996_, lean_object* v_inst_2997_, lean_object* v_t_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Std_ExtDTreeMap_toList(v_00_u03b1_2994_, v_00_u03b2_2995_, v_cmp_2996_, v_inst_2997_, v_t_2998_);
lean_dec_ref(v_cmp_2996_);
return v_res_2999_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_3001_, lean_object* v_a_3002_, lean_object* v_x_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_fst_3005_; lean_object* v_snd_3006_; lean_object* v_r_3007_; lean_object* v___x_3008_; 
v_fst_3005_ = lean_ctor_get(v_a_3002_, 0);
lean_inc(v_fst_3005_);
v_snd_3006_ = lean_ctor_get(v_a_3002_, 1);
lean_inc(v_snd_3006_);
lean_dec_ref(v_a_3002_);
v_r_3007_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3001_, v_fst_3005_, v_snd_3006_, v___y_3004_);
v___x_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3008_, 0, v_r_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg(lean_object* v_l_3009_, lean_object* v_cmp_3010_){
_start:
{
lean_object* v___f_3011_; lean_object* v___x_3012_; lean_object* v_r_3013_; lean_object* v___x_3014_; 
v___f_3011_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3011_, 0, v_cmp_3010_);
v___x_3012_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3013_ = lean_box(1);
v___x_3014_ = l_List_forIn_x27_loop___redArg(v___x_3012_, v___f_3011_, v_l_3009_, v_r_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList(lean_object* v_00_u03b1_3015_, lean_object* v_00_u03b2_3016_, lean_object* v_l_3017_, lean_object* v_cmp_3018_){
_start:
{
lean_object* v___f_3019_; lean_object* v___x_3020_; lean_object* v_r_3021_; lean_object* v___x_3022_; 
v___f_3019_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3019_, 0, v_cmp_3018_);
v___x_3020_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3021_ = lean_box(1);
v___x_3022_ = l_List_forIn_x27_loop___redArg(v___x_3020_, v___f_3019_, v_l_3017_, v_r_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___redArg___lam__0(lean_object* v_l_3023_, lean_object* v_k_3024_, lean_object* v_v_3025_){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3026_, 0, v_k_3024_);
lean_ctor_set(v___x_3026_, 1, v_v_3025_);
v___x_3027_ = lean_array_push(v_l_3023_, v___x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___redArg(lean_object* v_t_3029_){
_start:
{
lean_object* v___f_3030_; lean_object* v___y_3032_; 
v___f_3030_ = ((lean_object*)(l_Std_ExtDTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3029_) == 0)
{
lean_object* v_size_3035_; 
v_size_3035_ = lean_ctor_get(v_t_3029_, 0);
lean_inc(v_size_3035_);
v___y_3032_ = v_size_3035_;
goto v___jp_3031_;
}
else
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_unsigned_to_nat(0u);
v___y_3032_ = v___x_3036_;
goto v___jp_3031_;
}
v___jp_3031_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = lean_mk_empty_array_with_capacity(v___y_3032_);
lean_dec(v___y_3032_);
v___x_3034_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3030_, v___x_3033_, v_t_3029_);
return v___x_3034_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray(lean_object* v_00_u03b1_3037_, lean_object* v_00_u03b2_3038_, lean_object* v_cmp_3039_, lean_object* v_inst_3040_, lean_object* v_t_3041_){
_start:
{
lean_object* v___f_3042_; lean_object* v___y_3044_; 
v___f_3042_ = ((lean_object*)(l_Std_ExtDTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3041_) == 0)
{
lean_object* v_size_3047_; 
v_size_3047_ = lean_ctor_get(v_t_3041_, 0);
lean_inc(v_size_3047_);
v___y_3044_ = v_size_3047_;
goto v___jp_3043_;
}
else
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_unsigned_to_nat(0u);
v___y_3044_ = v___x_3048_;
goto v___jp_3043_;
}
v___jp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = lean_mk_empty_array_with_capacity(v___y_3044_);
lean_dec(v___y_3044_);
v___x_3046_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3042_, v___x_3045_, v_t_3041_);
return v___x_3046_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___boxed(lean_object* v_00_u03b1_3049_, lean_object* v_00_u03b2_3050_, lean_object* v_cmp_3051_, lean_object* v_inst_3052_, lean_object* v_t_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Std_ExtDTreeMap_toArray(v_00_u03b1_3049_, v_00_u03b2_3050_, v_cmp_3051_, v_inst_3052_, v_t_3053_);
lean_dec_ref(v_cmp_3051_);
return v_res_3054_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray___redArg(lean_object* v_a_3056_, lean_object* v_cmp_3057_){
_start:
{
lean_object* v___f_3058_; lean_object* v___x_3059_; lean_object* v_r_3060_; size_t v_sz_3061_; size_t v___x_3062_; lean_object* v___x_3063_; 
v___f_3058_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3058_, 0, v_cmp_3057_);
v___x_3059_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3060_ = lean_box(1);
v_sz_3061_ = lean_array_size(v_a_3056_);
v___x_3062_ = ((size_t)0ULL);
v___x_3063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3059_, v_a_3056_, v___f_3058_, v_sz_3061_, v___x_3062_, v_r_3060_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray(lean_object* v_00_u03b1_3064_, lean_object* v_00_u03b2_3065_, lean_object* v_a_3066_, lean_object* v_cmp_3067_){
_start:
{
lean_object* v___f_3068_; lean_object* v___x_3069_; lean_object* v_r_3070_; size_t v_sz_3071_; size_t v___x_3072_; lean_object* v___x_3073_; 
v___f_3068_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3068_, 0, v_cmp_3067_);
v___x_3069_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3070_ = lean_box(1);
v_sz_3071_ = lean_array_size(v_a_3066_);
v___x_3072_ = ((size_t)0ULL);
v___x_3073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3069_, v_a_3066_, v___f_3068_, v_sz_3071_, v___x_3072_, v_r_3070_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_modify___redArg(lean_object* v_cmp_3074_, lean_object* v_t_3075_, lean_object* v_a_3076_, lean_object* v_f_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3074_, v_a_3076_, v_f_3077_, v_t_3075_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_modify(lean_object* v_00_u03b1_3079_, lean_object* v_00_u03b2_3080_, lean_object* v_cmp_3081_, lean_object* v_inst_3082_, lean_object* v_inst_3083_, lean_object* v_t_3084_, lean_object* v_a_3085_, lean_object* v_f_3086_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3081_, v_a_3085_, v_f_3086_, v_t_3084_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_alter___redArg(lean_object* v_cmp_3088_, lean_object* v_t_3089_, lean_object* v_a_3090_, lean_object* v_f_3091_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3088_, v_a_3090_, v_f_3091_, v_t_3089_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_alter(lean_object* v_00_u03b1_3093_, lean_object* v_00_u03b2_3094_, lean_object* v_cmp_3095_, lean_object* v_inst_3096_, lean_object* v_inst_3097_, lean_object* v_t_3098_, lean_object* v_a_3099_, lean_object* v_f_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3095_, v_a_3099_, v_f_3100_, v_t_3098_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_3102_, lean_object* v_mergeFn_3103_, lean_object* v_a_3104_, lean_object* v_x_3105_){
_start:
{
if (lean_obj_tag(v_x_3105_) == 0)
{
lean_object* v___x_3106_; 
lean_dec(v_a_3104_);
lean_dec(v_mergeFn_3103_);
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v_b_u2082_3102_);
return v___x_3106_;
}
else
{
lean_object* v_val_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3115_; 
v_val_3107_ = lean_ctor_get(v_x_3105_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_x_3105_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3109_ = v_x_3105_;
v_isShared_3110_ = v_isSharedCheck_3115_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_val_3107_);
lean_dec(v_x_3105_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3115_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3111_ = lean_apply_3(v_mergeFn_3103_, v_a_3104_, v_val_3107_, v_b_u2082_3102_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3111_);
v___x_3113_ = v___x_3109_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3116_, lean_object* v_cmp_3117_, lean_object* v_t_3118_, lean_object* v_a_3119_, lean_object* v_b_u2082_3120_){
_start:
{
lean_object* v___f_3121_; lean_object* v___x_3122_; 
lean_inc(v_a_3119_);
v___f_3121_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3121_, 0, v_b_u2082_3120_);
lean_closure_set(v___f_3121_, 1, v_mergeFn_3116_);
lean_closure_set(v___f_3121_, 2, v_a_3119_);
v___x_3122_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3117_, v_a_3119_, v___f_3121_, v_t_3118_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg(lean_object* v_cmp_3123_, lean_object* v_mergeFn_3124_, lean_object* v_t_u2081_3125_, lean_object* v_t_u2082_3126_){
_start:
{
lean_object* v___f_3127_; lean_object* v___x_3128_; 
v___f_3127_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3127_, 0, v_mergeFn_3124_);
lean_closure_set(v___f_3127_, 1, v_cmp_3123_);
v___x_3128_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3127_, v_t_u2081_3125_, v_t_u2082_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith(lean_object* v_00_u03b1_3129_, lean_object* v_00_u03b2_3130_, lean_object* v_cmp_3131_, lean_object* v_inst_3132_, lean_object* v_inst_3133_, lean_object* v_mergeFn_3134_, lean_object* v_t_u2081_3135_, lean_object* v_t_u2082_3136_){
_start:
{
lean_object* v___f_3137_; lean_object* v___x_3138_; 
v___f_3137_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3137_, 0, v_mergeFn_3134_);
lean_closure_set(v___f_3137_, 1, v_cmp_3131_);
v___x_3138_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3137_, v_t_u2081_3135_, v_t_u2082_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___redArg___lam__0(lean_object* v_x1_3139_, lean_object* v_x2_3140_, lean_object* v_x3_3141_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_x1_3139_);
lean_ctor_set(v___x_3142_, 1, v_x2_3140_);
v___x_3143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
lean_ctor_set(v___x_3143_, 1, v_x3_3141_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___redArg(lean_object* v_t_3145_){
_start:
{
lean_object* v___f_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___f_3146_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toList___redArg___closed__0));
v___x_3147_ = lean_box(0);
v___x_3148_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3149_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3148_, v___f_3146_, v___x_3147_, v_t_3145_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList(lean_object* v_00_u03b1_3150_, lean_object* v_cmp_3151_, lean_object* v_00_u03b2_3152_, lean_object* v_inst_3153_, lean_object* v_t_3154_){
_start:
{
lean_object* v___f_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___f_3155_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toList___redArg___closed__0));
v___x_3156_ = lean_box(0);
v___x_3157_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3158_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3157_, v___f_3155_, v___x_3156_, v_t_3154_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___boxed(lean_object* v_00_u03b1_3159_, lean_object* v_cmp_3160_, lean_object* v_00_u03b2_3161_, lean_object* v_inst_3162_, lean_object* v_t_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Std_ExtDTreeMap_Const_toList(v_00_u03b1_3159_, v_cmp_3160_, v_00_u03b2_3161_, v_inst_3162_, v_t_3163_);
lean_dec_ref(v_cmp_3160_);
return v_res_3164_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0(lean_object* v_cmp_3166_, lean_object* v_a_3167_, lean_object* v_x_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_fst_3170_; lean_object* v_snd_3171_; lean_object* v_r_3172_; lean_object* v___x_3173_; 
v_fst_3170_ = lean_ctor_get(v_a_3167_, 0);
lean_inc(v_fst_3170_);
v_snd_3171_ = lean_ctor_get(v_a_3167_, 1);
lean_inc(v_snd_3171_);
lean_dec_ref(v_a_3167_);
v_r_3172_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3166_, v_fst_3170_, v_snd_3171_, v___y_3169_);
v___x_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3173_, 0, v_r_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg(lean_object* v_l_3174_, lean_object* v_cmp_3175_){
_start:
{
lean_object* v___f_3176_; lean_object* v___x_3177_; lean_object* v_r_3178_; lean_object* v___x_3179_; 
v___f_3176_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3176_, 0, v_cmp_3175_);
v___x_3177_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3178_ = lean_box(1);
v___x_3179_ = l_List_forIn_x27_loop___redArg(v___x_3177_, v___f_3176_, v_l_3174_, v_r_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList(lean_object* v_00_u03b1_3180_, lean_object* v_00_u03b2_3181_, lean_object* v_l_3182_, lean_object* v_cmp_3183_){
_start:
{
lean_object* v___f_3184_; lean_object* v___x_3185_; lean_object* v_r_3186_; lean_object* v___x_3187_; 
v___f_3184_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3184_, 0, v_cmp_3183_);
v___x_3185_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3186_ = lean_box(1);
v___x_3187_ = l_List_forIn_x27_loop___redArg(v___x_3185_, v___f_3184_, v_l_3182_, v_r_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg___lam__0(lean_object* v_acc_3188_, lean_object* v_k_3189_, lean_object* v_v_3190_){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v_k_3189_);
lean_ctor_set(v___x_3191_, 1, v_v_3190_);
v___x_3192_ = lean_array_push(v_acc_3188_, v___x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg(lean_object* v_t_3196_){
_start:
{
lean_object* v___f_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___f_3197_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0));
v___x_3198_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1));
v___x_3199_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3197_, v___x_3198_, v_t_3196_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray(lean_object* v_00_u03b1_3200_, lean_object* v_cmp_3201_, lean_object* v_00_u03b2_3202_, lean_object* v_inst_3203_, lean_object* v_t_3204_){
_start:
{
lean_object* v___f_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___f_3205_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0));
v___x_3206_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1));
v___x_3207_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3205_, v___x_3206_, v_t_3204_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___boxed(lean_object* v_00_u03b1_3208_, lean_object* v_cmp_3209_, lean_object* v_00_u03b2_3210_, lean_object* v_inst_3211_, lean_object* v_t_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Std_ExtDTreeMap_Const_toArray(v_00_u03b1_3208_, v_cmp_3209_, v_00_u03b2_3210_, v_inst_3211_, v_t_3212_);
lean_dec_ref(v_cmp_3209_);
return v_res_3213_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray___redArg(lean_object* v_a_3215_, lean_object* v_cmp_3216_){
_start:
{
lean_object* v___f_3217_; lean_object* v___x_3218_; lean_object* v_r_3219_; size_t v_sz_3220_; size_t v___x_3221_; lean_object* v___x_3222_; 
v___f_3217_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3217_, 0, v_cmp_3216_);
v___x_3218_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3219_ = lean_box(1);
v_sz_3220_ = lean_array_size(v_a_3215_);
v___x_3221_ = ((size_t)0ULL);
v___x_3222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3218_, v_a_3215_, v___f_3217_, v_sz_3220_, v___x_3221_, v_r_3219_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray(lean_object* v_00_u03b1_3223_, lean_object* v_00_u03b2_3224_, lean_object* v_a_3225_, lean_object* v_cmp_3226_){
_start:
{
lean_object* v___f_3227_; lean_object* v___x_3228_; lean_object* v_r_3229_; size_t v_sz_3230_; size_t v___x_3231_; lean_object* v___x_3232_; 
v___f_3227_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3227_, 0, v_cmp_3226_);
v___x_3228_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3229_ = lean_box(1);
v_sz_3230_ = lean_array_size(v_a_3225_);
v___x_3231_ = ((size_t)0ULL);
v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3228_, v_a_3225_, v___f_3227_, v_sz_3230_, v___x_3231_, v_r_3229_);
return v___x_3232_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_3234_, lean_object* v_a_3235_, lean_object* v_x_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v___x_3238_; 
lean_inc(v___y_3237_);
lean_inc(v_a_3235_);
lean_inc_ref(v_cmp_3234_);
v___x_3238_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3234_, v_a_3235_, v___y_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = lean_box(0);
v___x_3240_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3234_, v_a_3235_, v___x_3239_, v___y_3237_);
v___x_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
return v___x_3241_;
}
else
{
lean_object* v___x_3242_; 
lean_dec(v_a_3235_);
lean_dec_ref(v_cmp_3234_);
v___x_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3242_, 0, v___y_3237_);
return v___x_3242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg(lean_object* v_l_3243_, lean_object* v_cmp_3244_){
_start:
{
lean_object* v___f_3245_; lean_object* v___x_3246_; lean_object* v_r_3247_; lean_object* v___x_3248_; 
v___f_3245_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3245_, 0, v_cmp_3244_);
v___x_3246_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3247_ = lean_box(1);
v___x_3248_ = l_List_forIn_x27_loop___redArg(v___x_3246_, v___f_3245_, v_l_3243_, v_r_3247_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList(lean_object* v_00_u03b1_3249_, lean_object* v_l_3250_, lean_object* v_cmp_3251_){
_start:
{
lean_object* v___f_3252_; lean_object* v___x_3253_; lean_object* v_r_3254_; lean_object* v___x_3255_; 
v___f_3252_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3252_, 0, v_cmp_3251_);
v___x_3253_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3254_ = lean_box(1);
v___x_3255_ = l_List_forIn_x27_loop___redArg(v___x_3253_, v___f_3252_, v_l_3250_, v_r_3254_);
return v___x_3255_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray___redArg(lean_object* v_a_3257_, lean_object* v_cmp_3258_){
_start:
{
lean_object* v___f_3259_; lean_object* v___x_3260_; lean_object* v_r_3261_; size_t v_sz_3262_; size_t v___x_3263_; lean_object* v___x_3264_; 
v___f_3259_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3259_, 0, v_cmp_3258_);
v___x_3260_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3261_ = lean_box(1);
v_sz_3262_ = lean_array_size(v_a_3257_);
v___x_3263_ = ((size_t)0ULL);
v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3260_, v_a_3257_, v___f_3259_, v_sz_3262_, v___x_3263_, v_r_3261_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray(lean_object* v_00_u03b1_3265_, lean_object* v_a_3266_, lean_object* v_cmp_3267_){
_start:
{
lean_object* v___f_3268_; lean_object* v___x_3269_; lean_object* v_r_3270_; size_t v_sz_3271_; size_t v___x_3272_; lean_object* v___x_3273_; 
v___f_3268_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3268_, 0, v_cmp_3267_);
v___x_3269_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3270_ = lean_box(1);
v_sz_3271_ = lean_array_size(v_a_3266_);
v___x_3272_ = ((size_t)0ULL);
v___x_3273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3269_, v_a_3266_, v___f_3268_, v_sz_3271_, v___x_3272_, v_r_3270_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_modify___redArg(lean_object* v_cmp_3274_, lean_object* v_t_3275_, lean_object* v_a_3276_, lean_object* v_f_3277_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3274_, v_a_3276_, v_f_3277_, v_t_3275_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_modify(lean_object* v_00_u03b1_3279_, lean_object* v_cmp_3280_, lean_object* v_00_u03b2_3281_, lean_object* v_inst_3282_, lean_object* v_t_3283_, lean_object* v_a_3284_, lean_object* v_f_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3280_, v_a_3284_, v_f_3285_, v_t_3283_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_alter___redArg(lean_object* v_cmp_3287_, lean_object* v_t_3288_, lean_object* v_a_3289_, lean_object* v_f_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3287_, v_a_3289_, v_f_3290_, v_t_3288_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_alter(lean_object* v_00_u03b1_3292_, lean_object* v_cmp_3293_, lean_object* v_00_u03b2_3294_, lean_object* v_inst_3295_, lean_object* v_t_3296_, lean_object* v_a_3297_, lean_object* v_f_3298_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3293_, v_a_3297_, v_f_3298_, v_t_3296_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3300_, lean_object* v_cmp_3301_, lean_object* v_t_3302_, lean_object* v_a_3303_, lean_object* v_b_u2082_3304_){
_start:
{
lean_object* v___f_3305_; lean_object* v___x_3306_; 
lean_inc(v_a_3303_);
v___f_3305_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3305_, 0, v_b_u2082_3304_);
lean_closure_set(v___f_3305_, 1, v_mergeFn_3300_);
lean_closure_set(v___f_3305_, 2, v_a_3303_);
v___x_3306_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3301_, v_a_3303_, v___f_3305_, v_t_3302_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith___redArg(lean_object* v_cmp_3307_, lean_object* v_mergeFn_3308_, lean_object* v_t_u2081_3309_, lean_object* v_t_u2082_3310_){
_start:
{
lean_object* v___f_3311_; lean_object* v___x_3312_; 
v___f_3311_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3311_, 0, v_mergeFn_3308_);
lean_closure_set(v___f_3311_, 1, v_cmp_3307_);
v___x_3312_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3311_, v_t_u2081_3309_, v_t_u2082_3310_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith(lean_object* v_00_u03b1_3313_, lean_object* v_cmp_3314_, lean_object* v_00_u03b2_3315_, lean_object* v_inst_3316_, lean_object* v_mergeFn_3317_, lean_object* v_t_u2081_3318_, lean_object* v_t_u2082_3319_){
_start:
{
lean_object* v___f_3320_; lean_object* v___x_3321_; 
v___f_3320_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3320_, 0, v_mergeFn_3317_);
lean_closure_set(v___f_3320_, 1, v_cmp_3314_);
v___x_3321_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3320_, v_t_u2081_3318_, v_t_u2082_3319_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_3322_, lean_object* v_x_3323_, lean_object* v_____s_3324_){
_start:
{
lean_object* v_fst_3325_; lean_object* v_snd_3326_; lean_object* v_acc_3327_; lean_object* v___x_3328_; 
v_fst_3325_ = lean_ctor_get(v_x_3323_, 0);
lean_inc(v_fst_3325_);
v_snd_3326_ = lean_ctor_get(v_x_3323_, 1);
lean_inc(v_snd_3326_);
lean_dec_ref(v_x_3323_);
v_acc_3327_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3322_, v_fst_3325_, v_snd_3326_, v_____s_3324_);
v___x_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_acc_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany___redArg(lean_object* v_cmp_3329_, lean_object* v_inst_3330_, lean_object* v_t_3331_, lean_object* v_l_3332_){
_start:
{
lean_object* v___f_3333_; lean_object* v___x_3334_; 
v___f_3333_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3333_, 0, v_cmp_3329_);
v___x_3334_ = lean_apply_4(v_inst_3330_, lean_box(0), v_l_3332_, v_t_3331_, v___f_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany(lean_object* v_00_u03b1_3335_, lean_object* v_00_u03b2_3336_, lean_object* v_cmp_3337_, lean_object* v_inst_3338_, lean_object* v_00_u03c1_3339_, lean_object* v_inst_3340_, lean_object* v_t_3341_, lean_object* v_l_3342_){
_start:
{
lean_object* v___f_3343_; lean_object* v___x_3344_; 
v___f_3343_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3343_, 0, v_cmp_3337_);
v___x_3344_ = lean_apply_4(v_inst_3340_, lean_box(0), v_l_3342_, v_t_3341_, v___f_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_3345_, lean_object* v_a_3346_, lean_object* v_____s_3347_){
_start:
{
lean_object* v_acc_3348_; lean_object* v___x_3349_; 
v_acc_3348_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_3345_, v_a_3346_, v_____s_3347_);
v___x_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_acc_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany___redArg(lean_object* v_cmp_3350_, lean_object* v_inst_3351_, lean_object* v_t_3352_, lean_object* v_l_3353_){
_start:
{
lean_object* v___f_3354_; lean_object* v___x_3355_; 
v___f_3354_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3354_, 0, v_cmp_3350_);
v___x_3355_ = lean_apply_4(v_inst_3351_, lean_box(0), v_l_3353_, v_t_3352_, v___f_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany(lean_object* v_00_u03b1_3356_, lean_object* v_00_u03b2_3357_, lean_object* v_cmp_3358_, lean_object* v_inst_3359_, lean_object* v_00_u03c1_3360_, lean_object* v_inst_3361_, lean_object* v_t_3362_, lean_object* v_l_3363_){
_start:
{
lean_object* v___f_3364_; lean_object* v___x_3365_; 
v___f_3364_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3364_, 0, v_cmp_3358_);
v___x_3365_ = lean_apply_4(v_inst_3361_, lean_box(0), v_l_3363_, v_t_3362_, v___f_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0(lean_object* v_cmp_3366_, lean_object* v_x_3367_, lean_object* v_____s_3368_){
_start:
{
lean_object* v_fst_3369_; lean_object* v_snd_3370_; lean_object* v_acc_3371_; lean_object* v___x_3372_; 
v_fst_3369_ = lean_ctor_get(v_x_3367_, 0);
lean_inc(v_fst_3369_);
v_snd_3370_ = lean_ctor_get(v_x_3367_, 1);
lean_inc(v_snd_3370_);
lean_dec_ref(v_x_3367_);
v_acc_3371_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3366_, v_fst_3369_, v_snd_3370_, v_____s_3368_);
v___x_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3372_, 0, v_acc_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany___redArg(lean_object* v_cmp_3373_, lean_object* v_inst_3374_, lean_object* v_t_3375_, lean_object* v_l_3376_){
_start:
{
lean_object* v___f_3377_; lean_object* v___x_3378_; 
v___f_3377_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3377_, 0, v_cmp_3373_);
v___x_3378_ = lean_apply_4(v_inst_3374_, lean_box(0), v_l_3376_, v_t_3375_, v___f_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany(lean_object* v_00_u03b1_3379_, lean_object* v_cmp_3380_, lean_object* v_00_u03b2_3381_, lean_object* v_inst_3382_, lean_object* v_00_u03c1_3383_, lean_object* v_inst_3384_, lean_object* v_t_3385_, lean_object* v_l_3386_){
_start:
{
lean_object* v___f_3387_; lean_object* v___x_3388_; 
v___f_3387_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3387_, 0, v_cmp_3380_);
v___x_3388_ = lean_apply_4(v_inst_3384_, lean_box(0), v_l_3386_, v_t_3385_, v___f_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_3389_, lean_object* v_a_3390_, lean_object* v_____s_3391_){
_start:
{
uint8_t v___x_3392_; 
lean_inc(v_____s_3391_);
lean_inc(v_a_3390_);
lean_inc_ref(v_cmp_3389_);
v___x_3392_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3389_, v_a_3390_, v_____s_3391_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = lean_box(0);
v___x_3394_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3389_, v_a_3390_, v___x_3393_, v_____s_3391_);
v___x_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
return v___x_3395_;
}
else
{
lean_object* v___x_3396_; 
lean_dec(v_a_3390_);
lean_dec_ref(v_cmp_3389_);
v___x_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3396_, 0, v_____s_3391_);
return v___x_3396_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_3397_, lean_object* v_inst_3398_, lean_object* v_t_3399_, lean_object* v_l_3400_){
_start:
{
lean_object* v___f_3401_; lean_object* v___x_3402_; 
v___f_3401_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3401_, 0, v_cmp_3397_);
v___x_3402_ = lean_apply_4(v_inst_3398_, lean_box(0), v_l_3400_, v_t_3399_, v___f_3401_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_3403_, lean_object* v_cmp_3404_, lean_object* v_inst_3405_, lean_object* v_00_u03c1_3406_, lean_object* v_inst_3407_, lean_object* v_t_3408_, lean_object* v_l_3409_){
_start:
{
lean_object* v___f_3410_; lean_object* v___x_3411_; 
v___f_3410_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3410_, 0, v_cmp_3404_);
v___x_3411_ = lean_apply_4(v_inst_3407_, lean_box(0), v_l_3409_, v_t_3408_, v___f_3410_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_union___redArg(lean_object* v_cmp_3412_, lean_object* v_m_u2081_3413_, lean_object* v_m_u2082_3414_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3412_, v_m_u2081_3413_, v_m_u2082_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_union(lean_object* v_00_u03b1_3416_, lean_object* v_00_u03b2_3417_, lean_object* v_cmp_3418_, lean_object* v_inst_3419_, lean_object* v_m_u2081_3420_, lean_object* v_m_u2082_3421_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3418_, v_m_u2081_3420_, v_m_u2082_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instUnionOfTransCmp___redArg(lean_object* v_cmp_3423_){
_start:
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_union), 6, 4);
lean_closure_set(v___x_3424_, 0, lean_box(0));
lean_closure_set(v___x_3424_, 1, lean_box(0));
lean_closure_set(v___x_3424_, 2, v_cmp_3423_);
lean_closure_set(v___x_3424_, 3, lean_box(0));
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instUnionOfTransCmp(lean_object* v_00_u03b1_3425_, lean_object* v_00_u03b2_3426_, lean_object* v_cmp_3427_, lean_object* v_inst_3428_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_union), 6, 4);
lean_closure_set(v___x_3429_, 0, lean_box(0));
lean_closure_set(v___x_3429_, 1, lean_box(0));
lean_closure_set(v___x_3429_, 2, v_cmp_3427_);
lean_closure_set(v___x_3429_, 3, lean_box(0));
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_inter___redArg(lean_object* v_cmp_3430_, lean_object* v_m_u2081_3431_, lean_object* v_m_u2082_3432_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3430_, v_m_u2081_3431_, v_m_u2082_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_inter(lean_object* v_00_u03b1_3434_, lean_object* v_00_u03b2_3435_, lean_object* v_cmp_3436_, lean_object* v_inst_3437_, lean_object* v_m_u2081_3438_, lean_object* v_m_u2082_3439_){
_start:
{
lean_object* v___x_3440_; 
v___x_3440_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3436_, v_m_u2081_3438_, v_m_u2082_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInterOfTransCmp___redArg(lean_object* v_cmp_3441_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_inter), 6, 4);
lean_closure_set(v___x_3442_, 0, lean_box(0));
lean_closure_set(v___x_3442_, 1, lean_box(0));
lean_closure_set(v___x_3442_, 2, v_cmp_3441_);
lean_closure_set(v___x_3442_, 3, lean_box(0));
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInterOfTransCmp(lean_object* v_00_u03b1_3443_, lean_object* v_00_u03b2_3444_, lean_object* v_cmp_3445_, lean_object* v_inst_3446_){
_start:
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_inter), 6, 4);
lean_closure_set(v___x_3447_, 0, lean_box(0));
lean_closure_set(v___x_3447_, 1, lean_box(0));
lean_closure_set(v___x_3447_, 2, v_cmp_3445_);
lean_closure_set(v___x_3447_, 3, lean_box(0));
return v___x_3447_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(lean_object* v_cmp_3448_, lean_object* v_inst_3449_, lean_object* v_x_3450_, lean_object* v_y_3451_){
_start:
{
uint8_t v___x_3452_; 
v___x_3452_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3448_, v_inst_3449_, v_x_3450_, v_y_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_3453_, lean_object* v_inst_3454_, lean_object* v_x_3455_, lean_object* v_y_3456_){
_start:
{
uint8_t v_res_3457_; lean_object* v_r_3458_; 
v_res_3457_ = l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(v_cmp_3453_, v_inst_3454_, v_x_3455_, v_y_3456_);
v_r_3458_ = lean_box(v_res_3457_);
return v_r_3458_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(lean_object* v_cmp_3459_, lean_object* v_inst_3460_){
_start:
{
lean_object* v___f_3461_; lean_object* v___x_3462_; 
lean_inc_ref(v_cmp_3459_);
v___f_3461_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3461_, 0, v_cmp_3459_);
lean_closure_set(v___f_3461_, 1, v_inst_3460_);
v___x_3462_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_lift_u2082___boxed), 8, 6);
lean_closure_set(v___x_3462_, 0, lean_box(0));
lean_closure_set(v___x_3462_, 1, lean_box(0));
lean_closure_set(v___x_3462_, 2, v_cmp_3459_);
lean_closure_set(v___x_3462_, 3, lean_box(0));
lean_closure_set(v___x_3462_, 4, v___f_3461_);
lean_closure_set(v___x_3462_, 5, lean_box(0));
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp(lean_object* v_00_u03b1_3463_, lean_object* v_00_u03b2_3464_, lean_object* v_cmp_3465_, lean_object* v_inst_3466_, lean_object* v_inst_3467_, lean_object* v_inst_3468_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_3465_, v_inst_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object* v_cmp_3470_, lean_object* v_inst_3471_, lean_object* v_x_3472_, lean_object* v_x_3473_){
_start:
{
uint8_t v___x_3474_; 
v___x_3474_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3470_, v_inst_3471_, v_x_3472_, v_x_3473_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_3475_, lean_object* v_inst_3476_, lean_object* v_x_3477_, lean_object* v_x_3478_){
_start:
{
uint8_t v_res_3479_; lean_object* v_r_3480_; 
v_res_3479_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(v_cmp_3475_, v_inst_3476_, v_x_3477_, v_x_3478_);
v_r_3480_ = lean_box(v_res_3479_);
return v_r_3480_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object* v_00_u03b1_3481_, lean_object* v_00_u03b2_3482_, lean_object* v_cmp_3483_, lean_object* v_inst_3484_, lean_object* v_inst_3485_, lean_object* v_inst_3486_, lean_object* v_inst_3487_, lean_object* v_x_3488_, lean_object* v_x_3489_){
_start:
{
uint8_t v___x_3490_; 
v___x_3490_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3483_, v_inst_3486_, v_x_3488_, v_x_3489_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_3491_, lean_object* v_00_u03b2_3492_, lean_object* v_cmp_3493_, lean_object* v_inst_3494_, lean_object* v_inst_3495_, lean_object* v_inst_3496_, lean_object* v_inst_3497_, lean_object* v_x_3498_, lean_object* v_x_3499_){
_start:
{
uint8_t v_res_3500_; lean_object* v_r_3501_; 
v_res_3500_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(v_00_u03b1_3491_, v_00_u03b2_3492_, v_cmp_3493_, v_inst_3494_, v_inst_3495_, v_inst_3496_, v_inst_3497_, v_x_3498_, v_x_3499_);
v_r_3501_ = lean_box(v_res_3500_);
return v_r_3501_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_Const_beq___redArg(lean_object* v_cmp_3502_, lean_object* v_inst_3503_, lean_object* v_m_u2081_3504_, lean_object* v_m_u2082_3505_){
_start:
{
uint8_t v___x_3506_; 
v___x_3506_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3502_, v_inst_3503_, v_m_u2081_3504_, v_m_u2082_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_beq___redArg___boxed(lean_object* v_cmp_3507_, lean_object* v_inst_3508_, lean_object* v_m_u2081_3509_, lean_object* v_m_u2082_3510_){
_start:
{
uint8_t v_res_3511_; lean_object* v_r_3512_; 
v_res_3511_ = l_Std_ExtDTreeMap_Const_beq___redArg(v_cmp_3507_, v_inst_3508_, v_m_u2081_3509_, v_m_u2082_3510_);
v_r_3512_ = lean_box(v_res_3511_);
return v_r_3512_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_Const_beq(lean_object* v_00_u03b1_3513_, lean_object* v_cmp_3514_, lean_object* v_00_u03b2_3515_, lean_object* v_inst_3516_, lean_object* v_inst_3517_, lean_object* v_m_u2081_3518_, lean_object* v_m_u2082_3519_){
_start:
{
uint8_t v___x_3520_; 
v___x_3520_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3514_, v_inst_3517_, v_m_u2081_3518_, v_m_u2082_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_beq___boxed(lean_object* v_00_u03b1_3521_, lean_object* v_cmp_3522_, lean_object* v_00_u03b2_3523_, lean_object* v_inst_3524_, lean_object* v_inst_3525_, lean_object* v_m_u2081_3526_, lean_object* v_m_u2082_3527_){
_start:
{
uint8_t v_res_3528_; lean_object* v_r_3529_; 
v_res_3528_ = l_Std_ExtDTreeMap_Const_beq(v_00_u03b1_3521_, v_cmp_3522_, v_00_u03b2_3523_, v_inst_3524_, v_inst_3525_, v_m_u2081_3526_, v_m_u2082_3527_);
v_r_3529_ = lean_box(v_res_3528_);
return v_r_3529_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_diff___redArg(lean_object* v_cmp_3530_, lean_object* v_m_u2081_3531_, lean_object* v_m_u2082_3532_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_3530_, v_m_u2081_3531_, v_m_u2082_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_diff(lean_object* v_00_u03b1_3534_, lean_object* v_00_u03b2_3535_, lean_object* v_cmp_3536_, lean_object* v_inst_3537_, lean_object* v_m_u2081_3538_, lean_object* v_m_u2082_3539_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_3536_, v_m_u2081_3538_, v_m_u2082_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSDiffOfTransCmp___redArg(lean_object* v_cmp_3541_){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_diff), 6, 4);
lean_closure_set(v___x_3542_, 0, lean_box(0));
lean_closure_set(v___x_3542_, 1, lean_box(0));
lean_closure_set(v___x_3542_, 2, v_cmp_3541_);
lean_closure_set(v___x_3542_, 3, lean_box(0));
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSDiffOfTransCmp(lean_object* v_00_u03b1_3543_, lean_object* v_00_u03b2_3544_, lean_object* v_cmp_3545_, lean_object* v_inst_3546_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_diff), 6, 4);
lean_closure_set(v___x_3547_, 0, lean_box(0));
lean_closure_set(v___x_3547_, 1, lean_box(0));
lean_closure_set(v___x_3547_, 2, v_cmp_3545_);
lean_closure_set(v___x_3547_, 3, lean_box(0));
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_3551_, lean_object* v___x_3552_, lean_object* v_m_3553_, lean_object* v_prec_3554_){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3555_ = ((lean_object*)(l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_3556_ = lean_box(0);
v___x_3557_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3558_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3557_, v___f_3551_, v___x_3556_, v_m_3553_);
v___x_3559_ = l_List_repr___redArg(v___x_3552_, v___x_3558_);
v___x_3560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3555_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = l_Repr_addAppParen(v___x_3560_, v_prec_3554_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_3562_, lean_object* v___x_3563_, lean_object* v_m_3564_, lean_object* v_prec_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(v___f_3562_, v___x_3563_, v_m_3564_, v_prec_3565_);
lean_dec(v_prec_3565_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(lean_object* v_inst_3567_, lean_object* v_inst_3568_){
_start:
{
lean_object* v___f_3569_; lean_object* v___x_3570_; lean_object* v___f_3571_; 
v___f_3569_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3570_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_3570_, 0, lean_box(0));
lean_closure_set(v___x_3570_, 1, lean_box(0));
lean_closure_set(v___x_3570_, 2, v_inst_3567_);
lean_closure_set(v___x_3570_, 3, v_inst_3568_);
v___f_3571_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3571_, 0, v___f_3569_);
lean_closure_set(v___f_3571_, 1, v___x_3570_);
return v___f_3571_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp(lean_object* v_00_u03b1_3572_, lean_object* v_00_u03b2_3573_, lean_object* v_cmp_3574_, lean_object* v_inst_3575_, lean_object* v_inst_3576_, lean_object* v_inst_3577_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(v_inst_3576_, v_inst_3577_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_3579_, lean_object* v_00_u03b2_3580_, lean_object* v_cmp_3581_, lean_object* v_inst_3582_, lean_object* v_inst_3583_, lean_object* v_inst_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Std_ExtDTreeMap_instReprOfTransCmp(v_00_u03b1_3579_, v_00_u03b2_3580_, v_cmp_3581_, v_inst_3582_, v_inst_3583_, v_inst_3584_);
lean_dec_ref(v_cmp_3581_);
return v_res_3585_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ExtDTreeMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
