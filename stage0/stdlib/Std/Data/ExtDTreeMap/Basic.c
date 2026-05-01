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
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___redArg___boxed(lean_object* v_cmp_458_, lean_object* v_t_459_, lean_object* v_a_460_, lean_object* v_inst_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_ExtDTreeMap_get_x21___redArg(v_cmp_458_, v_t_459_, v_a_460_, v_inst_461_);
lean_dec(v_inst_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21(lean_object* v_00_u03b1_463_, lean_object* v_00_u03b2_464_, lean_object* v_cmp_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_t_468_, lean_object* v_a_469_, lean_object* v_inst_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_465_, v_t_468_, v_a_469_, v_inst_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_get_x21___boxed(lean_object* v_00_u03b1_472_, lean_object* v_00_u03b2_473_, lean_object* v_cmp_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_t_477_, lean_object* v_a_478_, lean_object* v_inst_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_ExtDTreeMap_get_x21(v_00_u03b1_472_, v_00_u03b2_473_, v_cmp_474_, v_inst_475_, v_inst_476_, v_t_477_, v_a_478_, v_inst_479_);
lean_dec(v_inst_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg(lean_object* v_cmp_481_, lean_object* v_t_482_, lean_object* v_a_483_, lean_object* v_fallback_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_481_, v_t_482_, v_a_483_, v_fallback_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___redArg___boxed(lean_object* v_cmp_486_, lean_object* v_t_487_, lean_object* v_a_488_, lean_object* v_fallback_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_ExtDTreeMap_getD___redArg(v_cmp_486_, v_t_487_, v_a_488_, v_fallback_489_);
lean_dec(v_fallback_489_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD(lean_object* v_00_u03b1_491_, lean_object* v_00_u03b2_492_, lean_object* v_cmp_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_t_496_, lean_object* v_a_497_, lean_object* v_fallback_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_493_, v_t_496_, v_a_497_, v_fallback_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getD___boxed(lean_object* v_00_u03b1_500_, lean_object* v_00_u03b2_501_, lean_object* v_cmp_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_t_505_, lean_object* v_a_506_, lean_object* v_fallback_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_ExtDTreeMap_getD(v_00_u03b1_500_, v_00_u03b2_501_, v_cmp_502_, v_inst_503_, v_inst_504_, v_t_505_, v_a_506_, v_fallback_507_);
lean_dec(v_fallback_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f___redArg(lean_object* v_cmp_509_, lean_object* v_t_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_509_, v_t_510_, v_a_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x3f(lean_object* v_00_u03b1_513_, lean_object* v_00_u03b2_514_, lean_object* v_cmp_515_, lean_object* v_inst_516_, lean_object* v_t_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_515_, v_t_517_, v_a_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey___redArg(lean_object* v_cmp_520_, lean_object* v_t_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_520_, v_t_521_, v_a_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey(lean_object* v_00_u03b1_524_, lean_object* v_00_u03b2_525_, lean_object* v_cmp_526_, lean_object* v_inst_527_, lean_object* v_t_528_, lean_object* v_a_529_, lean_object* v_h_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_526_, v_t_528_, v_a_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___redArg(lean_object* v_cmp_532_, lean_object* v_inst_533_, lean_object* v_t_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_532_, v_t_534_, v_a_535_, v_inst_533_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___redArg___boxed(lean_object* v_cmp_537_, lean_object* v_inst_538_, lean_object* v_t_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_ExtDTreeMap_getKey_x21___redArg(v_cmp_537_, v_inst_538_, v_t_539_, v_a_540_);
lean_dec(v_inst_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_, lean_object* v_cmp_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_t_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_544_, v_t_547_, v_a_548_, v_inst_546_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKey_x21___boxed(lean_object* v_00_u03b1_550_, lean_object* v_00_u03b2_551_, lean_object* v_cmp_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_t_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_ExtDTreeMap_getKey_x21(v_00_u03b1_550_, v_00_u03b2_551_, v_cmp_552_, v_inst_553_, v_inst_554_, v_t_555_, v_a_556_);
lean_dec(v_inst_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___redArg(lean_object* v_cmp_558_, lean_object* v_t_559_, lean_object* v_a_560_, lean_object* v_fallback_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_558_, v_t_559_, v_a_560_, v_fallback_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_563_, lean_object* v_t_564_, lean_object* v_a_565_, lean_object* v_fallback_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_ExtDTreeMap_getKeyD___redArg(v_cmp_563_, v_t_564_, v_a_565_, v_fallback_566_);
lean_dec(v_fallback_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD(lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_cmp_570_, lean_object* v_inst_571_, lean_object* v_t_572_, lean_object* v_a_573_, lean_object* v_fallback_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_570_, v_t_572_, v_a_573_, v_fallback_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_576_, lean_object* v_00_u03b2_577_, lean_object* v_cmp_578_, lean_object* v_inst_579_, lean_object* v_t_580_, lean_object* v_a_581_, lean_object* v_fallback_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_ExtDTreeMap_getKeyD(v_00_u03b1_576_, v_00_u03b2_577_, v_cmp_578_, v_inst_579_, v_t_580_, v_a_581_, v_fallback_582_);
lean_dec(v_fallback_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___redArg(lean_object* v_t_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_ExtDTreeMap_minEntry_x3f___redArg(v_t_586_);
lean_dec(v_t_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_cmp_590_, lean_object* v_inst_591_, lean_object* v_t_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_594_, lean_object* v_00_u03b2_595_, lean_object* v_cmp_596_, lean_object* v_inst_597_, lean_object* v_t_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_ExtDTreeMap_minEntry_x3f(v_00_u03b1_594_, v_00_u03b2_595_, v_cmp_596_, v_inst_597_, v_t_598_);
lean_dec(v_t_598_);
lean_dec_ref(v_cmp_596_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___redArg(lean_object* v_t_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___redArg___boxed(lean_object* v_t_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_ExtDTreeMap_minEntry___redArg(v_t_602_);
lean_dec(v_t_602_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry(lean_object* v_00_u03b1_604_, lean_object* v_00_u03b2_605_, lean_object* v_cmp_606_, lean_object* v_inst_607_, lean_object* v_t_608_, lean_object* v_h_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry___boxed(lean_object* v_00_u03b1_611_, lean_object* v_00_u03b2_612_, lean_object* v_cmp_613_, lean_object* v_inst_614_, lean_object* v_t_615_, lean_object* v_h_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_ExtDTreeMap_minEntry(v_00_u03b1_611_, v_00_u03b2_612_, v_cmp_613_, v_inst_614_, v_t_615_, v_h_616_);
lean_dec(v_t_615_);
lean_dec_ref(v_cmp_613_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___redArg(lean_object* v_inst_618_, lean_object* v_t_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_618_, v_t_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_621_, lean_object* v_t_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_ExtDTreeMap_minEntry_x21___redArg(v_inst_621_, v_t_622_);
lean_dec(v_t_622_);
lean_dec_ref(v_inst_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21(lean_object* v_00_u03b1_624_, lean_object* v_00_u03b2_625_, lean_object* v_cmp_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_t_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_628_, v_t_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_631_, lean_object* v_00_u03b2_632_, lean_object* v_cmp_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_t_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Std_ExtDTreeMap_minEntry_x21(v_00_u03b1_631_, v_00_u03b2_632_, v_cmp_633_, v_inst_634_, v_inst_635_, v_t_636_);
lean_dec(v_t_636_);
lean_dec_ref(v_inst_635_);
lean_dec_ref(v_cmp_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___redArg(lean_object* v_t_638_, lean_object* v_fallback_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_638_, v_fallback_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___redArg___boxed(lean_object* v_t_641_, lean_object* v_fallback_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_ExtDTreeMap_minEntryD___redArg(v_t_641_, v_fallback_642_);
lean_dec_ref(v_fallback_642_);
lean_dec(v_t_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD(lean_object* v_00_u03b1_644_, lean_object* v_00_u03b2_645_, lean_object* v_cmp_646_, lean_object* v_inst_647_, lean_object* v_t_648_, lean_object* v_fallback_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_648_, v_fallback_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_651_, lean_object* v_00_u03b2_652_, lean_object* v_cmp_653_, lean_object* v_inst_654_, lean_object* v_t_655_, lean_object* v_fallback_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_ExtDTreeMap_minEntryD(v_00_u03b1_651_, v_00_u03b2_652_, v_cmp_653_, v_inst_654_, v_t_655_, v_fallback_656_);
lean_dec_ref(v_fallback_656_);
lean_dec(v_t_655_);
lean_dec_ref(v_cmp_653_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___redArg(lean_object* v_t_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_ExtDTreeMap_maxEntry_x3f___redArg(v_t_660_);
lean_dec(v_t_660_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_cmp_664_, lean_object* v_inst_665_, lean_object* v_t_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_cmp_670_, lean_object* v_inst_671_, lean_object* v_t_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_ExtDTreeMap_maxEntry_x3f(v_00_u03b1_668_, v_00_u03b2_669_, v_cmp_670_, v_inst_671_, v_t_672_);
lean_dec(v_t_672_);
lean_dec_ref(v_cmp_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___redArg(lean_object* v_t_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___redArg___boxed(lean_object* v_t_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_ExtDTreeMap_maxEntry___redArg(v_t_676_);
lean_dec(v_t_676_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_cmp_680_, lean_object* v_inst_681_, lean_object* v_t_682_, lean_object* v_h_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_685_, lean_object* v_00_u03b2_686_, lean_object* v_cmp_687_, lean_object* v_inst_688_, lean_object* v_t_689_, lean_object* v_h_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_ExtDTreeMap_maxEntry(v_00_u03b1_685_, v_00_u03b2_686_, v_cmp_687_, v_inst_688_, v_t_689_, v_h_690_);
lean_dec(v_t_689_);
lean_dec_ref(v_cmp_687_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___redArg(lean_object* v_inst_692_, lean_object* v_t_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_692_, v_t_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_695_, lean_object* v_t_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_ExtDTreeMap_maxEntry_x21___redArg(v_inst_695_, v_t_696_);
lean_dec(v_t_696_);
lean_dec_ref(v_inst_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_cmp_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_t_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_702_, v_t_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_705_, lean_object* v_00_u03b2_706_, lean_object* v_cmp_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_t_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_ExtDTreeMap_maxEntry_x21(v_00_u03b1_705_, v_00_u03b2_706_, v_cmp_707_, v_inst_708_, v_inst_709_, v_t_710_);
lean_dec(v_t_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_cmp_707_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___redArg(lean_object* v_t_712_, lean_object* v_fallback_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_712_, v_fallback_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_715_, lean_object* v_fallback_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_ExtDTreeMap_maxEntryD___redArg(v_t_715_, v_fallback_716_);
lean_dec_ref(v_fallback_716_);
lean_dec(v_t_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD(lean_object* v_00_u03b1_718_, lean_object* v_00_u03b2_719_, lean_object* v_cmp_720_, lean_object* v_inst_721_, lean_object* v_t_722_, lean_object* v_fallback_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_722_, v_fallback_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_725_, lean_object* v_00_u03b2_726_, lean_object* v_cmp_727_, lean_object* v_inst_728_, lean_object* v_t_729_, lean_object* v_fallback_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_ExtDTreeMap_maxEntryD(v_00_u03b1_725_, v_00_u03b2_726_, v_cmp_727_, v_inst_728_, v_t_729_, v_fallback_730_);
lean_dec_ref(v_fallback_730_);
lean_dec(v_t_729_);
lean_dec_ref(v_cmp_727_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___redArg(lean_object* v_t_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_ExtDTreeMap_minKey_x3f___redArg(v_t_734_);
lean_dec(v_t_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f(lean_object* v_00_u03b1_736_, lean_object* v_00_u03b2_737_, lean_object* v_cmp_738_, lean_object* v_inst_739_, lean_object* v_t_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_742_, lean_object* v_00_u03b2_743_, lean_object* v_cmp_744_, lean_object* v_inst_745_, lean_object* v_t_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_ExtDTreeMap_minKey_x3f(v_00_u03b1_742_, v_00_u03b2_743_, v_cmp_744_, v_inst_745_, v_t_746_);
lean_dec(v_t_746_);
lean_dec_ref(v_cmp_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___redArg(lean_object* v_t_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___redArg___boxed(lean_object* v_t_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_ExtDTreeMap_minKey___redArg(v_t_750_);
lean_dec(v_t_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey(lean_object* v_00_u03b1_752_, lean_object* v_00_u03b2_753_, lean_object* v_cmp_754_, lean_object* v_inst_755_, lean_object* v_t_756_, lean_object* v_h_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey___boxed(lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_cmp_761_, lean_object* v_inst_762_, lean_object* v_t_763_, lean_object* v_h_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_ExtDTreeMap_minKey(v_00_u03b1_759_, v_00_u03b2_760_, v_cmp_761_, v_inst_762_, v_t_763_, v_h_764_);
lean_dec(v_t_763_);
lean_dec_ref(v_cmp_761_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___redArg(lean_object* v_inst_766_, lean_object* v_t_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_766_, v_t_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_769_, lean_object* v_t_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_ExtDTreeMap_minKey_x21___redArg(v_inst_769_, v_t_770_);
lean_dec(v_t_770_);
lean_dec(v_inst_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_cmp_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_t_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_776_, v_t_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_779_, lean_object* v_00_u03b2_780_, lean_object* v_cmp_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_t_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_ExtDTreeMap_minKey_x21(v_00_u03b1_779_, v_00_u03b2_780_, v_cmp_781_, v_inst_782_, v_inst_783_, v_t_784_);
lean_dec(v_t_784_);
lean_dec(v_inst_783_);
lean_dec_ref(v_cmp_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___redArg(lean_object* v_t_786_, lean_object* v_fallback_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_786_, v_fallback_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___redArg___boxed(lean_object* v_t_789_, lean_object* v_fallback_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_ExtDTreeMap_minKeyD___redArg(v_t_789_, v_fallback_790_);
lean_dec(v_fallback_790_);
lean_dec(v_t_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_cmp_794_, lean_object* v_inst_795_, lean_object* v_t_796_, lean_object* v_fallback_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_796_, v_fallback_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_799_, lean_object* v_00_u03b2_800_, lean_object* v_cmp_801_, lean_object* v_inst_802_, lean_object* v_t_803_, lean_object* v_fallback_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_ExtDTreeMap_minKeyD(v_00_u03b1_799_, v_00_u03b2_800_, v_cmp_801_, v_inst_802_, v_t_803_, v_fallback_804_);
lean_dec(v_fallback_804_);
lean_dec(v_t_803_);
lean_dec_ref(v_cmp_801_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___redArg(lean_object* v_t_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_ExtDTreeMap_maxKey_x3f___redArg(v_t_808_);
lean_dec(v_t_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f(lean_object* v_00_u03b1_810_, lean_object* v_00_u03b2_811_, lean_object* v_cmp_812_, lean_object* v_inst_813_, lean_object* v_t_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_cmp_818_, lean_object* v_inst_819_, lean_object* v_t_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Std_ExtDTreeMap_maxKey_x3f(v_00_u03b1_816_, v_00_u03b2_817_, v_cmp_818_, v_inst_819_, v_t_820_);
lean_dec(v_t_820_);
lean_dec_ref(v_cmp_818_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___redArg(lean_object* v_t_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___redArg___boxed(lean_object* v_t_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_ExtDTreeMap_maxKey___redArg(v_t_824_);
lean_dec(v_t_824_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey(lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_cmp_828_, lean_object* v_inst_829_, lean_object* v_t_830_, lean_object* v_h_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_830_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey___boxed(lean_object* v_00_u03b1_833_, lean_object* v_00_u03b2_834_, lean_object* v_cmp_835_, lean_object* v_inst_836_, lean_object* v_t_837_, lean_object* v_h_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_ExtDTreeMap_maxKey(v_00_u03b1_833_, v_00_u03b2_834_, v_cmp_835_, v_inst_836_, v_t_837_, v_h_838_);
lean_dec(v_t_837_);
lean_dec_ref(v_cmp_835_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___redArg(lean_object* v_inst_840_, lean_object* v_t_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_840_, v_t_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_843_, lean_object* v_t_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_ExtDTreeMap_maxKey_x21___redArg(v_inst_843_, v_t_844_);
lean_dec(v_t_844_);
lean_dec(v_inst_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21(lean_object* v_00_u03b1_846_, lean_object* v_00_u03b2_847_, lean_object* v_cmp_848_, lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_t_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_850_, v_t_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_853_, lean_object* v_00_u03b2_854_, lean_object* v_cmp_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_t_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_ExtDTreeMap_maxKey_x21(v_00_u03b1_853_, v_00_u03b2_854_, v_cmp_855_, v_inst_856_, v_inst_857_, v_t_858_);
lean_dec(v_t_858_);
lean_dec(v_inst_857_);
lean_dec_ref(v_cmp_855_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___redArg(lean_object* v_t_860_, lean_object* v_fallback_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_860_, v_fallback_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_863_, lean_object* v_fallback_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_ExtDTreeMap_maxKeyD___redArg(v_t_863_, v_fallback_864_);
lean_dec(v_fallback_864_);
lean_dec(v_t_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD(lean_object* v_00_u03b1_866_, lean_object* v_00_u03b2_867_, lean_object* v_cmp_868_, lean_object* v_inst_869_, lean_object* v_t_870_, lean_object* v_fallback_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_870_, v_fallback_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_873_, lean_object* v_00_u03b2_874_, lean_object* v_cmp_875_, lean_object* v_inst_876_, lean_object* v_t_877_, lean_object* v_fallback_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_ExtDTreeMap_maxKeyD(v_00_u03b1_873_, v_00_u03b2_874_, v_cmp_875_, v_inst_876_, v_t_877_, v_fallback_878_);
lean_dec(v_fallback_878_);
lean_dec(v_t_877_);
lean_dec_ref(v_cmp_875_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_880_, lean_object* v_n_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_880_, v_n_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_883_, lean_object* v_n_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(v_t_883_, v_n_884_);
lean_dec(v_t_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_886_, lean_object* v_00_u03b2_887_, lean_object* v_cmp_888_, lean_object* v_inst_889_, lean_object* v_t_890_, lean_object* v_n_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_890_, v_n_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_893_, lean_object* v_00_u03b2_894_, lean_object* v_cmp_895_, lean_object* v_inst_896_, lean_object* v_t_897_, lean_object* v_n_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_ExtDTreeMap_entryAtIdx_x3f(v_00_u03b1_893_, v_00_u03b2_894_, v_cmp_895_, v_inst_896_, v_t_897_, v_n_898_);
lean_dec(v_t_897_);
lean_dec_ref(v_cmp_895_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___redArg(lean_object* v_t_900_, lean_object* v_n_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_900_, v_n_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_903_, lean_object* v_n_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_ExtDTreeMap_entryAtIdx___redArg(v_t_903_, v_n_904_);
lean_dec(v_t_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx(lean_object* v_00_u03b1_906_, lean_object* v_00_u03b2_907_, lean_object* v_cmp_908_, lean_object* v_inst_909_, lean_object* v_t_910_, lean_object* v_n_911_, lean_object* v_h_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_910_, v_n_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_914_, lean_object* v_00_u03b2_915_, lean_object* v_cmp_916_, lean_object* v_inst_917_, lean_object* v_t_918_, lean_object* v_n_919_, lean_object* v_h_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_ExtDTreeMap_entryAtIdx(v_00_u03b1_914_, v_00_u03b2_915_, v_cmp_916_, v_inst_917_, v_t_918_, v_n_919_, v_h_920_);
lean_dec(v_t_918_);
lean_dec_ref(v_cmp_916_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_922_, lean_object* v_t_923_, lean_object* v_n_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_922_, v_t_923_, v_n_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_926_, lean_object* v_t_927_, lean_object* v_n_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(v_inst_926_, v_t_927_, v_n_928_);
lean_dec(v_t_927_);
lean_dec_ref(v_inst_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_930_, lean_object* v_00_u03b2_931_, lean_object* v_cmp_932_, lean_object* v_inst_933_, lean_object* v_inst_934_, lean_object* v_t_935_, lean_object* v_n_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_934_, v_t_935_, v_n_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_938_, lean_object* v_00_u03b2_939_, lean_object* v_cmp_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_t_943_, lean_object* v_n_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_ExtDTreeMap_entryAtIdx_x21(v_00_u03b1_938_, v_00_u03b2_939_, v_cmp_940_, v_inst_941_, v_inst_942_, v_t_943_, v_n_944_);
lean_dec(v_t_943_);
lean_dec_ref(v_inst_942_);
lean_dec_ref(v_cmp_940_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___redArg(lean_object* v_t_946_, lean_object* v_n_947_, lean_object* v_fallback_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_946_, v_n_947_, v_fallback_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_950_, lean_object* v_n_951_, lean_object* v_fallback_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_ExtDTreeMap_entryAtIdxD___redArg(v_t_950_, v_n_951_, v_fallback_952_);
lean_dec_ref(v_fallback_952_);
lean_dec(v_t_950_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD(lean_object* v_00_u03b1_954_, lean_object* v_00_u03b2_955_, lean_object* v_cmp_956_, lean_object* v_inst_957_, lean_object* v_t_958_, lean_object* v_n_959_, lean_object* v_fallback_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_958_, v_n_959_, v_fallback_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_962_, lean_object* v_00_u03b2_963_, lean_object* v_cmp_964_, lean_object* v_inst_965_, lean_object* v_t_966_, lean_object* v_n_967_, lean_object* v_fallback_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Std_ExtDTreeMap_entryAtIdxD(v_00_u03b1_962_, v_00_u03b2_963_, v_cmp_964_, v_inst_965_, v_t_966_, v_n_967_, v_fallback_968_);
lean_dec_ref(v_fallback_968_);
lean_dec(v_t_966_);
lean_dec_ref(v_cmp_964_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_970_, lean_object* v_n_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_970_, v_n_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_973_, lean_object* v_n_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(v_t_973_, v_n_974_);
lean_dec(v_t_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_976_, lean_object* v_00_u03b2_977_, lean_object* v_cmp_978_, lean_object* v_inst_979_, lean_object* v_t_980_, lean_object* v_n_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_980_, v_n_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_983_, lean_object* v_00_u03b2_984_, lean_object* v_cmp_985_, lean_object* v_inst_986_, lean_object* v_t_987_, lean_object* v_n_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_ExtDTreeMap_keyAtIdx_x3f(v_00_u03b1_983_, v_00_u03b2_984_, v_cmp_985_, v_inst_986_, v_t_987_, v_n_988_);
lean_dec(v_t_987_);
lean_dec_ref(v_cmp_985_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___redArg(lean_object* v_t_990_, lean_object* v_n_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_990_, v_n_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_993_, lean_object* v_n_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Std_ExtDTreeMap_keyAtIdx___redArg(v_t_993_, v_n_994_);
lean_dec(v_t_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx(lean_object* v_00_u03b1_996_, lean_object* v_00_u03b2_997_, lean_object* v_cmp_998_, lean_object* v_inst_999_, lean_object* v_t_1000_, lean_object* v_n_1001_, lean_object* v_h_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1000_, v_n_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_cmp_1006_, lean_object* v_inst_1007_, lean_object* v_t_1008_, lean_object* v_n_1009_, lean_object* v_h_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Std_ExtDTreeMap_keyAtIdx(v_00_u03b1_1004_, v_00_u03b2_1005_, v_cmp_1006_, v_inst_1007_, v_t_1008_, v_n_1009_, v_h_1010_);
lean_dec(v_t_1008_);
lean_dec_ref(v_cmp_1006_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_1012_, lean_object* v_t_1013_, lean_object* v_n_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1012_, v_t_1013_, v_n_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_1016_, lean_object* v_t_1017_, lean_object* v_n_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(v_inst_1016_, v_t_1017_, v_n_1018_);
lean_dec(v_t_1017_);
lean_dec(v_inst_1016_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_1020_, lean_object* v_00_u03b2_1021_, lean_object* v_cmp_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_t_1025_, lean_object* v_n_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1024_, v_t_1025_, v_n_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_00_u03b2_1029_, lean_object* v_cmp_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_t_1033_, lean_object* v_n_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Std_ExtDTreeMap_keyAtIdx_x21(v_00_u03b1_1028_, v_00_u03b2_1029_, v_cmp_1030_, v_inst_1031_, v_inst_1032_, v_t_1033_, v_n_1034_);
lean_dec(v_t_1033_);
lean_dec(v_inst_1032_);
lean_dec_ref(v_cmp_1030_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___redArg(lean_object* v_t_1036_, lean_object* v_n_1037_, lean_object* v_fallback_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1036_, v_n_1037_, v_fallback_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_1040_, lean_object* v_n_1041_, lean_object* v_fallback_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Std_ExtDTreeMap_keyAtIdxD___redArg(v_t_1040_, v_n_1041_, v_fallback_1042_);
lean_dec(v_fallback_1042_);
lean_dec(v_t_1040_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD(lean_object* v_00_u03b1_1044_, lean_object* v_00_u03b2_1045_, lean_object* v_cmp_1046_, lean_object* v_inst_1047_, lean_object* v_t_1048_, lean_object* v_n_1049_, lean_object* v_fallback_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1048_, v_n_1049_, v_fallback_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_1052_, lean_object* v_00_u03b2_1053_, lean_object* v_cmp_1054_, lean_object* v_inst_1055_, lean_object* v_t_1056_, lean_object* v_n_1057_, lean_object* v_fallback_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std_ExtDTreeMap_keyAtIdxD(v_00_u03b1_1052_, v_00_u03b2_1053_, v_cmp_1054_, v_inst_1055_, v_t_1056_, v_n_1057_, v_fallback_1058_);
lean_dec(v_fallback_1058_);
lean_dec(v_t_1056_);
lean_dec_ref(v_cmp_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1060_, lean_object* v_t_1061_, lean_object* v_k_1062_){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1060_, v_k_1062_, v___x_1063_, v_t_1061_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1065_, lean_object* v_00_u03b2_1066_, lean_object* v_cmp_1067_, lean_object* v_inst_1068_, lean_object* v_t_1069_, lean_object* v_k_1070_){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_box(0);
v___x_1072_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1067_, v_k_1070_, v___x_1071_, v_t_1069_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1073_, lean_object* v_t_1074_, lean_object* v_k_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1073_, v_k_1075_, v___x_1076_, v_t_1074_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_cmp_1080_, lean_object* v_inst_1081_, lean_object* v_t_1082_, lean_object* v_k_1083_){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_box(0);
v___x_1085_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1080_, v_k_1083_, v___x_1084_, v_t_1082_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1086_, lean_object* v_t_1087_, lean_object* v_k_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1086_, v_k_1088_, v___x_1089_, v_t_1087_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1091_, lean_object* v_00_u03b2_1092_, lean_object* v_cmp_1093_, lean_object* v_inst_1094_, lean_object* v_t_1095_, lean_object* v_k_1096_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_box(0);
v___x_1098_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1093_, v_k_1096_, v___x_1097_, v_t_1095_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1099_, lean_object* v_t_1100_, lean_object* v_k_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_box(0);
v___x_1103_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1099_, v_k_1101_, v___x_1102_, v_t_1100_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_cmp_1106_, lean_object* v_inst_1107_, lean_object* v_t_1108_, lean_object* v_k_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1106_, v_k_1109_, v___x_1110_, v_t_1108_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE___redArg(lean_object* v_cmp_1112_, lean_object* v_t_1113_, lean_object* v_k_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_1112_, v_k_1114_, v_t_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE(lean_object* v_00_u03b1_1116_, lean_object* v_00_u03b2_1117_, lean_object* v_cmp_1118_, lean_object* v_inst_1119_, lean_object* v_t_1120_, lean_object* v_k_1121_, lean_object* v_h_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_1118_, v_k_1121_, v_t_1120_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT___redArg(lean_object* v_cmp_1124_, lean_object* v_t_1125_, lean_object* v_k_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_1124_, v_k_1126_, v_t_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT(lean_object* v_00_u03b1_1128_, lean_object* v_00_u03b2_1129_, lean_object* v_cmp_1130_, lean_object* v_inst_1131_, lean_object* v_t_1132_, lean_object* v_k_1133_, lean_object* v_h_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_1130_, v_k_1133_, v_t_1132_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE___redArg(lean_object* v_cmp_1136_, lean_object* v_t_1137_, lean_object* v_k_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_1136_, v_k_1138_, v_t_1137_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE(lean_object* v_00_u03b1_1140_, lean_object* v_00_u03b2_1141_, lean_object* v_cmp_1142_, lean_object* v_inst_1143_, lean_object* v_t_1144_, lean_object* v_k_1145_, lean_object* v_h_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_1142_, v_k_1145_, v_t_1144_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT___redArg(lean_object* v_cmp_1148_, lean_object* v_t_1149_, lean_object* v_k_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_1148_, v_k_1150_, v_t_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT(lean_object* v_00_u03b1_1152_, lean_object* v_00_u03b2_1153_, lean_object* v_cmp_1154_, lean_object* v_inst_1155_, lean_object* v_t_1156_, lean_object* v_k_1157_, lean_object* v_h_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_1154_, v_k_1157_, v_t_1156_);
return v___x_1159_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1163_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1164_ = lean_unsigned_to_nat(14u);
v___x_1165_ = lean_unsigned_to_nat(22u);
v___x_1166_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1167_ = ((lean_object*)(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1168_ = l_mkPanicMessageWithDecl(v___x_1167_, v___x_1166_, v___x_1165_, v___x_1164_, v___x_1163_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1169_, lean_object* v_inst_1170_, lean_object* v_t_1171_, lean_object* v_k_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_box(0);
v___x_1174_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1169_, v_k_1172_, v___x_1173_, v_t_1171_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1176_ = l_panic___redArg(v_inst_1170_, v___x_1175_);
return v___x_1176_;
}
else
{
lean_object* v_val_1177_; 
v_val_1177_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_val_1177_);
lean_dec_ref(v___x_1174_);
return v_val_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1178_, lean_object* v_inst_1179_, lean_object* v_t_1180_, lean_object* v_k_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Std_ExtDTreeMap_getEntryGE_x21___redArg(v_cmp_1178_, v_inst_1179_, v_t_1180_, v_k_1181_);
lean_dec_ref(v_inst_1179_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_cmp_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_t_1188_, lean_object* v_k_1189_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_box(0);
v___x_1191_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1185_, v_k_1189_, v___x_1190_, v_t_1188_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1193_ = l_panic___redArg(v_inst_1187_, v___x_1192_);
return v___x_1193_;
}
else
{
lean_object* v_val_1194_; 
v_val_1194_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_val_1194_);
lean_dec_ref(v___x_1191_);
return v_val_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1195_, lean_object* v_00_u03b2_1196_, lean_object* v_cmp_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_t_1200_, lean_object* v_k_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Std_ExtDTreeMap_getEntryGE_x21(v_00_u03b1_1195_, v_00_u03b2_1196_, v_cmp_1197_, v_inst_1198_, v_inst_1199_, v_t_1200_, v_k_1201_);
lean_dec_ref(v_inst_1199_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1203_, lean_object* v_inst_1204_, lean_object* v_t_1205_, lean_object* v_k_1206_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_box(0);
v___x_1208_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1203_, v_k_1206_, v___x_1207_, v_t_1205_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1210_ = l_panic___redArg(v_inst_1204_, v___x_1209_);
return v___x_1210_;
}
else
{
lean_object* v_val_1211_; 
v_val_1211_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_val_1211_);
lean_dec_ref(v___x_1208_);
return v_val_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1212_, lean_object* v_inst_1213_, lean_object* v_t_1214_, lean_object* v_k_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Std_ExtDTreeMap_getEntryGT_x21___redArg(v_cmp_1212_, v_inst_1213_, v_t_1214_, v_k_1215_);
lean_dec_ref(v_inst_1213_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1217_, lean_object* v_00_u03b2_1218_, lean_object* v_cmp_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_t_1222_, lean_object* v_k_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = lean_box(0);
v___x_1225_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1219_, v_k_1223_, v___x_1224_, v_t_1222_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1227_ = l_panic___redArg(v_inst_1221_, v___x_1226_);
return v___x_1227_;
}
else
{
lean_object* v_val_1228_; 
v_val_1228_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_val_1228_);
lean_dec_ref(v___x_1225_);
return v_val_1228_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1229_, lean_object* v_00_u03b2_1230_, lean_object* v_cmp_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_t_1234_, lean_object* v_k_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_ExtDTreeMap_getEntryGT_x21(v_00_u03b1_1229_, v_00_u03b2_1230_, v_cmp_1231_, v_inst_1232_, v_inst_1233_, v_t_1234_, v_k_1235_);
lean_dec_ref(v_inst_1233_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1237_, lean_object* v_inst_1238_, lean_object* v_t_1239_, lean_object* v_k_1240_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_box(0);
v___x_1242_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1237_, v_k_1240_, v___x_1241_, v_t_1239_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1244_ = l_panic___redArg(v_inst_1238_, v___x_1243_);
return v___x_1244_;
}
else
{
lean_object* v_val_1245_; 
v_val_1245_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_val_1245_);
lean_dec_ref(v___x_1242_);
return v_val_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1246_, lean_object* v_inst_1247_, lean_object* v_t_1248_, lean_object* v_k_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Std_ExtDTreeMap_getEntryLE_x21___redArg(v_cmp_1246_, v_inst_1247_, v_t_1248_, v_k_1249_);
lean_dec_ref(v_inst_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1251_, lean_object* v_00_u03b2_1252_, lean_object* v_cmp_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_t_1256_, lean_object* v_k_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_box(0);
v___x_1259_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1253_, v_k_1257_, v___x_1258_, v_t_1256_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1261_ = l_panic___redArg(v_inst_1255_, v___x_1260_);
return v___x_1261_;
}
else
{
lean_object* v_val_1262_; 
v_val_1262_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_val_1262_);
lean_dec_ref(v___x_1259_);
return v_val_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1263_, lean_object* v_00_u03b2_1264_, lean_object* v_cmp_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_t_1268_, lean_object* v_k_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Std_ExtDTreeMap_getEntryLE_x21(v_00_u03b1_1263_, v_00_u03b2_1264_, v_cmp_1265_, v_inst_1266_, v_inst_1267_, v_t_1268_, v_k_1269_);
lean_dec_ref(v_inst_1267_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1271_, lean_object* v_inst_1272_, lean_object* v_t_1273_, lean_object* v_k_1274_){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_box(0);
v___x_1276_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1271_, v_k_1274_, v___x_1275_, v_t_1273_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1278_ = l_panic___redArg(v_inst_1272_, v___x_1277_);
return v___x_1278_;
}
else
{
lean_object* v_val_1279_; 
v_val_1279_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_val_1279_);
lean_dec_ref(v___x_1276_);
return v_val_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1280_, lean_object* v_inst_1281_, lean_object* v_t_1282_, lean_object* v_k_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Std_ExtDTreeMap_getEntryLT_x21___redArg(v_cmp_1280_, v_inst_1281_, v_t_1282_, v_k_1283_);
lean_dec_ref(v_inst_1281_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1285_, lean_object* v_00_u03b2_1286_, lean_object* v_cmp_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_t_1290_, lean_object* v_k_1291_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_box(0);
v___x_1293_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1287_, v_k_1291_, v___x_1292_, v_t_1290_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1295_ = l_panic___redArg(v_inst_1289_, v___x_1294_);
return v___x_1295_;
}
else
{
lean_object* v_val_1296_; 
v_val_1296_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_val_1296_);
lean_dec_ref(v___x_1293_);
return v_val_1296_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1297_, lean_object* v_00_u03b2_1298_, lean_object* v_cmp_1299_, lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_t_1302_, lean_object* v_k_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Std_ExtDTreeMap_getEntryLT_x21(v_00_u03b1_1297_, v_00_u03b2_1298_, v_cmp_1299_, v_inst_1300_, v_inst_1301_, v_t_1302_, v_k_1303_);
lean_dec_ref(v_inst_1301_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___redArg(lean_object* v_cmp_1305_, lean_object* v_t_1306_, lean_object* v_k_1307_, lean_object* v_fallback_1308_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1305_, v_k_1307_, v___x_1309_, v_t_1306_);
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
lean_dec_ref(v___x_1310_);
return v_val_1311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1312_, lean_object* v_t_1313_, lean_object* v_k_1314_, lean_object* v_fallback_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Std_ExtDTreeMap_getEntryGED___redArg(v_cmp_1312_, v_t_1313_, v_k_1314_, v_fallback_1315_);
lean_dec_ref(v_fallback_1315_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED(lean_object* v_00_u03b1_1317_, lean_object* v_00_u03b2_1318_, lean_object* v_cmp_1319_, lean_object* v_inst_1320_, lean_object* v_t_1321_, lean_object* v_k_1322_, lean_object* v_fallback_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1319_, v_k_1322_, v___x_1324_, v_t_1321_);
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
lean_dec_ref(v___x_1325_);
return v_val_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_00_u03b2_1328_, lean_object* v_cmp_1329_, lean_object* v_inst_1330_, lean_object* v_t_1331_, lean_object* v_k_1332_, lean_object* v_fallback_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Std_ExtDTreeMap_getEntryGED(v_00_u03b1_1327_, v_00_u03b2_1328_, v_cmp_1329_, v_inst_1330_, v_t_1331_, v_k_1332_, v_fallback_1333_);
lean_dec_ref(v_fallback_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1335_, lean_object* v_t_1336_, lean_object* v_k_1337_, lean_object* v_fallback_1338_){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1335_, v_k_1337_, v___x_1339_, v_t_1336_);
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
lean_dec_ref(v___x_1340_);
return v_val_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1342_, lean_object* v_t_1343_, lean_object* v_k_1344_, lean_object* v_fallback_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_ExtDTreeMap_getEntryGTD___redArg(v_cmp_1342_, v_t_1343_, v_k_1344_, v_fallback_1345_);
lean_dec_ref(v_fallback_1345_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD(lean_object* v_00_u03b1_1347_, lean_object* v_00_u03b2_1348_, lean_object* v_cmp_1349_, lean_object* v_inst_1350_, lean_object* v_t_1351_, lean_object* v_k_1352_, lean_object* v_fallback_1353_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1349_, v_k_1352_, v___x_1354_, v_t_1351_);
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
lean_dec_ref(v___x_1355_);
return v_val_1356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1357_, lean_object* v_00_u03b2_1358_, lean_object* v_cmp_1359_, lean_object* v_inst_1360_, lean_object* v_t_1361_, lean_object* v_k_1362_, lean_object* v_fallback_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Std_ExtDTreeMap_getEntryGTD(v_00_u03b1_1357_, v_00_u03b2_1358_, v_cmp_1359_, v_inst_1360_, v_t_1361_, v_k_1362_, v_fallback_1363_);
lean_dec_ref(v_fallback_1363_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___redArg(lean_object* v_cmp_1365_, lean_object* v_t_1366_, lean_object* v_k_1367_, lean_object* v_fallback_1368_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_box(0);
v___x_1370_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1365_, v_k_1367_, v___x_1369_, v_t_1366_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_inc_ref(v_fallback_1368_);
return v_fallback_1368_;
}
else
{
lean_object* v_val_1371_; 
v_val_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_val_1371_);
lean_dec_ref(v___x_1370_);
return v_val_1371_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1372_, lean_object* v_t_1373_, lean_object* v_k_1374_, lean_object* v_fallback_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Std_ExtDTreeMap_getEntryLED___redArg(v_cmp_1372_, v_t_1373_, v_k_1374_, v_fallback_1375_);
lean_dec_ref(v_fallback_1375_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED(lean_object* v_00_u03b1_1377_, lean_object* v_00_u03b2_1378_, lean_object* v_cmp_1379_, lean_object* v_inst_1380_, lean_object* v_t_1381_, lean_object* v_k_1382_, lean_object* v_fallback_1383_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_box(0);
v___x_1385_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1379_, v_k_1382_, v___x_1384_, v_t_1381_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_inc_ref(v_fallback_1383_);
return v_fallback_1383_;
}
else
{
lean_object* v_val_1386_; 
v_val_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_val_1386_);
lean_dec_ref(v___x_1385_);
return v_val_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1387_, lean_object* v_00_u03b2_1388_, lean_object* v_cmp_1389_, lean_object* v_inst_1390_, lean_object* v_t_1391_, lean_object* v_k_1392_, lean_object* v_fallback_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Std_ExtDTreeMap_getEntryLED(v_00_u03b1_1387_, v_00_u03b2_1388_, v_cmp_1389_, v_inst_1390_, v_t_1391_, v_k_1392_, v_fallback_1393_);
lean_dec_ref(v_fallback_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1395_, lean_object* v_t_1396_, lean_object* v_k_1397_, lean_object* v_fallback_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_box(0);
v___x_1400_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1395_, v_k_1397_, v___x_1399_, v_t_1396_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_inc_ref(v_fallback_1398_);
return v_fallback_1398_;
}
else
{
lean_object* v_val_1401_; 
v_val_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_val_1401_);
lean_dec_ref(v___x_1400_);
return v_val_1401_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1402_, lean_object* v_t_1403_, lean_object* v_k_1404_, lean_object* v_fallback_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Std_ExtDTreeMap_getEntryLTD___redArg(v_cmp_1402_, v_t_1403_, v_k_1404_, v_fallback_1405_);
lean_dec_ref(v_fallback_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD(lean_object* v_00_u03b1_1407_, lean_object* v_00_u03b2_1408_, lean_object* v_cmp_1409_, lean_object* v_inst_1410_, lean_object* v_t_1411_, lean_object* v_k_1412_, lean_object* v_fallback_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1409_, v_k_1412_, v___x_1414_, v_t_1411_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_inc_ref(v_fallback_1413_);
return v_fallback_1413_;
}
else
{
lean_object* v_val_1416_; 
v_val_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_val_1416_);
lean_dec_ref(v___x_1415_);
return v_val_1416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1417_, lean_object* v_00_u03b2_1418_, lean_object* v_cmp_1419_, lean_object* v_inst_1420_, lean_object* v_t_1421_, lean_object* v_k_1422_, lean_object* v_fallback_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Std_ExtDTreeMap_getEntryLTD(v_00_u03b1_1417_, v_00_u03b2_1418_, v_cmp_1419_, v_inst_1420_, v_t_1421_, v_k_1422_, v_fallback_1423_);
lean_dec_ref(v_fallback_1423_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1425_, lean_object* v_t_1426_, lean_object* v_k_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_box(0);
v___x_1429_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1425_, v_k_1427_, v___x_1428_, v_t_1426_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1430_, lean_object* v_00_u03b2_1431_, lean_object* v_cmp_1432_, lean_object* v_inst_1433_, lean_object* v_t_1434_, lean_object* v_k_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = lean_box(0);
v___x_1437_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1432_, v_k_1435_, v___x_1436_, v_t_1434_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1438_, lean_object* v_t_1439_, lean_object* v_k_1440_){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_box(0);
v___x_1442_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1438_, v_k_1440_, v___x_1441_, v_t_1439_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1443_, lean_object* v_00_u03b2_1444_, lean_object* v_cmp_1445_, lean_object* v_inst_1446_, lean_object* v_t_1447_, lean_object* v_k_1448_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_box(0);
v___x_1450_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1445_, v_k_1448_, v___x_1449_, v_t_1447_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1451_, lean_object* v_t_1452_, lean_object* v_k_1453_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_box(0);
v___x_1455_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1451_, v_k_1453_, v___x_1454_, v_t_1452_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1456_, lean_object* v_00_u03b2_1457_, lean_object* v_cmp_1458_, lean_object* v_inst_1459_, lean_object* v_t_1460_, lean_object* v_k_1461_){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_box(0);
v___x_1463_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1458_, v_k_1461_, v___x_1462_, v_t_1460_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1464_, lean_object* v_t_1465_, lean_object* v_k_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1464_, v_k_1466_, v___x_1467_, v_t_1465_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1469_, lean_object* v_00_u03b2_1470_, lean_object* v_cmp_1471_, lean_object* v_inst_1472_, lean_object* v_t_1473_, lean_object* v_k_1474_){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_box(0);
v___x_1476_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1471_, v_k_1474_, v___x_1475_, v_t_1473_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE___redArg(lean_object* v_cmp_1477_, lean_object* v_t_1478_, lean_object* v_k_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1477_, v_k_1479_, v_t_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE(lean_object* v_00_u03b1_1481_, lean_object* v_00_u03b2_1482_, lean_object* v_cmp_1483_, lean_object* v_inst_1484_, lean_object* v_t_1485_, lean_object* v_k_1486_, lean_object* v_h_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1483_, v_k_1486_, v_t_1485_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT___redArg(lean_object* v_cmp_1489_, lean_object* v_t_1490_, lean_object* v_k_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1489_, v_k_1491_, v_t_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT(lean_object* v_00_u03b1_1493_, lean_object* v_00_u03b2_1494_, lean_object* v_cmp_1495_, lean_object* v_inst_1496_, lean_object* v_t_1497_, lean_object* v_k_1498_, lean_object* v_h_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1495_, v_k_1498_, v_t_1497_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE___redArg(lean_object* v_cmp_1501_, lean_object* v_t_1502_, lean_object* v_k_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1501_, v_k_1503_, v_t_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE(lean_object* v_00_u03b1_1505_, lean_object* v_00_u03b2_1506_, lean_object* v_cmp_1507_, lean_object* v_inst_1508_, lean_object* v_t_1509_, lean_object* v_k_1510_, lean_object* v_h_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1507_, v_k_1510_, v_t_1509_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT___redArg(lean_object* v_cmp_1513_, lean_object* v_t_1514_, lean_object* v_k_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1513_, v_k_1515_, v_t_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT(lean_object* v_00_u03b1_1517_, lean_object* v_00_u03b2_1518_, lean_object* v_cmp_1519_, lean_object* v_inst_1520_, lean_object* v_t_1521_, lean_object* v_k_1522_, lean_object* v_h_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1519_, v_k_1522_, v_t_1521_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1525_, lean_object* v_inst_1526_, lean_object* v_t_1527_, lean_object* v_k_1528_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_box(0);
v___x_1530_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1525_, v_k_1528_, v___x_1529_, v_t_1527_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1532_ = l_panic___redArg(v_inst_1526_, v___x_1531_);
return v___x_1532_;
}
else
{
lean_object* v_val_1533_; 
v_val_1533_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_val_1533_);
lean_dec_ref(v___x_1530_);
return v_val_1533_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1534_, lean_object* v_inst_1535_, lean_object* v_t_1536_, lean_object* v_k_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Std_ExtDTreeMap_getKeyGE_x21___redArg(v_cmp_1534_, v_inst_1535_, v_t_1536_, v_k_1537_);
lean_dec(v_inst_1535_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1539_, lean_object* v_00_u03b2_1540_, lean_object* v_cmp_1541_, lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_t_1544_, lean_object* v_k_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_box(0);
v___x_1547_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1541_, v_k_1545_, v___x_1546_, v_t_1544_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1549_ = l_panic___redArg(v_inst_1543_, v___x_1548_);
return v___x_1549_;
}
else
{
lean_object* v_val_1550_; 
v_val_1550_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_val_1550_);
lean_dec_ref(v___x_1547_);
return v_val_1550_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1551_, lean_object* v_00_u03b2_1552_, lean_object* v_cmp_1553_, lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_t_1556_, lean_object* v_k_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Std_ExtDTreeMap_getKeyGE_x21(v_00_u03b1_1551_, v_00_u03b2_1552_, v_cmp_1553_, v_inst_1554_, v_inst_1555_, v_t_1556_, v_k_1557_);
lean_dec(v_inst_1555_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1559_, lean_object* v_inst_1560_, lean_object* v_t_1561_, lean_object* v_k_1562_){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_box(0);
v___x_1564_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1559_, v_k_1562_, v___x_1563_, v_t_1561_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1566_ = l_panic___redArg(v_inst_1560_, v___x_1565_);
return v___x_1566_;
}
else
{
lean_object* v_val_1567_; 
v_val_1567_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_val_1567_);
lean_dec_ref(v___x_1564_);
return v_val_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1568_, lean_object* v_inst_1569_, lean_object* v_t_1570_, lean_object* v_k_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Std_ExtDTreeMap_getKeyGT_x21___redArg(v_cmp_1568_, v_inst_1569_, v_t_1570_, v_k_1571_);
lean_dec(v_inst_1569_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1573_, lean_object* v_00_u03b2_1574_, lean_object* v_cmp_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_t_1578_, lean_object* v_k_1579_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_box(0);
v___x_1581_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1575_, v_k_1579_, v___x_1580_, v_t_1578_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1583_ = l_panic___redArg(v_inst_1577_, v___x_1582_);
return v___x_1583_;
}
else
{
lean_object* v_val_1584_; 
v_val_1584_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_val_1584_);
lean_dec_ref(v___x_1581_);
return v_val_1584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1585_, lean_object* v_00_u03b2_1586_, lean_object* v_cmp_1587_, lean_object* v_inst_1588_, lean_object* v_inst_1589_, lean_object* v_t_1590_, lean_object* v_k_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Std_ExtDTreeMap_getKeyGT_x21(v_00_u03b1_1585_, v_00_u03b2_1586_, v_cmp_1587_, v_inst_1588_, v_inst_1589_, v_t_1590_, v_k_1591_);
lean_dec(v_inst_1589_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1593_, lean_object* v_inst_1594_, lean_object* v_t_1595_, lean_object* v_k_1596_){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = lean_box(0);
v___x_1598_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1593_, v_k_1596_, v___x_1597_, v_t_1595_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1600_ = l_panic___redArg(v_inst_1594_, v___x_1599_);
return v___x_1600_;
}
else
{
lean_object* v_val_1601_; 
v_val_1601_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_val_1601_);
lean_dec_ref(v___x_1598_);
return v_val_1601_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1602_, lean_object* v_inst_1603_, lean_object* v_t_1604_, lean_object* v_k_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Std_ExtDTreeMap_getKeyLE_x21___redArg(v_cmp_1602_, v_inst_1603_, v_t_1604_, v_k_1605_);
lean_dec(v_inst_1603_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1607_, lean_object* v_00_u03b2_1608_, lean_object* v_cmp_1609_, lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_t_1612_, lean_object* v_k_1613_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_box(0);
v___x_1615_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1609_, v_k_1613_, v___x_1614_, v_t_1612_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1617_ = l_panic___redArg(v_inst_1611_, v___x_1616_);
return v___x_1617_;
}
else
{
lean_object* v_val_1618_; 
v_val_1618_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_val_1618_);
lean_dec_ref(v___x_1615_);
return v_val_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1619_, lean_object* v_00_u03b2_1620_, lean_object* v_cmp_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_t_1624_, lean_object* v_k_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Std_ExtDTreeMap_getKeyLE_x21(v_00_u03b1_1619_, v_00_u03b2_1620_, v_cmp_1621_, v_inst_1622_, v_inst_1623_, v_t_1624_, v_k_1625_);
lean_dec(v_inst_1623_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1627_, lean_object* v_inst_1628_, lean_object* v_t_1629_, lean_object* v_k_1630_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_box(0);
v___x_1632_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1627_, v_k_1630_, v___x_1631_, v_t_1629_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1634_ = l_panic___redArg(v_inst_1628_, v___x_1633_);
return v___x_1634_;
}
else
{
lean_object* v_val_1635_; 
v_val_1635_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_val_1635_);
lean_dec_ref(v___x_1632_);
return v_val_1635_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1636_, lean_object* v_inst_1637_, lean_object* v_t_1638_, lean_object* v_k_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Std_ExtDTreeMap_getKeyLT_x21___redArg(v_cmp_1636_, v_inst_1637_, v_t_1638_, v_k_1639_);
lean_dec(v_inst_1637_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1641_, lean_object* v_00_u03b2_1642_, lean_object* v_cmp_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_t_1646_, lean_object* v_k_1647_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_box(0);
v___x_1649_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1643_, v_k_1647_, v___x_1648_, v_t_1646_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1651_ = l_panic___redArg(v_inst_1645_, v___x_1650_);
return v___x_1651_;
}
else
{
lean_object* v_val_1652_; 
v_val_1652_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_val_1652_);
lean_dec_ref(v___x_1649_);
return v_val_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1653_, lean_object* v_00_u03b2_1654_, lean_object* v_cmp_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_t_1658_, lean_object* v_k_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Std_ExtDTreeMap_getKeyLT_x21(v_00_u03b1_1653_, v_00_u03b2_1654_, v_cmp_1655_, v_inst_1656_, v_inst_1657_, v_t_1658_, v_k_1659_);
lean_dec(v_inst_1657_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___redArg(lean_object* v_cmp_1661_, lean_object* v_t_1662_, lean_object* v_k_1663_, lean_object* v_fallback_1664_){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_box(0);
v___x_1666_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1661_, v_k_1663_, v___x_1665_, v_t_1662_);
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
lean_dec_ref(v___x_1666_);
return v_val_1667_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1668_, lean_object* v_t_1669_, lean_object* v_k_1670_, lean_object* v_fallback_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Std_ExtDTreeMap_getKeyGED___redArg(v_cmp_1668_, v_t_1669_, v_k_1670_, v_fallback_1671_);
lean_dec(v_fallback_1671_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED(lean_object* v_00_u03b1_1673_, lean_object* v_00_u03b2_1674_, lean_object* v_cmp_1675_, lean_object* v_inst_1676_, lean_object* v_t_1677_, lean_object* v_k_1678_, lean_object* v_fallback_1679_){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_box(0);
v___x_1681_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1675_, v_k_1678_, v___x_1680_, v_t_1677_);
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
lean_dec_ref(v___x_1681_);
return v_val_1682_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1683_, lean_object* v_00_u03b2_1684_, lean_object* v_cmp_1685_, lean_object* v_inst_1686_, lean_object* v_t_1687_, lean_object* v_k_1688_, lean_object* v_fallback_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_ExtDTreeMap_getKeyGED(v_00_u03b1_1683_, v_00_u03b2_1684_, v_cmp_1685_, v_inst_1686_, v_t_1687_, v_k_1688_, v_fallback_1689_);
lean_dec(v_fallback_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1691_, lean_object* v_t_1692_, lean_object* v_k_1693_, lean_object* v_fallback_1694_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = lean_box(0);
v___x_1696_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1691_, v_k_1693_, v___x_1695_, v_t_1692_);
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
lean_dec_ref(v___x_1696_);
return v_val_1697_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1698_, lean_object* v_t_1699_, lean_object* v_k_1700_, lean_object* v_fallback_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Std_ExtDTreeMap_getKeyGTD___redArg(v_cmp_1698_, v_t_1699_, v_k_1700_, v_fallback_1701_);
lean_dec(v_fallback_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD(lean_object* v_00_u03b1_1703_, lean_object* v_00_u03b2_1704_, lean_object* v_cmp_1705_, lean_object* v_inst_1706_, lean_object* v_t_1707_, lean_object* v_k_1708_, lean_object* v_fallback_1709_){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_box(0);
v___x_1711_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1705_, v_k_1708_, v___x_1710_, v_t_1707_);
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
lean_dec_ref(v___x_1711_);
return v_val_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_cmp_1715_, lean_object* v_inst_1716_, lean_object* v_t_1717_, lean_object* v_k_1718_, lean_object* v_fallback_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Std_ExtDTreeMap_getKeyGTD(v_00_u03b1_1713_, v_00_u03b2_1714_, v_cmp_1715_, v_inst_1716_, v_t_1717_, v_k_1718_, v_fallback_1719_);
lean_dec(v_fallback_1719_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___redArg(lean_object* v_cmp_1721_, lean_object* v_t_1722_, lean_object* v_k_1723_, lean_object* v_fallback_1724_){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_box(0);
v___x_1726_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1721_, v_k_1723_, v___x_1725_, v_t_1722_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_inc(v_fallback_1724_);
return v_fallback_1724_;
}
else
{
lean_object* v_val_1727_; 
v_val_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_val_1727_);
lean_dec_ref(v___x_1726_);
return v_val_1727_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1728_, lean_object* v_t_1729_, lean_object* v_k_1730_, lean_object* v_fallback_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Std_ExtDTreeMap_getKeyLED___redArg(v_cmp_1728_, v_t_1729_, v_k_1730_, v_fallback_1731_);
lean_dec(v_fallback_1731_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED(lean_object* v_00_u03b1_1733_, lean_object* v_00_u03b2_1734_, lean_object* v_cmp_1735_, lean_object* v_inst_1736_, lean_object* v_t_1737_, lean_object* v_k_1738_, lean_object* v_fallback_1739_){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = lean_box(0);
v___x_1741_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1735_, v_k_1738_, v___x_1740_, v_t_1737_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_inc(v_fallback_1739_);
return v_fallback_1739_;
}
else
{
lean_object* v_val_1742_; 
v_val_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_val_1742_);
lean_dec_ref(v___x_1741_);
return v_val_1742_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1743_, lean_object* v_00_u03b2_1744_, lean_object* v_cmp_1745_, lean_object* v_inst_1746_, lean_object* v_t_1747_, lean_object* v_k_1748_, lean_object* v_fallback_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Std_ExtDTreeMap_getKeyLED(v_00_u03b1_1743_, v_00_u03b2_1744_, v_cmp_1745_, v_inst_1746_, v_t_1747_, v_k_1748_, v_fallback_1749_);
lean_dec(v_fallback_1749_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1751_, lean_object* v_t_1752_, lean_object* v_k_1753_, lean_object* v_fallback_1754_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_box(0);
v___x_1756_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1751_, v_k_1753_, v___x_1755_, v_t_1752_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_inc(v_fallback_1754_);
return v_fallback_1754_;
}
else
{
lean_object* v_val_1757_; 
v_val_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_val_1757_);
lean_dec_ref(v___x_1756_);
return v_val_1757_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1758_, lean_object* v_t_1759_, lean_object* v_k_1760_, lean_object* v_fallback_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Std_ExtDTreeMap_getKeyLTD___redArg(v_cmp_1758_, v_t_1759_, v_k_1760_, v_fallback_1761_);
lean_dec(v_fallback_1761_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD(lean_object* v_00_u03b1_1763_, lean_object* v_00_u03b2_1764_, lean_object* v_cmp_1765_, lean_object* v_inst_1766_, lean_object* v_t_1767_, lean_object* v_k_1768_, lean_object* v_fallback_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_box(0);
v___x_1771_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1765_, v_k_1768_, v___x_1770_, v_t_1767_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_inc(v_fallback_1769_);
return v_fallback_1769_;
}
else
{
lean_object* v_val_1772_; 
v_val_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_val_1772_);
lean_dec_ref(v___x_1771_);
return v_val_1772_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1773_, lean_object* v_00_u03b2_1774_, lean_object* v_cmp_1775_, lean_object* v_inst_1776_, lean_object* v_t_1777_, lean_object* v_k_1778_, lean_object* v_fallback_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Std_ExtDTreeMap_getKeyLTD(v_00_u03b1_1773_, v_00_u03b2_1774_, v_cmp_1775_, v_inst_1776_, v_t_1777_, v_k_1778_, v_fallback_1779_);
lean_dec(v_fallback_1779_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1781_, lean_object* v_t_1782_, lean_object* v_a_1783_, lean_object* v_b_1784_){
_start:
{
lean_object* v___x_1785_; 
lean_inc(v_a_1783_);
lean_inc(v_t_1782_);
lean_inc_ref(v_cmp_1781_);
v___x_1785_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1781_, v_t_1782_, v_a_1783_);
if (lean_obj_tag(v___x_1785_) == 0)
{
uint8_t v___x_1786_; 
lean_inc(v_t_1782_);
lean_inc(v_a_1783_);
lean_inc_ref(v_cmp_1781_);
v___x_1786_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1781_, v_a_1783_, v_t_1782_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1781_, v_a_1783_, v_b_1784_, v_t_1782_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1785_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; 
lean_dec(v_b_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_cmp_1781_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1785_);
lean_ctor_set(v___x_1789_, 1, v_t_1782_);
return v___x_1789_;
}
}
else
{
lean_object* v___x_1790_; 
lean_dec(v_b_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_cmp_1781_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1785_);
lean_ctor_set(v___x_1790_, 1, v_t_1782_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1791_, lean_object* v_cmp_1792_, lean_object* v_00_u03b2_1793_, lean_object* v_inst_1794_, lean_object* v_t_1795_, lean_object* v_a_1796_, lean_object* v_b_1797_){
_start:
{
lean_object* v___x_1798_; 
lean_inc(v_a_1796_);
lean_inc(v_t_1795_);
lean_inc_ref(v_cmp_1792_);
v___x_1798_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1792_, v_t_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1798_) == 0)
{
uint8_t v___x_1799_; 
lean_inc(v_t_1795_);
lean_inc(v_a_1796_);
lean_inc_ref(v_cmp_1792_);
v___x_1799_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1792_, v_a_1796_, v_t_1795_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1792_, v_a_1796_, v_b_1797_, v_t_1795_);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1798_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; 
lean_dec(v_b_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_cmp_1792_);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1798_);
lean_ctor_set(v___x_1802_, 1, v_t_1795_);
return v___x_1802_;
}
}
else
{
lean_object* v___x_1803_; 
lean_dec(v_b_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_cmp_1792_);
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1798_);
lean_ctor_set(v___x_1803_, 1, v_t_1795_);
return v___x_1803_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x3f___redArg(lean_object* v_cmp_1804_, lean_object* v_t_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1804_, v_t_1805_, v_a_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x3f(lean_object* v_00_u03b1_1808_, lean_object* v_cmp_1809_, lean_object* v_00_u03b2_1810_, lean_object* v_inst_1811_, lean_object* v_t_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1809_, v_t_1812_, v_a_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get___redArg(lean_object* v_cmp_1815_, lean_object* v_t_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1815_, v_t_1816_, v_a_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get(lean_object* v_00_u03b1_1819_, lean_object* v_cmp_1820_, lean_object* v_00_u03b2_1821_, lean_object* v_inst_1822_, lean_object* v_t_1823_, lean_object* v_a_1824_, lean_object* v_h_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1820_, v_t_1823_, v_a_1824_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___redArg(lean_object* v_cmp_1827_, lean_object* v_inst_1828_, lean_object* v_t_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1827_, v_inst_1828_, v_t_1829_, v_a_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___redArg___boxed(lean_object* v_cmp_1832_, lean_object* v_inst_1833_, lean_object* v_t_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Std_ExtDTreeMap_Const_get_x21___redArg(v_cmp_1832_, v_inst_1833_, v_t_1834_, v_a_1835_);
lean_dec(v_inst_1833_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21(lean_object* v_00_u03b1_1837_, lean_object* v_cmp_1838_, lean_object* v_00_u03b2_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_t_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1838_, v_inst_1841_, v_t_1842_, v_a_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_get_x21___boxed(lean_object* v_00_u03b1_1845_, lean_object* v_cmp_1846_, lean_object* v_00_u03b2_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_t_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Std_ExtDTreeMap_Const_get_x21(v_00_u03b1_1845_, v_cmp_1846_, v_00_u03b2_1847_, v_inst_1848_, v_inst_1849_, v_t_1850_, v_a_1851_);
lean_dec(v_inst_1849_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___redArg(lean_object* v_cmp_1853_, lean_object* v_t_1854_, lean_object* v_a_1855_, lean_object* v_fallback_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1853_, v_t_1854_, v_a_1855_, v_fallback_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___redArg___boxed(lean_object* v_cmp_1858_, lean_object* v_t_1859_, lean_object* v_a_1860_, lean_object* v_fallback_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Std_ExtDTreeMap_Const_getD___redArg(v_cmp_1858_, v_t_1859_, v_a_1860_, v_fallback_1861_);
lean_dec(v_fallback_1861_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD(lean_object* v_00_u03b1_1863_, lean_object* v_cmp_1864_, lean_object* v_00_u03b2_1865_, lean_object* v_inst_1866_, lean_object* v_t_1867_, lean_object* v_a_1868_, lean_object* v_fallback_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1864_, v_t_1867_, v_a_1868_, v_fallback_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getD___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_cmp_1872_, lean_object* v_00_u03b2_1873_, lean_object* v_inst_1874_, lean_object* v_t_1875_, lean_object* v_a_1876_, lean_object* v_fallback_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Std_ExtDTreeMap_Const_getD(v_00_u03b1_1871_, v_cmp_1872_, v_00_u03b2_1873_, v_inst_1874_, v_t_1875_, v_a_1876_, v_fallback_1877_);
lean_dec(v_fallback_1877_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(lean_object* v_t_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(v_t_1881_);
lean_dec(v_t_1881_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f(lean_object* v_00_u03b1_1883_, lean_object* v_cmp_1884_, lean_object* v_00_u03b2_1885_, lean_object* v_inst_1886_, lean_object* v_t_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1889_, lean_object* v_cmp_1890_, lean_object* v_00_u03b2_1891_, lean_object* v_inst_1892_, lean_object* v_t_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Std_ExtDTreeMap_Const_minEntry_x3f(v_00_u03b1_1889_, v_cmp_1890_, v_00_u03b2_1891_, v_inst_1892_, v_t_1893_);
lean_dec(v_t_1893_);
lean_dec_ref(v_cmp_1890_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___redArg(lean_object* v_t_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___redArg___boxed(lean_object* v_t_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Std_ExtDTreeMap_Const_minEntry___redArg(v_t_1897_);
lean_dec(v_t_1897_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry(lean_object* v_00_u03b1_1899_, lean_object* v_cmp_1900_, lean_object* v_00_u03b2_1901_, lean_object* v_inst_1902_, lean_object* v_t_1903_, lean_object* v_h_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1903_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry___boxed(lean_object* v_00_u03b1_1906_, lean_object* v_cmp_1907_, lean_object* v_00_u03b2_1908_, lean_object* v_inst_1909_, lean_object* v_t_1910_, lean_object* v_h_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Std_ExtDTreeMap_Const_minEntry(v_00_u03b1_1906_, v_cmp_1907_, v_00_u03b2_1908_, v_inst_1909_, v_t_1910_, v_h_1911_);
lean_dec(v_t_1910_);
lean_dec_ref(v_cmp_1907_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(lean_object* v_inst_1913_, lean_object* v_t_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1913_, v_t_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1916_, lean_object* v_t_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(v_inst_1916_, v_t_1917_);
lean_dec(v_t_1917_);
lean_dec_ref(v_inst_1916_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21(lean_object* v_00_u03b1_1919_, lean_object* v_cmp_1920_, lean_object* v_00_u03b2_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_t_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1923_, v_t_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1926_, lean_object* v_cmp_1927_, lean_object* v_00_u03b2_1928_, lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v_t_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Std_ExtDTreeMap_Const_minEntry_x21(v_00_u03b1_1926_, v_cmp_1927_, v_00_u03b2_1928_, v_inst_1929_, v_inst_1930_, v_t_1931_);
lean_dec(v_t_1931_);
lean_dec_ref(v_inst_1930_);
lean_dec_ref(v_cmp_1927_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___redArg(lean_object* v_t_1933_, lean_object* v_fallback_1934_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1933_, v_fallback_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___redArg___boxed(lean_object* v_t_1936_, lean_object* v_fallback_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Std_ExtDTreeMap_Const_minEntryD___redArg(v_t_1936_, v_fallback_1937_);
lean_dec_ref(v_fallback_1937_);
lean_dec(v_t_1936_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD(lean_object* v_00_u03b1_1939_, lean_object* v_cmp_1940_, lean_object* v_00_u03b2_1941_, lean_object* v_inst_1942_, lean_object* v_t_1943_, lean_object* v_fallback_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1943_, v_fallback_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_minEntryD___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_cmp_1947_, lean_object* v_00_u03b2_1948_, lean_object* v_inst_1949_, lean_object* v_t_1950_, lean_object* v_fallback_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Std_ExtDTreeMap_Const_minEntryD(v_00_u03b1_1946_, v_cmp_1947_, v_00_u03b2_1948_, v_inst_1949_, v_t_1950_, v_fallback_1951_);
lean_dec_ref(v_fallback_1951_);
lean_dec(v_t_1950_);
lean_dec_ref(v_cmp_1947_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(lean_object* v_t_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(v_t_1955_);
lean_dec(v_t_1955_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f(lean_object* v_00_u03b1_1957_, lean_object* v_cmp_1958_, lean_object* v_00_u03b2_1959_, lean_object* v_inst_1960_, lean_object* v_t_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1963_, lean_object* v_cmp_1964_, lean_object* v_00_u03b2_1965_, lean_object* v_inst_1966_, lean_object* v_t_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Std_ExtDTreeMap_Const_maxEntry_x3f(v_00_u03b1_1963_, v_cmp_1964_, v_00_u03b2_1965_, v_inst_1966_, v_t_1967_);
lean_dec(v_t_1967_);
lean_dec_ref(v_cmp_1964_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___redArg(lean_object* v_t_1969_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___redArg___boxed(lean_object* v_t_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Std_ExtDTreeMap_Const_maxEntry___redArg(v_t_1971_);
lean_dec(v_t_1971_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry(lean_object* v_00_u03b1_1973_, lean_object* v_cmp_1974_, lean_object* v_00_u03b2_1975_, lean_object* v_inst_1976_, lean_object* v_t_1977_, lean_object* v_h_1978_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1977_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry___boxed(lean_object* v_00_u03b1_1980_, lean_object* v_cmp_1981_, lean_object* v_00_u03b2_1982_, lean_object* v_inst_1983_, lean_object* v_t_1984_, lean_object* v_h_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Std_ExtDTreeMap_Const_maxEntry(v_00_u03b1_1980_, v_cmp_1981_, v_00_u03b2_1982_, v_inst_1983_, v_t_1984_, v_h_1985_);
lean_dec(v_t_1984_);
lean_dec_ref(v_cmp_1981_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(lean_object* v_inst_1987_, lean_object* v_t_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1987_, v_t_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_1990_, lean_object* v_t_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(v_inst_1990_, v_t_1991_);
lean_dec(v_t_1991_);
lean_dec_ref(v_inst_1990_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21(lean_object* v_00_u03b1_1993_, lean_object* v_cmp_1994_, lean_object* v_00_u03b2_1995_, lean_object* v_inst_1996_, lean_object* v_inst_1997_, lean_object* v_t_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1997_, v_t_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_2000_, lean_object* v_cmp_2001_, lean_object* v_00_u03b2_2002_, lean_object* v_inst_2003_, lean_object* v_inst_2004_, lean_object* v_t_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Std_ExtDTreeMap_Const_maxEntry_x21(v_00_u03b1_2000_, v_cmp_2001_, v_00_u03b2_2002_, v_inst_2003_, v_inst_2004_, v_t_2005_);
lean_dec(v_t_2005_);
lean_dec_ref(v_inst_2004_);
lean_dec_ref(v_cmp_2001_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___redArg(lean_object* v_t_2007_, lean_object* v_fallback_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_2007_, v_fallback_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___redArg___boxed(lean_object* v_t_2010_, lean_object* v_fallback_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Std_ExtDTreeMap_Const_maxEntryD___redArg(v_t_2010_, v_fallback_2011_);
lean_dec_ref(v_fallback_2011_);
lean_dec(v_t_2010_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD(lean_object* v_00_u03b1_2013_, lean_object* v_cmp_2014_, lean_object* v_00_u03b2_2015_, lean_object* v_inst_2016_, lean_object* v_t_2017_, lean_object* v_fallback_2018_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_2017_, v_fallback_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_maxEntryD___boxed(lean_object* v_00_u03b1_2020_, lean_object* v_cmp_2021_, lean_object* v_00_u03b2_2022_, lean_object* v_inst_2023_, lean_object* v_t_2024_, lean_object* v_fallback_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Std_ExtDTreeMap_Const_maxEntryD(v_00_u03b1_2020_, v_cmp_2021_, v_00_u03b2_2022_, v_inst_2023_, v_t_2024_, v_fallback_2025_);
lean_dec_ref(v_fallback_2025_);
lean_dec(v_t_2024_);
lean_dec_ref(v_cmp_2021_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(lean_object* v_t_2027_, lean_object* v_n_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_2027_, v_n_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_2030_, lean_object* v_n_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(v_t_2030_, v_n_2031_);
lean_dec(v_t_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_2033_, lean_object* v_cmp_2034_, lean_object* v_00_u03b2_2035_, lean_object* v_inst_2036_, lean_object* v_t_2037_, lean_object* v_n_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_2037_, v_n_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_2040_, lean_object* v_cmp_2041_, lean_object* v_00_u03b2_2042_, lean_object* v_inst_2043_, lean_object* v_t_2044_, lean_object* v_n_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(v_00_u03b1_2040_, v_cmp_2041_, v_00_u03b2_2042_, v_inst_2043_, v_t_2044_, v_n_2045_);
lean_dec(v_t_2044_);
lean_dec_ref(v_cmp_2041_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(lean_object* v_t_2047_, lean_object* v_n_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_2047_, v_n_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___redArg___boxed(lean_object* v_t_2050_, lean_object* v_n_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(v_t_2050_, v_n_2051_);
lean_dec(v_t_2050_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx(lean_object* v_00_u03b1_2053_, lean_object* v_cmp_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_inst_2056_, lean_object* v_t_2057_, lean_object* v_n_2058_, lean_object* v_h_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_2057_, v_n_2058_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_2061_, lean_object* v_cmp_2062_, lean_object* v_00_u03b2_2063_, lean_object* v_inst_2064_, lean_object* v_t_2065_, lean_object* v_n_2066_, lean_object* v_h_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Std_ExtDTreeMap_Const_entryAtIdx(v_00_u03b1_2061_, v_cmp_2062_, v_00_u03b2_2063_, v_inst_2064_, v_t_2065_, v_n_2066_, v_h_2067_);
lean_dec(v_t_2065_);
lean_dec_ref(v_cmp_2062_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(lean_object* v_inst_2069_, lean_object* v_t_2070_, lean_object* v_n_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_2069_, v_t_2070_, v_n_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_2073_, lean_object* v_t_2074_, lean_object* v_n_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(v_inst_2073_, v_t_2074_, v_n_2075_);
lean_dec(v_t_2074_);
lean_dec_ref(v_inst_2073_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21(lean_object* v_00_u03b1_2077_, lean_object* v_cmp_2078_, lean_object* v_00_u03b2_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_t_2082_, lean_object* v_n_2083_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_2081_, v_t_2082_, v_n_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_2085_, lean_object* v_cmp_2086_, lean_object* v_00_u03b2_2087_, lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_t_2090_, lean_object* v_n_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x21(v_00_u03b1_2085_, v_cmp_2086_, v_00_u03b2_2087_, v_inst_2088_, v_inst_2089_, v_t_2090_, v_n_2091_);
lean_dec(v_t_2090_);
lean_dec_ref(v_inst_2089_);
lean_dec_ref(v_cmp_2086_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(lean_object* v_t_2093_, lean_object* v_n_2094_, lean_object* v_fallback_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_2093_, v_n_2094_, v_fallback_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_2097_, lean_object* v_n_2098_, lean_object* v_fallback_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(v_t_2097_, v_n_2098_, v_fallback_2099_);
lean_dec_ref(v_fallback_2099_);
lean_dec(v_t_2097_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD(lean_object* v_00_u03b1_2101_, lean_object* v_cmp_2102_, lean_object* v_00_u03b2_2103_, lean_object* v_inst_2104_, lean_object* v_t_2105_, lean_object* v_n_2106_, lean_object* v_fallback_2107_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_2105_, v_n_2106_, v_fallback_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_2109_, lean_object* v_cmp_2110_, lean_object* v_00_u03b2_2111_, lean_object* v_inst_2112_, lean_object* v_t_2113_, lean_object* v_n_2114_, lean_object* v_fallback_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Std_ExtDTreeMap_Const_entryAtIdxD(v_00_u03b1_2109_, v_cmp_2110_, v_00_u03b2_2111_, v_inst_2112_, v_t_2113_, v_n_2114_, v_fallback_2115_);
lean_dec_ref(v_fallback_2115_);
lean_dec(v_t_2113_);
lean_dec_ref(v_cmp_2110_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_2117_, lean_object* v_t_2118_, lean_object* v_k_2119_){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = lean_box(0);
v___x_2121_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2117_, v_k_2119_, v___x_2120_, v_t_2118_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x3f(lean_object* v_00_u03b1_2122_, lean_object* v_cmp_2123_, lean_object* v_00_u03b2_2124_, lean_object* v_inst_2125_, lean_object* v_t_2126_, lean_object* v_k_2127_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = lean_box(0);
v___x_2129_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2123_, v_k_2127_, v___x_2128_, v_t_2126_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_2130_, lean_object* v_t_2131_, lean_object* v_k_2132_){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = lean_box(0);
v___x_2134_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2130_, v_k_2132_, v___x_2133_, v_t_2131_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x3f(lean_object* v_00_u03b1_2135_, lean_object* v_cmp_2136_, lean_object* v_00_u03b2_2137_, lean_object* v_inst_2138_, lean_object* v_t_2139_, lean_object* v_k_2140_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_box(0);
v___x_2142_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2136_, v_k_2140_, v___x_2141_, v_t_2139_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_2143_, lean_object* v_t_2144_, lean_object* v_k_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_box(0);
v___x_2147_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2143_, v_k_2145_, v___x_2146_, v_t_2144_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x3f(lean_object* v_00_u03b1_2148_, lean_object* v_cmp_2149_, lean_object* v_00_u03b2_2150_, lean_object* v_inst_2151_, lean_object* v_t_2152_, lean_object* v_k_2153_){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_box(0);
v___x_2155_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2149_, v_k_2153_, v___x_2154_, v_t_2152_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_2156_, lean_object* v_t_2157_, lean_object* v_k_2158_){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_box(0);
v___x_2160_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2156_, v_k_2158_, v___x_2159_, v_t_2157_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x3f(lean_object* v_00_u03b1_2161_, lean_object* v_cmp_2162_, lean_object* v_00_u03b2_2163_, lean_object* v_inst_2164_, lean_object* v_t_2165_, lean_object* v_k_2166_){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = lean_box(0);
v___x_2168_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2162_, v_k_2166_, v___x_2167_, v_t_2165_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE___redArg(lean_object* v_cmp_2169_, lean_object* v_t_2170_, lean_object* v_k_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_2169_, v_k_2171_, v_t_2170_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE(lean_object* v_00_u03b1_2173_, lean_object* v_cmp_2174_, lean_object* v_00_u03b2_2175_, lean_object* v_inst_2176_, lean_object* v_t_2177_, lean_object* v_k_2178_, lean_object* v_h_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_2174_, v_k_2178_, v_t_2177_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT___redArg(lean_object* v_cmp_2181_, lean_object* v_t_2182_, lean_object* v_k_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_2181_, v_k_2183_, v_t_2182_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT(lean_object* v_00_u03b1_2185_, lean_object* v_cmp_2186_, lean_object* v_00_u03b2_2187_, lean_object* v_inst_2188_, lean_object* v_t_2189_, lean_object* v_k_2190_, lean_object* v_h_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_2186_, v_k_2190_, v_t_2189_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE___redArg(lean_object* v_cmp_2193_, lean_object* v_t_2194_, lean_object* v_k_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_2193_, v_k_2195_, v_t_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE(lean_object* v_00_u03b1_2197_, lean_object* v_cmp_2198_, lean_object* v_00_u03b2_2199_, lean_object* v_inst_2200_, lean_object* v_t_2201_, lean_object* v_k_2202_, lean_object* v_h_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_2198_, v_k_2202_, v_t_2201_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT___redArg(lean_object* v_cmp_2205_, lean_object* v_t_2206_, lean_object* v_k_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_2205_, v_k_2207_, v_t_2206_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT(lean_object* v_00_u03b1_2209_, lean_object* v_cmp_2210_, lean_object* v_00_u03b2_2211_, lean_object* v_inst_2212_, lean_object* v_t_2213_, lean_object* v_k_2214_, lean_object* v_h_2215_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_2210_, v_k_2214_, v_t_2213_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg(lean_object* v_cmp_2217_, lean_object* v_inst_2218_, lean_object* v_t_2219_, lean_object* v_k_2220_){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_box(0);
v___x_2222_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2217_, v_k_2220_, v___x_2221_, v_t_2219_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2224_ = l_panic___redArg(v_inst_2218_, v___x_2223_);
return v___x_2224_;
}
else
{
lean_object* v_val_2225_; 
v_val_2225_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_val_2225_);
lean_dec_ref(v___x_2222_);
return v_val_2225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_2226_, lean_object* v_inst_2227_, lean_object* v_t_2228_, lean_object* v_k_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg(v_cmp_2226_, v_inst_2227_, v_t_2228_, v_k_2229_);
lean_dec_ref(v_inst_2227_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21(lean_object* v_00_u03b1_2231_, lean_object* v_cmp_2232_, lean_object* v_00_u03b2_2233_, lean_object* v_inst_2234_, lean_object* v_inst_2235_, lean_object* v_t_2236_, lean_object* v_k_2237_){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_box(0);
v___x_2239_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2232_, v_k_2237_, v___x_2238_, v_t_2236_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2241_ = l_panic___redArg(v_inst_2235_, v___x_2240_);
return v___x_2241_;
}
else
{
lean_object* v_val_2242_; 
v_val_2242_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_val_2242_);
lean_dec_ref(v___x_2239_);
return v_val_2242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_2243_, lean_object* v_cmp_2244_, lean_object* v_00_u03b2_2245_, lean_object* v_inst_2246_, lean_object* v_inst_2247_, lean_object* v_t_2248_, lean_object* v_k_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Std_ExtDTreeMap_Const_getEntryGE_x21(v_00_u03b1_2243_, v_cmp_2244_, v_00_u03b2_2245_, v_inst_2246_, v_inst_2247_, v_t_2248_, v_k_2249_);
lean_dec_ref(v_inst_2247_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(lean_object* v_cmp_2251_, lean_object* v_inst_2252_, lean_object* v_t_2253_, lean_object* v_k_2254_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2251_, v_k_2254_, v___x_2255_, v_t_2253_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2258_ = l_panic___redArg(v_inst_2252_, v___x_2257_);
return v___x_2258_;
}
else
{
lean_object* v_val_2259_; 
v_val_2259_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_val_2259_);
lean_dec_ref(v___x_2256_);
return v_val_2259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_2260_, lean_object* v_inst_2261_, lean_object* v_t_2262_, lean_object* v_k_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(v_cmp_2260_, v_inst_2261_, v_t_2262_, v_k_2263_);
lean_dec_ref(v_inst_2261_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21(lean_object* v_00_u03b1_2265_, lean_object* v_cmp_2266_, lean_object* v_00_u03b2_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_t_2270_, lean_object* v_k_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_box(0);
v___x_2273_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2266_, v_k_2271_, v___x_2272_, v_t_2270_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2275_ = l_panic___redArg(v_inst_2269_, v___x_2274_);
return v___x_2275_;
}
else
{
lean_object* v_val_2276_; 
v_val_2276_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_val_2276_);
lean_dec_ref(v___x_2273_);
return v_val_2276_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_2277_, lean_object* v_cmp_2278_, lean_object* v_00_u03b2_2279_, lean_object* v_inst_2280_, lean_object* v_inst_2281_, lean_object* v_t_2282_, lean_object* v_k_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Std_ExtDTreeMap_Const_getEntryGT_x21(v_00_u03b1_2277_, v_cmp_2278_, v_00_u03b2_2279_, v_inst_2280_, v_inst_2281_, v_t_2282_, v_k_2283_);
lean_dec_ref(v_inst_2281_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(lean_object* v_cmp_2285_, lean_object* v_inst_2286_, lean_object* v_t_2287_, lean_object* v_k_2288_){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2285_, v_k_2288_, v___x_2289_, v_t_2287_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2292_ = l_panic___redArg(v_inst_2286_, v___x_2291_);
return v___x_2292_;
}
else
{
lean_object* v_val_2293_; 
v_val_2293_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_val_2293_);
lean_dec_ref(v___x_2290_);
return v_val_2293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_2294_, lean_object* v_inst_2295_, lean_object* v_t_2296_, lean_object* v_k_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(v_cmp_2294_, v_inst_2295_, v_t_2296_, v_k_2297_);
lean_dec_ref(v_inst_2295_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21(lean_object* v_00_u03b1_2299_, lean_object* v_cmp_2300_, lean_object* v_00_u03b2_2301_, lean_object* v_inst_2302_, lean_object* v_inst_2303_, lean_object* v_t_2304_, lean_object* v_k_2305_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_box(0);
v___x_2307_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2300_, v_k_2305_, v___x_2306_, v_t_2304_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2309_ = l_panic___redArg(v_inst_2303_, v___x_2308_);
return v___x_2309_;
}
else
{
lean_object* v_val_2310_; 
v_val_2310_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_val_2310_);
lean_dec_ref(v___x_2307_);
return v_val_2310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2311_, lean_object* v_cmp_2312_, lean_object* v_00_u03b2_2313_, lean_object* v_inst_2314_, lean_object* v_inst_2315_, lean_object* v_t_2316_, lean_object* v_k_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Std_ExtDTreeMap_Const_getEntryLE_x21(v_00_u03b1_2311_, v_cmp_2312_, v_00_u03b2_2313_, v_inst_2314_, v_inst_2315_, v_t_2316_, v_k_2317_);
lean_dec_ref(v_inst_2315_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(lean_object* v_cmp_2319_, lean_object* v_inst_2320_, lean_object* v_t_2321_, lean_object* v_k_2322_){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_box(0);
v___x_2324_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2319_, v_k_2322_, v___x_2323_, v_t_2321_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2326_ = l_panic___redArg(v_inst_2320_, v___x_2325_);
return v___x_2326_;
}
else
{
lean_object* v_val_2327_; 
v_val_2327_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_val_2327_);
lean_dec_ref(v___x_2324_);
return v_val_2327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_2328_, lean_object* v_inst_2329_, lean_object* v_t_2330_, lean_object* v_k_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(v_cmp_2328_, v_inst_2329_, v_t_2330_, v_k_2331_);
lean_dec_ref(v_inst_2329_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21(lean_object* v_00_u03b1_2333_, lean_object* v_cmp_2334_, lean_object* v_00_u03b2_2335_, lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_t_2338_, lean_object* v_k_2339_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_box(0);
v___x_2341_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2334_, v_k_2339_, v___x_2340_, v_t_2338_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_obj_once(&l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2343_ = l_panic___redArg(v_inst_2337_, v___x_2342_);
return v___x_2343_;
}
else
{
lean_object* v_val_2344_; 
v_val_2344_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_val_2344_);
lean_dec_ref(v___x_2341_);
return v_val_2344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2345_, lean_object* v_cmp_2346_, lean_object* v_00_u03b2_2347_, lean_object* v_inst_2348_, lean_object* v_inst_2349_, lean_object* v_t_2350_, lean_object* v_k_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Std_ExtDTreeMap_Const_getEntryLT_x21(v_00_u03b1_2345_, v_cmp_2346_, v_00_u03b2_2347_, v_inst_2348_, v_inst_2349_, v_t_2350_, v_k_2351_);
lean_dec_ref(v_inst_2349_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___redArg(lean_object* v_cmp_2353_, lean_object* v_t_2354_, lean_object* v_k_2355_, lean_object* v_fallback_2356_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_box(0);
v___x_2358_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2353_, v_k_2355_, v___x_2357_, v_t_2354_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_inc_ref(v_fallback_2356_);
return v_fallback_2356_;
}
else
{
lean_object* v_val_2359_; 
v_val_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_val_2359_);
lean_dec_ref(v___x_2358_);
return v_val_2359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2360_, lean_object* v_t_2361_, lean_object* v_k_2362_, lean_object* v_fallback_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Std_ExtDTreeMap_Const_getEntryGED___redArg(v_cmp_2360_, v_t_2361_, v_k_2362_, v_fallback_2363_);
lean_dec_ref(v_fallback_2363_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED(lean_object* v_00_u03b1_2365_, lean_object* v_cmp_2366_, lean_object* v_00_u03b2_2367_, lean_object* v_inst_2368_, lean_object* v_t_2369_, lean_object* v_k_2370_, lean_object* v_fallback_2371_){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = lean_box(0);
v___x_2373_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2366_, v_k_2370_, v___x_2372_, v_t_2369_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_inc_ref(v_fallback_2371_);
return v_fallback_2371_;
}
else
{
lean_object* v_val_2374_; 
v_val_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_val_2374_);
lean_dec_ref(v___x_2373_);
return v_val_2374_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2375_, lean_object* v_cmp_2376_, lean_object* v_00_u03b2_2377_, lean_object* v_inst_2378_, lean_object* v_t_2379_, lean_object* v_k_2380_, lean_object* v_fallback_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Std_ExtDTreeMap_Const_getEntryGED(v_00_u03b1_2375_, v_cmp_2376_, v_00_u03b2_2377_, v_inst_2378_, v_t_2379_, v_k_2380_, v_fallback_2381_);
lean_dec_ref(v_fallback_2381_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(lean_object* v_cmp_2383_, lean_object* v_t_2384_, lean_object* v_k_2385_, lean_object* v_fallback_2386_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_box(0);
v___x_2388_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2383_, v_k_2385_, v___x_2387_, v_t_2384_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_inc_ref(v_fallback_2386_);
return v_fallback_2386_;
}
else
{
lean_object* v_val_2389_; 
v_val_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_val_2389_);
lean_dec_ref(v___x_2388_);
return v_val_2389_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2390_, lean_object* v_t_2391_, lean_object* v_k_2392_, lean_object* v_fallback_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(v_cmp_2390_, v_t_2391_, v_k_2392_, v_fallback_2393_);
lean_dec_ref(v_fallback_2393_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD(lean_object* v_00_u03b1_2395_, lean_object* v_cmp_2396_, lean_object* v_00_u03b2_2397_, lean_object* v_inst_2398_, lean_object* v_t_2399_, lean_object* v_k_2400_, lean_object* v_fallback_2401_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = lean_box(0);
v___x_2403_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2396_, v_k_2400_, v___x_2402_, v_t_2399_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_inc_ref(v_fallback_2401_);
return v_fallback_2401_;
}
else
{
lean_object* v_val_2404_; 
v_val_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_val_2404_);
lean_dec_ref(v___x_2403_);
return v_val_2404_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2405_, lean_object* v_cmp_2406_, lean_object* v_00_u03b2_2407_, lean_object* v_inst_2408_, lean_object* v_t_2409_, lean_object* v_k_2410_, lean_object* v_fallback_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Std_ExtDTreeMap_Const_getEntryGTD(v_00_u03b1_2405_, v_cmp_2406_, v_00_u03b2_2407_, v_inst_2408_, v_t_2409_, v_k_2410_, v_fallback_2411_);
lean_dec_ref(v_fallback_2411_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___redArg(lean_object* v_cmp_2413_, lean_object* v_t_2414_, lean_object* v_k_2415_, lean_object* v_fallback_2416_){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_box(0);
v___x_2418_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2413_, v_k_2415_, v___x_2417_, v_t_2414_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_inc_ref(v_fallback_2416_);
return v_fallback_2416_;
}
else
{
lean_object* v_val_2419_; 
v_val_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_val_2419_);
lean_dec_ref(v___x_2418_);
return v_val_2419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2420_, lean_object* v_t_2421_, lean_object* v_k_2422_, lean_object* v_fallback_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Std_ExtDTreeMap_Const_getEntryLED___redArg(v_cmp_2420_, v_t_2421_, v_k_2422_, v_fallback_2423_);
lean_dec_ref(v_fallback_2423_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED(lean_object* v_00_u03b1_2425_, lean_object* v_cmp_2426_, lean_object* v_00_u03b2_2427_, lean_object* v_inst_2428_, lean_object* v_t_2429_, lean_object* v_k_2430_, lean_object* v_fallback_2431_){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = lean_box(0);
v___x_2433_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2426_, v_k_2430_, v___x_2432_, v_t_2429_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_inc_ref(v_fallback_2431_);
return v_fallback_2431_;
}
else
{
lean_object* v_val_2434_; 
v_val_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_val_2434_);
lean_dec_ref(v___x_2433_);
return v_val_2434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2435_, lean_object* v_cmp_2436_, lean_object* v_00_u03b2_2437_, lean_object* v_inst_2438_, lean_object* v_t_2439_, lean_object* v_k_2440_, lean_object* v_fallback_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Std_ExtDTreeMap_Const_getEntryLED(v_00_u03b1_2435_, v_cmp_2436_, v_00_u03b2_2437_, v_inst_2438_, v_t_2439_, v_k_2440_, v_fallback_2441_);
lean_dec_ref(v_fallback_2441_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(lean_object* v_cmp_2443_, lean_object* v_t_2444_, lean_object* v_k_2445_, lean_object* v_fallback_2446_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_box(0);
v___x_2448_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2443_, v_k_2445_, v___x_2447_, v_t_2444_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_inc_ref(v_fallback_2446_);
return v_fallback_2446_;
}
else
{
lean_object* v_val_2449_; 
v_val_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_val_2449_);
lean_dec_ref(v___x_2448_);
return v_val_2449_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2450_, lean_object* v_t_2451_, lean_object* v_k_2452_, lean_object* v_fallback_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(v_cmp_2450_, v_t_2451_, v_k_2452_, v_fallback_2453_);
lean_dec_ref(v_fallback_2453_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD(lean_object* v_00_u03b1_2455_, lean_object* v_cmp_2456_, lean_object* v_00_u03b2_2457_, lean_object* v_inst_2458_, lean_object* v_t_2459_, lean_object* v_k_2460_, lean_object* v_fallback_2461_){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = lean_box(0);
v___x_2463_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2456_, v_k_2460_, v___x_2462_, v_t_2459_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_inc_ref(v_fallback_2461_);
return v_fallback_2461_;
}
else
{
lean_object* v_val_2464_; 
v_val_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_val_2464_);
lean_dec_ref(v___x_2463_);
return v_val_2464_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2465_, lean_object* v_cmp_2466_, lean_object* v_00_u03b2_2467_, lean_object* v_inst_2468_, lean_object* v_t_2469_, lean_object* v_k_2470_, lean_object* v_fallback_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Std_ExtDTreeMap_Const_getEntryLTD(v_00_u03b1_2465_, v_cmp_2466_, v_00_u03b2_2467_, v_inst_2468_, v_t_2469_, v_k_2470_, v_fallback_2471_);
lean_dec_ref(v_fallback_2471_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter___redArg(lean_object* v_f_2473_, lean_object* v_t_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2473_, v_t_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter(lean_object* v_00_u03b1_2476_, lean_object* v_00_u03b2_2477_, lean_object* v_cmp_2478_, lean_object* v_f_2479_, lean_object* v_t_2480_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2479_, v_t_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filter___boxed(lean_object* v_00_u03b1_2482_, lean_object* v_00_u03b2_2483_, lean_object* v_cmp_2484_, lean_object* v_f_2485_, lean_object* v_t_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Std_ExtDTreeMap_filter(v_00_u03b1_2482_, v_00_u03b2_2483_, v_cmp_2484_, v_f_2485_, v_t_2486_);
lean_dec_ref(v_cmp_2484_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap___redArg(lean_object* v_f_2488_, lean_object* v_t_2489_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_2488_, v_t_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap(lean_object* v_00_u03b1_2491_, lean_object* v_00_u03b2_2492_, lean_object* v_00_u03b3_2493_, lean_object* v_cmp_2494_, lean_object* v_f_2495_, lean_object* v_t_2496_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_2495_, v_t_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_filterMap___boxed(lean_object* v_00_u03b1_2498_, lean_object* v_00_u03b2_2499_, lean_object* v_00_u03b3_2500_, lean_object* v_cmp_2501_, lean_object* v_f_2502_, lean_object* v_t_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Std_ExtDTreeMap_filterMap(v_00_u03b1_2498_, v_00_u03b2_2499_, v_00_u03b3_2500_, v_cmp_2501_, v_f_2502_, v_t_2503_);
lean_dec_ref(v_cmp_2501_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map___redArg(lean_object* v_f_2505_, lean_object* v_t_2506_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_2505_, v_t_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map(lean_object* v_00_u03b1_2508_, lean_object* v_00_u03b2_2509_, lean_object* v_00_u03b3_2510_, lean_object* v_cmp_2511_, lean_object* v_f_2512_, lean_object* v_t_2513_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_2512_, v_t_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_map___boxed(lean_object* v_00_u03b1_2515_, lean_object* v_00_u03b2_2516_, lean_object* v_00_u03b3_2517_, lean_object* v_cmp_2518_, lean_object* v_f_2519_, lean_object* v_t_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Std_ExtDTreeMap_map(v_00_u03b1_2515_, v_00_u03b2_2516_, v_00_u03b3_2517_, v_cmp_2518_, v_f_2519_, v_t_2520_);
lean_dec_ref(v_cmp_2518_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM___redArg(lean_object* v_inst_2522_, lean_object* v_f_2523_, lean_object* v_init_2524_, lean_object* v_t_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2522_, v_f_2523_, v_init_2524_, v_t_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM(lean_object* v_00_u03b1_2527_, lean_object* v_00_u03b2_2528_, lean_object* v_cmp_2529_, lean_object* v_00_u03b4_2530_, lean_object* v_m_2531_, lean_object* v_inst_2532_, lean_object* v_inst_2533_, lean_object* v_inst_2534_, lean_object* v_f_2535_, lean_object* v_init_2536_, lean_object* v_t_2537_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2532_, v_f_2535_, v_init_2536_, v_t_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldlM___boxed(lean_object* v_00_u03b1_2539_, lean_object* v_00_u03b2_2540_, lean_object* v_cmp_2541_, lean_object* v_00_u03b4_2542_, lean_object* v_m_2543_, lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_f_2547_, lean_object* v_init_2548_, lean_object* v_t_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Std_ExtDTreeMap_foldlM(v_00_u03b1_2539_, v_00_u03b2_2540_, v_cmp_2541_, v_00_u03b4_2542_, v_m_2543_, v_inst_2544_, v_inst_2545_, v_inst_2546_, v_f_2547_, v_init_2548_, v_t_2549_);
lean_dec_ref(v_cmp_2541_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl___redArg(lean_object* v_f_2551_, lean_object* v_init_2552_, lean_object* v_t_2553_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2551_, v_init_2552_, v_t_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl(lean_object* v_00_u03b1_2555_, lean_object* v_00_u03b2_2556_, lean_object* v_cmp_2557_, lean_object* v_00_u03b4_2558_, lean_object* v_inst_2559_, lean_object* v_f_2560_, lean_object* v_init_2561_, lean_object* v_t_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2560_, v_init_2561_, v_t_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldl___boxed(lean_object* v_00_u03b1_2564_, lean_object* v_00_u03b2_2565_, lean_object* v_cmp_2566_, lean_object* v_00_u03b4_2567_, lean_object* v_inst_2568_, lean_object* v_f_2569_, lean_object* v_init_2570_, lean_object* v_t_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Std_ExtDTreeMap_foldl(v_00_u03b1_2564_, v_00_u03b2_2565_, v_cmp_2566_, v_00_u03b4_2567_, v_inst_2568_, v_f_2569_, v_init_2570_, v_t_2571_);
lean_dec_ref(v_cmp_2566_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM___redArg(lean_object* v_inst_2573_, lean_object* v_f_2574_, lean_object* v_init_2575_, lean_object* v_t_2576_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2573_, v_f_2574_, v_init_2575_, v_t_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM(lean_object* v_00_u03b1_2578_, lean_object* v_00_u03b2_2579_, lean_object* v_cmp_2580_, lean_object* v_00_u03b4_2581_, lean_object* v_m_2582_, lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_inst_2585_, lean_object* v_f_2586_, lean_object* v_init_2587_, lean_object* v_t_2588_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2583_, v_f_2586_, v_init_2587_, v_t_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldrM___boxed(lean_object* v_00_u03b1_2590_, lean_object* v_00_u03b2_2591_, lean_object* v_cmp_2592_, lean_object* v_00_u03b4_2593_, lean_object* v_m_2594_, lean_object* v_inst_2595_, lean_object* v_inst_2596_, lean_object* v_inst_2597_, lean_object* v_f_2598_, lean_object* v_init_2599_, lean_object* v_t_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Std_ExtDTreeMap_foldrM(v_00_u03b1_2590_, v_00_u03b2_2591_, v_cmp_2592_, v_00_u03b4_2593_, v_m_2594_, v_inst_2595_, v_inst_2596_, v_inst_2597_, v_f_2598_, v_init_2599_, v_t_2600_);
lean_dec_ref(v_cmp_2592_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___redArg___lam__0(lean_object* v_f_2602_, lean_object* v_x1_2603_, lean_object* v_x2_2604_, lean_object* v_x3_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = lean_apply_3(v_f_2602_, v_x1_2603_, v_x2_2604_, v_x3_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___redArg(lean_object* v_f_2626_, lean_object* v_init_2627_, lean_object* v_t_2628_){
_start:
{
lean_object* v___f_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___f_2629_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2629_, 0, v_f_2626_);
v___x_2630_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2631_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2630_, v___f_2629_, v_init_2627_, v_t_2628_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr(lean_object* v_00_u03b1_2632_, lean_object* v_00_u03b2_2633_, lean_object* v_cmp_2634_, lean_object* v_00_u03b4_2635_, lean_object* v_inst_2636_, lean_object* v_f_2637_, lean_object* v_init_2638_, lean_object* v_t_2639_){
_start:
{
lean_object* v___f_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___f_2640_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2640_, 0, v_f_2637_);
v___x_2641_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2642_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2641_, v___f_2640_, v_init_2638_, v_t_2639_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_foldr___boxed(lean_object* v_00_u03b1_2643_, lean_object* v_00_u03b2_2644_, lean_object* v_cmp_2645_, lean_object* v_00_u03b4_2646_, lean_object* v_inst_2647_, lean_object* v_f_2648_, lean_object* v_init_2649_, lean_object* v_t_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Std_ExtDTreeMap_foldr(v_00_u03b1_2643_, v_00_u03b2_2644_, v_cmp_2645_, v_00_u03b4_2646_, v_inst_2647_, v_f_2648_, v_init_2649_, v_t_2650_);
lean_dec_ref(v_cmp_2645_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition___redArg___lam__0(lean_object* v_f_2652_, lean_object* v_cmp_2653_, lean_object* v_x_2654_, lean_object* v_a_2655_, lean_object* v_b_2656_){
_start:
{
lean_object* v_fst_2657_; lean_object* v_snd_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2672_; 
v_fst_2657_ = lean_ctor_get(v_x_2654_, 0);
v_snd_2658_ = lean_ctor_get(v_x_2654_, 1);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_x_2654_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2660_ = v_x_2654_;
v_isShared_2661_ = v_isSharedCheck_2672_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_snd_2658_);
lean_inc(v_fst_2657_);
lean_dec(v_x_2654_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2672_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; uint8_t v___x_2663_; 
lean_inc(v_b_2656_);
lean_inc(v_a_2655_);
v___x_2662_ = lean_apply_2(v_f_2652_, v_a_2655_, v_b_2656_);
v___x_2663_ = lean_unbox(v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2664_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2653_, v_a_2655_, v_b_2656_, v_snd_2658_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v___x_2664_);
v___x_2666_ = v___x_2660_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_fst_2657_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2668_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2653_, v_a_2655_, v_b_2656_, v_fst_2657_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2668_);
v___x_2670_ = v___x_2660_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_snd_2658_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition___redArg(lean_object* v_cmp_2675_, lean_object* v_f_2676_, lean_object* v_t_2677_){
_start:
{
lean_object* v___f_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___f_2678_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2678_, 0, v_f_2676_);
lean_closure_set(v___f_2678_, 1, v_cmp_2675_);
v___x_2679_ = ((lean_object*)(l_Std_ExtDTreeMap_partition___redArg___closed__0));
v___x_2680_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2678_, v___x_2679_, v_t_2677_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_partition(lean_object* v_00_u03b1_2681_, lean_object* v_00_u03b2_2682_, lean_object* v_cmp_2683_, lean_object* v_inst_2684_, lean_object* v_f_2685_, lean_object* v_t_2686_){
_start:
{
lean_object* v___f_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___f_2687_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2687_, 0, v_f_2685_);
lean_closure_set(v___f_2687_, 1, v_cmp_2683_);
v___x_2688_ = ((lean_object*)(l_Std_ExtDTreeMap_partition___redArg___closed__0));
v___x_2689_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2687_, v___x_2688_, v_t_2686_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___redArg___lam__0(lean_object* v_f_2690_, lean_object* v_x_2691_, lean_object* v_k_2692_, lean_object* v_v_2693_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_apply_2(v_f_2690_, v_k_2692_, v_v_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___redArg(lean_object* v_inst_2695_, lean_object* v_f_2696_, lean_object* v_t_2697_){
_start:
{
lean_object* v___f_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___f_2698_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2698_, 0, v_f_2696_);
v___x_2699_ = lean_box(0);
v___x_2700_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2695_, v___f_2698_, v___x_2699_, v_t_2697_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM(lean_object* v_00_u03b1_2701_, lean_object* v_00_u03b2_2702_, lean_object* v_cmp_2703_, lean_object* v_m_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_f_2708_, lean_object* v_t_2709_){
_start:
{
lean_object* v___f_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___f_2710_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2710_, 0, v_f_2708_);
v___x_2711_ = lean_box(0);
v___x_2712_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2705_, v___f_2710_, v___x_2711_, v_t_2709_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forM___boxed(lean_object* v_00_u03b1_2713_, lean_object* v_00_u03b2_2714_, lean_object* v_cmp_2715_, lean_object* v_m_2716_, lean_object* v_inst_2717_, lean_object* v_inst_2718_, lean_object* v_inst_2719_, lean_object* v_f_2720_, lean_object* v_t_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Std_ExtDTreeMap_forM(v_00_u03b1_2713_, v_00_u03b2_2714_, v_cmp_2715_, v_m_2716_, v_inst_2717_, v_inst_2718_, v_inst_2719_, v_f_2720_, v_t_2721_);
lean_dec_ref(v_cmp_2715_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___redArg___lam__0(lean_object* v_toPure_2723_, lean_object* v_____do__lift_2724_){
_start:
{
lean_object* v_a_2725_; lean_object* v___x_2726_; 
v_a_2725_ = lean_ctor_get(v_____do__lift_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref(v_____do__lift_2724_);
v___x_2726_ = lean_apply_2(v_toPure_2723_, lean_box(0), v_a_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___redArg(lean_object* v_inst_2727_, lean_object* v_f_2728_, lean_object* v_init_2729_, lean_object* v_t_2730_){
_start:
{
lean_object* v_toApplicative_2731_; lean_object* v_toBind_2732_; lean_object* v_toPure_2733_; lean_object* v___x_2734_; lean_object* v___f_2735_; lean_object* v___x_2736_; 
v_toApplicative_2731_ = lean_ctor_get(v_inst_2727_, 0);
v_toBind_2732_ = lean_ctor_get(v_inst_2727_, 1);
lean_inc(v_toBind_2732_);
v_toPure_2733_ = lean_ctor_get(v_toApplicative_2731_, 1);
lean_inc(v_toPure_2733_);
v___x_2734_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2727_, v_f_2728_, v_init_2729_, v_t_2730_);
v___f_2735_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2735_, 0, v_toPure_2733_);
v___x_2736_ = lean_apply_4(v_toBind_2732_, lean_box(0), lean_box(0), v___x_2734_, v___f_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn(lean_object* v_00_u03b1_2737_, lean_object* v_00_u03b2_2738_, lean_object* v_cmp_2739_, lean_object* v_00_u03b4_2740_, lean_object* v_m_2741_, lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_inst_2744_, lean_object* v_f_2745_, lean_object* v_init_2746_, lean_object* v_t_2747_){
_start:
{
lean_object* v_toApplicative_2748_; lean_object* v_toBind_2749_; lean_object* v_toPure_2750_; lean_object* v___x_2751_; lean_object* v___f_2752_; lean_object* v___x_2753_; 
v_toApplicative_2748_ = lean_ctor_get(v_inst_2742_, 0);
v_toBind_2749_ = lean_ctor_get(v_inst_2742_, 1);
lean_inc(v_toBind_2749_);
v_toPure_2750_ = lean_ctor_get(v_toApplicative_2748_, 1);
lean_inc(v_toPure_2750_);
v___x_2751_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2742_, v_f_2745_, v_init_2746_, v_t_2747_);
v___f_2752_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2752_, 0, v_toPure_2750_);
v___x_2753_ = lean_apply_4(v_toBind_2749_, lean_box(0), lean_box(0), v___x_2751_, v___f_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_forIn___boxed(lean_object* v_00_u03b1_2754_, lean_object* v_00_u03b2_2755_, lean_object* v_cmp_2756_, lean_object* v_00_u03b4_2757_, lean_object* v_m_2758_, lean_object* v_inst_2759_, lean_object* v_inst_2760_, lean_object* v_inst_2761_, lean_object* v_f_2762_, lean_object* v_init_2763_, lean_object* v_t_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Std_ExtDTreeMap_forIn(v_00_u03b1_2754_, v_00_u03b2_2755_, v_cmp_2756_, v_00_u03b4_2757_, v_m_2758_, v_inst_2759_, v_inst_2760_, v_inst_2761_, v_f_2762_, v_init_2763_, v_t_2764_);
lean_dec_ref(v_cmp_2756_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2766_, lean_object* v_x_2767_, lean_object* v_k_2768_, lean_object* v_v_2769_){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v_k_2768_);
lean_ctor_set(v___x_2770_, 1, v_v_2769_);
v___x_2771_ = lean_apply_1(v_f_2766_, v___x_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_2772_, lean_object* v_t_2773_, lean_object* v_f_2774_){
_start:
{
lean_object* v___f_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___f_2775_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2775_, 0, v_f_2774_);
v___x_2776_ = lean_box(0);
v___x_2777_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2772_, v___f_2775_, v___x_2776_, v_t_2773_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2778_){
_start:
{
lean_object* v___f_2779_; 
v___f_2779_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2779_, 0, v_inst_2778_);
return v___f_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2780_, lean_object* v_00_u03b2_2781_, lean_object* v_cmp_2782_, lean_object* v_m_2783_, lean_object* v_inst_2784_, lean_object* v_inst_2785_, lean_object* v_inst_2786_){
_start:
{
lean_object* v___f_2787_; 
v___f_2787_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2787_, 0, v_inst_2785_);
return v___f_2787_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2788_, lean_object* v_00_u03b2_2789_, lean_object* v_cmp_2790_, lean_object* v_m_2791_, lean_object* v_inst_2792_, lean_object* v_inst_2793_, lean_object* v_inst_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(v_00_u03b1_2788_, v_00_u03b2_2789_, v_cmp_2790_, v_m_2791_, v_inst_2792_, v_inst_2793_, v_inst_2794_);
lean_dec_ref(v_cmp_2790_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2796_, lean_object* v_a_2797_, lean_object* v_b_2798_, lean_object* v_acc_2799_){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v_a_2797_);
lean_ctor_set(v___x_2800_, 1, v_b_2798_);
v___x_2801_ = lean_apply_2(v_f_2796_, v___x_2800_, v_acc_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_2802_, lean_object* v_00_u03b2_2803_, lean_object* v_m_2804_, lean_object* v_init_2805_, lean_object* v_f_2806_){
_start:
{
lean_object* v_toApplicative_2807_; lean_object* v_toBind_2808_; lean_object* v_toPure_2809_; lean_object* v___f_2810_; lean_object* v___x_2811_; lean_object* v___f_2812_; lean_object* v___x_2813_; 
v_toApplicative_2807_ = lean_ctor_get(v_inst_2802_, 0);
v_toBind_2808_ = lean_ctor_get(v_inst_2802_, 1);
lean_inc(v_toBind_2808_);
v_toPure_2809_ = lean_ctor_get(v_toApplicative_2807_, 1);
lean_inc(v_toPure_2809_);
v___f_2810_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2810_, 0, v_f_2806_);
v___x_2811_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2802_, v___f_2810_, v_init_2805_, v_m_2804_);
v___f_2812_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2812_, 0, v_toPure_2809_);
v___x_2813_ = lean_apply_4(v_toBind_2808_, lean_box(0), lean_box(0), v___x_2811_, v___f_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2814_){
_start:
{
lean_object* v___f_2815_; 
v___f_2815_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2815_, 0, v_inst_2814_);
return v___f_2815_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2816_, lean_object* v_00_u03b2_2817_, lean_object* v_cmp_2818_, lean_object* v_m_2819_, lean_object* v_inst_2820_, lean_object* v_inst_2821_, lean_object* v_inst_2822_){
_start:
{
lean_object* v___f_2823_; 
v___f_2823_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2823_, 0, v_inst_2821_);
return v___f_2823_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2824_, lean_object* v_00_u03b2_2825_, lean_object* v_cmp_2826_, lean_object* v_m_2827_, lean_object* v_inst_2828_, lean_object* v_inst_2829_, lean_object* v_inst_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(v_00_u03b1_2824_, v_00_u03b2_2825_, v_cmp_2826_, v_m_2827_, v_inst_2828_, v_inst_2829_, v_inst_2830_);
lean_dec_ref(v_cmp_2826_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2832_, lean_object* v_x_2833_, lean_object* v_k_2834_, lean_object* v_v_2835_){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2836_, 0, v_k_2834_);
lean_ctor_set(v___x_2836_, 1, v_v_2835_);
v___x_2837_ = lean_apply_1(v_f_2832_, v___x_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___redArg(lean_object* v_inst_2838_, lean_object* v_f_2839_, lean_object* v_t_2840_){
_start:
{
lean_object* v___f_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___f_2841_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2841_, 0, v_f_2839_);
v___x_2842_ = lean_box(0);
v___x_2843_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2838_, v___f_2841_, v___x_2842_, v_t_2840_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried(lean_object* v_00_u03b1_2844_, lean_object* v_cmp_2845_, lean_object* v_m_2846_, lean_object* v_inst_2847_, lean_object* v_inst_2848_, lean_object* v_00_u03b2_2849_, lean_object* v_inst_2850_, lean_object* v_f_2851_, lean_object* v_t_2852_){
_start:
{
lean_object* v___f_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___f_2853_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2853_, 0, v_f_2851_);
v___x_2854_ = lean_box(0);
v___x_2855_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2847_, v___f_2853_, v___x_2854_, v_t_2852_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2856_, lean_object* v_cmp_2857_, lean_object* v_m_2858_, lean_object* v_inst_2859_, lean_object* v_inst_2860_, lean_object* v_00_u03b2_2861_, lean_object* v_inst_2862_, lean_object* v_f_2863_, lean_object* v_t_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Std_ExtDTreeMap_Const_forMUncurried(v_00_u03b1_2856_, v_cmp_2857_, v_m_2858_, v_inst_2859_, v_inst_2860_, v_00_u03b2_2861_, v_inst_2862_, v_f_2863_, v_t_2864_);
lean_dec_ref(v_cmp_2857_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2866_, lean_object* v_a_2867_, lean_object* v_b_2868_, lean_object* v_acc_2869_){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2870_, 0, v_a_2867_);
lean_ctor_set(v___x_2870_, 1, v_b_2868_);
v___x_2871_ = lean_apply_2(v_f_2866_, v___x_2870_, v_acc_2869_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___redArg(lean_object* v_inst_2872_, lean_object* v_f_2873_, lean_object* v_init_2874_, lean_object* v_t_2875_){
_start:
{
lean_object* v_toApplicative_2876_; lean_object* v_toBind_2877_; lean_object* v_toPure_2878_; lean_object* v___f_2879_; lean_object* v___x_2880_; lean_object* v___f_2881_; lean_object* v___x_2882_; 
v_toApplicative_2876_ = lean_ctor_get(v_inst_2872_, 0);
v_toBind_2877_ = lean_ctor_get(v_inst_2872_, 1);
lean_inc(v_toBind_2877_);
v_toPure_2878_ = lean_ctor_get(v_toApplicative_2876_, 1);
lean_inc(v_toPure_2878_);
v___f_2879_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2879_, 0, v_f_2873_);
v___x_2880_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2872_, v___f_2879_, v_init_2874_, v_t_2875_);
v___f_2881_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2881_, 0, v_toPure_2878_);
v___x_2882_ = lean_apply_4(v_toBind_2877_, lean_box(0), lean_box(0), v___x_2880_, v___f_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried(lean_object* v_00_u03b1_2883_, lean_object* v_cmp_2884_, lean_object* v_00_u03b4_2885_, lean_object* v_m_2886_, lean_object* v_inst_2887_, lean_object* v_inst_2888_, lean_object* v_00_u03b2_2889_, lean_object* v_inst_2890_, lean_object* v_f_2891_, lean_object* v_init_2892_, lean_object* v_t_2893_){
_start:
{
lean_object* v_toApplicative_2894_; lean_object* v_toBind_2895_; lean_object* v_toPure_2896_; lean_object* v___f_2897_; lean_object* v___x_2898_; lean_object* v___f_2899_; lean_object* v___x_2900_; 
v_toApplicative_2894_ = lean_ctor_get(v_inst_2887_, 0);
v_toBind_2895_ = lean_ctor_get(v_inst_2887_, 1);
lean_inc(v_toBind_2895_);
v_toPure_2896_ = lean_ctor_get(v_toApplicative_2894_, 1);
lean_inc(v_toPure_2896_);
v___f_2897_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2897_, 0, v_f_2891_);
v___x_2898_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2887_, v___f_2897_, v_init_2892_, v_t_2893_);
v___f_2899_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2899_, 0, v_toPure_2896_);
v___x_2900_ = lean_apply_4(v_toBind_2895_, lean_box(0), lean_box(0), v___x_2898_, v___f_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2901_, lean_object* v_cmp_2902_, lean_object* v_00_u03b4_2903_, lean_object* v_m_2904_, lean_object* v_inst_2905_, lean_object* v_inst_2906_, lean_object* v_00_u03b2_2907_, lean_object* v_inst_2908_, lean_object* v_f_2909_, lean_object* v_init_2910_, lean_object* v_t_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Std_ExtDTreeMap_Const_forInUncurried(v_00_u03b1_2901_, v_cmp_2902_, v_00_u03b4_2903_, v_m_2904_, v_inst_2905_, v_inst_2906_, v_00_u03b2_2907_, v_inst_2908_, v_f_2909_, v_init_2910_, v_t_2911_);
lean_dec_ref(v_cmp_2902_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___lam__0(lean_object* v_p_2913_, lean_object* v___x_2914_, lean_object* v___x_2915_, lean_object* v_a_2916_, lean_object* v_b_2917_, lean_object* v_acc_2918_){
_start:
{
lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = lean_apply_2(v_p_2913_, v_a_2916_, v_b_2917_);
v___x_2920_ = lean_unbox(v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2914_);
return v___x_2921_;
}
else
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_dec_ref(v___x_2914_);
v___x_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2919_);
v___x_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
lean_ctor_set(v___x_2923_, 1, v___x_2915_);
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
return v___x_2924_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2925_, lean_object* v___x_2926_, lean_object* v___x_2927_, lean_object* v_a_2928_, lean_object* v_b_2929_, lean_object* v_acc_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Std_ExtDTreeMap_any___redArg___lam__0(v_p_2925_, v___x_2926_, v___x_2927_, v_a_2928_, v_b_2929_, v_acc_2930_);
lean_dec_ref(v_acc_2930_);
return v_res_2931_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_any___redArg(lean_object* v_t_2935_, lean_object* v_p_2936_){
_start:
{
lean_object* v___y_2938_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___f_2946_; lean_object* v___x_2947_; lean_object* v_a_2948_; 
v___x_2943_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2944_ = lean_box(0);
v___x_2945_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_2946_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2946_, 0, v_p_2936_);
lean_closure_set(v___f_2946_, 1, v___x_2945_);
lean_closure_set(v___f_2946_, 2, v___x_2944_);
v___x_2947_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2943_, v___f_2946_, v___x_2945_, v_t_2935_);
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec(v___x_2947_);
v___y_2938_ = v_a_2948_;
goto v___jp_2937_;
v___jp_2937_:
{
lean_object* v_fst_2939_; 
v_fst_2939_ = lean_ctor_get(v___y_2938_, 0);
lean_inc(v_fst_2939_);
lean_dec_ref(v___y_2938_);
if (lean_obj_tag(v_fst_2939_) == 0)
{
uint8_t v___x_2940_; 
v___x_2940_ = 0;
return v___x_2940_;
}
else
{
lean_object* v_val_2941_; uint8_t v___x_2942_; 
v_val_2941_ = lean_ctor_get(v_fst_2939_, 0);
lean_inc(v_val_2941_);
lean_dec_ref(v_fst_2939_);
v___x_2942_ = lean_unbox(v_val_2941_);
lean_dec(v_val_2941_);
return v___x_2942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___redArg___boxed(lean_object* v_t_2949_, lean_object* v_p_2950_){
_start:
{
uint8_t v_res_2951_; lean_object* v_r_2952_; 
v_res_2951_ = l_Std_ExtDTreeMap_any___redArg(v_t_2949_, v_p_2950_);
v_r_2952_ = lean_box(v_res_2951_);
return v_r_2952_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_any(lean_object* v_00_u03b1_2953_, lean_object* v_00_u03b2_2954_, lean_object* v_cmp_2955_, lean_object* v_inst_2956_, lean_object* v_t_2957_, lean_object* v_p_2958_){
_start:
{
lean_object* v___y_2960_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___f_2968_; lean_object* v___x_2969_; lean_object* v_a_2970_; 
v___x_2965_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_2966_ = lean_box(0);
v___x_2967_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_2968_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2968_, 0, v_p_2958_);
lean_closure_set(v___f_2968_, 1, v___x_2967_);
lean_closure_set(v___f_2968_, 2, v___x_2966_);
v___x_2969_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2965_, v___f_2968_, v___x_2967_, v_t_2957_);
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec(v___x_2969_);
v___y_2960_ = v_a_2970_;
goto v___jp_2959_;
v___jp_2959_:
{
lean_object* v_fst_2961_; 
v_fst_2961_ = lean_ctor_get(v___y_2960_, 0);
lean_inc(v_fst_2961_);
lean_dec_ref(v___y_2960_);
if (lean_obj_tag(v_fst_2961_) == 0)
{
uint8_t v___x_2962_; 
v___x_2962_ = 0;
return v___x_2962_;
}
else
{
lean_object* v_val_2963_; uint8_t v___x_2964_; 
v_val_2963_ = lean_ctor_get(v_fst_2961_, 0);
lean_inc(v_val_2963_);
lean_dec_ref(v_fst_2961_);
v___x_2964_ = lean_unbox(v_val_2963_);
lean_dec(v_val_2963_);
return v___x_2964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_any___boxed(lean_object* v_00_u03b1_2971_, lean_object* v_00_u03b2_2972_, lean_object* v_cmp_2973_, lean_object* v_inst_2974_, lean_object* v_t_2975_, lean_object* v_p_2976_){
_start:
{
uint8_t v_res_2977_; lean_object* v_r_2978_; 
v_res_2977_ = l_Std_ExtDTreeMap_any(v_00_u03b1_2971_, v_00_u03b2_2972_, v_cmp_2973_, v_inst_2974_, v_t_2975_, v_p_2976_);
lean_dec_ref(v_cmp_2973_);
v_r_2978_ = lean_box(v_res_2977_);
return v_r_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___lam__0(lean_object* v_p_2979_, lean_object* v___x_2980_, lean_object* v___x_2981_, lean_object* v_a_2982_, lean_object* v_b_2983_, lean_object* v_acc_2984_){
_start:
{
lean_object* v___x_2985_; uint8_t v___x_2986_; 
v___x_2985_ = lean_apply_2(v_p_2979_, v_a_2982_, v_b_2983_);
v___x_2986_ = lean_unbox(v___x_2985_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec_ref(v___x_2981_);
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v___x_2980_);
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
return v___x_2989_;
}
else
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2981_);
return v___x_2990_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_2991_, lean_object* v___x_2992_, lean_object* v___x_2993_, lean_object* v_a_2994_, lean_object* v_b_2995_, lean_object* v_acc_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Std_ExtDTreeMap_all___redArg___lam__0(v_p_2991_, v___x_2992_, v___x_2993_, v_a_2994_, v_b_2995_, v_acc_2996_);
lean_dec_ref(v_acc_2996_);
return v_res_2997_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_all___redArg(lean_object* v_t_2998_, lean_object* v_p_2999_){
_start:
{
lean_object* v___y_3001_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___f_3009_; lean_object* v___x_3010_; lean_object* v_a_3011_; 
v___x_3006_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3007_ = lean_box(0);
v___x_3008_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_3009_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3009_, 0, v_p_2999_);
lean_closure_set(v___f_3009_, 1, v___x_3007_);
lean_closure_set(v___f_3009_, 2, v___x_3008_);
v___x_3010_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_3006_, v___f_3009_, v___x_3008_, v_t_2998_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec(v___x_3010_);
v___y_3001_ = v_a_3011_;
goto v___jp_3000_;
v___jp_3000_:
{
lean_object* v_fst_3002_; 
v_fst_3002_ = lean_ctor_get(v___y_3001_, 0);
lean_inc(v_fst_3002_);
lean_dec_ref(v___y_3001_);
if (lean_obj_tag(v_fst_3002_) == 0)
{
uint8_t v___x_3003_; 
v___x_3003_ = 1;
return v___x_3003_;
}
else
{
lean_object* v_val_3004_; uint8_t v___x_3005_; 
v_val_3004_ = lean_ctor_get(v_fst_3002_, 0);
lean_inc(v_val_3004_);
lean_dec_ref(v_fst_3002_);
v___x_3005_ = lean_unbox(v_val_3004_);
lean_dec(v_val_3004_);
return v___x_3005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___redArg___boxed(lean_object* v_t_3012_, lean_object* v_p_3013_){
_start:
{
uint8_t v_res_3014_; lean_object* v_r_3015_; 
v_res_3014_ = l_Std_ExtDTreeMap_all___redArg(v_t_3012_, v_p_3013_);
v_r_3015_ = lean_box(v_res_3014_);
return v_r_3015_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_all(lean_object* v_00_u03b1_3016_, lean_object* v_00_u03b2_3017_, lean_object* v_cmp_3018_, lean_object* v_inst_3019_, lean_object* v_t_3020_, lean_object* v_p_3021_){
_start:
{
lean_object* v___y_3023_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___f_3031_; lean_object* v___x_3032_; lean_object* v_a_3033_; 
v___x_3028_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3029_ = lean_box(0);
v___x_3030_ = ((lean_object*)(l_Std_ExtDTreeMap_any___redArg___closed__0));
v___f_3031_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3031_, 0, v_p_3021_);
lean_closure_set(v___f_3031_, 1, v___x_3029_);
lean_closure_set(v___f_3031_, 2, v___x_3030_);
v___x_3032_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_3028_, v___f_3031_, v___x_3030_, v_t_3020_);
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec(v___x_3032_);
v___y_3023_ = v_a_3033_;
goto v___jp_3022_;
v___jp_3022_:
{
lean_object* v_fst_3024_; 
v_fst_3024_ = lean_ctor_get(v___y_3023_, 0);
lean_inc(v_fst_3024_);
lean_dec_ref(v___y_3023_);
if (lean_obj_tag(v_fst_3024_) == 0)
{
uint8_t v___x_3025_; 
v___x_3025_ = 1;
return v___x_3025_;
}
else
{
lean_object* v_val_3026_; uint8_t v___x_3027_; 
v_val_3026_ = lean_ctor_get(v_fst_3024_, 0);
lean_inc(v_val_3026_);
lean_dec_ref(v_fst_3024_);
v___x_3027_ = lean_unbox(v_val_3026_);
lean_dec(v_val_3026_);
return v___x_3027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_all___boxed(lean_object* v_00_u03b1_3034_, lean_object* v_00_u03b2_3035_, lean_object* v_cmp_3036_, lean_object* v_inst_3037_, lean_object* v_t_3038_, lean_object* v_p_3039_){
_start:
{
uint8_t v_res_3040_; lean_object* v_r_3041_; 
v_res_3040_ = l_Std_ExtDTreeMap_all(v_00_u03b1_3034_, v_00_u03b2_3035_, v_cmp_3036_, v_inst_3037_, v_t_3038_, v_p_3039_);
lean_dec_ref(v_cmp_3036_);
v_r_3041_ = lean_box(v_res_3040_);
return v_r_3041_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg___lam__0(lean_object* v_x1_3042_, lean_object* v_x2_3043_, lean_object* v_x3_3044_){
_start:
{
lean_object* v___x_3045_; 
v___x_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3045_, 0, v_x1_3042_);
lean_ctor_set(v___x_3045_, 1, v_x3_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_3046_, lean_object* v_x2_3047_, lean_object* v_x3_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Std_ExtDTreeMap_keys___redArg___lam__0(v_x1_3046_, v_x2_3047_, v_x3_3048_);
lean_dec(v_x2_3047_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___redArg(lean_object* v_t_3051_){
_start:
{
lean_object* v___f_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___f_3052_ = ((lean_object*)(l_Std_ExtDTreeMap_keys___redArg___closed__0));
v___x_3053_ = lean_box(0);
v___x_3054_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3055_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3054_, v___f_3052_, v___x_3053_, v_t_3051_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys(lean_object* v_00_u03b1_3056_, lean_object* v_00_u03b2_3057_, lean_object* v_cmp_3058_, lean_object* v_inst_3059_, lean_object* v_t_3060_){
_start:
{
lean_object* v___f_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___f_3061_ = ((lean_object*)(l_Std_ExtDTreeMap_keys___redArg___closed__0));
v___x_3062_ = lean_box(0);
v___x_3063_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3064_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3063_, v___f_3061_, v___x_3062_, v_t_3060_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keys___boxed(lean_object* v_00_u03b1_3065_, lean_object* v_00_u03b2_3066_, lean_object* v_cmp_3067_, lean_object* v_inst_3068_, lean_object* v_t_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Std_ExtDTreeMap_keys(v_00_u03b1_3065_, v_00_u03b2_3066_, v_cmp_3067_, v_inst_3068_, v_t_3069_);
lean_dec_ref(v_cmp_3067_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg___lam__0(lean_object* v_l_3071_, lean_object* v_k_3072_, lean_object* v_x_3073_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_array_push(v_l_3071_, v_k_3072_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_3075_, lean_object* v_k_3076_, lean_object* v_x_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Std_ExtDTreeMap_keysArray___redArg___lam__0(v_l_3075_, v_k_3076_, v_x_3077_);
lean_dec(v_x_3077_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___redArg(lean_object* v_t_3080_){
_start:
{
lean_object* v___f_3081_; lean_object* v___y_3083_; 
v___f_3081_ = ((lean_object*)(l_Std_ExtDTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_3080_) == 0)
{
lean_object* v_size_3086_; 
v_size_3086_ = lean_ctor_get(v_t_3080_, 0);
lean_inc(v_size_3086_);
v___y_3083_ = v_size_3086_;
goto v___jp_3082_;
}
else
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_unsigned_to_nat(0u);
v___y_3083_ = v___x_3087_;
goto v___jp_3082_;
}
v___jp_3082_:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_mk_empty_array_with_capacity(v___y_3083_);
lean_dec(v___y_3083_);
v___x_3085_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3081_, v___x_3084_, v_t_3080_);
return v___x_3085_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray(lean_object* v_00_u03b1_3088_, lean_object* v_00_u03b2_3089_, lean_object* v_cmp_3090_, lean_object* v_inst_3091_, lean_object* v_t_3092_){
_start:
{
lean_object* v___f_3093_; lean_object* v___y_3095_; 
v___f_3093_ = ((lean_object*)(l_Std_ExtDTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_3092_) == 0)
{
lean_object* v_size_3098_; 
v_size_3098_ = lean_ctor_get(v_t_3092_, 0);
lean_inc(v_size_3098_);
v___y_3095_ = v_size_3098_;
goto v___jp_3094_;
}
else
{
lean_object* v___x_3099_; 
v___x_3099_ = lean_unsigned_to_nat(0u);
v___y_3095_ = v___x_3099_;
goto v___jp_3094_;
}
v___jp_3094_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_mk_empty_array_with_capacity(v___y_3095_);
lean_dec(v___y_3095_);
v___x_3097_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3093_, v___x_3096_, v_t_3092_);
return v___x_3097_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_keysArray___boxed(lean_object* v_00_u03b1_3100_, lean_object* v_00_u03b2_3101_, lean_object* v_cmp_3102_, lean_object* v_inst_3103_, lean_object* v_t_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Std_ExtDTreeMap_keysArray(v_00_u03b1_3100_, v_00_u03b2_3101_, v_cmp_3102_, v_inst_3103_, v_t_3104_);
lean_dec_ref(v_cmp_3102_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg___lam__0(lean_object* v_x1_3106_, lean_object* v_x2_3107_, lean_object* v_x3_3108_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3109_, 0, v_x2_3107_);
lean_ctor_set(v___x_3109_, 1, v_x3_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_3110_, lean_object* v_x2_3111_, lean_object* v_x3_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Std_ExtDTreeMap_values___redArg___lam__0(v_x1_3110_, v_x2_3111_, v_x3_3112_);
lean_dec(v_x1_3110_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___redArg(lean_object* v_t_3115_){
_start:
{
lean_object* v___f_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___f_3116_ = ((lean_object*)(l_Std_ExtDTreeMap_values___redArg___closed__0));
v___x_3117_ = lean_box(0);
v___x_3118_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3119_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3118_, v___f_3116_, v___x_3117_, v_t_3115_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values(lean_object* v_00_u03b1_3120_, lean_object* v_cmp_3121_, lean_object* v_inst_3122_, lean_object* v_00_u03b2_3123_, lean_object* v_t_3124_){
_start:
{
lean_object* v___f_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___f_3125_ = ((lean_object*)(l_Std_ExtDTreeMap_values___redArg___closed__0));
v___x_3126_ = lean_box(0);
v___x_3127_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3128_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3127_, v___f_3125_, v___x_3126_, v_t_3124_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_values___boxed(lean_object* v_00_u03b1_3129_, lean_object* v_cmp_3130_, lean_object* v_inst_3131_, lean_object* v_00_u03b2_3132_, lean_object* v_t_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Std_ExtDTreeMap_values(v_00_u03b1_3129_, v_cmp_3130_, v_inst_3131_, v_00_u03b2_3132_, v_t_3133_);
lean_dec_ref(v_cmp_3130_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_3135_, lean_object* v_x_3136_, lean_object* v_v_3137_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = lean_array_push(v_l_3135_, v_v_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_3139_, lean_object* v_x_3140_, lean_object* v_v_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(v_l_3139_, v_x_3140_, v_v_3141_);
lean_dec(v_x_3140_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___redArg(lean_object* v_t_3144_){
_start:
{
lean_object* v___f_3145_; lean_object* v___y_3147_; 
v___f_3145_ = ((lean_object*)(l_Std_ExtDTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_3144_) == 0)
{
lean_object* v_size_3150_; 
v_size_3150_ = lean_ctor_get(v_t_3144_, 0);
lean_inc(v_size_3150_);
v___y_3147_ = v_size_3150_;
goto v___jp_3146_;
}
else
{
lean_object* v___x_3151_; 
v___x_3151_ = lean_unsigned_to_nat(0u);
v___y_3147_ = v___x_3151_;
goto v___jp_3146_;
}
v___jp_3146_:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = lean_mk_empty_array_with_capacity(v___y_3147_);
lean_dec(v___y_3147_);
v___x_3149_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3145_, v___x_3148_, v_t_3144_);
return v___x_3149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray(lean_object* v_00_u03b1_3152_, lean_object* v_cmp_3153_, lean_object* v_inst_3154_, lean_object* v_00_u03b2_3155_, lean_object* v_t_3156_){
_start:
{
lean_object* v___f_3157_; lean_object* v___y_3159_; 
v___f_3157_ = ((lean_object*)(l_Std_ExtDTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_3156_) == 0)
{
lean_object* v_size_3162_; 
v_size_3162_ = lean_ctor_get(v_t_3156_, 0);
lean_inc(v_size_3162_);
v___y_3159_ = v_size_3162_;
goto v___jp_3158_;
}
else
{
lean_object* v___x_3163_; 
v___x_3163_ = lean_unsigned_to_nat(0u);
v___y_3159_ = v___x_3163_;
goto v___jp_3158_;
}
v___jp_3158_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = lean_mk_empty_array_with_capacity(v___y_3159_);
lean_dec(v___y_3159_);
v___x_3161_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3157_, v___x_3160_, v_t_3156_);
return v___x_3161_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_3164_, lean_object* v_cmp_3165_, lean_object* v_inst_3166_, lean_object* v_00_u03b2_3167_, lean_object* v_t_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Std_ExtDTreeMap_valuesArray(v_00_u03b1_3164_, v_cmp_3165_, v_inst_3166_, v_00_u03b2_3167_, v_t_3168_);
lean_dec_ref(v_cmp_3165_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___redArg___lam__0(lean_object* v_x1_3170_, lean_object* v_x2_3171_, lean_object* v_x3_3172_){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3173_, 0, v_x1_3170_);
lean_ctor_set(v___x_3173_, 1, v_x2_3171_);
v___x_3174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v_x3_3172_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___redArg(lean_object* v_t_3176_){
_start:
{
lean_object* v___f_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___f_3177_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3178_ = lean_box(0);
v___x_3179_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3180_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3179_, v___f_3177_, v___x_3178_, v_t_3176_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList(lean_object* v_00_u03b1_3181_, lean_object* v_00_u03b2_3182_, lean_object* v_cmp_3183_, lean_object* v_inst_3184_, lean_object* v_t_3185_){
_start:
{
lean_object* v___f_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___f_3186_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3187_ = lean_box(0);
v___x_3188_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3189_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3188_, v___f_3186_, v___x_3187_, v_t_3185_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toList___boxed(lean_object* v_00_u03b1_3190_, lean_object* v_00_u03b2_3191_, lean_object* v_cmp_3192_, lean_object* v_inst_3193_, lean_object* v_t_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Std_ExtDTreeMap_toList(v_00_u03b1_3190_, v_00_u03b2_3191_, v_cmp_3192_, v_inst_3193_, v_t_3194_);
lean_dec_ref(v_cmp_3192_);
return v_res_3195_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_3197_, lean_object* v_a_3198_, lean_object* v_x_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_fst_3201_; lean_object* v_snd_3202_; lean_object* v_r_3203_; lean_object* v___x_3204_; 
v_fst_3201_ = lean_ctor_get(v_a_3198_, 0);
lean_inc(v_fst_3201_);
v_snd_3202_ = lean_ctor_get(v_a_3198_, 1);
lean_inc(v_snd_3202_);
lean_dec_ref(v_a_3198_);
v_r_3203_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3197_, v_fst_3201_, v_snd_3202_, v___y_3200_);
v___x_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3204_, 0, v_r_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg(lean_object* v_l_3205_, lean_object* v_cmp_3206_){
_start:
{
lean_object* v___f_3207_; lean_object* v___x_3208_; lean_object* v_r_3209_; lean_object* v___x_3210_; 
v___f_3207_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3207_, 0, v_cmp_3206_);
v___x_3208_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3209_ = lean_box(1);
v___x_3210_ = l_List_forIn_x27_loop___redArg(v___x_3208_, v___f_3207_, v_l_3205_, v_r_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___redArg___boxed(lean_object* v_l_3211_, lean_object* v_cmp_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Std_ExtDTreeMap_ofList___redArg(v_l_3211_, v_cmp_3212_);
lean_dec(v_l_3211_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList(lean_object* v_00_u03b1_3214_, lean_object* v_00_u03b2_3215_, lean_object* v_l_3216_, lean_object* v_cmp_3217_){
_start:
{
lean_object* v___f_3218_; lean_object* v___x_3219_; lean_object* v_r_3220_; lean_object* v___x_3221_; 
v___f_3218_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3218_, 0, v_cmp_3217_);
v___x_3219_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3220_ = lean_box(1);
v___x_3221_ = l_List_forIn_x27_loop___redArg(v___x_3219_, v___f_3218_, v_l_3216_, v_r_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofList___boxed(lean_object* v_00_u03b1_3222_, lean_object* v_00_u03b2_3223_, lean_object* v_l_3224_, lean_object* v_cmp_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Std_ExtDTreeMap_ofList(v_00_u03b1_3222_, v_00_u03b2_3223_, v_l_3224_, v_cmp_3225_);
lean_dec(v_l_3224_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___redArg___lam__0(lean_object* v_l_3227_, lean_object* v_k_3228_, lean_object* v_v_3229_){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_k_3228_);
lean_ctor_set(v___x_3230_, 1, v_v_3229_);
v___x_3231_ = lean_array_push(v_l_3227_, v___x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___redArg(lean_object* v_t_3233_){
_start:
{
lean_object* v___f_3234_; lean_object* v___y_3236_; 
v___f_3234_ = ((lean_object*)(l_Std_ExtDTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3233_) == 0)
{
lean_object* v_size_3239_; 
v_size_3239_ = lean_ctor_get(v_t_3233_, 0);
lean_inc(v_size_3239_);
v___y_3236_ = v_size_3239_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3240_; 
v___x_3240_ = lean_unsigned_to_nat(0u);
v___y_3236_ = v___x_3240_;
goto v___jp_3235_;
}
v___jp_3235_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = lean_mk_empty_array_with_capacity(v___y_3236_);
lean_dec(v___y_3236_);
v___x_3238_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3234_, v___x_3237_, v_t_3233_);
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray(lean_object* v_00_u03b1_3241_, lean_object* v_00_u03b2_3242_, lean_object* v_cmp_3243_, lean_object* v_inst_3244_, lean_object* v_t_3245_){
_start:
{
lean_object* v___f_3246_; lean_object* v___y_3248_; 
v___f_3246_ = ((lean_object*)(l_Std_ExtDTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3245_) == 0)
{
lean_object* v_size_3251_; 
v_size_3251_ = lean_ctor_get(v_t_3245_, 0);
lean_inc(v_size_3251_);
v___y_3248_ = v_size_3251_;
goto v___jp_3247_;
}
else
{
lean_object* v___x_3252_; 
v___x_3252_ = lean_unsigned_to_nat(0u);
v___y_3248_ = v___x_3252_;
goto v___jp_3247_;
}
v___jp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = lean_mk_empty_array_with_capacity(v___y_3248_);
lean_dec(v___y_3248_);
v___x_3250_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3246_, v___x_3249_, v_t_3245_);
return v___x_3250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_toArray___boxed(lean_object* v_00_u03b1_3253_, lean_object* v_00_u03b2_3254_, lean_object* v_cmp_3255_, lean_object* v_inst_3256_, lean_object* v_t_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Std_ExtDTreeMap_toArray(v_00_u03b1_3253_, v_00_u03b2_3254_, v_cmp_3255_, v_inst_3256_, v_t_3257_);
lean_dec_ref(v_cmp_3255_);
return v_res_3258_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray___redArg(lean_object* v_a_3260_, lean_object* v_cmp_3261_){
_start:
{
lean_object* v___f_3262_; lean_object* v___x_3263_; lean_object* v_r_3264_; size_t v_sz_3265_; size_t v___x_3266_; lean_object* v___x_3267_; 
v___f_3262_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3262_, 0, v_cmp_3261_);
v___x_3263_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3264_ = lean_box(1);
v_sz_3265_ = lean_array_size(v_a_3260_);
v___x_3266_ = ((size_t)0ULL);
v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3263_, v_a_3260_, v___f_3262_, v_sz_3265_, v___x_3266_, v_r_3264_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_ofArray(lean_object* v_00_u03b1_3268_, lean_object* v_00_u03b2_3269_, lean_object* v_a_3270_, lean_object* v_cmp_3271_){
_start:
{
lean_object* v___f_3272_; lean_object* v___x_3273_; lean_object* v_r_3274_; size_t v_sz_3275_; size_t v___x_3276_; lean_object* v___x_3277_; 
v___f_3272_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3272_, 0, v_cmp_3271_);
v___x_3273_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3274_ = lean_box(1);
v_sz_3275_ = lean_array_size(v_a_3270_);
v___x_3276_ = ((size_t)0ULL);
v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3273_, v_a_3270_, v___f_3272_, v_sz_3275_, v___x_3276_, v_r_3274_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_modify___redArg(lean_object* v_cmp_3278_, lean_object* v_t_3279_, lean_object* v_a_3280_, lean_object* v_f_3281_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3278_, v_a_3280_, v_f_3281_, v_t_3279_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_modify(lean_object* v_00_u03b1_3283_, lean_object* v_00_u03b2_3284_, lean_object* v_cmp_3285_, lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_t_3288_, lean_object* v_a_3289_, lean_object* v_f_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3285_, v_a_3289_, v_f_3290_, v_t_3288_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_alter___redArg(lean_object* v_cmp_3292_, lean_object* v_t_3293_, lean_object* v_a_3294_, lean_object* v_f_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3292_, v_a_3294_, v_f_3295_, v_t_3293_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_alter(lean_object* v_00_u03b1_3297_, lean_object* v_00_u03b2_3298_, lean_object* v_cmp_3299_, lean_object* v_inst_3300_, lean_object* v_inst_3301_, lean_object* v_t_3302_, lean_object* v_a_3303_, lean_object* v_f_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3299_, v_a_3303_, v_f_3304_, v_t_3302_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_3306_, lean_object* v_mergeFn_3307_, lean_object* v_a_3308_, lean_object* v_x_3309_){
_start:
{
if (lean_obj_tag(v_x_3309_) == 0)
{
lean_object* v___x_3310_; 
lean_dec(v_a_3308_);
lean_dec(v_mergeFn_3307_);
v___x_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3310_, 0, v_b_u2082_3306_);
return v___x_3310_;
}
else
{
lean_object* v_val_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3319_; 
v_val_3311_ = lean_ctor_get(v_x_3309_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v_x_3309_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3313_ = v_x_3309_;
v_isShared_3314_ = v_isSharedCheck_3319_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_val_3311_);
lean_dec(v_x_3309_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3319_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
v___x_3315_ = lean_apply_3(v_mergeFn_3307_, v_a_3308_, v_val_3311_, v_b_u2082_3306_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v___x_3315_);
v___x_3317_ = v___x_3313_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3320_, lean_object* v_cmp_3321_, lean_object* v_t_3322_, lean_object* v_a_3323_, lean_object* v_b_u2082_3324_){
_start:
{
lean_object* v___f_3325_; lean_object* v___x_3326_; 
lean_inc(v_a_3323_);
v___f_3325_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3325_, 0, v_b_u2082_3324_);
lean_closure_set(v___f_3325_, 1, v_mergeFn_3320_);
lean_closure_set(v___f_3325_, 2, v_a_3323_);
v___x_3326_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3321_, v_a_3323_, v___f_3325_, v_t_3322_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith___redArg(lean_object* v_cmp_3327_, lean_object* v_mergeFn_3328_, lean_object* v_t_u2081_3329_, lean_object* v_t_u2082_3330_){
_start:
{
lean_object* v___f_3331_; lean_object* v___x_3332_; 
v___f_3331_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3331_, 0, v_mergeFn_3328_);
lean_closure_set(v___f_3331_, 1, v_cmp_3327_);
v___x_3332_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3331_, v_t_u2081_3329_, v_t_u2082_3330_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_mergeWith(lean_object* v_00_u03b1_3333_, lean_object* v_00_u03b2_3334_, lean_object* v_cmp_3335_, lean_object* v_inst_3336_, lean_object* v_inst_3337_, lean_object* v_mergeFn_3338_, lean_object* v_t_u2081_3339_, lean_object* v_t_u2082_3340_){
_start:
{
lean_object* v___f_3341_; lean_object* v___x_3342_; 
v___f_3341_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3341_, 0, v_mergeFn_3338_);
lean_closure_set(v___f_3341_, 1, v_cmp_3335_);
v___x_3342_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3341_, v_t_u2081_3339_, v_t_u2082_3340_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___redArg___lam__0(lean_object* v_x1_3343_, lean_object* v_x2_3344_, lean_object* v_x3_3345_){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3346_, 0, v_x1_3343_);
lean_ctor_set(v___x_3346_, 1, v_x2_3344_);
v___x_3347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
lean_ctor_set(v___x_3347_, 1, v_x3_3345_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___redArg(lean_object* v_t_3349_){
_start:
{
lean_object* v___f_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___f_3350_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toList___redArg___closed__0));
v___x_3351_ = lean_box(0);
v___x_3352_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3353_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3352_, v___f_3350_, v___x_3351_, v_t_3349_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList(lean_object* v_00_u03b1_3354_, lean_object* v_cmp_3355_, lean_object* v_00_u03b2_3356_, lean_object* v_inst_3357_, lean_object* v_t_3358_){
_start:
{
lean_object* v___f_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___f_3359_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toList___redArg___closed__0));
v___x_3360_ = lean_box(0);
v___x_3361_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3362_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3361_, v___f_3359_, v___x_3360_, v_t_3358_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toList___boxed(lean_object* v_00_u03b1_3363_, lean_object* v_cmp_3364_, lean_object* v_00_u03b2_3365_, lean_object* v_inst_3366_, lean_object* v_t_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Std_ExtDTreeMap_Const_toList(v_00_u03b1_3363_, v_cmp_3364_, v_00_u03b2_3365_, v_inst_3366_, v_t_3367_);
lean_dec_ref(v_cmp_3364_);
return v_res_3368_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0(lean_object* v_cmp_3370_, lean_object* v_a_3371_, lean_object* v_x_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_fst_3374_; lean_object* v_snd_3375_; lean_object* v_r_3376_; lean_object* v___x_3377_; 
v_fst_3374_ = lean_ctor_get(v_a_3371_, 0);
lean_inc(v_fst_3374_);
v_snd_3375_ = lean_ctor_get(v_a_3371_, 1);
lean_inc(v_snd_3375_);
lean_dec_ref(v_a_3371_);
v_r_3376_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3370_, v_fst_3374_, v_snd_3375_, v___y_3373_);
v___x_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3377_, 0, v_r_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg(lean_object* v_l_3378_, lean_object* v_cmp_3379_){
_start:
{
lean_object* v___f_3380_; lean_object* v___x_3381_; lean_object* v_r_3382_; lean_object* v___x_3383_; 
v___f_3380_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3380_, 0, v_cmp_3379_);
v___x_3381_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3382_ = lean_box(1);
v___x_3383_ = l_List_forIn_x27_loop___redArg(v___x_3381_, v___f_3380_, v_l_3378_, v_r_3382_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___redArg___boxed(lean_object* v_l_3384_, lean_object* v_cmp_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Std_ExtDTreeMap_Const_ofList___redArg(v_l_3384_, v_cmp_3385_);
lean_dec(v_l_3384_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList(lean_object* v_00_u03b1_3387_, lean_object* v_00_u03b2_3388_, lean_object* v_l_3389_, lean_object* v_cmp_3390_){
_start:
{
lean_object* v___f_3391_; lean_object* v___x_3392_; lean_object* v_r_3393_; lean_object* v___x_3394_; 
v___f_3391_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3391_, 0, v_cmp_3390_);
v___x_3392_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3393_ = lean_box(1);
v___x_3394_ = l_List_forIn_x27_loop___redArg(v___x_3392_, v___f_3391_, v_l_3389_, v_r_3393_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofList___boxed(lean_object* v_00_u03b1_3395_, lean_object* v_00_u03b2_3396_, lean_object* v_l_3397_, lean_object* v_cmp_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Std_ExtDTreeMap_Const_ofList(v_00_u03b1_3395_, v_00_u03b2_3396_, v_l_3397_, v_cmp_3398_);
lean_dec(v_l_3397_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg___lam__0(lean_object* v_acc_3400_, lean_object* v_k_3401_, lean_object* v_v_3402_){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3403_, 0, v_k_3401_);
lean_ctor_set(v___x_3403_, 1, v_v_3402_);
v___x_3404_ = lean_array_push(v_acc_3400_, v___x_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___redArg(lean_object* v_t_3408_){
_start:
{
lean_object* v___f_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___f_3409_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0));
v___x_3410_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1));
v___x_3411_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3409_, v___x_3410_, v_t_3408_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray(lean_object* v_00_u03b1_3412_, lean_object* v_cmp_3413_, lean_object* v_00_u03b2_3414_, lean_object* v_inst_3415_, lean_object* v_t_3416_){
_start:
{
lean_object* v___f_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___f_3417_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0));
v___x_3418_ = ((lean_object*)(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1));
v___x_3419_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3417_, v___x_3418_, v_t_3416_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_toArray___boxed(lean_object* v_00_u03b1_3420_, lean_object* v_cmp_3421_, lean_object* v_00_u03b2_3422_, lean_object* v_inst_3423_, lean_object* v_t_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Std_ExtDTreeMap_Const_toArray(v_00_u03b1_3420_, v_cmp_3421_, v_00_u03b2_3422_, v_inst_3423_, v_t_3424_);
lean_dec_ref(v_cmp_3421_);
return v_res_3425_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray___redArg(lean_object* v_a_3427_, lean_object* v_cmp_3428_){
_start:
{
lean_object* v___f_3429_; lean_object* v___x_3430_; lean_object* v_r_3431_; size_t v_sz_3432_; size_t v___x_3433_; lean_object* v___x_3434_; 
v___f_3429_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3429_, 0, v_cmp_3428_);
v___x_3430_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3431_ = lean_box(1);
v_sz_3432_ = lean_array_size(v_a_3427_);
v___x_3433_ = ((size_t)0ULL);
v___x_3434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3430_, v_a_3427_, v___f_3429_, v_sz_3432_, v___x_3433_, v_r_3431_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_ofArray(lean_object* v_00_u03b1_3435_, lean_object* v_00_u03b2_3436_, lean_object* v_a_3437_, lean_object* v_cmp_3438_){
_start:
{
lean_object* v___f_3439_; lean_object* v___x_3440_; lean_object* v_r_3441_; size_t v_sz_3442_; size_t v___x_3443_; lean_object* v___x_3444_; 
v___f_3439_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3439_, 0, v_cmp_3438_);
v___x_3440_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3441_ = lean_box(1);
v_sz_3442_ = lean_array_size(v_a_3437_);
v___x_3443_ = ((size_t)0ULL);
v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3440_, v_a_3437_, v___f_3439_, v_sz_3442_, v___x_3443_, v_r_3441_);
return v___x_3444_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_3446_, lean_object* v_a_3447_, lean_object* v_x_3448_, lean_object* v___y_3449_){
_start:
{
uint8_t v___x_3450_; 
lean_inc(v___y_3449_);
lean_inc(v_a_3447_);
lean_inc_ref(v_cmp_3446_);
v___x_3450_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3446_, v_a_3447_, v___y_3449_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = lean_box(0);
v___x_3452_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3446_, v_a_3447_, v___x_3451_, v___y_3449_);
v___x_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
else
{
lean_object* v___x_3454_; 
lean_dec(v_a_3447_);
lean_dec_ref(v_cmp_3446_);
v___x_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3454_, 0, v___y_3449_);
return v___x_3454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg(lean_object* v_l_3455_, lean_object* v_cmp_3456_){
_start:
{
lean_object* v___f_3457_; lean_object* v___x_3458_; lean_object* v_r_3459_; lean_object* v___x_3460_; 
v___f_3457_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3457_, 0, v_cmp_3456_);
v___x_3458_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3459_ = lean_box(1);
v___x_3460_ = l_List_forIn_x27_loop___redArg(v___x_3458_, v___f_3457_, v_l_3455_, v_r_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___redArg___boxed(lean_object* v_l_3461_, lean_object* v_cmp_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Std_ExtDTreeMap_Const_unitOfList___redArg(v_l_3461_, v_cmp_3462_);
lean_dec(v_l_3461_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList(lean_object* v_00_u03b1_3464_, lean_object* v_l_3465_, lean_object* v_cmp_3466_){
_start:
{
lean_object* v___f_3467_; lean_object* v___x_3468_; lean_object* v_r_3469_; lean_object* v___x_3470_; 
v___f_3467_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3467_, 0, v_cmp_3466_);
v___x_3468_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3469_ = lean_box(1);
v___x_3470_ = l_List_forIn_x27_loop___redArg(v___x_3468_, v___f_3467_, v_l_3465_, v_r_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfList___boxed(lean_object* v_00_u03b1_3471_, lean_object* v_l_3472_, lean_object* v_cmp_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Std_ExtDTreeMap_Const_unitOfList(v_00_u03b1_3471_, v_l_3472_, v_cmp_3473_);
lean_dec(v_l_3472_);
return v_res_3474_;
}
}
static lean_object* _init_l_Std_ExtDTreeMap_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = lean_obj_once(&l_Std_ExtDTreeMap___auto__1___closed__26, &l_Std_ExtDTreeMap___auto__1___closed__26_once, _init_l_Std_ExtDTreeMap___auto__1___closed__26);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray___redArg(lean_object* v_a_3476_, lean_object* v_cmp_3477_){
_start:
{
lean_object* v___f_3478_; lean_object* v___x_3479_; lean_object* v_r_3480_; size_t v_sz_3481_; size_t v___x_3482_; lean_object* v___x_3483_; 
v___f_3478_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3478_, 0, v_cmp_3477_);
v___x_3479_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3480_ = lean_box(1);
v_sz_3481_ = lean_array_size(v_a_3476_);
v___x_3482_ = ((size_t)0ULL);
v___x_3483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3479_, v_a_3476_, v___f_3478_, v_sz_3481_, v___x_3482_, v_r_3480_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_unitOfArray(lean_object* v_00_u03b1_3484_, lean_object* v_a_3485_, lean_object* v_cmp_3486_){
_start:
{
lean_object* v___f_3487_; lean_object* v___x_3488_; lean_object* v_r_3489_; size_t v_sz_3490_; size_t v___x_3491_; lean_object* v___x_3492_; 
v___f_3487_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3487_, 0, v_cmp_3486_);
v___x_3488_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v_r_3489_ = lean_box(1);
v_sz_3490_ = lean_array_size(v_a_3485_);
v___x_3491_ = ((size_t)0ULL);
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3488_, v_a_3485_, v___f_3487_, v_sz_3490_, v___x_3491_, v_r_3489_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_modify___redArg(lean_object* v_cmp_3493_, lean_object* v_t_3494_, lean_object* v_a_3495_, lean_object* v_f_3496_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3493_, v_a_3495_, v_f_3496_, v_t_3494_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_modify(lean_object* v_00_u03b1_3498_, lean_object* v_cmp_3499_, lean_object* v_00_u03b2_3500_, lean_object* v_inst_3501_, lean_object* v_t_3502_, lean_object* v_a_3503_, lean_object* v_f_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3499_, v_a_3503_, v_f_3504_, v_t_3502_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_alter___redArg(lean_object* v_cmp_3506_, lean_object* v_t_3507_, lean_object* v_a_3508_, lean_object* v_f_3509_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3506_, v_a_3508_, v_f_3509_, v_t_3507_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_alter(lean_object* v_00_u03b1_3511_, lean_object* v_cmp_3512_, lean_object* v_00_u03b2_3513_, lean_object* v_inst_3514_, lean_object* v_t_3515_, lean_object* v_a_3516_, lean_object* v_f_3517_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3512_, v_a_3516_, v_f_3517_, v_t_3515_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3519_, lean_object* v_cmp_3520_, lean_object* v_t_3521_, lean_object* v_a_3522_, lean_object* v_b_u2082_3523_){
_start:
{
lean_object* v___f_3524_; lean_object* v___x_3525_; 
lean_inc(v_a_3522_);
v___f_3524_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3524_, 0, v_b_u2082_3523_);
lean_closure_set(v___f_3524_, 1, v_mergeFn_3519_);
lean_closure_set(v___f_3524_, 2, v_a_3522_);
v___x_3525_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3520_, v_a_3522_, v___f_3524_, v_t_3521_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith___redArg(lean_object* v_cmp_3526_, lean_object* v_mergeFn_3527_, lean_object* v_t_u2081_3528_, lean_object* v_t_u2082_3529_){
_start:
{
lean_object* v___f_3530_; lean_object* v___x_3531_; 
v___f_3530_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3530_, 0, v_mergeFn_3527_);
lean_closure_set(v___f_3530_, 1, v_cmp_3526_);
v___x_3531_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3530_, v_t_u2081_3528_, v_t_u2082_3529_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_mergeWith(lean_object* v_00_u03b1_3532_, lean_object* v_cmp_3533_, lean_object* v_00_u03b2_3534_, lean_object* v_inst_3535_, lean_object* v_mergeFn_3536_, lean_object* v_t_u2081_3537_, lean_object* v_t_u2082_3538_){
_start:
{
lean_object* v___f_3539_; lean_object* v___x_3540_; 
v___f_3539_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3539_, 0, v_mergeFn_3536_);
lean_closure_set(v___f_3539_, 1, v_cmp_3533_);
v___x_3540_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3539_, v_t_u2081_3537_, v_t_u2082_3538_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_3541_, lean_object* v_x_3542_, lean_object* v_____s_3543_){
_start:
{
lean_object* v_fst_3544_; lean_object* v_snd_3545_; lean_object* v_acc_3546_; lean_object* v___x_3547_; 
v_fst_3544_ = lean_ctor_get(v_x_3542_, 0);
lean_inc(v_fst_3544_);
v_snd_3545_ = lean_ctor_get(v_x_3542_, 1);
lean_inc(v_snd_3545_);
lean_dec_ref(v_x_3542_);
v_acc_3546_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3541_, v_fst_3544_, v_snd_3545_, v_____s_3543_);
v___x_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3547_, 0, v_acc_3546_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany___redArg(lean_object* v_cmp_3548_, lean_object* v_inst_3549_, lean_object* v_t_3550_, lean_object* v_l_3551_){
_start:
{
lean_object* v___f_3552_; lean_object* v___x_3553_; 
v___f_3552_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3552_, 0, v_cmp_3548_);
v___x_3553_ = lean_apply_4(v_inst_3549_, lean_box(0), v_l_3551_, v_t_3550_, v___f_3552_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_insertMany(lean_object* v_00_u03b1_3554_, lean_object* v_00_u03b2_3555_, lean_object* v_cmp_3556_, lean_object* v_inst_3557_, lean_object* v_00_u03c1_3558_, lean_object* v_inst_3559_, lean_object* v_t_3560_, lean_object* v_l_3561_){
_start:
{
lean_object* v___f_3562_; lean_object* v___x_3563_; 
v___f_3562_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3562_, 0, v_cmp_3556_);
v___x_3563_ = lean_apply_4(v_inst_3559_, lean_box(0), v_l_3561_, v_t_3560_, v___f_3562_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_3564_, lean_object* v_a_3565_, lean_object* v_____s_3566_){
_start:
{
lean_object* v_acc_3567_; lean_object* v___x_3568_; 
v_acc_3567_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_3564_, v_a_3565_, v_____s_3566_);
v___x_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3568_, 0, v_acc_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany___redArg(lean_object* v_cmp_3569_, lean_object* v_inst_3570_, lean_object* v_t_3571_, lean_object* v_l_3572_){
_start:
{
lean_object* v___f_3573_; lean_object* v___x_3574_; 
v___f_3573_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3573_, 0, v_cmp_3569_);
v___x_3574_ = lean_apply_4(v_inst_3570_, lean_box(0), v_l_3572_, v_t_3571_, v___f_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_eraseMany(lean_object* v_00_u03b1_3575_, lean_object* v_00_u03b2_3576_, lean_object* v_cmp_3577_, lean_object* v_inst_3578_, lean_object* v_00_u03c1_3579_, lean_object* v_inst_3580_, lean_object* v_t_3581_, lean_object* v_l_3582_){
_start:
{
lean_object* v___f_3583_; lean_object* v___x_3584_; 
v___f_3583_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3583_, 0, v_cmp_3577_);
v___x_3584_ = lean_apply_4(v_inst_3580_, lean_box(0), v_l_3582_, v_t_3581_, v___f_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0(lean_object* v_cmp_3585_, lean_object* v_x_3586_, lean_object* v_____s_3587_){
_start:
{
lean_object* v_fst_3588_; lean_object* v_snd_3589_; lean_object* v_acc_3590_; lean_object* v___x_3591_; 
v_fst_3588_ = lean_ctor_get(v_x_3586_, 0);
lean_inc(v_fst_3588_);
v_snd_3589_ = lean_ctor_get(v_x_3586_, 1);
lean_inc(v_snd_3589_);
lean_dec_ref(v_x_3586_);
v_acc_3590_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3585_, v_fst_3588_, v_snd_3589_, v_____s_3587_);
v___x_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3591_, 0, v_acc_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany___redArg(lean_object* v_cmp_3592_, lean_object* v_inst_3593_, lean_object* v_t_3594_, lean_object* v_l_3595_){
_start:
{
lean_object* v___f_3596_; lean_object* v___x_3597_; 
v___f_3596_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3596_, 0, v_cmp_3592_);
v___x_3597_ = lean_apply_4(v_inst_3593_, lean_box(0), v_l_3595_, v_t_3594_, v___f_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertMany(lean_object* v_00_u03b1_3598_, lean_object* v_cmp_3599_, lean_object* v_00_u03b2_3600_, lean_object* v_inst_3601_, lean_object* v_00_u03c1_3602_, lean_object* v_inst_3603_, lean_object* v_t_3604_, lean_object* v_l_3605_){
_start:
{
lean_object* v___f_3606_; lean_object* v___x_3607_; 
v___f_3606_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3606_, 0, v_cmp_3599_);
v___x_3607_ = lean_apply_4(v_inst_3603_, lean_box(0), v_l_3605_, v_t_3604_, v___f_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_3608_, lean_object* v_a_3609_, lean_object* v_____s_3610_){
_start:
{
uint8_t v___x_3611_; 
lean_inc(v_____s_3610_);
lean_inc(v_a_3609_);
lean_inc_ref(v_cmp_3608_);
v___x_3611_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3608_, v_a_3609_, v_____s_3610_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3612_ = lean_box(0);
v___x_3613_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3608_, v_a_3609_, v___x_3612_, v_____s_3610_);
v___x_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
return v___x_3614_;
}
else
{
lean_object* v___x_3615_; 
lean_dec(v_a_3609_);
lean_dec_ref(v_cmp_3608_);
v___x_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3615_, 0, v_____s_3610_);
return v___x_3615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_3616_, lean_object* v_inst_3617_, lean_object* v_t_3618_, lean_object* v_l_3619_){
_start:
{
lean_object* v___f_3620_; lean_object* v___x_3621_; 
v___f_3620_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3620_, 0, v_cmp_3616_);
v___x_3621_ = lean_apply_4(v_inst_3617_, lean_box(0), v_l_3619_, v_t_3618_, v___f_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_3622_, lean_object* v_cmp_3623_, lean_object* v_inst_3624_, lean_object* v_00_u03c1_3625_, lean_object* v_inst_3626_, lean_object* v_t_3627_, lean_object* v_l_3628_){
_start:
{
lean_object* v___f_3629_; lean_object* v___x_3630_; 
v___f_3629_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3629_, 0, v_cmp_3623_);
v___x_3630_ = lean_apply_4(v_inst_3626_, lean_box(0), v_l_3628_, v_t_3627_, v___f_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_union___redArg(lean_object* v_cmp_3631_, lean_object* v_m_u2081_3632_, lean_object* v_m_u2082_3633_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3631_, v_m_u2081_3632_, v_m_u2082_3633_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_union(lean_object* v_00_u03b1_3635_, lean_object* v_00_u03b2_3636_, lean_object* v_cmp_3637_, lean_object* v_inst_3638_, lean_object* v_m_u2081_3639_, lean_object* v_m_u2082_3640_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3637_, v_m_u2081_3639_, v_m_u2082_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instUnionOfTransCmp___redArg(lean_object* v_cmp_3642_){
_start:
{
lean_object* v___x_3643_; 
v___x_3643_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_union), 6, 4);
lean_closure_set(v___x_3643_, 0, lean_box(0));
lean_closure_set(v___x_3643_, 1, lean_box(0));
lean_closure_set(v___x_3643_, 2, v_cmp_3642_);
lean_closure_set(v___x_3643_, 3, lean_box(0));
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instUnionOfTransCmp(lean_object* v_00_u03b1_3644_, lean_object* v_00_u03b2_3645_, lean_object* v_cmp_3646_, lean_object* v_inst_3647_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_union), 6, 4);
lean_closure_set(v___x_3648_, 0, lean_box(0));
lean_closure_set(v___x_3648_, 1, lean_box(0));
lean_closure_set(v___x_3648_, 2, v_cmp_3646_);
lean_closure_set(v___x_3648_, 3, lean_box(0));
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_inter___redArg(lean_object* v_cmp_3649_, lean_object* v_m_u2081_3650_, lean_object* v_m_u2082_3651_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3649_, v_m_u2081_3650_, v_m_u2082_3651_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_inter(lean_object* v_00_u03b1_3653_, lean_object* v_00_u03b2_3654_, lean_object* v_cmp_3655_, lean_object* v_inst_3656_, lean_object* v_m_u2081_3657_, lean_object* v_m_u2082_3658_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3655_, v_m_u2081_3657_, v_m_u2082_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInterOfTransCmp___redArg(lean_object* v_cmp_3660_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_inter), 6, 4);
lean_closure_set(v___x_3661_, 0, lean_box(0));
lean_closure_set(v___x_3661_, 1, lean_box(0));
lean_closure_set(v___x_3661_, 2, v_cmp_3660_);
lean_closure_set(v___x_3661_, 3, lean_box(0));
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instInterOfTransCmp(lean_object* v_00_u03b1_3662_, lean_object* v_00_u03b2_3663_, lean_object* v_cmp_3664_, lean_object* v_inst_3665_){
_start:
{
lean_object* v___x_3666_; 
v___x_3666_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_inter), 6, 4);
lean_closure_set(v___x_3666_, 0, lean_box(0));
lean_closure_set(v___x_3666_, 1, lean_box(0));
lean_closure_set(v___x_3666_, 2, v_cmp_3664_);
lean_closure_set(v___x_3666_, 3, lean_box(0));
return v___x_3666_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(lean_object* v_cmp_3667_, lean_object* v_inst_3668_, lean_object* v_x_3669_, lean_object* v_y_3670_){
_start:
{
uint8_t v___x_3671_; 
v___x_3671_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3667_, v_inst_3668_, v_x_3669_, v_y_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_3672_, lean_object* v_inst_3673_, lean_object* v_x_3674_, lean_object* v_y_3675_){
_start:
{
uint8_t v_res_3676_; lean_object* v_r_3677_; 
v_res_3676_ = l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(v_cmp_3672_, v_inst_3673_, v_x_3674_, v_y_3675_);
v_r_3677_ = lean_box(v_res_3676_);
return v_r_3677_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(lean_object* v_cmp_3678_, lean_object* v_inst_3679_){
_start:
{
lean_object* v___f_3680_; lean_object* v___x_3681_; 
lean_inc_ref(v_cmp_3678_);
v___f_3680_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3680_, 0, v_cmp_3678_);
lean_closure_set(v___f_3680_, 1, v_inst_3679_);
v___x_3681_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_lift_u2082___boxed), 8, 6);
lean_closure_set(v___x_3681_, 0, lean_box(0));
lean_closure_set(v___x_3681_, 1, lean_box(0));
lean_closure_set(v___x_3681_, 2, v_cmp_3678_);
lean_closure_set(v___x_3681_, 3, lean_box(0));
lean_closure_set(v___x_3681_, 4, v___f_3680_);
lean_closure_set(v___x_3681_, 5, lean_box(0));
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp(lean_object* v_00_u03b1_3682_, lean_object* v_00_u03b2_3683_, lean_object* v_cmp_3684_, lean_object* v_inst_3685_, lean_object* v_inst_3686_, lean_object* v_inst_3687_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_3684_, v_inst_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object* v_cmp_3689_, lean_object* v_inst_3690_, lean_object* v_x_3691_, lean_object* v_x_3692_){
_start:
{
uint8_t v___x_3693_; 
v___x_3693_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3689_, v_inst_3690_, v_x_3691_, v_x_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_3694_, lean_object* v_inst_3695_, lean_object* v_x_3696_, lean_object* v_x_3697_){
_start:
{
uint8_t v_res_3698_; lean_object* v_r_3699_; 
v_res_3698_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(v_cmp_3694_, v_inst_3695_, v_x_3696_, v_x_3697_);
v_r_3699_ = lean_box(v_res_3698_);
return v_r_3699_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object* v_00_u03b1_3700_, lean_object* v_00_u03b2_3701_, lean_object* v_cmp_3702_, lean_object* v_inst_3703_, lean_object* v_inst_3704_, lean_object* v_inst_3705_, lean_object* v_inst_3706_, lean_object* v_x_3707_, lean_object* v_x_3708_){
_start:
{
uint8_t v___x_3709_; 
v___x_3709_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3702_, v_inst_3705_, v_x_3707_, v_x_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_3710_, lean_object* v_00_u03b2_3711_, lean_object* v_cmp_3712_, lean_object* v_inst_3713_, lean_object* v_inst_3714_, lean_object* v_inst_3715_, lean_object* v_inst_3716_, lean_object* v_x_3717_, lean_object* v_x_3718_){
_start:
{
uint8_t v_res_3719_; lean_object* v_r_3720_; 
v_res_3719_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(v_00_u03b1_3710_, v_00_u03b2_3711_, v_cmp_3712_, v_inst_3713_, v_inst_3714_, v_inst_3715_, v_inst_3716_, v_x_3717_, v_x_3718_);
v_r_3720_ = lean_box(v_res_3719_);
return v_r_3720_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_Const_beq___redArg(lean_object* v_cmp_3721_, lean_object* v_inst_3722_, lean_object* v_m_u2081_3723_, lean_object* v_m_u2082_3724_){
_start:
{
uint8_t v___x_3725_; 
v___x_3725_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3721_, v_inst_3722_, v_m_u2081_3723_, v_m_u2082_3724_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_beq___redArg___boxed(lean_object* v_cmp_3726_, lean_object* v_inst_3727_, lean_object* v_m_u2081_3728_, lean_object* v_m_u2082_3729_){
_start:
{
uint8_t v_res_3730_; lean_object* v_r_3731_; 
v_res_3730_ = l_Std_ExtDTreeMap_Const_beq___redArg(v_cmp_3726_, v_inst_3727_, v_m_u2081_3728_, v_m_u2082_3729_);
v_r_3731_ = lean_box(v_res_3730_);
return v_r_3731_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDTreeMap_Const_beq(lean_object* v_00_u03b1_3732_, lean_object* v_cmp_3733_, lean_object* v_00_u03b2_3734_, lean_object* v_inst_3735_, lean_object* v_inst_3736_, lean_object* v_m_u2081_3737_, lean_object* v_m_u2082_3738_){
_start:
{
uint8_t v___x_3739_; 
v___x_3739_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3733_, v_inst_3736_, v_m_u2081_3737_, v_m_u2082_3738_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_Const_beq___boxed(lean_object* v_00_u03b1_3740_, lean_object* v_cmp_3741_, lean_object* v_00_u03b2_3742_, lean_object* v_inst_3743_, lean_object* v_inst_3744_, lean_object* v_m_u2081_3745_, lean_object* v_m_u2082_3746_){
_start:
{
uint8_t v_res_3747_; lean_object* v_r_3748_; 
v_res_3747_ = l_Std_ExtDTreeMap_Const_beq(v_00_u03b1_3740_, v_cmp_3741_, v_00_u03b2_3742_, v_inst_3743_, v_inst_3744_, v_m_u2081_3745_, v_m_u2082_3746_);
v_r_3748_ = lean_box(v_res_3747_);
return v_r_3748_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_diff___redArg(lean_object* v_cmp_3749_, lean_object* v_m_u2081_3750_, lean_object* v_m_u2082_3751_){
_start:
{
lean_object* v___x_3752_; 
v___x_3752_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_3749_, v_m_u2081_3750_, v_m_u2082_3751_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_diff(lean_object* v_00_u03b1_3753_, lean_object* v_00_u03b2_3754_, lean_object* v_cmp_3755_, lean_object* v_inst_3756_, lean_object* v_m_u2081_3757_, lean_object* v_m_u2082_3758_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_3755_, v_m_u2081_3757_, v_m_u2082_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSDiffOfTransCmp___redArg(lean_object* v_cmp_3760_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_diff), 6, 4);
lean_closure_set(v___x_3761_, 0, lean_box(0));
lean_closure_set(v___x_3761_, 1, lean_box(0));
lean_closure_set(v___x_3761_, 2, v_cmp_3760_);
lean_closure_set(v___x_3761_, 3, lean_box(0));
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instSDiffOfTransCmp(lean_object* v_00_u03b1_3762_, lean_object* v_00_u03b2_3763_, lean_object* v_cmp_3764_, lean_object* v_inst_3765_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_diff), 6, 4);
lean_closure_set(v___x_3766_, 0, lean_box(0));
lean_closure_set(v___x_3766_, 1, lean_box(0));
lean_closure_set(v___x_3766_, 2, v_cmp_3764_);
lean_closure_set(v___x_3766_, 3, lean_box(0));
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_3770_, lean_object* v___x_3771_, lean_object* v_m_3772_, lean_object* v_prec_3773_){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3774_ = ((lean_object*)(l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_3775_ = lean_box(0);
v___x_3776_ = ((lean_object*)(l_Std_ExtDTreeMap_foldr___redArg___closed__9));
v___x_3777_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3776_, v___f_3770_, v___x_3775_, v_m_3772_);
v___x_3778_ = l_List_repr___redArg(v___x_3771_, v___x_3777_);
v___x_3779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3774_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = l_Repr_addAppParen(v___x_3779_, v_prec_3773_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_3781_, lean_object* v___x_3782_, lean_object* v_m_3783_, lean_object* v_prec_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(v___f_3781_, v___x_3782_, v_m_3783_, v_prec_3784_);
lean_dec(v_prec_3784_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(lean_object* v_inst_3786_, lean_object* v_inst_3787_){
_start:
{
lean_object* v___f_3788_; lean_object* v___x_3789_; lean_object* v___f_3790_; 
v___f_3788_ = ((lean_object*)(l_Std_ExtDTreeMap_toList___redArg___closed__0));
v___x_3789_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_3789_, 0, lean_box(0));
lean_closure_set(v___x_3789_, 1, lean_box(0));
lean_closure_set(v___x_3789_, 2, v_inst_3786_);
lean_closure_set(v___x_3789_, 3, v_inst_3787_);
v___f_3790_ = lean_alloc_closure((void*)(l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3790_, 0, v___f_3788_);
lean_closure_set(v___f_3790_, 1, v___x_3789_);
return v___f_3790_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp(lean_object* v_00_u03b1_3791_, lean_object* v_00_u03b2_3792_, lean_object* v_cmp_3793_, lean_object* v_inst_3794_, lean_object* v_inst_3795_, lean_object* v_inst_3796_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(v_inst_3795_, v_inst_3796_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDTreeMap_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_3798_, lean_object* v_00_u03b2_3799_, lean_object* v_cmp_3800_, lean_object* v_inst_3801_, lean_object* v_inst_3802_, lean_object* v_inst_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Std_ExtDTreeMap_instReprOfTransCmp(v_00_u03b1_3798_, v_00_u03b2_3799_, v_cmp_3800_, v_inst_3801_, v_inst_3802_, v_inst_3803_);
lean_dec_ref(v_cmp_3800_);
return v_res_3804_;
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
