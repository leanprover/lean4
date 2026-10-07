// Lean compiler output
// Module: Std.Data.DTreeMap.Basic
// Imports: public import Std.Data.DTreeMap.Internal.WF.Defs
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
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link2___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sigma_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_DTreeMap___auto__1___closed__0 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__0_value;
static const lean_string_object l_Std_DTreeMap___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_DTreeMap___auto__1___closed__1 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__1_value;
static const lean_string_object l_Std_DTreeMap___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_DTreeMap___auto__1___closed__2 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__2_value;
static const lean_string_object l_Std_DTreeMap___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_DTreeMap___auto__1___closed__3 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_DTreeMap___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_DTreeMap___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_DTreeMap___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_DTreeMap___auto__1___closed__4 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__4_value;
static const lean_array_object l_Std_DTreeMap___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DTreeMap___auto__1___closed__5 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__5_value;
static const lean_string_object l_Std_DTreeMap___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_DTreeMap___auto__1___closed__6 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_DTreeMap___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_DTreeMap___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_DTreeMap___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_DTreeMap___auto__1___closed__7 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__7_value;
static const lean_string_object l_Std_DTreeMap___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_DTreeMap___auto__1___closed__8 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_DTreeMap___auto__1___closed__9 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__9_value;
static const lean_string_object l_Std_DTreeMap___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_DTreeMap___auto__1___closed__10 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__10_value;
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_DTreeMap___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_DTreeMap___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_DTreeMap___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_DTreeMap___auto__1___closed__11 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__11_value;
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__12;
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__13;
static const lean_string_object l_Std_DTreeMap___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_DTreeMap___auto__1___closed__14 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__14_value;
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap___auto__1___closed__15 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__15_value;
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_DTreeMap___auto__1___closed__16 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__16_value;
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_DTreeMap___auto__1___closed__15_value),((lean_object*)&l_Std_DTreeMap___auto__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap___auto__1___closed__17 = (const lean_object*)&l_Std_DTreeMap___auto__1___closed__17_value;
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__18;
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__19;
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__20;
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__21;
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__22;
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__23;
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__24;
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__25;
LEAN_EXPORT lean_object* l_Std_DTreeMap___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__0 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_DTreeMap_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DTreeMap"};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__1 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_DTreeMap_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__2 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__2_value;
static const lean_ctor_object l_Std_DTreeMap_term___x7em___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DTreeMap_term___x7em___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__3_value_aux_0),((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 1, 106, 2, 110, 100, 218, 30)}};
static const lean_ctor_object l_Std_DTreeMap_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__3_value_aux_1),((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(44, 43, 1, 87, 104, 172, 157, 47)}};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__3 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__3_value;
static const lean_string_object l_Std_DTreeMap_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__4 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__4_value;
static const lean_ctor_object l_Std_DTreeMap_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__5 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__5_value;
static const lean_string_object l_Std_DTreeMap_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__6 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__6_value)}};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__7 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__7_value;
static const lean_string_object l_Std_DTreeMap_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__8 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__9 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_DTreeMap_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__9_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__10 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_DTreeMap_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__5_value),((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__7_value),((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__10_value)}};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__11 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_DTreeMap_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_DTreeMap_term___x7em___00__closed__12 = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__12_value;
LEAN_EXPORT const lean_object* l_Std_DTreeMap_term___x7em__ = (const lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__12_value;
static const lean_string_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__0 = (const lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__1 = (const lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__1_value;
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value_aux_0),((lean_object*)&l_Std_DTreeMap___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value_aux_1),((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value_aux_2),((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2 = (const lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3 = (const lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3_value;
static lean_once_cell_t l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4;
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__5 = (const lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__5_value;
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value_aux_0),((lean_object*)&l_Std_DTreeMap_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 1, 106, 2, 110, 100, 218, 30)}};
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value_aux_1),((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(109, 77, 17, 86, 91, 18, 195, 187)}};
static const lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6 = (const lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__7 = (const lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value)}};
static const lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__8 = (const lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__9 = (const lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__7_value),((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__9_value)}};
static const lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__10 = (const lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__10_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__0 = (const lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__1 = (const lean_object*)&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_getEntryGE_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_getEntryGE_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_getEntryGE_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_foldr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_foldr___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__0_value;
static const lean_closure_object l_Std_DTreeMap_foldr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_foldr___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__1_value;
static const lean_closure_object l_Std_DTreeMap_foldr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_foldr___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__2_value;
static const lean_closure_object l_Std_DTreeMap_foldr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_foldr___redArg___closed__3 = (const lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__3_value;
static const lean_closure_object l_Std_DTreeMap_foldr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_foldr___redArg___closed__4 = (const lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__4_value;
static const lean_closure_object l_Std_DTreeMap_foldr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_foldr___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__5_value;
static const lean_closure_object l_Std_DTreeMap_foldr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_foldr___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_foldr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__0_value),((lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__1_value)}};
static const lean_object* l_Std_DTreeMap_foldr___redArg___closed__7 = (const lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__7_value;
static const lean_ctor_object l_Std_DTreeMap_foldr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__7_value),((lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__2_value),((lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__3_value),((lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__4_value),((lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__5_value)}};
static const lean_object* l_Std_DTreeMap_foldr___redArg___closed__8 = (const lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_foldr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__8_value),((lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__6_value)}};
static const lean_object* l_Std_DTreeMap_foldr___redArg___closed__9 = (const lean_object*)&l_Std_DTreeMap_foldr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_partition___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_partition___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_partition___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_any___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_any___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_any___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_DTreeMap_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_keys___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_keys___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_keysArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_values___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_values___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_values(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_valuesArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_toList___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_toArray___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Const_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Const_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Const_toList___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Const_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Const_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Const_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Const_toArray___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Const_toArray___redArg___closed__0_value;
static const lean_array_object l_Std_DTreeMap_Const_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DTreeMap_Const_toArray___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Const_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instUnion___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instUnion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_inter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instBEqOfLawfulEqCmp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instBEqOfLawfulEqCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSDiff___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSDiff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_instRepr___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.DTreeMap.ofList "};
static const lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_instRepr___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_instRepr___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_DTreeMap_instRepr___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_instRepr___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__12, &l_Std_DTreeMap___auto__1___closed__12_once, _init_l_Std_DTreeMap___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__17));
v___x_45_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__13, &l_Std_DTreeMap___auto__1___closed__13_once, _init_l_Std_DTreeMap___auto__1___closed__13);
v___x_46_ = lean_array_push(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__18, &l_Std_DTreeMap___auto__1___closed__18_once, _init_l_Std_DTreeMap___auto__1___closed__18);
v___x_48_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__11));
v___x_49_ = lean_box(2);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__19, &l_Std_DTreeMap___auto__1___closed__19_once, _init_l_Std_DTreeMap___auto__1___closed__19);
v___x_52_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__5));
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__21(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__20, &l_Std_DTreeMap___auto__1___closed__20_once, _init_l_Std_DTreeMap___auto__1___closed__20);
v___x_55_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__9));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__22(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__21, &l_Std_DTreeMap___auto__1___closed__21_once, _init_l_Std_DTreeMap___auto__1___closed__21);
v___x_59_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__5));
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__23(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__22, &l_Std_DTreeMap___auto__1___closed__22_once, _init_l_Std_DTreeMap___auto__1___closed__22);
v___x_62_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__7));
v___x_63_ = lean_box(2);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__24(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__23, &l_Std_DTreeMap___auto__1___closed__23_once, _init_l_Std_DTreeMap___auto__1___closed__23);
v___x_66_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__25(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__24, &l_Std_DTreeMap___auto__1___closed__24_once, _init_l_Std_DTreeMap___auto__1___closed__24);
v___x_69_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__4));
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall___redArg___boxed(lean_object* v___dummy_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_DTreeMap_instCoeTypeForall___redArg();
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall(lean_object* v_00_u03b1_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(0);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty___redArg(){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(1);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty___redArg___boxed(lean_object* v___dummy_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_DTreeMap_empty___redArg();
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_cmp_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(1);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty___boxed(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_cmp_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_DTreeMap_empty(v_00_u03b1_87_, v_00_u03b2_88_, v_cmp_89_);
lean_dec_ref(v_cmp_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(1);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_DTreeMap_instEmptyCollection___redArg();
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_cmp_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_box(1);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_cmp_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_DTreeMap_instEmptyCollection(v_00_u03b1_99_, v_00_u03b2_100_, v_cmp_101_);
lean_dec_ref(v_cmp_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(1);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited___redArg___boxed(lean_object* v___dummy_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_DTreeMap_instInhabited___redArg();
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_cmp_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(1);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited___boxed(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_cmp_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_DTreeMap_instInhabited(v_00_u03b1_111_, v_00_u03b2_112_, v_cmp_113_);
lean_dec_ref(v_cmp_113_);
return v_res_114_;
}
}
static lean_object* _init_l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3));
v___x_153_ = l_String_toRawSubstring_x27(v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1(lean_object* v_x_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__3));
lean_inc(v_x_171_);
v___x_175_ = l_Lean_Syntax_isOfKind(v_x_171_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_x_171_);
v___x_176_ = lean_box(1);
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v_a_173_);
return v___x_177_;
}
else
{
lean_object* v_quotContext_178_; lean_object* v_currMacroScope_179_; lean_object* v_ref_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_quotContext_178_ = lean_ctor_get(v_a_172_, 1);
v_currMacroScope_179_ = lean_ctor_get(v_a_172_, 2);
v_ref_180_ = lean_ctor_get(v_a_172_, 5);
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = l_Lean_Syntax_getArg(v_x_171_, v___x_181_);
v___x_183_ = lean_unsigned_to_nat(2u);
v___x_184_ = l_Lean_Syntax_getArg(v_x_171_, v___x_183_);
lean_dec(v_x_171_);
v___x_185_ = 0;
v___x_186_ = l_Lean_SourceInfo_fromRef(v_ref_180_, v___x_185_);
v___x_187_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2));
v___x_188_ = lean_obj_once(&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4, &l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4_once, _init_l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4);
v___x_189_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_179_);
lean_inc(v_quotContext_178_);
v___x_190_ = l_Lean_addMacroScope(v_quotContext_178_, v___x_189_, v_currMacroScope_179_);
v___x_191_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__10));
lean_inc_n(v___x_186_, 2);
v___x_192_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_192_, 0, v___x_186_);
lean_ctor_set(v___x_192_, 1, v___x_188_);
lean_ctor_set(v___x_192_, 2, v___x_190_);
lean_ctor_set(v___x_192_, 3, v___x_191_);
v___x_193_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__9));
v___x_194_ = l_Lean_Syntax_node2(v___x_186_, v___x_193_, v___x_182_, v___x_184_);
v___x_195_ = l_Lean_Syntax_node2(v___x_186_, v___x_187_, v___x_192_, v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_173_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___boxed(lean_object* v_x_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1(v_x_197_, v_a_198_, v_a_199_);
lean_dec_ref(v_a_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(lean_object* v_x_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2));
lean_inc(v_x_204_);
v___x_208_ = l_Lean_Syntax_isOfKind(v_x_204_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v_x_204_);
v___x_209_ = lean_box(0);
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v_a_206_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = l_Lean_Syntax_getArg(v_x_204_, v___x_211_);
v___x_213_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__1));
lean_inc(v___x_212_);
v___x_214_ = l_Lean_Syntax_isOfKind(v___x_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec(v___x_212_);
lean_dec(v_x_204_);
v___x_215_ = lean_box(0);
v___x_216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v_a_206_);
return v___x_216_;
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = l_Lean_Syntax_getArg(v_x_204_, v___x_217_);
lean_dec(v_x_204_);
v___x_219_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_218_);
v___x_220_ = l_Lean_Syntax_matchesNull(v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v___x_218_);
lean_dec(v___x_212_);
v___x_221_ = lean_box(0);
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_a_206_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v_ref_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_223_ = l_Lean_Syntax_getArg(v___x_218_, v___x_211_);
v___x_224_ = l_Lean_Syntax_getArg(v___x_218_, v___x_217_);
lean_dec(v___x_218_);
v_ref_225_ = l_Lean_replaceRef(v___x_212_, v_a_205_);
lean_dec(v___x_212_);
v___x_226_ = 0;
v___x_227_ = l_Lean_SourceInfo_fromRef(v_ref_225_, v___x_226_);
lean_dec(v_ref_225_);
v___x_228_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__3));
v___x_229_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__6));
lean_inc(v___x_227_);
v___x_230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_227_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_Syntax_node3(v___x_227_, v___x_228_, v___x_223_, v___x_230_, v___x_224_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v_a_206_);
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___boxed(lean_object* v_x_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(v_x_233_, v_a_234_, v_a_235_);
lean_dec(v_a_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insert___redArg(lean_object* v_cmp_237_, lean_object* v_t_238_, lean_object* v_a_239_, lean_object* v_b_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_237_, v_a_239_, v_b_240_, v_t_238_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insert(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b2_243_, lean_object* v_cmp_244_, lean_object* v_t_245_, lean_object* v_a_246_, lean_object* v_b_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_244_, v_a_246_, v_b_247_, v_t_245_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma___redArg___lam__0(lean_object* v_cmp_249_, lean_object* v_e_250_){
_start:
{
lean_object* v_fst_251_; lean_object* v_snd_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_fst_251_ = lean_ctor_get(v_e_250_, 0);
lean_inc(v_fst_251_);
v_snd_252_ = lean_ctor_get(v_e_250_, 1);
lean_inc(v_snd_252_);
lean_dec_ref(v_e_250_);
v___x_253_ = lean_box(1);
v___x_254_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_249_, v_fst_251_, v_snd_252_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma___redArg(lean_object* v_cmp_255_){
_start:
{
lean_object* v___f_256_; 
v___f_256_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_256_, 0, v_cmp_255_);
return v___f_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma(lean_object* v_00_u03b1_257_, lean_object* v_00_u03b2_258_, lean_object* v_cmp_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_260_, 0, v_cmp_259_);
return v___f_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma___redArg___lam__0(lean_object* v_cmp_261_, lean_object* v_e_262_, lean_object* v_s_263_){
_start:
{
lean_object* v_fst_264_; lean_object* v_snd_265_; lean_object* v___x_266_; 
v_fst_264_ = lean_ctor_get(v_e_262_, 0);
lean_inc(v_fst_264_);
v_snd_265_ = lean_ctor_get(v_e_262_, 1);
lean_inc(v_snd_265_);
lean_dec_ref(v_e_262_);
v___x_266_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_261_, v_fst_264_, v_snd_265_, v_s_263_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma___redArg(lean_object* v_cmp_267_){
_start:
{
lean_object* v___f_268_; 
v___f_268_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_268_, 0, v_cmp_267_);
return v___f_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_cmp_271_){
_start:
{
lean_object* v___f_272_; 
v___f_272_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_272_, 0, v_cmp_271_);
return v___f_272_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertIfNew___redArg(lean_object* v_cmp_273_, lean_object* v_t_274_, lean_object* v_a_275_, lean_object* v_b_276_){
_start:
{
uint8_t v___x_277_; 
lean_inc(v_t_274_);
lean_inc(v_a_275_);
lean_inc_ref(v_cmp_273_);
v___x_277_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_273_, v_a_275_, v_t_274_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_273_, v_a_275_, v_b_276_, v_t_274_);
return v___x_278_;
}
else
{
lean_dec(v_b_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_cmp_273_);
return v_t_274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertIfNew(lean_object* v_00_u03b1_279_, lean_object* v_00_u03b2_280_, lean_object* v_cmp_281_, lean_object* v_t_282_, lean_object* v_a_283_, lean_object* v_b_284_){
_start:
{
uint8_t v___x_285_; 
lean_inc(v_t_282_);
lean_inc(v_a_283_);
lean_inc_ref(v_cmp_281_);
v___x_285_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_281_, v_a_283_, v_t_282_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
v___x_286_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_281_, v_a_283_, v_b_284_, v_t_282_);
return v___x_286_;
}
else
{
lean_dec(v_b_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_cmp_281_);
return v_t_282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsert___redArg(lean_object* v_cmp_287_, lean_object* v_t_288_, lean_object* v_a_289_, lean_object* v_b_290_){
_start:
{
lean_object* v_sz_291_; lean_object* v_m_292_; lean_object* v___y_294_; 
v_sz_291_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_288_);
v_m_292_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_287_, v_a_289_, v_b_290_, v_t_288_);
if (lean_obj_tag(v_m_292_) == 0)
{
lean_object* v_size_298_; 
v_size_298_ = lean_ctor_get(v_m_292_, 0);
lean_inc(v_size_298_);
v___y_294_ = v_size_298_;
goto v___jp_293_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___y_294_ = v___x_299_;
goto v___jp_293_;
}
v___jp_293_:
{
uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_nat_dec_eq(v_sz_291_, v___y_294_);
lean_dec(v___y_294_);
lean_dec(v_sz_291_);
v___x_296_ = lean_box(v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_m_292_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsert(lean_object* v_00_u03b1_300_, lean_object* v_00_u03b2_301_, lean_object* v_cmp_302_, lean_object* v_t_303_, lean_object* v_a_304_, lean_object* v_b_305_){
_start:
{
lean_object* v_sz_306_; lean_object* v_m_307_; lean_object* v___y_309_; 
v_sz_306_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_303_);
v_m_307_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_302_, v_a_304_, v_b_305_, v_t_303_);
if (lean_obj_tag(v_m_307_) == 0)
{
lean_object* v_size_313_; 
v_size_313_ = lean_ctor_get(v_m_307_, 0);
lean_inc(v_size_313_);
v___y_309_ = v_size_313_;
goto v___jp_308_;
}
else
{
lean_object* v___x_314_; 
v___x_314_ = lean_unsigned_to_nat(0u);
v___y_309_ = v___x_314_;
goto v___jp_308_;
}
v___jp_308_:
{
uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_nat_dec_eq(v_sz_306_, v___y_309_);
lean_dec(v___y_309_);
lean_dec(v_sz_306_);
v___x_311_ = lean_box(v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v_m_307_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_315_, lean_object* v_t_316_, lean_object* v_a_317_, lean_object* v_b_318_){
_start:
{
uint8_t v___x_319_; 
lean_inc(v_t_316_);
lean_inc(v_a_317_);
lean_inc_ref(v_cmp_315_);
v___x_319_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_315_, v_a_317_, v_t_316_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_315_, v_a_317_, v_b_318_, v_t_316_);
v___x_321_ = lean_box(v___x_319_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
return v___x_322_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v_b_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_cmp_315_);
v___x_323_ = lean_box(v___x_319_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v_t_316_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_325_, lean_object* v_00_u03b2_326_, lean_object* v_cmp_327_, lean_object* v_t_328_, lean_object* v_a_329_, lean_object* v_b_330_){
_start:
{
uint8_t v___x_331_; 
lean_inc(v_t_328_);
lean_inc(v_a_329_);
lean_inc_ref(v_cmp_327_);
v___x_331_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_327_, v_a_329_, v_t_328_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_327_, v_a_329_, v_b_330_, v_t_328_);
v___x_333_ = lean_box(v___x_331_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_332_);
return v___x_334_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_b_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_cmp_327_);
v___x_335_ = lean_box(v___x_331_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_t_328_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_337_, lean_object* v_t_338_, lean_object* v_a_339_, lean_object* v_b_340_){
_start:
{
lean_object* v___x_341_; 
lean_inc(v_a_339_);
lean_inc(v_t_338_);
lean_inc_ref(v_cmp_337_);
v___x_341_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_337_, v_t_338_, v_a_339_);
if (lean_obj_tag(v___x_341_) == 0)
{
uint8_t v___x_342_; 
lean_inc(v_t_338_);
lean_inc(v_a_339_);
lean_inc_ref(v_cmp_337_);
v___x_342_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_337_, v_a_339_, v_t_338_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_337_, v_a_339_, v_b_340_, v_t_338_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_341_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
return v___x_344_;
}
else
{
lean_object* v___x_345_; 
lean_dec(v_b_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_cmp_337_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_341_);
lean_ctor_set(v___x_345_, 1, v_t_338_);
return v___x_345_;
}
}
else
{
lean_object* v___x_346_; 
lean_dec(v_b_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_cmp_337_);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_341_);
lean_ctor_set(v___x_346_, 1, v_t_338_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_347_, lean_object* v_00_u03b2_348_, lean_object* v_cmp_349_, lean_object* v_inst_350_, lean_object* v_t_351_, lean_object* v_a_352_, lean_object* v_b_353_){
_start:
{
lean_object* v___x_354_; 
lean_inc(v_a_352_);
lean_inc(v_t_351_);
lean_inc_ref(v_cmp_349_);
v___x_354_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_349_, v_t_351_, v_a_352_);
if (lean_obj_tag(v___x_354_) == 0)
{
uint8_t v___x_355_; 
lean_inc(v_t_351_);
lean_inc(v_a_352_);
lean_inc_ref(v_cmp_349_);
v___x_355_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_349_, v_a_352_, v_t_351_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_349_, v_a_352_, v_b_353_, v_t_351_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_354_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; 
lean_dec(v_b_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_cmp_349_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_354_);
lean_ctor_set(v___x_358_, 1, v_t_351_);
return v___x_358_;
}
}
else
{
lean_object* v___x_359_; 
lean_dec(v_b_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_cmp_349_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_354_);
lean_ctor_set(v___x_359_, 1, v_t_351_);
return v___x_359_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_contains___redArg(lean_object* v_cmp_360_, lean_object* v_t_361_, lean_object* v_a_362_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_360_, v_a_362_, v_t_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_contains___redArg___boxed(lean_object* v_cmp_364_, lean_object* v_t_365_, lean_object* v_a_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Std_DTreeMap_contains___redArg(v_cmp_364_, v_t_365_, v_a_366_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_contains(lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_, lean_object* v_cmp_371_, lean_object* v_t_372_, lean_object* v_a_373_){
_start:
{
uint8_t v___x_374_; 
v___x_374_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_371_, v_a_373_, v_t_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_contains___boxed(lean_object* v_00_u03b1_375_, lean_object* v_00_u03b2_376_, lean_object* v_cmp_377_, lean_object* v_t_378_, lean_object* v_a_379_){
_start:
{
uint8_t v_res_380_; lean_object* v_r_381_; 
v_res_380_ = l_Std_DTreeMap_contains(v_00_u03b1_375_, v_00_u03b2_376_, v_cmp_377_, v_t_378_, v_a_379_);
v_r_381_ = lean_box(v_res_380_);
return v_r_381_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___redArg(){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_box(0);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___redArg___boxed(lean_object* v___dummy_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_DTreeMap_instMembership___redArg();
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership(lean_object* v_00_u03b1_386_, lean_object* v_00_u03b2_387_, lean_object* v_cmp_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_box(0);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___boxed(lean_object* v_00_u03b1_390_, lean_object* v_00_u03b2_391_, lean_object* v_cmp_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_DTreeMap_instMembership(v_00_u03b1_390_, v_00_u03b2_391_, v_cmp_392_);
lean_dec_ref(v_cmp_392_);
return v_res_393_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableMem___redArg(lean_object* v_cmp_394_, lean_object* v_m_395_, lean_object* v_a_396_){
_start:
{
uint8_t v___x_397_; 
v___x_397_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_394_, v_a_396_, v_m_395_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_398_, lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Std_DTreeMap_instDecidableMem___redArg(v_cmp_398_, v_m_399_, v_a_400_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableMem(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_cmp_405_, lean_object* v_m_406_, lean_object* v_a_407_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_405_, v_a_407_, v_m_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_409_, lean_object* v_00_u03b2_410_, lean_object* v_cmp_411_, lean_object* v_m_412_, lean_object* v_a_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Std_DTreeMap_instDecidableMem(v_00_u03b1_409_, v_00_u03b2_410_, v_cmp_411_, v_m_412_, v_a_413_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___redArg(lean_object* v_t_416_){
_start:
{
if (lean_obj_tag(v_t_416_) == 0)
{
lean_object* v_size_417_; 
v_size_417_ = lean_ctor_get(v_t_416_, 0);
lean_inc(v_size_417_);
return v_size_417_;
}
else
{
lean_object* v___x_418_; 
v___x_418_ = lean_unsigned_to_nat(0u);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___redArg___boxed(lean_object* v_t_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_DTreeMap_size___redArg(v_t_419_);
lean_dec(v_t_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size(lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_cmp_423_, lean_object* v_t_424_){
_start:
{
if (lean_obj_tag(v_t_424_) == 0)
{
lean_object* v_size_425_; 
v_size_425_ = lean_ctor_get(v_t_424_, 0);
lean_inc(v_size_425_);
return v_size_425_;
}
else
{
lean_object* v___x_426_; 
v___x_426_ = lean_unsigned_to_nat(0u);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___boxed(lean_object* v_00_u03b1_427_, lean_object* v_00_u03b2_428_, lean_object* v_cmp_429_, lean_object* v_t_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_DTreeMap_size(v_00_u03b1_427_, v_00_u03b2_428_, v_cmp_429_, v_t_430_);
lean_dec(v_t_430_);
lean_dec_ref(v_cmp_429_);
return v_res_431_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_isEmpty___redArg(lean_object* v_t_432_){
_start:
{
if (lean_obj_tag(v_t_432_) == 0)
{
uint8_t v___x_433_; 
v___x_433_ = 0;
return v___x_433_;
}
else
{
uint8_t v___x_434_; 
v___x_434_ = 1;
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isEmpty___redArg___boxed(lean_object* v_t_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_Std_DTreeMap_isEmpty___redArg(v_t_435_);
lean_dec(v_t_435_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_isEmpty(lean_object* v_00_u03b1_438_, lean_object* v_00_u03b2_439_, lean_object* v_cmp_440_, lean_object* v_t_441_){
_start:
{
if (lean_obj_tag(v_t_441_) == 0)
{
uint8_t v___x_442_; 
v___x_442_ = 0;
return v___x_442_;
}
else
{
uint8_t v___x_443_; 
v___x_443_ = 1;
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_444_, lean_object* v_00_u03b2_445_, lean_object* v_cmp_446_, lean_object* v_t_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l_Std_DTreeMap_isEmpty(v_00_u03b1_444_, v_00_u03b2_445_, v_cmp_446_, v_t_447_);
lean_dec(v_t_447_);
lean_dec_ref(v_cmp_446_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_erase___redArg(lean_object* v_cmp_450_, lean_object* v_t_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_450_, v_a_452_, v_t_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_erase(lean_object* v_00_u03b1_454_, lean_object* v_00_u03b2_455_, lean_object* v_cmp_456_, lean_object* v_t_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_456_, v_a_458_, v_t_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x3f___redArg(lean_object* v_cmp_460_, lean_object* v_t_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_460_, v_t_461_, v_a_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x3f(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_cmp_466_, lean_object* v_inst_467_, lean_object* v_t_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_466_, v_t_468_, v_a_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get___redArg(lean_object* v_cmp_471_, lean_object* v_t_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_471_, v_t_472_, v_a_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get(lean_object* v_00_u03b1_475_, lean_object* v_00_u03b2_476_, lean_object* v_cmp_477_, lean_object* v_inst_478_, lean_object* v_t_479_, lean_object* v_a_480_, lean_object* v_h_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_477_, v_t_479_, v_a_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___redArg(lean_object* v_cmp_483_, lean_object* v_t_484_, lean_object* v_a_485_, lean_object* v_inst_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_483_, v_t_484_, v_a_485_, v_inst_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___redArg___boxed(lean_object* v_cmp_488_, lean_object* v_t_489_, lean_object* v_a_490_, lean_object* v_inst_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_DTreeMap_get_x21___redArg(v_cmp_488_, v_t_489_, v_a_490_, v_inst_491_);
lean_dec(v_inst_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_cmp_495_, lean_object* v_inst_496_, lean_object* v_t_497_, lean_object* v_a_498_, lean_object* v_inst_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_495_, v_t_497_, v_a_498_, v_inst_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___boxed(lean_object* v_00_u03b1_501_, lean_object* v_00_u03b2_502_, lean_object* v_cmp_503_, lean_object* v_inst_504_, lean_object* v_t_505_, lean_object* v_a_506_, lean_object* v_inst_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_DTreeMap_get_x21(v_00_u03b1_501_, v_00_u03b2_502_, v_cmp_503_, v_inst_504_, v_t_505_, v_a_506_, v_inst_507_);
lean_dec(v_inst_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg(lean_object* v_cmp_509_, lean_object* v_t_510_, lean_object* v_a_511_, lean_object* v_fallback_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_509_, v_t_510_, v_a_511_, v_fallback_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg___boxed(lean_object* v_cmp_514_, lean_object* v_t_515_, lean_object* v_a_516_, lean_object* v_fallback_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_DTreeMap_getD___redArg(v_cmp_514_, v_t_515_, v_a_516_, v_fallback_517_);
lean_dec(v_fallback_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_cmp_521_, lean_object* v_inst_522_, lean_object* v_t_523_, lean_object* v_a_524_, lean_object* v_fallback_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_521_, v_t_523_, v_a_524_, v_fallback_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___boxed(lean_object* v_00_u03b1_527_, lean_object* v_00_u03b2_528_, lean_object* v_cmp_529_, lean_object* v_inst_530_, lean_object* v_t_531_, lean_object* v_a_532_, lean_object* v_fallback_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_DTreeMap_getD(v_00_u03b1_527_, v_00_u03b2_528_, v_cmp_529_, v_inst_530_, v_t_531_, v_a_532_, v_fallback_533_);
lean_dec(v_fallback_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f___redArg(lean_object* v_cmp_535_, lean_object* v_t_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_535_, v_t_536_, v_a_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f(lean_object* v_00_u03b1_539_, lean_object* v_00_u03b2_540_, lean_object* v_cmp_541_, lean_object* v_t_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_541_, v_t_542_, v_a_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey___redArg(lean_object* v_cmp_545_, lean_object* v_t_546_, lean_object* v_a_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_545_, v_t_546_, v_a_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey(lean_object* v_00_u03b1_549_, lean_object* v_00_u03b2_550_, lean_object* v_cmp_551_, lean_object* v_t_552_, lean_object* v_a_553_, lean_object* v_h_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_551_, v_t_552_, v_a_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___redArg(lean_object* v_cmp_556_, lean_object* v_inst_557_, lean_object* v_t_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_556_, v_t_558_, v_a_559_, v_inst_557_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___redArg___boxed(lean_object* v_cmp_561_, lean_object* v_inst_562_, lean_object* v_t_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Std_DTreeMap_getKey_x21___redArg(v_cmp_561_, v_inst_562_, v_t_563_, v_a_564_);
lean_dec(v_inst_562_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21(lean_object* v_00_u03b1_566_, lean_object* v_00_u03b2_567_, lean_object* v_cmp_568_, lean_object* v_inst_569_, lean_object* v_t_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_568_, v_t_570_, v_a_571_, v_inst_569_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___boxed(lean_object* v_00_u03b1_573_, lean_object* v_00_u03b2_574_, lean_object* v_cmp_575_, lean_object* v_inst_576_, lean_object* v_t_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_DTreeMap_getKey_x21(v_00_u03b1_573_, v_00_u03b2_574_, v_cmp_575_, v_inst_576_, v_t_577_, v_a_578_);
lean_dec(v_inst_576_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___redArg(lean_object* v_cmp_580_, lean_object* v_t_581_, lean_object* v_a_582_, lean_object* v_fallback_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_580_, v_t_581_, v_a_582_, v_fallback_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_585_, lean_object* v_t_586_, lean_object* v_a_587_, lean_object* v_fallback_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Std_DTreeMap_getKeyD___redArg(v_cmp_585_, v_t_586_, v_a_587_, v_fallback_588_);
lean_dec(v_fallback_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD(lean_object* v_00_u03b1_590_, lean_object* v_00_u03b2_591_, lean_object* v_cmp_592_, lean_object* v_t_593_, lean_object* v_a_594_, lean_object* v_fallback_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_592_, v_t_593_, v_a_594_, v_fallback_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_597_, lean_object* v_00_u03b2_598_, lean_object* v_cmp_599_, lean_object* v_t_600_, lean_object* v_a_601_, lean_object* v_fallback_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_DTreeMap_getKeyD(v_00_u03b1_597_, v_00_u03b2_598_, v_cmp_599_, v_t_600_, v_a_601_, v_fallback_602_);
lean_dec(v_fallback_602_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x3f___redArg(lean_object* v_cmp_604_, lean_object* v_t_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_604_, v_t_605_, v_a_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x3f(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_cmp_610_, lean_object* v_t_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_610_, v_t_611_, v_a_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry___redArg(lean_object* v_cmp_614_, lean_object* v_t_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_614_, v_t_615_, v_a_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry(lean_object* v_00_u03b1_618_, lean_object* v_00_u03b2_619_, lean_object* v_cmp_620_, lean_object* v_t_621_, lean_object* v_a_622_, lean_object* v_h_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_620_, v_t_621_, v_a_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___redArg(lean_object* v_cmp_625_, lean_object* v_t_626_, lean_object* v_a_627_, lean_object* v_fallback_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_625_, v_t_626_, v_a_627_, v_fallback_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___redArg___boxed(lean_object* v_cmp_630_, lean_object* v_t_631_, lean_object* v_a_632_, lean_object* v_fallback_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_DTreeMap_getEntryD___redArg(v_cmp_630_, v_t_631_, v_a_632_, v_fallback_633_);
lean_dec_ref(v_fallback_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD(lean_object* v_00_u03b1_635_, lean_object* v_00_u03b2_636_, lean_object* v_cmp_637_, lean_object* v_t_638_, lean_object* v_a_639_, lean_object* v_fallback_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_637_, v_t_638_, v_a_639_, v_fallback_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___boxed(lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_cmp_644_, lean_object* v_t_645_, lean_object* v_a_646_, lean_object* v_fallback_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_DTreeMap_getEntryD(v_00_u03b1_642_, v_00_u03b2_643_, v_cmp_644_, v_t_645_, v_a_646_, v_fallback_647_);
lean_dec_ref(v_fallback_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___redArg(lean_object* v_cmp_649_, lean_object* v_inst_650_, lean_object* v_t_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_649_, v_inst_650_, v_t_651_, v_a_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___redArg___boxed(lean_object* v_cmp_654_, lean_object* v_inst_655_, lean_object* v_t_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_DTreeMap_getEntry_x21___redArg(v_cmp_654_, v_inst_655_, v_t_656_, v_a_657_);
lean_dec_ref(v_inst_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21(lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_cmp_661_, lean_object* v_inst_662_, lean_object* v_t_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_661_, v_inst_662_, v_t_663_, v_a_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___boxed(lean_object* v_00_u03b1_666_, lean_object* v_00_u03b2_667_, lean_object* v_cmp_668_, lean_object* v_inst_669_, lean_object* v_t_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Std_DTreeMap_getEntry_x21(v_00_u03b1_666_, v_00_u03b2_667_, v_cmp_668_, v_inst_669_, v_t_670_, v_a_671_);
lean_dec_ref(v_inst_669_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___redArg(lean_object* v_t_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_DTreeMap_minEntry_x3f___redArg(v_t_675_);
lean_dec(v_t_675_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f(lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_cmp_679_, lean_object* v_t_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_cmp_684_, lean_object* v_t_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Std_DTreeMap_minEntry_x3f(v_00_u03b1_682_, v_00_u03b2_683_, v_cmp_684_, v_t_685_);
lean_dec(v_t_685_);
lean_dec_ref(v_cmp_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___redArg(lean_object* v_t_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___redArg___boxed(lean_object* v_t_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_DTreeMap_minEntry___redArg(v_t_689_);
lean_dec(v_t_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry(lean_object* v_00_u03b1_691_, lean_object* v_00_u03b2_692_, lean_object* v_cmp_693_, lean_object* v_t_694_, lean_object* v_h_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_694_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___boxed(lean_object* v_00_u03b1_697_, lean_object* v_00_u03b2_698_, lean_object* v_cmp_699_, lean_object* v_t_700_, lean_object* v_h_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_DTreeMap_minEntry(v_00_u03b1_697_, v_00_u03b2_698_, v_cmp_699_, v_t_700_, v_h_701_);
lean_dec(v_t_700_);
lean_dec_ref(v_cmp_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___redArg(lean_object* v_inst_703_, lean_object* v_t_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_703_, v_t_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_706_, lean_object* v_t_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Std_DTreeMap_minEntry_x21___redArg(v_inst_706_, v_t_707_);
lean_dec(v_t_707_);
lean_dec_ref(v_inst_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21(lean_object* v_00_u03b1_709_, lean_object* v_00_u03b2_710_, lean_object* v_cmp_711_, lean_object* v_inst_712_, lean_object* v_t_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_712_, v_t_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_715_, lean_object* v_00_u03b2_716_, lean_object* v_cmp_717_, lean_object* v_inst_718_, lean_object* v_t_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_DTreeMap_minEntry_x21(v_00_u03b1_715_, v_00_u03b2_716_, v_cmp_717_, v_inst_718_, v_t_719_);
lean_dec(v_t_719_);
lean_dec_ref(v_inst_718_);
lean_dec_ref(v_cmp_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___redArg(lean_object* v_t_721_, lean_object* v_fallback_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_721_, v_fallback_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___redArg___boxed(lean_object* v_t_724_, lean_object* v_fallback_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Std_DTreeMap_minEntryD___redArg(v_t_724_, v_fallback_725_);
lean_dec_ref(v_fallback_725_);
lean_dec(v_t_724_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD(lean_object* v_00_u03b1_727_, lean_object* v_00_u03b2_728_, lean_object* v_cmp_729_, lean_object* v_t_730_, lean_object* v_fallback_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_730_, v_fallback_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_733_, lean_object* v_00_u03b2_734_, lean_object* v_cmp_735_, lean_object* v_t_736_, lean_object* v_fallback_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_DTreeMap_minEntryD(v_00_u03b1_733_, v_00_u03b2_734_, v_cmp_735_, v_t_736_, v_fallback_737_);
lean_dec_ref(v_fallback_737_);
lean_dec(v_t_736_);
lean_dec_ref(v_cmp_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___redArg(lean_object* v_t_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Std_DTreeMap_maxEntry_x3f___redArg(v_t_741_);
lean_dec(v_t_741_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_743_, lean_object* v_00_u03b2_744_, lean_object* v_cmp_745_, lean_object* v_t_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_748_, lean_object* v_00_u03b2_749_, lean_object* v_cmp_750_, lean_object* v_t_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Std_DTreeMap_maxEntry_x3f(v_00_u03b1_748_, v_00_u03b2_749_, v_cmp_750_, v_t_751_);
lean_dec(v_t_751_);
lean_dec_ref(v_cmp_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___redArg(lean_object* v_t_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___redArg___boxed(lean_object* v_t_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_DTreeMap_maxEntry___redArg(v_t_755_);
lean_dec(v_t_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry(lean_object* v_00_u03b1_757_, lean_object* v_00_u03b2_758_, lean_object* v_cmp_759_, lean_object* v_t_760_, lean_object* v_h_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_760_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_cmp_765_, lean_object* v_t_766_, lean_object* v_h_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_DTreeMap_maxEntry(v_00_u03b1_763_, v_00_u03b2_764_, v_cmp_765_, v_t_766_, v_h_767_);
lean_dec(v_t_766_);
lean_dec_ref(v_cmp_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___redArg(lean_object* v_inst_769_, lean_object* v_t_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_769_, v_t_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_772_, lean_object* v_t_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_DTreeMap_maxEntry_x21___redArg(v_inst_772_, v_t_773_);
lean_dec(v_t_773_);
lean_dec_ref(v_inst_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21(lean_object* v_00_u03b1_775_, lean_object* v_00_u03b2_776_, lean_object* v_cmp_777_, lean_object* v_inst_778_, lean_object* v_t_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_778_, v_t_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_781_, lean_object* v_00_u03b2_782_, lean_object* v_cmp_783_, lean_object* v_inst_784_, lean_object* v_t_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_DTreeMap_maxEntry_x21(v_00_u03b1_781_, v_00_u03b2_782_, v_cmp_783_, v_inst_784_, v_t_785_);
lean_dec(v_t_785_);
lean_dec_ref(v_inst_784_);
lean_dec_ref(v_cmp_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___redArg(lean_object* v_t_787_, lean_object* v_fallback_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_787_, v_fallback_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_790_, lean_object* v_fallback_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_DTreeMap_maxEntryD___redArg(v_t_790_, v_fallback_791_);
lean_dec_ref(v_fallback_791_);
lean_dec(v_t_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD(lean_object* v_00_u03b1_793_, lean_object* v_00_u03b2_794_, lean_object* v_cmp_795_, lean_object* v_t_796_, lean_object* v_fallback_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_796_, v_fallback_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_799_, lean_object* v_00_u03b2_800_, lean_object* v_cmp_801_, lean_object* v_t_802_, lean_object* v_fallback_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_DTreeMap_maxEntryD(v_00_u03b1_799_, v_00_u03b2_800_, v_cmp_801_, v_t_802_, v_fallback_803_);
lean_dec_ref(v_fallback_803_);
lean_dec(v_t_802_);
lean_dec_ref(v_cmp_801_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___redArg(lean_object* v_t_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_DTreeMap_minKey_x3f___redArg(v_t_807_);
lean_dec(v_t_807_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f(lean_object* v_00_u03b1_809_, lean_object* v_00_u03b2_810_, lean_object* v_cmp_811_, lean_object* v_t_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_814_, lean_object* v_00_u03b2_815_, lean_object* v_cmp_816_, lean_object* v_t_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_DTreeMap_minKey_x3f(v_00_u03b1_814_, v_00_u03b2_815_, v_cmp_816_, v_t_817_);
lean_dec(v_t_817_);
lean_dec_ref(v_cmp_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___redArg(lean_object* v_t_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___redArg___boxed(lean_object* v_t_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DTreeMap_minKey___redArg(v_t_821_);
lean_dec(v_t_821_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey(lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_cmp_825_, lean_object* v_t_826_, lean_object* v_h_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___boxed(lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_cmp_831_, lean_object* v_t_832_, lean_object* v_h_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_DTreeMap_minKey(v_00_u03b1_829_, v_00_u03b2_830_, v_cmp_831_, v_t_832_, v_h_833_);
lean_dec(v_t_832_);
lean_dec_ref(v_cmp_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___redArg(lean_object* v_inst_835_, lean_object* v_t_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_835_, v_t_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_838_, lean_object* v_t_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_DTreeMap_minKey_x21___redArg(v_inst_838_, v_t_839_);
lean_dec(v_t_839_);
lean_dec(v_inst_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21(lean_object* v_00_u03b1_841_, lean_object* v_00_u03b2_842_, lean_object* v_cmp_843_, lean_object* v_inst_844_, lean_object* v_t_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_844_, v_t_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_847_, lean_object* v_00_u03b2_848_, lean_object* v_cmp_849_, lean_object* v_inst_850_, lean_object* v_t_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_DTreeMap_minKey_x21(v_00_u03b1_847_, v_00_u03b2_848_, v_cmp_849_, v_inst_850_, v_t_851_);
lean_dec(v_t_851_);
lean_dec(v_inst_850_);
lean_dec_ref(v_cmp_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___redArg(lean_object* v_t_853_, lean_object* v_fallback_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_853_, v_fallback_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___redArg___boxed(lean_object* v_t_856_, lean_object* v_fallback_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_DTreeMap_minKeyD___redArg(v_t_856_, v_fallback_857_);
lean_dec(v_fallback_857_);
lean_dec(v_t_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD(lean_object* v_00_u03b1_859_, lean_object* v_00_u03b2_860_, lean_object* v_cmp_861_, lean_object* v_t_862_, lean_object* v_fallback_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_862_, v_fallback_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_865_, lean_object* v_00_u03b2_866_, lean_object* v_cmp_867_, lean_object* v_t_868_, lean_object* v_fallback_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_DTreeMap_minKeyD(v_00_u03b1_865_, v_00_u03b2_866_, v_cmp_867_, v_t_868_, v_fallback_869_);
lean_dec(v_fallback_869_);
lean_dec(v_t_868_);
lean_dec_ref(v_cmp_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___redArg(lean_object* v_t_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Std_DTreeMap_maxKey_x3f___redArg(v_t_873_);
lean_dec(v_t_873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f(lean_object* v_00_u03b1_875_, lean_object* v_00_u03b2_876_, lean_object* v_cmp_877_, lean_object* v_t_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_880_, lean_object* v_00_u03b2_881_, lean_object* v_cmp_882_, lean_object* v_t_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_DTreeMap_maxKey_x3f(v_00_u03b1_880_, v_00_u03b2_881_, v_cmp_882_, v_t_883_);
lean_dec(v_t_883_);
lean_dec_ref(v_cmp_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___redArg(lean_object* v_t_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___redArg___boxed(lean_object* v_t_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Std_DTreeMap_maxKey___redArg(v_t_887_);
lean_dec(v_t_887_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey(lean_object* v_00_u03b1_889_, lean_object* v_00_u03b2_890_, lean_object* v_cmp_891_, lean_object* v_t_892_, lean_object* v_h_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___boxed(lean_object* v_00_u03b1_895_, lean_object* v_00_u03b2_896_, lean_object* v_cmp_897_, lean_object* v_t_898_, lean_object* v_h_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Std_DTreeMap_maxKey(v_00_u03b1_895_, v_00_u03b2_896_, v_cmp_897_, v_t_898_, v_h_899_);
lean_dec(v_t_898_);
lean_dec_ref(v_cmp_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___redArg(lean_object* v_inst_901_, lean_object* v_t_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_901_, v_t_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_904_, lean_object* v_t_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_DTreeMap_maxKey_x21___redArg(v_inst_904_, v_t_905_);
lean_dec(v_t_905_);
lean_dec(v_inst_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_cmp_909_, lean_object* v_inst_910_, lean_object* v_t_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_910_, v_t_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_913_, lean_object* v_00_u03b2_914_, lean_object* v_cmp_915_, lean_object* v_inst_916_, lean_object* v_t_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Std_DTreeMap_maxKey_x21(v_00_u03b1_913_, v_00_u03b2_914_, v_cmp_915_, v_inst_916_, v_t_917_);
lean_dec(v_t_917_);
lean_dec(v_inst_916_);
lean_dec_ref(v_cmp_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___redArg(lean_object* v_t_919_, lean_object* v_fallback_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_919_, v_fallback_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_922_, lean_object* v_fallback_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Std_DTreeMap_maxKeyD___redArg(v_t_922_, v_fallback_923_);
lean_dec(v_fallback_923_);
lean_dec(v_t_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_cmp_927_, lean_object* v_t_928_, lean_object* v_fallback_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_928_, v_fallback_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_931_, lean_object* v_00_u03b2_932_, lean_object* v_cmp_933_, lean_object* v_t_934_, lean_object* v_fallback_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Std_DTreeMap_maxKeyD(v_00_u03b1_931_, v_00_u03b2_932_, v_cmp_933_, v_t_934_, v_fallback_935_);
lean_dec(v_fallback_935_);
lean_dec(v_t_934_);
lean_dec_ref(v_cmp_933_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_937_, lean_object* v_n_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_937_, v_n_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_940_, lean_object* v_n_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_DTreeMap_entryAtIdx_x3f___redArg(v_t_940_, v_n_941_);
lean_dec(v_t_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_943_, lean_object* v_00_u03b2_944_, lean_object* v_cmp_945_, lean_object* v_t_946_, lean_object* v_n_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_946_, v_n_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_949_, lean_object* v_00_u03b2_950_, lean_object* v_cmp_951_, lean_object* v_t_952_, lean_object* v_n_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_DTreeMap_entryAtIdx_x3f(v_00_u03b1_949_, v_00_u03b2_950_, v_cmp_951_, v_t_952_, v_n_953_);
lean_dec(v_t_952_);
lean_dec_ref(v_cmp_951_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___redArg(lean_object* v_t_955_, lean_object* v_n_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_955_, v_n_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_958_, lean_object* v_n_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Std_DTreeMap_entryAtIdx___redArg(v_t_958_, v_n_959_);
lean_dec(v_t_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx(lean_object* v_00_u03b1_961_, lean_object* v_00_u03b2_962_, lean_object* v_cmp_963_, lean_object* v_t_964_, lean_object* v_n_965_, lean_object* v_h_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_964_, v_n_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_968_, lean_object* v_00_u03b2_969_, lean_object* v_cmp_970_, lean_object* v_t_971_, lean_object* v_n_972_, lean_object* v_h_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Std_DTreeMap_entryAtIdx(v_00_u03b1_968_, v_00_u03b2_969_, v_cmp_970_, v_t_971_, v_n_972_, v_h_973_);
lean_dec(v_t_971_);
lean_dec_ref(v_cmp_970_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_975_, lean_object* v_t_976_, lean_object* v_n_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_975_, v_t_976_, v_n_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_979_, lean_object* v_t_980_, lean_object* v_n_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Std_DTreeMap_entryAtIdx_x21___redArg(v_inst_979_, v_t_980_, v_n_981_);
lean_dec(v_t_980_);
lean_dec_ref(v_inst_979_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_983_, lean_object* v_00_u03b2_984_, lean_object* v_cmp_985_, lean_object* v_inst_986_, lean_object* v_t_987_, lean_object* v_n_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_986_, v_t_987_, v_n_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_990_, lean_object* v_00_u03b2_991_, lean_object* v_cmp_992_, lean_object* v_inst_993_, lean_object* v_t_994_, lean_object* v_n_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Std_DTreeMap_entryAtIdx_x21(v_00_u03b1_990_, v_00_u03b2_991_, v_cmp_992_, v_inst_993_, v_t_994_, v_n_995_);
lean_dec(v_t_994_);
lean_dec_ref(v_inst_993_);
lean_dec_ref(v_cmp_992_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___redArg(lean_object* v_t_997_, lean_object* v_n_998_, lean_object* v_fallback_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_997_, v_n_998_, v_fallback_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_1001_, lean_object* v_n_1002_, lean_object* v_fallback_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Std_DTreeMap_entryAtIdxD___redArg(v_t_1001_, v_n_1002_, v_fallback_1003_);
lean_dec_ref(v_fallback_1003_);
lean_dec(v_t_1001_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD(lean_object* v_00_u03b1_1005_, lean_object* v_00_u03b2_1006_, lean_object* v_cmp_1007_, lean_object* v_t_1008_, lean_object* v_n_1009_, lean_object* v_fallback_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_1008_, v_n_1009_, v_fallback_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_1012_, lean_object* v_00_u03b2_1013_, lean_object* v_cmp_1014_, lean_object* v_t_1015_, lean_object* v_n_1016_, lean_object* v_fallback_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Std_DTreeMap_entryAtIdxD(v_00_u03b1_1012_, v_00_u03b2_1013_, v_cmp_1014_, v_t_1015_, v_n_1016_, v_fallback_1017_);
lean_dec_ref(v_fallback_1017_);
lean_dec(v_t_1015_);
lean_dec_ref(v_cmp_1014_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_1019_, lean_object* v_n_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_1019_, v_n_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_1022_, lean_object* v_n_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_DTreeMap_keyAtIdx_x3f___redArg(v_t_1022_, v_n_1023_);
lean_dec(v_t_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_cmp_1027_, lean_object* v_t_1028_, lean_object* v_n_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_1028_, v_n_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_1031_, lean_object* v_00_u03b2_1032_, lean_object* v_cmp_1033_, lean_object* v_t_1034_, lean_object* v_n_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Std_DTreeMap_keyAtIdx_x3f(v_00_u03b1_1031_, v_00_u03b2_1032_, v_cmp_1033_, v_t_1034_, v_n_1035_);
lean_dec(v_t_1034_);
lean_dec_ref(v_cmp_1033_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___redArg(lean_object* v_t_1037_, lean_object* v_n_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1037_, v_n_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_1040_, lean_object* v_n_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Std_DTreeMap_keyAtIdx___redArg(v_t_1040_, v_n_1041_);
lean_dec(v_t_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx(lean_object* v_00_u03b1_1043_, lean_object* v_00_u03b2_1044_, lean_object* v_cmp_1045_, lean_object* v_t_1046_, lean_object* v_n_1047_, lean_object* v_h_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1046_, v_n_1047_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_cmp_1052_, lean_object* v_t_1053_, lean_object* v_n_1054_, lean_object* v_h_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_DTreeMap_keyAtIdx(v_00_u03b1_1050_, v_00_u03b2_1051_, v_cmp_1052_, v_t_1053_, v_n_1054_, v_h_1055_);
lean_dec(v_t_1053_);
lean_dec_ref(v_cmp_1052_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_1057_, lean_object* v_t_1058_, lean_object* v_n_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1057_, v_t_1058_, v_n_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_1061_, lean_object* v_t_1062_, lean_object* v_n_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Std_DTreeMap_keyAtIdx_x21___redArg(v_inst_1061_, v_t_1062_, v_n_1063_);
lean_dec(v_t_1062_);
lean_dec(v_inst_1061_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_1065_, lean_object* v_00_u03b2_1066_, lean_object* v_cmp_1067_, lean_object* v_inst_1068_, lean_object* v_t_1069_, lean_object* v_n_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1068_, v_t_1069_, v_n_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_1072_, lean_object* v_00_u03b2_1073_, lean_object* v_cmp_1074_, lean_object* v_inst_1075_, lean_object* v_t_1076_, lean_object* v_n_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Std_DTreeMap_keyAtIdx_x21(v_00_u03b1_1072_, v_00_u03b2_1073_, v_cmp_1074_, v_inst_1075_, v_t_1076_, v_n_1077_);
lean_dec(v_t_1076_);
lean_dec(v_inst_1075_);
lean_dec_ref(v_cmp_1074_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___redArg(lean_object* v_t_1079_, lean_object* v_n_1080_, lean_object* v_fallback_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1079_, v_n_1080_, v_fallback_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_1083_, lean_object* v_n_1084_, lean_object* v_fallback_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Std_DTreeMap_keyAtIdxD___redArg(v_t_1083_, v_n_1084_, v_fallback_1085_);
lean_dec(v_fallback_1085_);
lean_dec(v_t_1083_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD(lean_object* v_00_u03b1_1087_, lean_object* v_00_u03b2_1088_, lean_object* v_cmp_1089_, lean_object* v_t_1090_, lean_object* v_n_1091_, lean_object* v_fallback_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1090_, v_n_1091_, v_fallback_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_1094_, lean_object* v_00_u03b2_1095_, lean_object* v_cmp_1096_, lean_object* v_t_1097_, lean_object* v_n_1098_, lean_object* v_fallback_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Std_DTreeMap_keyAtIdxD(v_00_u03b1_1094_, v_00_u03b2_1095_, v_cmp_1096_, v_t_1097_, v_n_1098_, v_fallback_1099_);
lean_dec(v_fallback_1099_);
lean_dec(v_t_1097_);
lean_dec_ref(v_cmp_1096_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1101_, lean_object* v_t_1102_, lean_object* v_k_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_box(0);
v___x_1105_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1101_, v_k_1103_, v___x_1104_, v_t_1102_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_cmp_1108_, lean_object* v_t_1109_, lean_object* v_k_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1108_, v_k_1110_, v___x_1111_, v_t_1109_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1113_, lean_object* v_t_1114_, lean_object* v_k_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_box(0);
v___x_1117_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1113_, v_k_1115_, v___x_1116_, v_t_1114_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1118_, lean_object* v_00_u03b2_1119_, lean_object* v_cmp_1120_, lean_object* v_t_1121_, lean_object* v_k_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_box(0);
v___x_1124_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1120_, v_k_1122_, v___x_1123_, v_t_1121_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1125_, lean_object* v_t_1126_, lean_object* v_k_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_box(0);
v___x_1129_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1125_, v_k_1127_, v___x_1128_, v_t_1126_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1130_, lean_object* v_00_u03b2_1131_, lean_object* v_cmp_1132_, lean_object* v_t_1133_, lean_object* v_k_1134_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_box(0);
v___x_1136_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1132_, v_k_1134_, v___x_1135_, v_t_1133_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1137_, lean_object* v_t_1138_, lean_object* v_k_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_box(0);
v___x_1141_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1137_, v_k_1139_, v___x_1140_, v_t_1138_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1142_, lean_object* v_00_u03b2_1143_, lean_object* v_cmp_1144_, lean_object* v_t_1145_, lean_object* v_k_1146_){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_box(0);
v___x_1148_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1144_, v_k_1146_, v___x_1147_, v_t_1145_);
return v___x_1148_;
}
}
static lean_object* _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1152_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1153_ = lean_unsigned_to_nat(14u);
v___x_1154_ = lean_unsigned_to_nat(22u);
v___x_1155_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1156_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1157_ = l_mkPanicMessageWithDecl(v___x_1156_, v___x_1155_, v___x_1154_, v___x_1153_, v___x_1152_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1158_, lean_object* v_inst_1159_, lean_object* v_t_1160_, lean_object* v_k_1161_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_box(0);
v___x_1163_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1158_, v_k_1161_, v___x_1162_, v_t_1160_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1165_ = l_panic___redArg(v_inst_1159_, v___x_1164_);
return v___x_1165_;
}
else
{
lean_object* v_val_1166_; 
v_val_1166_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v___x_1163_, 1);
return v_val_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1167_, lean_object* v_inst_1168_, lean_object* v_t_1169_, lean_object* v_k_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Std_DTreeMap_getEntryGE_x21___redArg(v_cmp_1167_, v_inst_1168_, v_t_1169_, v_k_1170_);
lean_dec_ref(v_inst_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_cmp_1174_, lean_object* v_inst_1175_, lean_object* v_t_1176_, lean_object* v_k_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = lean_box(0);
v___x_1179_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1174_, v_k_1177_, v___x_1178_, v_t_1176_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1181_ = l_panic___redArg(v_inst_1175_, v___x_1180_);
return v___x_1181_;
}
else
{
lean_object* v_val_1182_; 
v_val_1182_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_val_1182_);
lean_dec_ref_known(v___x_1179_, 1);
return v_val_1182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_cmp_1185_, lean_object* v_inst_1186_, lean_object* v_t_1187_, lean_object* v_k_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Std_DTreeMap_getEntryGE_x21(v_00_u03b1_1183_, v_00_u03b2_1184_, v_cmp_1185_, v_inst_1186_, v_t_1187_, v_k_1188_);
lean_dec_ref(v_inst_1186_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1190_, lean_object* v_inst_1191_, lean_object* v_t_1192_, lean_object* v_k_1193_){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_box(0);
v___x_1195_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1190_, v_k_1193_, v___x_1194_, v_t_1192_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1197_ = l_panic___redArg(v_inst_1191_, v___x_1196_);
return v___x_1197_;
}
else
{
lean_object* v_val_1198_; 
v_val_1198_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v___x_1195_, 1);
return v_val_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1199_, lean_object* v_inst_1200_, lean_object* v_t_1201_, lean_object* v_k_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Std_DTreeMap_getEntryGT_x21___redArg(v_cmp_1199_, v_inst_1200_, v_t_1201_, v_k_1202_);
lean_dec_ref(v_inst_1200_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1204_, lean_object* v_00_u03b2_1205_, lean_object* v_cmp_1206_, lean_object* v_inst_1207_, lean_object* v_t_1208_, lean_object* v_k_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_box(0);
v___x_1211_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1206_, v_k_1209_, v___x_1210_, v_t_1208_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1215_, lean_object* v_00_u03b2_1216_, lean_object* v_cmp_1217_, lean_object* v_inst_1218_, lean_object* v_t_1219_, lean_object* v_k_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Std_DTreeMap_getEntryGT_x21(v_00_u03b1_1215_, v_00_u03b2_1216_, v_cmp_1217_, v_inst_1218_, v_t_1219_, v_k_1220_);
lean_dec_ref(v_inst_1218_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1222_, lean_object* v_inst_1223_, lean_object* v_t_1224_, lean_object* v_k_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_box(0);
v___x_1227_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1222_, v_k_1225_, v___x_1226_, v_t_1224_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1229_ = l_panic___redArg(v_inst_1223_, v___x_1228_);
return v___x_1229_;
}
else
{
lean_object* v_val_1230_; 
v_val_1230_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_val_1230_);
lean_dec_ref_known(v___x_1227_, 1);
return v_val_1230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1231_, lean_object* v_inst_1232_, lean_object* v_t_1233_, lean_object* v_k_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Std_DTreeMap_getEntryLE_x21___redArg(v_cmp_1231_, v_inst_1232_, v_t_1233_, v_k_1234_);
lean_dec_ref(v_inst_1232_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1236_, lean_object* v_00_u03b2_1237_, lean_object* v_cmp_1238_, lean_object* v_inst_1239_, lean_object* v_t_1240_, lean_object* v_k_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_box(0);
v___x_1243_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1238_, v_k_1241_, v___x_1242_, v_t_1240_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1247_, lean_object* v_00_u03b2_1248_, lean_object* v_cmp_1249_, lean_object* v_inst_1250_, lean_object* v_t_1251_, lean_object* v_k_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Std_DTreeMap_getEntryLE_x21(v_00_u03b1_1247_, v_00_u03b2_1248_, v_cmp_1249_, v_inst_1250_, v_t_1251_, v_k_1252_);
lean_dec_ref(v_inst_1250_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1254_, lean_object* v_inst_1255_, lean_object* v_t_1256_, lean_object* v_k_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_box(0);
v___x_1259_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1254_, v_k_1257_, v___x_1258_, v_t_1256_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1261_ = l_panic___redArg(v_inst_1255_, v___x_1260_);
return v___x_1261_;
}
else
{
lean_object* v_val_1262_; 
v_val_1262_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v___x_1259_, 1);
return v_val_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1263_, lean_object* v_inst_1264_, lean_object* v_t_1265_, lean_object* v_k_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_DTreeMap_getEntryLT_x21___redArg(v_cmp_1263_, v_inst_1264_, v_t_1265_, v_k_1266_);
lean_dec_ref(v_inst_1264_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1268_, lean_object* v_00_u03b2_1269_, lean_object* v_cmp_1270_, lean_object* v_inst_1271_, lean_object* v_t_1272_, lean_object* v_k_1273_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_box(0);
v___x_1275_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1270_, v_k_1273_, v___x_1274_, v_t_1272_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1277_ = l_panic___redArg(v_inst_1271_, v___x_1276_);
return v___x_1277_;
}
else
{
lean_object* v_val_1278_; 
v_val_1278_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_val_1278_);
lean_dec_ref_known(v___x_1275_, 1);
return v_val_1278_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1279_, lean_object* v_00_u03b2_1280_, lean_object* v_cmp_1281_, lean_object* v_inst_1282_, lean_object* v_t_1283_, lean_object* v_k_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Std_DTreeMap_getEntryLT_x21(v_00_u03b1_1279_, v_00_u03b2_1280_, v_cmp_1281_, v_inst_1282_, v_t_1283_, v_k_1284_);
lean_dec_ref(v_inst_1282_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___redArg(lean_object* v_cmp_1286_, lean_object* v_t_1287_, lean_object* v_k_1288_, lean_object* v_fallback_1289_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_box(0);
v___x_1291_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1286_, v_k_1288_, v___x_1290_, v_t_1287_);
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
lean_dec_ref_known(v___x_1291_, 1);
return v_val_1292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1293_, lean_object* v_t_1294_, lean_object* v_k_1295_, lean_object* v_fallback_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Std_DTreeMap_getEntryGED___redArg(v_cmp_1293_, v_t_1294_, v_k_1295_, v_fallback_1296_);
lean_dec_ref(v_fallback_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED(lean_object* v_00_u03b1_1298_, lean_object* v_00_u03b2_1299_, lean_object* v_cmp_1300_, lean_object* v_t_1301_, lean_object* v_k_1302_, lean_object* v_fallback_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1300_, v_k_1302_, v___x_1304_, v_t_1301_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_00_u03b2_1308_, lean_object* v_cmp_1309_, lean_object* v_t_1310_, lean_object* v_k_1311_, lean_object* v_fallback_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Std_DTreeMap_getEntryGED(v_00_u03b1_1307_, v_00_u03b2_1308_, v_cmp_1309_, v_t_1310_, v_k_1311_, v_fallback_1312_);
lean_dec_ref(v_fallback_1312_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1314_, lean_object* v_t_1315_, lean_object* v_k_1316_, lean_object* v_fallback_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_box(0);
v___x_1319_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1314_, v_k_1316_, v___x_1318_, v_t_1315_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_inc_ref(v_fallback_1317_);
return v_fallback_1317_;
}
else
{
lean_object* v_val_1320_; 
v_val_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_val_1320_);
lean_dec_ref_known(v___x_1319_, 1);
return v_val_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1321_, lean_object* v_t_1322_, lean_object* v_k_1323_, lean_object* v_fallback_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Std_DTreeMap_getEntryGTD___redArg(v_cmp_1321_, v_t_1322_, v_k_1323_, v_fallback_1324_);
lean_dec_ref(v_fallback_1324_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD(lean_object* v_00_u03b1_1326_, lean_object* v_00_u03b2_1327_, lean_object* v_cmp_1328_, lean_object* v_t_1329_, lean_object* v_k_1330_, lean_object* v_fallback_1331_){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_box(0);
v___x_1333_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1328_, v_k_1330_, v___x_1332_, v_t_1329_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_inc_ref(v_fallback_1331_);
return v_fallback_1331_;
}
else
{
lean_object* v_val_1334_; 
v_val_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_val_1334_);
lean_dec_ref_known(v___x_1333_, 1);
return v_val_1334_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_cmp_1337_, lean_object* v_t_1338_, lean_object* v_k_1339_, lean_object* v_fallback_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_DTreeMap_getEntryGTD(v_00_u03b1_1335_, v_00_u03b2_1336_, v_cmp_1337_, v_t_1338_, v_k_1339_, v_fallback_1340_);
lean_dec_ref(v_fallback_1340_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___redArg(lean_object* v_cmp_1342_, lean_object* v_t_1343_, lean_object* v_k_1344_, lean_object* v_fallback_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_box(0);
v___x_1347_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1342_, v_k_1344_, v___x_1346_, v_t_1343_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_inc_ref(v_fallback_1345_);
return v_fallback_1345_;
}
else
{
lean_object* v_val_1348_; 
v_val_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_val_1348_);
lean_dec_ref_known(v___x_1347_, 1);
return v_val_1348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1349_, lean_object* v_t_1350_, lean_object* v_k_1351_, lean_object* v_fallback_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Std_DTreeMap_getEntryLED___redArg(v_cmp_1349_, v_t_1350_, v_k_1351_, v_fallback_1352_);
lean_dec_ref(v_fallback_1352_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED(lean_object* v_00_u03b1_1354_, lean_object* v_00_u03b2_1355_, lean_object* v_cmp_1356_, lean_object* v_t_1357_, lean_object* v_k_1358_, lean_object* v_fallback_1359_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_box(0);
v___x_1361_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1356_, v_k_1358_, v___x_1360_, v_t_1357_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_inc_ref(v_fallback_1359_);
return v_fallback_1359_;
}
else
{
lean_object* v_val_1362_; 
v_val_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v___x_1361_, 1);
return v_val_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_00_u03b2_1364_, lean_object* v_cmp_1365_, lean_object* v_t_1366_, lean_object* v_k_1367_, lean_object* v_fallback_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Std_DTreeMap_getEntryLED(v_00_u03b1_1363_, v_00_u03b2_1364_, v_cmp_1365_, v_t_1366_, v_k_1367_, v_fallback_1368_);
lean_dec_ref(v_fallback_1368_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1370_, lean_object* v_t_1371_, lean_object* v_k_1372_, lean_object* v_fallback_1373_){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1370_, v_k_1372_, v___x_1374_, v_t_1371_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1377_, lean_object* v_t_1378_, lean_object* v_k_1379_, lean_object* v_fallback_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Std_DTreeMap_getEntryLTD___redArg(v_cmp_1377_, v_t_1378_, v_k_1379_, v_fallback_1380_);
lean_dec_ref(v_fallback_1380_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD(lean_object* v_00_u03b1_1382_, lean_object* v_00_u03b2_1383_, lean_object* v_cmp_1384_, lean_object* v_t_1385_, lean_object* v_k_1386_, lean_object* v_fallback_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_box(0);
v___x_1389_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1384_, v_k_1386_, v___x_1388_, v_t_1385_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_inc_ref(v_fallback_1387_);
return v_fallback_1387_;
}
else
{
lean_object* v_val_1390_; 
v_val_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v___x_1389_, 1);
return v_val_1390_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1391_, lean_object* v_00_u03b2_1392_, lean_object* v_cmp_1393_, lean_object* v_t_1394_, lean_object* v_k_1395_, lean_object* v_fallback_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Std_DTreeMap_getEntryLTD(v_00_u03b1_1391_, v_00_u03b2_1392_, v_cmp_1393_, v_t_1394_, v_k_1395_, v_fallback_1396_);
lean_dec_ref(v_fallback_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1398_, lean_object* v_t_1399_, lean_object* v_k_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_box(0);
v___x_1402_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1398_, v_k_1400_, v___x_1401_, v_t_1399_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1403_, lean_object* v_00_u03b2_1404_, lean_object* v_cmp_1405_, lean_object* v_t_1406_, lean_object* v_k_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_box(0);
v___x_1409_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1405_, v_k_1407_, v___x_1408_, v_t_1406_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1410_, lean_object* v_t_1411_, lean_object* v_k_1412_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_box(0);
v___x_1414_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1410_, v_k_1412_, v___x_1413_, v_t_1411_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_cmp_1417_, lean_object* v_t_1418_, lean_object* v_k_1419_){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = lean_box(0);
v___x_1421_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1417_, v_k_1419_, v___x_1420_, v_t_1418_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1422_, lean_object* v_t_1423_, lean_object* v_k_1424_){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_box(0);
v___x_1426_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1422_, v_k_1424_, v___x_1425_, v_t_1423_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1427_, lean_object* v_00_u03b2_1428_, lean_object* v_cmp_1429_, lean_object* v_t_1430_, lean_object* v_k_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_box(0);
v___x_1433_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1429_, v_k_1431_, v___x_1432_, v_t_1430_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1434_, lean_object* v_t_1435_, lean_object* v_k_1436_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_box(0);
v___x_1438_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1434_, v_k_1436_, v___x_1437_, v_t_1435_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1439_, lean_object* v_00_u03b2_1440_, lean_object* v_cmp_1441_, lean_object* v_t_1442_, lean_object* v_k_1443_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_box(0);
v___x_1445_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1441_, v_k_1443_, v___x_1444_, v_t_1442_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1446_, lean_object* v_inst_1447_, lean_object* v_t_1448_, lean_object* v_k_1449_){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_box(0);
v___x_1451_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1446_, v_k_1449_, v___x_1450_, v_t_1448_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1453_ = l_panic___redArg(v_inst_1447_, v___x_1452_);
return v___x_1453_;
}
else
{
lean_object* v_val_1454_; 
v_val_1454_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_val_1454_);
lean_dec_ref_known(v___x_1451_, 1);
return v_val_1454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1455_, lean_object* v_inst_1456_, lean_object* v_t_1457_, lean_object* v_k_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Std_DTreeMap_getKeyGE_x21___redArg(v_cmp_1455_, v_inst_1456_, v_t_1457_, v_k_1458_);
lean_dec(v_inst_1456_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1460_, lean_object* v_00_u03b2_1461_, lean_object* v_cmp_1462_, lean_object* v_inst_1463_, lean_object* v_t_1464_, lean_object* v_k_1465_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_box(0);
v___x_1467_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1462_, v_k_1465_, v___x_1466_, v_t_1464_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1469_ = l_panic___redArg(v_inst_1463_, v___x_1468_);
return v___x_1469_;
}
else
{
lean_object* v_val_1470_; 
v_val_1470_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_val_1470_);
lean_dec_ref_known(v___x_1467_, 1);
return v_val_1470_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1471_, lean_object* v_00_u03b2_1472_, lean_object* v_cmp_1473_, lean_object* v_inst_1474_, lean_object* v_t_1475_, lean_object* v_k_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Std_DTreeMap_getKeyGE_x21(v_00_u03b1_1471_, v_00_u03b2_1472_, v_cmp_1473_, v_inst_1474_, v_t_1475_, v_k_1476_);
lean_dec(v_inst_1474_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1478_, lean_object* v_inst_1479_, lean_object* v_t_1480_, lean_object* v_k_1481_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_box(0);
v___x_1483_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1478_, v_k_1481_, v___x_1482_, v_t_1480_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1485_ = l_panic___redArg(v_inst_1479_, v___x_1484_);
return v___x_1485_;
}
else
{
lean_object* v_val_1486_; 
v_val_1486_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v___x_1483_, 1);
return v_val_1486_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1487_, lean_object* v_inst_1488_, lean_object* v_t_1489_, lean_object* v_k_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Std_DTreeMap_getKeyGT_x21___redArg(v_cmp_1487_, v_inst_1488_, v_t_1489_, v_k_1490_);
lean_dec(v_inst_1488_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1492_, lean_object* v_00_u03b2_1493_, lean_object* v_cmp_1494_, lean_object* v_inst_1495_, lean_object* v_t_1496_, lean_object* v_k_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_box(0);
v___x_1499_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1494_, v_k_1497_, v___x_1498_, v_t_1496_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1501_ = l_panic___redArg(v_inst_1495_, v___x_1500_);
return v___x_1501_;
}
else
{
lean_object* v_val_1502_; 
v_val_1502_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v___x_1499_, 1);
return v_val_1502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1503_, lean_object* v_00_u03b2_1504_, lean_object* v_cmp_1505_, lean_object* v_inst_1506_, lean_object* v_t_1507_, lean_object* v_k_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Std_DTreeMap_getKeyGT_x21(v_00_u03b1_1503_, v_00_u03b2_1504_, v_cmp_1505_, v_inst_1506_, v_t_1507_, v_k_1508_);
lean_dec(v_inst_1506_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1510_, lean_object* v_inst_1511_, lean_object* v_t_1512_, lean_object* v_k_1513_){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_box(0);
v___x_1515_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1510_, v_k_1513_, v___x_1514_, v_t_1512_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1517_ = l_panic___redArg(v_inst_1511_, v___x_1516_);
return v___x_1517_;
}
else
{
lean_object* v_val_1518_; 
v_val_1518_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_val_1518_);
lean_dec_ref_known(v___x_1515_, 1);
return v_val_1518_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1519_, lean_object* v_inst_1520_, lean_object* v_t_1521_, lean_object* v_k_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Std_DTreeMap_getKeyLE_x21___redArg(v_cmp_1519_, v_inst_1520_, v_t_1521_, v_k_1522_);
lean_dec(v_inst_1520_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1524_, lean_object* v_00_u03b2_1525_, lean_object* v_cmp_1526_, lean_object* v_inst_1527_, lean_object* v_t_1528_, lean_object* v_k_1529_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1526_, v_k_1529_, v___x_1530_, v_t_1528_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1535_, lean_object* v_00_u03b2_1536_, lean_object* v_cmp_1537_, lean_object* v_inst_1538_, lean_object* v_t_1539_, lean_object* v_k_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Std_DTreeMap_getKeyLE_x21(v_00_u03b1_1535_, v_00_u03b2_1536_, v_cmp_1537_, v_inst_1538_, v_t_1539_, v_k_1540_);
lean_dec(v_inst_1538_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1542_, lean_object* v_inst_1543_, lean_object* v_t_1544_, lean_object* v_k_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_box(0);
v___x_1547_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1542_, v_k_1545_, v___x_1546_, v_t_1544_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1549_ = l_panic___redArg(v_inst_1543_, v___x_1548_);
return v___x_1549_;
}
else
{
lean_object* v_val_1550_; 
v_val_1550_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_val_1550_);
lean_dec_ref_known(v___x_1547_, 1);
return v_val_1550_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1551_, lean_object* v_inst_1552_, lean_object* v_t_1553_, lean_object* v_k_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Std_DTreeMap_getKeyLT_x21___redArg(v_cmp_1551_, v_inst_1552_, v_t_1553_, v_k_1554_);
lean_dec(v_inst_1552_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1556_, lean_object* v_00_u03b2_1557_, lean_object* v_cmp_1558_, lean_object* v_inst_1559_, lean_object* v_t_1560_, lean_object* v_k_1561_){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1558_, v_k_1561_, v___x_1562_, v_t_1560_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1565_ = l_panic___redArg(v_inst_1559_, v___x_1564_);
return v___x_1565_;
}
else
{
lean_object* v_val_1566_; 
v_val_1566_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_val_1566_);
lean_dec_ref_known(v___x_1563_, 1);
return v_val_1566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1567_, lean_object* v_00_u03b2_1568_, lean_object* v_cmp_1569_, lean_object* v_inst_1570_, lean_object* v_t_1571_, lean_object* v_k_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Std_DTreeMap_getKeyLT_x21(v_00_u03b1_1567_, v_00_u03b2_1568_, v_cmp_1569_, v_inst_1570_, v_t_1571_, v_k_1572_);
lean_dec(v_inst_1570_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___redArg(lean_object* v_cmp_1574_, lean_object* v_t_1575_, lean_object* v_k_1576_, lean_object* v_fallback_1577_){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_box(0);
v___x_1579_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1574_, v_k_1576_, v___x_1578_, v_t_1575_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_inc(v_fallback_1577_);
return v_fallback_1577_;
}
else
{
lean_object* v_val_1580_; 
v_val_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v___x_1579_, 1);
return v_val_1580_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1581_, lean_object* v_t_1582_, lean_object* v_k_1583_, lean_object* v_fallback_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Std_DTreeMap_getKeyGED___redArg(v_cmp_1581_, v_t_1582_, v_k_1583_, v_fallback_1584_);
lean_dec(v_fallback_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED(lean_object* v_00_u03b1_1586_, lean_object* v_00_u03b2_1587_, lean_object* v_cmp_1588_, lean_object* v_t_1589_, lean_object* v_k_1590_, lean_object* v_fallback_1591_){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_box(0);
v___x_1593_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1588_, v_k_1590_, v___x_1592_, v_t_1589_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_inc(v_fallback_1591_);
return v_fallback_1591_;
}
else
{
lean_object* v_val_1594_; 
v_val_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v___x_1593_, 1);
return v_val_1594_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1595_, lean_object* v_00_u03b2_1596_, lean_object* v_cmp_1597_, lean_object* v_t_1598_, lean_object* v_k_1599_, lean_object* v_fallback_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Std_DTreeMap_getKeyGED(v_00_u03b1_1595_, v_00_u03b2_1596_, v_cmp_1597_, v_t_1598_, v_k_1599_, v_fallback_1600_);
lean_dec(v_fallback_1600_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1602_, lean_object* v_t_1603_, lean_object* v_k_1604_, lean_object* v_fallback_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = lean_box(0);
v___x_1607_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1602_, v_k_1604_, v___x_1606_, v_t_1603_);
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
lean_dec_ref_known(v___x_1607_, 1);
return v_val_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1609_, lean_object* v_t_1610_, lean_object* v_k_1611_, lean_object* v_fallback_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Std_DTreeMap_getKeyGTD___redArg(v_cmp_1609_, v_t_1610_, v_k_1611_, v_fallback_1612_);
lean_dec(v_fallback_1612_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD(lean_object* v_00_u03b1_1614_, lean_object* v_00_u03b2_1615_, lean_object* v_cmp_1616_, lean_object* v_t_1617_, lean_object* v_k_1618_, lean_object* v_fallback_1619_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_box(0);
v___x_1621_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1616_, v_k_1618_, v___x_1620_, v_t_1617_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1623_, lean_object* v_00_u03b2_1624_, lean_object* v_cmp_1625_, lean_object* v_t_1626_, lean_object* v_k_1627_, lean_object* v_fallback_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Std_DTreeMap_getKeyGTD(v_00_u03b1_1623_, v_00_u03b2_1624_, v_cmp_1625_, v_t_1626_, v_k_1627_, v_fallback_1628_);
lean_dec(v_fallback_1628_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___redArg(lean_object* v_cmp_1630_, lean_object* v_t_1631_, lean_object* v_k_1632_, lean_object* v_fallback_1633_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_box(0);
v___x_1635_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1630_, v_k_1632_, v___x_1634_, v_t_1631_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_inc(v_fallback_1633_);
return v_fallback_1633_;
}
else
{
lean_object* v_val_1636_; 
v_val_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_val_1636_);
lean_dec_ref_known(v___x_1635_, 1);
return v_val_1636_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1637_, lean_object* v_t_1638_, lean_object* v_k_1639_, lean_object* v_fallback_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Std_DTreeMap_getKeyLED___redArg(v_cmp_1637_, v_t_1638_, v_k_1639_, v_fallback_1640_);
lean_dec(v_fallback_1640_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED(lean_object* v_00_u03b1_1642_, lean_object* v_00_u03b2_1643_, lean_object* v_cmp_1644_, lean_object* v_t_1645_, lean_object* v_k_1646_, lean_object* v_fallback_1647_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_box(0);
v___x_1649_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1644_, v_k_1646_, v___x_1648_, v_t_1645_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_inc(v_fallback_1647_);
return v_fallback_1647_;
}
else
{
lean_object* v_val_1650_; 
v_val_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_val_1650_);
lean_dec_ref_known(v___x_1649_, 1);
return v_val_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1651_, lean_object* v_00_u03b2_1652_, lean_object* v_cmp_1653_, lean_object* v_t_1654_, lean_object* v_k_1655_, lean_object* v_fallback_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Std_DTreeMap_getKeyLED(v_00_u03b1_1651_, v_00_u03b2_1652_, v_cmp_1653_, v_t_1654_, v_k_1655_, v_fallback_1656_);
lean_dec(v_fallback_1656_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1658_, lean_object* v_t_1659_, lean_object* v_k_1660_, lean_object* v_fallback_1661_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = lean_box(0);
v___x_1663_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1658_, v_k_1660_, v___x_1662_, v_t_1659_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_inc(v_fallback_1661_);
return v_fallback_1661_;
}
else
{
lean_object* v_val_1664_; 
v_val_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_val_1664_);
lean_dec_ref_known(v___x_1663_, 1);
return v_val_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1665_, lean_object* v_t_1666_, lean_object* v_k_1667_, lean_object* v_fallback_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Std_DTreeMap_getKeyLTD___redArg(v_cmp_1665_, v_t_1666_, v_k_1667_, v_fallback_1668_);
lean_dec(v_fallback_1668_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD(lean_object* v_00_u03b1_1670_, lean_object* v_00_u03b2_1671_, lean_object* v_cmp_1672_, lean_object* v_t_1673_, lean_object* v_k_1674_, lean_object* v_fallback_1675_){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_box(0);
v___x_1677_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1672_, v_k_1674_, v___x_1676_, v_t_1673_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_inc(v_fallback_1675_);
return v_fallback_1675_;
}
else
{
lean_object* v_val_1678_; 
v_val_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_val_1678_);
lean_dec_ref_known(v___x_1677_, 1);
return v_val_1678_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1679_, lean_object* v_00_u03b2_1680_, lean_object* v_cmp_1681_, lean_object* v_t_1682_, lean_object* v_k_1683_, lean_object* v_fallback_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Std_DTreeMap_getKeyLTD(v_00_u03b1_1679_, v_00_u03b2_1680_, v_cmp_1681_, v_t_1682_, v_k_1683_, v_fallback_1684_);
lean_dec(v_fallback_1684_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1686_, lean_object* v_t_1687_, lean_object* v_a_1688_, lean_object* v_b_1689_){
_start:
{
lean_object* v___x_1690_; 
lean_inc(v_a_1688_);
lean_inc(v_t_1687_);
lean_inc_ref(v_cmp_1686_);
v___x_1690_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1686_, v_t_1687_, v_a_1688_);
if (lean_obj_tag(v___x_1690_) == 0)
{
uint8_t v___x_1691_; 
lean_inc(v_t_1687_);
lean_inc(v_a_1688_);
lean_inc_ref(v_cmp_1686_);
v___x_1691_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1686_, v_a_1688_, v_t_1687_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1686_, v_a_1688_, v_b_1689_, v_t_1687_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1690_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
return v___x_1693_;
}
else
{
lean_object* v___x_1694_; 
lean_dec(v_b_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_cmp_1686_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1690_);
lean_ctor_set(v___x_1694_, 1, v_t_1687_);
return v___x_1694_;
}
}
else
{
lean_object* v___x_1695_; 
lean_dec(v_b_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_cmp_1686_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1690_);
lean_ctor_set(v___x_1695_, 1, v_t_1687_);
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1696_, lean_object* v_cmp_1697_, lean_object* v_00_u03b2_1698_, lean_object* v_t_1699_, lean_object* v_a_1700_, lean_object* v_b_1701_){
_start:
{
lean_object* v___x_1702_; 
lean_inc(v_a_1700_);
lean_inc(v_t_1699_);
lean_inc_ref(v_cmp_1697_);
v___x_1702_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1697_, v_t_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1702_) == 0)
{
uint8_t v___x_1703_; 
lean_inc(v_t_1699_);
lean_inc(v_a_1700_);
lean_inc_ref(v_cmp_1697_);
v___x_1703_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1697_, v_a_1700_, v_t_1699_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1697_, v_a_1700_, v_b_1701_, v_t_1699_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1702_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; 
lean_dec(v_b_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_cmp_1697_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1702_);
lean_ctor_set(v___x_1706_, 1, v_t_1699_);
return v___x_1706_;
}
}
else
{
lean_object* v___x_1707_; 
lean_dec(v_b_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_cmp_1697_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1702_);
lean_ctor_set(v___x_1707_, 1, v_t_1699_);
return v___x_1707_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x3f___redArg(lean_object* v_cmp_1708_, lean_object* v_t_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1708_, v_t_1709_, v_a_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x3f(lean_object* v_00_u03b1_1712_, lean_object* v_cmp_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_t_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1713_, v_t_1715_, v_a_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get___redArg(lean_object* v_cmp_1718_, lean_object* v_t_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1718_, v_t_1719_, v_a_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get(lean_object* v_00_u03b1_1722_, lean_object* v_cmp_1723_, lean_object* v_00_u03b2_1724_, lean_object* v_t_1725_, lean_object* v_a_1726_, lean_object* v_h_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1723_, v_t_1725_, v_a_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___redArg(lean_object* v_cmp_1729_, lean_object* v_inst_1730_, lean_object* v_t_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1729_, v_inst_1730_, v_t_1731_, v_a_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___redArg___boxed(lean_object* v_cmp_1734_, lean_object* v_inst_1735_, lean_object* v_t_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Std_DTreeMap_Const_get_x21___redArg(v_cmp_1734_, v_inst_1735_, v_t_1736_, v_a_1737_);
lean_dec(v_inst_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21(lean_object* v_00_u03b1_1739_, lean_object* v_cmp_1740_, lean_object* v_00_u03b2_1741_, lean_object* v_inst_1742_, lean_object* v_t_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1740_, v_inst_1742_, v_t_1743_, v_a_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_cmp_1747_, lean_object* v_00_u03b2_1748_, lean_object* v_inst_1749_, lean_object* v_t_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Std_DTreeMap_Const_get_x21(v_00_u03b1_1746_, v_cmp_1747_, v_00_u03b2_1748_, v_inst_1749_, v_t_1750_, v_a_1751_);
lean_dec(v_inst_1749_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___redArg(lean_object* v_cmp_1753_, lean_object* v_t_1754_, lean_object* v_a_1755_, lean_object* v_fallback_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1753_, v_t_1754_, v_a_1755_, v_fallback_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___redArg___boxed(lean_object* v_cmp_1758_, lean_object* v_t_1759_, lean_object* v_a_1760_, lean_object* v_fallback_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Std_DTreeMap_Const_getD___redArg(v_cmp_1758_, v_t_1759_, v_a_1760_, v_fallback_1761_);
lean_dec(v_fallback_1761_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD(lean_object* v_00_u03b1_1763_, lean_object* v_cmp_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_t_1766_, lean_object* v_a_1767_, lean_object* v_fallback_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1764_, v_t_1766_, v_a_1767_, v_fallback_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___boxed(lean_object* v_00_u03b1_1770_, lean_object* v_cmp_1771_, lean_object* v_00_u03b2_1772_, lean_object* v_t_1773_, lean_object* v_a_1774_, lean_object* v_fallback_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_DTreeMap_Const_getD(v_00_u03b1_1770_, v_cmp_1771_, v_00_u03b2_1772_, v_t_1773_, v_a_1774_, v_fallback_1775_);
lean_dec(v_fallback_1775_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___redArg(lean_object* v_t_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Std_DTreeMap_Const_minEntry_x3f___redArg(v_t_1779_);
lean_dec(v_t_1779_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f(lean_object* v_00_u03b1_1781_, lean_object* v_cmp_1782_, lean_object* v_00_u03b2_1783_, lean_object* v_t_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1786_, lean_object* v_cmp_1787_, lean_object* v_00_u03b2_1788_, lean_object* v_t_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Std_DTreeMap_Const_minEntry_x3f(v_00_u03b1_1786_, v_cmp_1787_, v_00_u03b2_1788_, v_t_1789_);
lean_dec(v_t_1789_);
lean_dec_ref(v_cmp_1787_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___redArg(lean_object* v_t_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___redArg___boxed(lean_object* v_t_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_DTreeMap_Const_minEntry___redArg(v_t_1793_);
lean_dec(v_t_1793_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry(lean_object* v_00_u03b1_1795_, lean_object* v_cmp_1796_, lean_object* v_00_u03b2_1797_, lean_object* v_t_1798_, lean_object* v_h_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_cmp_1802_, lean_object* v_00_u03b2_1803_, lean_object* v_t_1804_, lean_object* v_h_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Std_DTreeMap_Const_minEntry(v_00_u03b1_1801_, v_cmp_1802_, v_00_u03b2_1803_, v_t_1804_, v_h_1805_);
lean_dec(v_t_1804_);
lean_dec_ref(v_cmp_1802_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___redArg(lean_object* v_inst_1807_, lean_object* v_t_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1807_, v_t_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1810_, lean_object* v_t_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Std_DTreeMap_Const_minEntry_x21___redArg(v_inst_1810_, v_t_1811_);
lean_dec(v_t_1811_);
lean_dec_ref(v_inst_1810_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21(lean_object* v_00_u03b1_1813_, lean_object* v_cmp_1814_, lean_object* v_00_u03b2_1815_, lean_object* v_inst_1816_, lean_object* v_t_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1816_, v_t_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_cmp_1820_, lean_object* v_00_u03b2_1821_, lean_object* v_inst_1822_, lean_object* v_t_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Std_DTreeMap_Const_minEntry_x21(v_00_u03b1_1819_, v_cmp_1820_, v_00_u03b2_1821_, v_inst_1822_, v_t_1823_);
lean_dec(v_t_1823_);
lean_dec_ref(v_inst_1822_);
lean_dec_ref(v_cmp_1820_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___redArg(lean_object* v_t_1825_, lean_object* v_fallback_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1825_, v_fallback_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___redArg___boxed(lean_object* v_t_1828_, lean_object* v_fallback_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Std_DTreeMap_Const_minEntryD___redArg(v_t_1828_, v_fallback_1829_);
lean_dec_ref(v_fallback_1829_);
lean_dec(v_t_1828_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD(lean_object* v_00_u03b1_1831_, lean_object* v_cmp_1832_, lean_object* v_00_u03b2_1833_, lean_object* v_t_1834_, lean_object* v_fallback_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1834_, v_fallback_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___boxed(lean_object* v_00_u03b1_1837_, lean_object* v_cmp_1838_, lean_object* v_00_u03b2_1839_, lean_object* v_t_1840_, lean_object* v_fallback_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Std_DTreeMap_Const_minEntryD(v_00_u03b1_1837_, v_cmp_1838_, v_00_u03b2_1839_, v_t_1840_, v_fallback_1841_);
lean_dec_ref(v_fallback_1841_);
lean_dec(v_t_1840_);
lean_dec_ref(v_cmp_1838_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___redArg(lean_object* v_t_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Std_DTreeMap_Const_maxEntry_x3f___redArg(v_t_1845_);
lean_dec(v_t_1845_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f(lean_object* v_00_u03b1_1847_, lean_object* v_cmp_1848_, lean_object* v_00_u03b2_1849_, lean_object* v_t_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1852_, lean_object* v_cmp_1853_, lean_object* v_00_u03b2_1854_, lean_object* v_t_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Std_DTreeMap_Const_maxEntry_x3f(v_00_u03b1_1852_, v_cmp_1853_, v_00_u03b2_1854_, v_t_1855_);
lean_dec(v_t_1855_);
lean_dec_ref(v_cmp_1853_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___redArg(lean_object* v_t_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___redArg___boxed(lean_object* v_t_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Std_DTreeMap_Const_maxEntry___redArg(v_t_1859_);
lean_dec(v_t_1859_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry(lean_object* v_00_u03b1_1861_, lean_object* v_cmp_1862_, lean_object* v_00_u03b2_1863_, lean_object* v_t_1864_, lean_object* v_h_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___boxed(lean_object* v_00_u03b1_1867_, lean_object* v_cmp_1868_, lean_object* v_00_u03b2_1869_, lean_object* v_t_1870_, lean_object* v_h_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Std_DTreeMap_Const_maxEntry(v_00_u03b1_1867_, v_cmp_1868_, v_00_u03b2_1869_, v_t_1870_, v_h_1871_);
lean_dec(v_t_1870_);
lean_dec_ref(v_cmp_1868_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___redArg(lean_object* v_inst_1873_, lean_object* v_t_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1873_, v_t_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_1876_, lean_object* v_t_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Std_DTreeMap_Const_maxEntry_x21___redArg(v_inst_1876_, v_t_1877_);
lean_dec(v_t_1877_);
lean_dec_ref(v_inst_1876_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21(lean_object* v_00_u03b1_1879_, lean_object* v_cmp_1880_, lean_object* v_00_u03b2_1881_, lean_object* v_inst_1882_, lean_object* v_t_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1882_, v_t_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_1885_, lean_object* v_cmp_1886_, lean_object* v_00_u03b2_1887_, lean_object* v_inst_1888_, lean_object* v_t_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Std_DTreeMap_Const_maxEntry_x21(v_00_u03b1_1885_, v_cmp_1886_, v_00_u03b2_1887_, v_inst_1888_, v_t_1889_);
lean_dec(v_t_1889_);
lean_dec_ref(v_inst_1888_);
lean_dec_ref(v_cmp_1886_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___redArg(lean_object* v_t_1891_, lean_object* v_fallback_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1891_, v_fallback_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___redArg___boxed(lean_object* v_t_1894_, lean_object* v_fallback_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Std_DTreeMap_Const_maxEntryD___redArg(v_t_1894_, v_fallback_1895_);
lean_dec_ref(v_fallback_1895_);
lean_dec(v_t_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD(lean_object* v_00_u03b1_1897_, lean_object* v_cmp_1898_, lean_object* v_00_u03b2_1899_, lean_object* v_t_1900_, lean_object* v_fallback_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1900_, v_fallback_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___boxed(lean_object* v_00_u03b1_1903_, lean_object* v_cmp_1904_, lean_object* v_00_u03b2_1905_, lean_object* v_t_1906_, lean_object* v_fallback_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Std_DTreeMap_Const_maxEntryD(v_00_u03b1_1903_, v_cmp_1904_, v_00_u03b2_1905_, v_t_1906_, v_fallback_1907_);
lean_dec_ref(v_fallback_1907_);
lean_dec(v_t_1906_);
lean_dec_ref(v_cmp_1904_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(lean_object* v_t_1909_, lean_object* v_n_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1909_, v_n_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_1912_, lean_object* v_n_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(v_t_1912_, v_n_1913_);
lean_dec(v_t_1912_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_1915_, lean_object* v_cmp_1916_, lean_object* v_00_u03b2_1917_, lean_object* v_t_1918_, lean_object* v_n_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1918_, v_n_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1921_, lean_object* v_cmp_1922_, lean_object* v_00_u03b2_1923_, lean_object* v_t_1924_, lean_object* v_n_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Std_DTreeMap_Const_entryAtIdx_x3f(v_00_u03b1_1921_, v_cmp_1922_, v_00_u03b2_1923_, v_t_1924_, v_n_1925_);
lean_dec(v_t_1924_);
lean_dec_ref(v_cmp_1922_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___redArg(lean_object* v_t_1927_, lean_object* v_n_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_1927_, v_n_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___redArg___boxed(lean_object* v_t_1930_, lean_object* v_n_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Std_DTreeMap_Const_entryAtIdx___redArg(v_t_1930_, v_n_1931_);
lean_dec(v_t_1930_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx(lean_object* v_00_u03b1_1933_, lean_object* v_cmp_1934_, lean_object* v_00_u03b2_1935_, lean_object* v_t_1936_, lean_object* v_n_1937_, lean_object* v_h_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_1936_, v_n_1937_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_1940_, lean_object* v_cmp_1941_, lean_object* v_00_u03b2_1942_, lean_object* v_t_1943_, lean_object* v_n_1944_, lean_object* v_h_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Std_DTreeMap_Const_entryAtIdx(v_00_u03b1_1940_, v_cmp_1941_, v_00_u03b2_1942_, v_t_1943_, v_n_1944_, v_h_1945_);
lean_dec(v_t_1943_);
lean_dec_ref(v_cmp_1941_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(lean_object* v_inst_1947_, lean_object* v_t_1948_, lean_object* v_n_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1947_, v_t_1948_, v_n_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_1951_, lean_object* v_t_1952_, lean_object* v_n_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(v_inst_1951_, v_t_1952_, v_n_1953_);
lean_dec(v_t_1952_);
lean_dec_ref(v_inst_1951_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21(lean_object* v_00_u03b1_1955_, lean_object* v_cmp_1956_, lean_object* v_00_u03b2_1957_, lean_object* v_inst_1958_, lean_object* v_t_1959_, lean_object* v_n_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1958_, v_t_1959_, v_n_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_1962_, lean_object* v_cmp_1963_, lean_object* v_00_u03b2_1964_, lean_object* v_inst_1965_, lean_object* v_t_1966_, lean_object* v_n_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Std_DTreeMap_Const_entryAtIdx_x21(v_00_u03b1_1962_, v_cmp_1963_, v_00_u03b2_1964_, v_inst_1965_, v_t_1966_, v_n_1967_);
lean_dec(v_t_1966_);
lean_dec_ref(v_inst_1965_);
lean_dec_ref(v_cmp_1963_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___redArg(lean_object* v_t_1969_, lean_object* v_n_1970_, lean_object* v_fallback_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1969_, v_n_1970_, v_fallback_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_1973_, lean_object* v_n_1974_, lean_object* v_fallback_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Std_DTreeMap_Const_entryAtIdxD___redArg(v_t_1973_, v_n_1974_, v_fallback_1975_);
lean_dec_ref(v_fallback_1975_);
lean_dec(v_t_1973_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD(lean_object* v_00_u03b1_1977_, lean_object* v_cmp_1978_, lean_object* v_00_u03b2_1979_, lean_object* v_t_1980_, lean_object* v_n_1981_, lean_object* v_fallback_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1980_, v_n_1981_, v_fallback_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_1984_, lean_object* v_cmp_1985_, lean_object* v_00_u03b2_1986_, lean_object* v_t_1987_, lean_object* v_n_1988_, lean_object* v_fallback_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Std_DTreeMap_Const_entryAtIdxD(v_00_u03b1_1984_, v_cmp_1985_, v_00_u03b2_1986_, v_t_1987_, v_n_1988_, v_fallback_1989_);
lean_dec_ref(v_fallback_1989_);
lean_dec(v_t_1987_);
lean_dec_ref(v_cmp_1985_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_1991_, lean_object* v_t_1992_, lean_object* v_k_1993_){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_box(0);
v___x_1995_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1991_, v_k_1993_, v___x_1994_, v_t_1992_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x3f(lean_object* v_00_u03b1_1996_, lean_object* v_cmp_1997_, lean_object* v_00_u03b2_1998_, lean_object* v_t_1999_, lean_object* v_k_2000_){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_box(0);
v___x_2002_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1997_, v_k_2000_, v___x_2001_, v_t_1999_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_2003_, lean_object* v_t_2004_, lean_object* v_k_2005_){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_box(0);
v___x_2007_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2003_, v_k_2005_, v___x_2006_, v_t_2004_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x3f(lean_object* v_00_u03b1_2008_, lean_object* v_cmp_2009_, lean_object* v_00_u03b2_2010_, lean_object* v_t_2011_, lean_object* v_k_2012_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_box(0);
v___x_2014_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2009_, v_k_2012_, v___x_2013_, v_t_2011_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_2015_, lean_object* v_t_2016_, lean_object* v_k_2017_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_box(0);
v___x_2019_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2015_, v_k_2017_, v___x_2018_, v_t_2016_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x3f(lean_object* v_00_u03b1_2020_, lean_object* v_cmp_2021_, lean_object* v_00_u03b2_2022_, lean_object* v_t_2023_, lean_object* v_k_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_box(0);
v___x_2026_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2021_, v_k_2024_, v___x_2025_, v_t_2023_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_2027_, lean_object* v_t_2028_, lean_object* v_k_2029_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_box(0);
v___x_2031_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2027_, v_k_2029_, v___x_2030_, v_t_2028_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x3f(lean_object* v_00_u03b1_2032_, lean_object* v_cmp_2033_, lean_object* v_00_u03b2_2034_, lean_object* v_t_2035_, lean_object* v_k_2036_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_box(0);
v___x_2038_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2033_, v_k_2036_, v___x_2037_, v_t_2035_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___redArg(lean_object* v_cmp_2039_, lean_object* v_inst_2040_, lean_object* v_t_2041_, lean_object* v_k_2042_){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_box(0);
v___x_2044_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2039_, v_k_2042_, v___x_2043_, v_t_2041_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2046_ = l_panic___redArg(v_inst_2040_, v___x_2045_);
return v___x_2046_;
}
else
{
lean_object* v_val_2047_; 
v_val_2047_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_val_2047_);
lean_dec_ref_known(v___x_2044_, 1);
return v_val_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_2048_, lean_object* v_inst_2049_, lean_object* v_t_2050_, lean_object* v_k_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Std_DTreeMap_Const_getEntryGE_x21___redArg(v_cmp_2048_, v_inst_2049_, v_t_2050_, v_k_2051_);
lean_dec_ref(v_inst_2049_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21(lean_object* v_00_u03b1_2053_, lean_object* v_cmp_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_inst_2056_, lean_object* v_t_2057_, lean_object* v_k_2058_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_box(0);
v___x_2060_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2054_, v_k_2058_, v___x_2059_, v_t_2057_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2062_ = l_panic___redArg(v_inst_2056_, v___x_2061_);
return v___x_2062_;
}
else
{
lean_object* v_val_2063_; 
v_val_2063_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_val_2063_);
lean_dec_ref_known(v___x_2060_, 1);
return v_val_2063_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_2064_, lean_object* v_cmp_2065_, lean_object* v_00_u03b2_2066_, lean_object* v_inst_2067_, lean_object* v_t_2068_, lean_object* v_k_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_DTreeMap_Const_getEntryGE_x21(v_00_u03b1_2064_, v_cmp_2065_, v_00_u03b2_2066_, v_inst_2067_, v_t_2068_, v_k_2069_);
lean_dec_ref(v_inst_2067_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___redArg(lean_object* v_cmp_2071_, lean_object* v_inst_2072_, lean_object* v_t_2073_, lean_object* v_k_2074_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_box(0);
v___x_2076_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2071_, v_k_2074_, v___x_2075_, v_t_2073_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2078_ = l_panic___redArg(v_inst_2072_, v___x_2077_);
return v___x_2078_;
}
else
{
lean_object* v_val_2079_; 
v_val_2079_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_val_2079_);
lean_dec_ref_known(v___x_2076_, 1);
return v_val_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_2080_, lean_object* v_inst_2081_, lean_object* v_t_2082_, lean_object* v_k_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Std_DTreeMap_Const_getEntryGT_x21___redArg(v_cmp_2080_, v_inst_2081_, v_t_2082_, v_k_2083_);
lean_dec_ref(v_inst_2081_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21(lean_object* v_00_u03b1_2085_, lean_object* v_cmp_2086_, lean_object* v_00_u03b2_2087_, lean_object* v_inst_2088_, lean_object* v_t_2089_, lean_object* v_k_2090_){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2086_, v_k_2090_, v___x_2091_, v_t_2089_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2094_ = l_panic___redArg(v_inst_2088_, v___x_2093_);
return v___x_2094_;
}
else
{
lean_object* v_val_2095_; 
v_val_2095_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v___x_2092_, 1);
return v_val_2095_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_2096_, lean_object* v_cmp_2097_, lean_object* v_00_u03b2_2098_, lean_object* v_inst_2099_, lean_object* v_t_2100_, lean_object* v_k_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Std_DTreeMap_Const_getEntryGT_x21(v_00_u03b1_2096_, v_cmp_2097_, v_00_u03b2_2098_, v_inst_2099_, v_t_2100_, v_k_2101_);
lean_dec_ref(v_inst_2099_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___redArg(lean_object* v_cmp_2103_, lean_object* v_inst_2104_, lean_object* v_t_2105_, lean_object* v_k_2106_){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_box(0);
v___x_2108_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2103_, v_k_2106_, v___x_2107_, v_t_2105_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2110_ = l_panic___redArg(v_inst_2104_, v___x_2109_);
return v___x_2110_;
}
else
{
lean_object* v_val_2111_; 
v_val_2111_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_val_2111_);
lean_dec_ref_known(v___x_2108_, 1);
return v_val_2111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_2112_, lean_object* v_inst_2113_, lean_object* v_t_2114_, lean_object* v_k_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Std_DTreeMap_Const_getEntryLE_x21___redArg(v_cmp_2112_, v_inst_2113_, v_t_2114_, v_k_2115_);
lean_dec_ref(v_inst_2113_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21(lean_object* v_00_u03b1_2117_, lean_object* v_cmp_2118_, lean_object* v_00_u03b2_2119_, lean_object* v_inst_2120_, lean_object* v_t_2121_, lean_object* v_k_2122_){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = lean_box(0);
v___x_2124_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2118_, v_k_2122_, v___x_2123_, v_t_2121_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2126_ = l_panic___redArg(v_inst_2120_, v___x_2125_);
return v___x_2126_;
}
else
{
lean_object* v_val_2127_; 
v_val_2127_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v___x_2124_, 1);
return v_val_2127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2128_, lean_object* v_cmp_2129_, lean_object* v_00_u03b2_2130_, lean_object* v_inst_2131_, lean_object* v_t_2132_, lean_object* v_k_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Std_DTreeMap_Const_getEntryLE_x21(v_00_u03b1_2128_, v_cmp_2129_, v_00_u03b2_2130_, v_inst_2131_, v_t_2132_, v_k_2133_);
lean_dec_ref(v_inst_2131_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___redArg(lean_object* v_cmp_2135_, lean_object* v_inst_2136_, lean_object* v_t_2137_, lean_object* v_k_2138_){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_box(0);
v___x_2140_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2135_, v_k_2138_, v___x_2139_, v_t_2137_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2142_ = l_panic___redArg(v_inst_2136_, v___x_2141_);
return v___x_2142_;
}
else
{
lean_object* v_val_2143_; 
v_val_2143_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v___x_2140_, 1);
return v_val_2143_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_2144_, lean_object* v_inst_2145_, lean_object* v_t_2146_, lean_object* v_k_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Std_DTreeMap_Const_getEntryLT_x21___redArg(v_cmp_2144_, v_inst_2145_, v_t_2146_, v_k_2147_);
lean_dec_ref(v_inst_2145_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21(lean_object* v_00_u03b1_2149_, lean_object* v_cmp_2150_, lean_object* v_00_u03b2_2151_, lean_object* v_inst_2152_, lean_object* v_t_2153_, lean_object* v_k_2154_){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2150_, v_k_2154_, v___x_2155_, v_t_2153_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2158_ = l_panic___redArg(v_inst_2152_, v___x_2157_);
return v___x_2158_;
}
else
{
lean_object* v_val_2159_; 
v_val_2159_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_val_2159_);
lean_dec_ref_known(v___x_2156_, 1);
return v_val_2159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2160_, lean_object* v_cmp_2161_, lean_object* v_00_u03b2_2162_, lean_object* v_inst_2163_, lean_object* v_t_2164_, lean_object* v_k_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Std_DTreeMap_Const_getEntryLT_x21(v_00_u03b1_2160_, v_cmp_2161_, v_00_u03b2_2162_, v_inst_2163_, v_t_2164_, v_k_2165_);
lean_dec_ref(v_inst_2163_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___redArg(lean_object* v_cmp_2167_, lean_object* v_t_2168_, lean_object* v_k_2169_, lean_object* v_fallback_2170_){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_box(0);
v___x_2172_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2167_, v_k_2169_, v___x_2171_, v_t_2168_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_inc_ref(v_fallback_2170_);
return v_fallback_2170_;
}
else
{
lean_object* v_val_2173_; 
v_val_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_val_2173_);
lean_dec_ref_known(v___x_2172_, 1);
return v_val_2173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2174_, lean_object* v_t_2175_, lean_object* v_k_2176_, lean_object* v_fallback_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Std_DTreeMap_Const_getEntryGED___redArg(v_cmp_2174_, v_t_2175_, v_k_2176_, v_fallback_2177_);
lean_dec_ref(v_fallback_2177_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED(lean_object* v_00_u03b1_2179_, lean_object* v_cmp_2180_, lean_object* v_00_u03b2_2181_, lean_object* v_t_2182_, lean_object* v_k_2183_, lean_object* v_fallback_2184_){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = lean_box(0);
v___x_2186_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2180_, v_k_2183_, v___x_2185_, v_t_2182_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_inc_ref(v_fallback_2184_);
return v_fallback_2184_;
}
else
{
lean_object* v_val_2187_; 
v_val_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_val_2187_);
lean_dec_ref_known(v___x_2186_, 1);
return v_val_2187_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2188_, lean_object* v_cmp_2189_, lean_object* v_00_u03b2_2190_, lean_object* v_t_2191_, lean_object* v_k_2192_, lean_object* v_fallback_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Std_DTreeMap_Const_getEntryGED(v_00_u03b1_2188_, v_cmp_2189_, v_00_u03b2_2190_, v_t_2191_, v_k_2192_, v_fallback_2193_);
lean_dec_ref(v_fallback_2193_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___redArg(lean_object* v_cmp_2195_, lean_object* v_t_2196_, lean_object* v_k_2197_, lean_object* v_fallback_2198_){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = lean_box(0);
v___x_2200_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2195_, v_k_2197_, v___x_2199_, v_t_2196_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_inc_ref(v_fallback_2198_);
return v_fallback_2198_;
}
else
{
lean_object* v_val_2201_; 
v_val_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_val_2201_);
lean_dec_ref_known(v___x_2200_, 1);
return v_val_2201_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2202_, lean_object* v_t_2203_, lean_object* v_k_2204_, lean_object* v_fallback_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Std_DTreeMap_Const_getEntryGTD___redArg(v_cmp_2202_, v_t_2203_, v_k_2204_, v_fallback_2205_);
lean_dec_ref(v_fallback_2205_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD(lean_object* v_00_u03b1_2207_, lean_object* v_cmp_2208_, lean_object* v_00_u03b2_2209_, lean_object* v_t_2210_, lean_object* v_k_2211_, lean_object* v_fallback_2212_){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_box(0);
v___x_2214_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2208_, v_k_2211_, v___x_2213_, v_t_2210_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_inc_ref(v_fallback_2212_);
return v_fallback_2212_;
}
else
{
lean_object* v_val_2215_; 
v_val_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_val_2215_);
lean_dec_ref_known(v___x_2214_, 1);
return v_val_2215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2216_, lean_object* v_cmp_2217_, lean_object* v_00_u03b2_2218_, lean_object* v_t_2219_, lean_object* v_k_2220_, lean_object* v_fallback_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Std_DTreeMap_Const_getEntryGTD(v_00_u03b1_2216_, v_cmp_2217_, v_00_u03b2_2218_, v_t_2219_, v_k_2220_, v_fallback_2221_);
lean_dec_ref(v_fallback_2221_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___redArg(lean_object* v_cmp_2223_, lean_object* v_t_2224_, lean_object* v_k_2225_, lean_object* v_fallback_2226_){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_box(0);
v___x_2228_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2223_, v_k_2225_, v___x_2227_, v_t_2224_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_inc_ref(v_fallback_2226_);
return v_fallback_2226_;
}
else
{
lean_object* v_val_2229_; 
v_val_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v___x_2228_, 1);
return v_val_2229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2230_, lean_object* v_t_2231_, lean_object* v_k_2232_, lean_object* v_fallback_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Std_DTreeMap_Const_getEntryLED___redArg(v_cmp_2230_, v_t_2231_, v_k_2232_, v_fallback_2233_);
lean_dec_ref(v_fallback_2233_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED(lean_object* v_00_u03b1_2235_, lean_object* v_cmp_2236_, lean_object* v_00_u03b2_2237_, lean_object* v_t_2238_, lean_object* v_k_2239_, lean_object* v_fallback_2240_){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_box(0);
v___x_2242_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2236_, v_k_2239_, v___x_2241_, v_t_2238_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_inc_ref(v_fallback_2240_);
return v_fallback_2240_;
}
else
{
lean_object* v_val_2243_; 
v_val_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_val_2243_);
lean_dec_ref_known(v___x_2242_, 1);
return v_val_2243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2244_, lean_object* v_cmp_2245_, lean_object* v_00_u03b2_2246_, lean_object* v_t_2247_, lean_object* v_k_2248_, lean_object* v_fallback_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Std_DTreeMap_Const_getEntryLED(v_00_u03b1_2244_, v_cmp_2245_, v_00_u03b2_2246_, v_t_2247_, v_k_2248_, v_fallback_2249_);
lean_dec_ref(v_fallback_2249_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___redArg(lean_object* v_cmp_2251_, lean_object* v_t_2252_, lean_object* v_k_2253_, lean_object* v_fallback_2254_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2251_, v_k_2253_, v___x_2255_, v_t_2252_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_inc_ref(v_fallback_2254_);
return v_fallback_2254_;
}
else
{
lean_object* v_val_2257_; 
v_val_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_val_2257_);
lean_dec_ref_known(v___x_2256_, 1);
return v_val_2257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2258_, lean_object* v_t_2259_, lean_object* v_k_2260_, lean_object* v_fallback_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Std_DTreeMap_Const_getEntryLTD___redArg(v_cmp_2258_, v_t_2259_, v_k_2260_, v_fallback_2261_);
lean_dec_ref(v_fallback_2261_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD(lean_object* v_00_u03b1_2263_, lean_object* v_cmp_2264_, lean_object* v_00_u03b2_2265_, lean_object* v_t_2266_, lean_object* v_k_2267_, lean_object* v_fallback_2268_){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = lean_box(0);
v___x_2270_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2264_, v_k_2267_, v___x_2269_, v_t_2266_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_inc_ref(v_fallback_2268_);
return v_fallback_2268_;
}
else
{
lean_object* v_val_2271_; 
v_val_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_val_2271_);
lean_dec_ref_known(v___x_2270_, 1);
return v_val_2271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2272_, lean_object* v_cmp_2273_, lean_object* v_00_u03b2_2274_, lean_object* v_t_2275_, lean_object* v_k_2276_, lean_object* v_fallback_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Std_DTreeMap_Const_getEntryLTD(v_00_u03b1_2272_, v_cmp_2273_, v_00_u03b2_2274_, v_t_2275_, v_k_2276_, v_fallback_2277_);
lean_dec_ref(v_fallback_2277_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter___redArg(lean_object* v_f_2279_, lean_object* v_t_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2279_, v_t_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter(lean_object* v_00_u03b1_2282_, lean_object* v_00_u03b2_2283_, lean_object* v_cmp_2284_, lean_object* v_f_2285_, lean_object* v_t_2286_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2285_, v_t_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter___boxed(lean_object* v_00_u03b1_2288_, lean_object* v_00_u03b2_2289_, lean_object* v_cmp_2290_, lean_object* v_f_2291_, lean_object* v_t_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Std_DTreeMap_filter(v_00_u03b1_2288_, v_00_u03b2_2289_, v_cmp_2290_, v_f_2291_, v_t_2292_);
lean_dec_ref(v_cmp_2290_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM___redArg(lean_object* v_inst_2294_, lean_object* v_f_2295_, lean_object* v_init_2296_, lean_object* v_t_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2294_, v_f_2295_, v_init_2296_, v_t_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM(lean_object* v_00_u03b1_2299_, lean_object* v_00_u03b2_2300_, lean_object* v_cmp_2301_, lean_object* v_00_u03b4_2302_, lean_object* v_m_2303_, lean_object* v_inst_2304_, lean_object* v_f_2305_, lean_object* v_init_2306_, lean_object* v_t_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2304_, v_f_2305_, v_init_2306_, v_t_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM___boxed(lean_object* v_00_u03b1_2309_, lean_object* v_00_u03b2_2310_, lean_object* v_cmp_2311_, lean_object* v_00_u03b4_2312_, lean_object* v_m_2313_, lean_object* v_inst_2314_, lean_object* v_f_2315_, lean_object* v_init_2316_, lean_object* v_t_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Std_DTreeMap_foldlM(v_00_u03b1_2309_, v_00_u03b2_2310_, v_cmp_2311_, v_00_u03b4_2312_, v_m_2313_, v_inst_2314_, v_f_2315_, v_init_2316_, v_t_2317_);
lean_dec_ref(v_cmp_2311_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl___redArg(lean_object* v_f_2319_, lean_object* v_init_2320_, lean_object* v_t_2321_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2319_, v_init_2320_, v_t_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl(lean_object* v_00_u03b1_2323_, lean_object* v_00_u03b2_2324_, lean_object* v_cmp_2325_, lean_object* v_00_u03b4_2326_, lean_object* v_f_2327_, lean_object* v_init_2328_, lean_object* v_t_2329_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2327_, v_init_2328_, v_t_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl___boxed(lean_object* v_00_u03b1_2331_, lean_object* v_00_u03b2_2332_, lean_object* v_cmp_2333_, lean_object* v_00_u03b4_2334_, lean_object* v_f_2335_, lean_object* v_init_2336_, lean_object* v_t_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Std_DTreeMap_foldl(v_00_u03b1_2331_, v_00_u03b2_2332_, v_cmp_2333_, v_00_u03b4_2334_, v_f_2335_, v_init_2336_, v_t_2337_);
lean_dec_ref(v_cmp_2333_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM___redArg(lean_object* v_inst_2339_, lean_object* v_f_2340_, lean_object* v_init_2341_, lean_object* v_t_2342_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2339_, v_f_2340_, v_init_2341_, v_t_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM(lean_object* v_00_u03b1_2344_, lean_object* v_00_u03b2_2345_, lean_object* v_cmp_2346_, lean_object* v_00_u03b4_2347_, lean_object* v_m_2348_, lean_object* v_inst_2349_, lean_object* v_f_2350_, lean_object* v_init_2351_, lean_object* v_t_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2349_, v_f_2350_, v_init_2351_, v_t_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM___boxed(lean_object* v_00_u03b1_2354_, lean_object* v_00_u03b2_2355_, lean_object* v_cmp_2356_, lean_object* v_00_u03b4_2357_, lean_object* v_m_2358_, lean_object* v_inst_2359_, lean_object* v_f_2360_, lean_object* v_init_2361_, lean_object* v_t_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Std_DTreeMap_foldrM(v_00_u03b1_2354_, v_00_u03b2_2355_, v_cmp_2356_, v_00_u03b4_2357_, v_m_2358_, v_inst_2359_, v_f_2360_, v_init_2361_, v_t_2362_);
lean_dec_ref(v_cmp_2356_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___redArg___lam__0(lean_object* v_f_2364_, lean_object* v_x1_2365_, lean_object* v_x2_2366_, lean_object* v_x3_2367_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_apply_3(v_f_2364_, v_x1_2365_, v_x2_2366_, v_x3_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___redArg(lean_object* v_f_2388_, lean_object* v_init_2389_, lean_object* v_t_2390_){
_start:
{
lean_object* v___f_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___f_2391_ = lean_alloc_closure((void*)(l_Std_DTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2391_, 0, v_f_2388_);
v___x_2392_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2393_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2392_, v___f_2391_, v_init_2389_, v_t_2390_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr(lean_object* v_00_u03b1_2394_, lean_object* v_00_u03b2_2395_, lean_object* v_cmp_2396_, lean_object* v_00_u03b4_2397_, lean_object* v_f_2398_, lean_object* v_init_2399_, lean_object* v_t_2400_){
_start:
{
lean_object* v___f_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___f_2401_ = lean_alloc_closure((void*)(l_Std_DTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2401_, 0, v_f_2398_);
v___x_2402_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2403_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2402_, v___f_2401_, v_init_2399_, v_t_2400_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___boxed(lean_object* v_00_u03b1_2404_, lean_object* v_00_u03b2_2405_, lean_object* v_cmp_2406_, lean_object* v_00_u03b4_2407_, lean_object* v_f_2408_, lean_object* v_init_2409_, lean_object* v_t_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Std_DTreeMap_foldr(v_00_u03b1_2404_, v_00_u03b2_2405_, v_cmp_2406_, v_00_u03b4_2407_, v_f_2408_, v_init_2409_, v_t_2410_);
lean_dec_ref(v_cmp_2406_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition___redArg___lam__0(lean_object* v_f_2412_, lean_object* v_cmp_2413_, lean_object* v_x_2414_, lean_object* v_a_2415_, lean_object* v_b_2416_){
_start:
{
lean_object* v_fst_2417_; lean_object* v_snd_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2432_; 
v_fst_2417_ = lean_ctor_get(v_x_2414_, 0);
v_snd_2418_ = lean_ctor_get(v_x_2414_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_x_2414_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2420_ = v_x_2414_;
v_isShared_2421_ = v_isSharedCheck_2432_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_snd_2418_);
lean_inc(v_fst_2417_);
lean_dec(v_x_2414_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2432_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; uint8_t v___x_2423_; 
lean_inc(v_b_2416_);
lean_inc(v_a_2415_);
v___x_2422_ = lean_apply_2(v_f_2412_, v_a_2415_, v_b_2416_);
v___x_2423_ = lean_unbox(v___x_2422_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2424_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2413_, v_a_2415_, v_b_2416_, v_snd_2418_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 1, v___x_2424_);
v___x_2426_ = v___x_2420_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_fst_2417_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
else
{
lean_object* v___x_2428_; lean_object* v___x_2430_; 
v___x_2428_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2413_, v_a_2415_, v_b_2416_, v_fst_2417_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2428_);
v___x_2430_ = v___x_2420_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_snd_2418_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition___redArg(lean_object* v_cmp_2435_, lean_object* v_f_2436_, lean_object* v_t_2437_){
_start:
{
lean_object* v___f_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___f_2438_ = lean_alloc_closure((void*)(l_Std_DTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2438_, 0, v_f_2436_);
lean_closure_set(v___f_2438_, 1, v_cmp_2435_);
v___x_2439_ = ((lean_object*)(l_Std_DTreeMap_partition___redArg___closed__0));
v___x_2440_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2438_, v___x_2439_, v_t_2437_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition(lean_object* v_00_u03b1_2441_, lean_object* v_00_u03b2_2442_, lean_object* v_cmp_2443_, lean_object* v_f_2444_, lean_object* v_t_2445_){
_start:
{
lean_object* v___f_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___f_2446_ = lean_alloc_closure((void*)(l_Std_DTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2446_, 0, v_f_2444_);
lean_closure_set(v___f_2446_, 1, v_cmp_2443_);
v___x_2447_ = ((lean_object*)(l_Std_DTreeMap_partition___redArg___closed__0));
v___x_2448_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2446_, v___x_2447_, v_t_2445_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___redArg___lam__0(lean_object* v_f_2449_, lean_object* v_x_2450_, lean_object* v_k_2451_, lean_object* v_v_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_apply_2(v_f_2449_, v_k_2451_, v_v_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___redArg(lean_object* v_inst_2454_, lean_object* v_f_2455_, lean_object* v_t_2456_){
_start:
{
lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___f_2457_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2457_, 0, v_f_2455_);
v___x_2458_ = lean_box(0);
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2454_, v___f_2457_, v___x_2458_, v_t_2456_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM(lean_object* v_00_u03b1_2460_, lean_object* v_00_u03b2_2461_, lean_object* v_cmp_2462_, lean_object* v_m_2463_, lean_object* v_inst_2464_, lean_object* v_f_2465_, lean_object* v_t_2466_){
_start:
{
lean_object* v___f_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___f_2467_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2467_, 0, v_f_2465_);
v___x_2468_ = lean_box(0);
v___x_2469_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2464_, v___f_2467_, v___x_2468_, v_t_2466_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___boxed(lean_object* v_00_u03b1_2470_, lean_object* v_00_u03b2_2471_, lean_object* v_cmp_2472_, lean_object* v_m_2473_, lean_object* v_inst_2474_, lean_object* v_f_2475_, lean_object* v_t_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Std_DTreeMap_forM(v_00_u03b1_2470_, v_00_u03b2_2471_, v_cmp_2472_, v_m_2473_, v_inst_2474_, v_f_2475_, v_t_2476_);
lean_dec_ref(v_cmp_2472_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___redArg___lam__0(lean_object* v_toPure_2478_, lean_object* v_____do__lift_2479_){
_start:
{
lean_object* v_a_2480_; lean_object* v___x_2481_; 
v_a_2480_ = lean_ctor_get(v_____do__lift_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref(v_____do__lift_2479_);
v___x_2481_ = lean_apply_2(v_toPure_2478_, lean_box(0), v_a_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___redArg(lean_object* v_inst_2482_, lean_object* v_f_2483_, lean_object* v_init_2484_, lean_object* v_t_2485_){
_start:
{
lean_object* v_toApplicative_2486_; lean_object* v_toBind_2487_; lean_object* v_toPure_2488_; lean_object* v___x_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; 
v_toApplicative_2486_ = lean_ctor_get(v_inst_2482_, 0);
v_toBind_2487_ = lean_ctor_get(v_inst_2482_, 1);
lean_inc(v_toBind_2487_);
v_toPure_2488_ = lean_ctor_get(v_toApplicative_2486_, 1);
lean_inc(v_toPure_2488_);
v___x_2489_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2482_, v_f_2483_, v_init_2484_, v_t_2485_);
v___f_2490_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2490_, 0, v_toPure_2488_);
v___x_2491_ = lean_apply_4(v_toBind_2487_, lean_box(0), lean_box(0), v___x_2489_, v___f_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn(lean_object* v_00_u03b1_2492_, lean_object* v_00_u03b2_2493_, lean_object* v_cmp_2494_, lean_object* v_00_u03b4_2495_, lean_object* v_m_2496_, lean_object* v_inst_2497_, lean_object* v_f_2498_, lean_object* v_init_2499_, lean_object* v_t_2500_){
_start:
{
lean_object* v_toApplicative_2501_; lean_object* v_toBind_2502_; lean_object* v_toPure_2503_; lean_object* v___x_2504_; lean_object* v___f_2505_; lean_object* v___x_2506_; 
v_toApplicative_2501_ = lean_ctor_get(v_inst_2497_, 0);
v_toBind_2502_ = lean_ctor_get(v_inst_2497_, 1);
lean_inc(v_toBind_2502_);
v_toPure_2503_ = lean_ctor_get(v_toApplicative_2501_, 1);
lean_inc(v_toPure_2503_);
v___x_2504_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2497_, v_f_2498_, v_init_2499_, v_t_2500_);
v___f_2505_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2505_, 0, v_toPure_2503_);
v___x_2506_ = lean_apply_4(v_toBind_2502_, lean_box(0), lean_box(0), v___x_2504_, v___f_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___boxed(lean_object* v_00_u03b1_2507_, lean_object* v_00_u03b2_2508_, lean_object* v_cmp_2509_, lean_object* v_00_u03b4_2510_, lean_object* v_m_2511_, lean_object* v_inst_2512_, lean_object* v_f_2513_, lean_object* v_init_2514_, lean_object* v_t_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Std_DTreeMap_forIn(v_00_u03b1_2507_, v_00_u03b2_2508_, v_cmp_2509_, v_00_u03b4_2510_, v_m_2511_, v_inst_2512_, v_f_2513_, v_init_2514_, v_t_2515_);
lean_dec_ref(v_cmp_2509_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_2517_, lean_object* v_x_2518_, lean_object* v_k_2519_, lean_object* v_v_2520_){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v_k_2519_);
lean_ctor_set(v___x_2521_, 1, v_v_2520_);
v___x_2522_ = lean_apply_1(v_f_2517_, v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1(lean_object* v_inst_2523_, lean_object* v_t_2524_, lean_object* v_f_2525_){
_start:
{
lean_object* v___f_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___f_2526_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2526_, 0, v_f_2525_);
v___x_2527_ = lean_box(0);
v___x_2528_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2523_, v___f_2526_, v___x_2527_, v_t_2524_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg(lean_object* v_inst_2529_){
_start:
{
lean_object* v___f_2530_; 
v___f_2530_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2530_, 0, v_inst_2529_);
return v___f_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad(lean_object* v_00_u03b1_2531_, lean_object* v_00_u03b2_2532_, lean_object* v_cmp_2533_, lean_object* v_m_2534_, lean_object* v_inst_2535_){
_start:
{
lean_object* v___f_2536_; 
v___f_2536_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2536_, 0, v_inst_2535_);
return v___f_2536_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___boxed(lean_object* v_00_u03b1_2537_, lean_object* v_00_u03b2_2538_, lean_object* v_cmp_2539_, lean_object* v_m_2540_, lean_object* v_inst_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Std_DTreeMap_instForMSigmaOfMonad(v_00_u03b1_2537_, v_00_u03b2_2538_, v_cmp_2539_, v_m_2540_, v_inst_2541_);
lean_dec_ref(v_cmp_2539_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_2543_, lean_object* v_a_2544_, lean_object* v_b_2545_, lean_object* v_acc_2546_){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v_a_2544_);
lean_ctor_set(v___x_2547_, 1, v_b_2545_);
v___x_2548_ = lean_apply_2(v_f_2543_, v___x_2547_, v_acc_2546_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_2549_, lean_object* v_00_u03b2_2550_, lean_object* v_m_2551_, lean_object* v_init_2552_, lean_object* v_f_2553_){
_start:
{
lean_object* v_toApplicative_2554_; lean_object* v_toBind_2555_; lean_object* v_toPure_2556_; lean_object* v___f_2557_; lean_object* v___x_2558_; lean_object* v___f_2559_; lean_object* v___x_2560_; 
v_toApplicative_2554_ = lean_ctor_get(v_inst_2549_, 0);
v_toBind_2555_ = lean_ctor_get(v_inst_2549_, 1);
lean_inc(v_toBind_2555_);
v_toPure_2556_ = lean_ctor_get(v_toApplicative_2554_, 1);
lean_inc(v_toPure_2556_);
v___f_2557_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2557_, 0, v_f_2553_);
v___x_2558_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2549_, v___f_2557_, v_init_2552_, v_m_2551_);
v___f_2559_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2559_, 0, v_toPure_2556_);
v___x_2560_ = lean_apply_4(v_toBind_2555_, lean_box(0), lean_box(0), v___x_2558_, v___f_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg(lean_object* v_inst_2561_){
_start:
{
lean_object* v___f_2562_; 
v___f_2562_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2562_, 0, v_inst_2561_);
return v___f_2562_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad(lean_object* v_00_u03b1_2563_, lean_object* v_00_u03b2_2564_, lean_object* v_cmp_2565_, lean_object* v_m_2566_, lean_object* v_inst_2567_){
_start:
{
lean_object* v___f_2568_; 
v___f_2568_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2568_, 0, v_inst_2567_);
return v___f_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___boxed(lean_object* v_00_u03b1_2569_, lean_object* v_00_u03b2_2570_, lean_object* v_cmp_2571_, lean_object* v_m_2572_, lean_object* v_inst_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Std_DTreeMap_instForInSigmaOfMonad(v_00_u03b1_2569_, v_00_u03b2_2570_, v_cmp_2571_, v_m_2572_, v_inst_2573_);
lean_dec_ref(v_cmp_2571_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2575_, lean_object* v_x_2576_, lean_object* v_k_2577_, lean_object* v_v_2578_){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v_k_2577_);
lean_ctor_set(v___x_2579_, 1, v_v_2578_);
v___x_2580_ = lean_apply_1(v_f_2575_, v___x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___redArg(lean_object* v_inst_2581_, lean_object* v_f_2582_, lean_object* v_t_2583_){
_start:
{
lean_object* v___f_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___f_2584_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2584_, 0, v_f_2582_);
v___x_2585_ = lean_box(0);
v___x_2586_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2581_, v___f_2584_, v___x_2585_, v_t_2583_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried(lean_object* v_00_u03b1_2587_, lean_object* v_cmp_2588_, lean_object* v_m_2589_, lean_object* v_inst_2590_, lean_object* v_00_u03b2_2591_, lean_object* v_f_2592_, lean_object* v_t_2593_){
_start:
{
lean_object* v___f_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___f_2594_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2594_, 0, v_f_2592_);
v___x_2595_ = lean_box(0);
v___x_2596_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2590_, v___f_2594_, v___x_2595_, v_t_2593_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2597_, lean_object* v_cmp_2598_, lean_object* v_m_2599_, lean_object* v_inst_2600_, lean_object* v_00_u03b2_2601_, lean_object* v_f_2602_, lean_object* v_t_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Std_DTreeMap_Const_forMUncurried(v_00_u03b1_2597_, v_cmp_2598_, v_m_2599_, v_inst_2600_, v_00_u03b2_2601_, v_f_2602_, v_t_2603_);
lean_dec_ref(v_cmp_2598_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2605_, lean_object* v_a_2606_, lean_object* v_b_2607_, lean_object* v_acc_2608_){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_a_2606_);
lean_ctor_set(v___x_2609_, 1, v_b_2607_);
v___x_2610_ = lean_apply_2(v_f_2605_, v___x_2609_, v_acc_2608_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___redArg(lean_object* v_inst_2611_, lean_object* v_f_2612_, lean_object* v_init_2613_, lean_object* v_t_2614_){
_start:
{
lean_object* v_toApplicative_2615_; lean_object* v_toBind_2616_; lean_object* v_toPure_2617_; lean_object* v___f_2618_; lean_object* v___x_2619_; lean_object* v___f_2620_; lean_object* v___x_2621_; 
v_toApplicative_2615_ = lean_ctor_get(v_inst_2611_, 0);
v_toBind_2616_ = lean_ctor_get(v_inst_2611_, 1);
lean_inc(v_toBind_2616_);
v_toPure_2617_ = lean_ctor_get(v_toApplicative_2615_, 1);
lean_inc(v_toPure_2617_);
v___f_2618_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2618_, 0, v_f_2612_);
v___x_2619_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2611_, v___f_2618_, v_init_2613_, v_t_2614_);
v___f_2620_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2620_, 0, v_toPure_2617_);
v___x_2621_ = lean_apply_4(v_toBind_2616_, lean_box(0), lean_box(0), v___x_2619_, v___f_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried(lean_object* v_00_u03b1_2622_, lean_object* v_cmp_2623_, lean_object* v_00_u03b4_2624_, lean_object* v_m_2625_, lean_object* v_inst_2626_, lean_object* v_00_u03b2_2627_, lean_object* v_f_2628_, lean_object* v_init_2629_, lean_object* v_t_2630_){
_start:
{
lean_object* v_toApplicative_2631_; lean_object* v_toBind_2632_; lean_object* v_toPure_2633_; lean_object* v___f_2634_; lean_object* v___x_2635_; lean_object* v___f_2636_; lean_object* v___x_2637_; 
v_toApplicative_2631_ = lean_ctor_get(v_inst_2626_, 0);
v_toBind_2632_ = lean_ctor_get(v_inst_2626_, 1);
lean_inc(v_toBind_2632_);
v_toPure_2633_ = lean_ctor_get(v_toApplicative_2631_, 1);
lean_inc(v_toPure_2633_);
v___f_2634_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2634_, 0, v_f_2628_);
v___x_2635_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2626_, v___f_2634_, v_init_2629_, v_t_2630_);
v___f_2636_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2636_, 0, v_toPure_2633_);
v___x_2637_ = lean_apply_4(v_toBind_2632_, lean_box(0), lean_box(0), v___x_2635_, v___f_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2638_, lean_object* v_cmp_2639_, lean_object* v_00_u03b4_2640_, lean_object* v_m_2641_, lean_object* v_inst_2642_, lean_object* v_00_u03b2_2643_, lean_object* v_f_2644_, lean_object* v_init_2645_, lean_object* v_t_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Std_DTreeMap_Const_forInUncurried(v_00_u03b1_2638_, v_cmp_2639_, v_00_u03b4_2640_, v_m_2641_, v_inst_2642_, v_00_u03b2_2643_, v_f_2644_, v_init_2645_, v_t_2646_);
lean_dec_ref(v_cmp_2639_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___lam__0(lean_object* v_p_2648_, lean_object* v___x_2649_, lean_object* v___x_2650_, lean_object* v_a_2651_, lean_object* v_b_2652_, lean_object* v_acc_2653_){
_start:
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = lean_apply_2(v_p_2648_, v_a_2651_, v_b_2652_);
v___x_2655_ = lean_unbox(v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2649_);
return v___x_2656_;
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec_ref(v___x_2649_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2654_);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
lean_ctor_set(v___x_2658_, 1, v___x_2650_);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
return v___x_2659_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2660_, lean_object* v___x_2661_, lean_object* v___x_2662_, lean_object* v_a_2663_, lean_object* v_b_2664_, lean_object* v_acc_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Std_DTreeMap_any___redArg___lam__0(v_p_2660_, v___x_2661_, v___x_2662_, v_a_2663_, v_b_2664_, v_acc_2665_);
lean_dec_ref(v_acc_2665_);
return v_res_2666_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_any___redArg(lean_object* v_t_2670_, lean_object* v_p_2671_){
_start:
{
lean_object* v___y_2673_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___f_2681_; lean_object* v___x_2682_; lean_object* v_a_2683_; 
v___x_2678_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2679_ = lean_box(0);
v___x_2680_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2681_ = lean_alloc_closure((void*)(l_Std_DTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2681_, 0, v_p_2671_);
lean_closure_set(v___f_2681_, 1, v___x_2680_);
lean_closure_set(v___f_2681_, 2, v___x_2679_);
v___x_2682_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2678_, v___f_2681_, v___x_2680_, v_t_2670_);
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___y_2673_ = v_a_2683_;
goto v___jp_2672_;
v___jp_2672_:
{
lean_object* v_fst_2674_; 
v_fst_2674_ = lean_ctor_get(v___y_2673_, 0);
lean_inc(v_fst_2674_);
lean_dec_ref(v___y_2673_);
if (lean_obj_tag(v_fst_2674_) == 0)
{
uint8_t v___x_2675_; 
v___x_2675_ = 0;
return v___x_2675_;
}
else
{
lean_object* v_val_2676_; uint8_t v___x_2677_; 
v_val_2676_ = lean_ctor_get(v_fst_2674_, 0);
lean_inc(v_val_2676_);
lean_dec_ref_known(v_fst_2674_, 1);
v___x_2677_ = lean_unbox(v_val_2676_);
lean_dec(v_val_2676_);
return v___x_2677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___boxed(lean_object* v_t_2684_, lean_object* v_p_2685_){
_start:
{
uint8_t v_res_2686_; lean_object* v_r_2687_; 
v_res_2686_ = l_Std_DTreeMap_any___redArg(v_t_2684_, v_p_2685_);
v_r_2687_ = lean_box(v_res_2686_);
return v_r_2687_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_any(lean_object* v_00_u03b1_2688_, lean_object* v_00_u03b2_2689_, lean_object* v_cmp_2690_, lean_object* v_t_2691_, lean_object* v_p_2692_){
_start:
{
lean_object* v___y_2694_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___f_2702_; lean_object* v___x_2703_; lean_object* v_a_2704_; 
v___x_2699_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2700_ = lean_box(0);
v___x_2701_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2702_ = lean_alloc_closure((void*)(l_Std_DTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2702_, 0, v_p_2692_);
lean_closure_set(v___f_2702_, 1, v___x_2701_);
lean_closure_set(v___f_2702_, 2, v___x_2700_);
v___x_2703_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2699_, v___f_2702_, v___x_2701_, v_t_2691_);
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___y_2694_ = v_a_2704_;
goto v___jp_2693_;
v___jp_2693_:
{
lean_object* v_fst_2695_; 
v_fst_2695_ = lean_ctor_get(v___y_2694_, 0);
lean_inc(v_fst_2695_);
lean_dec_ref(v___y_2694_);
if (lean_obj_tag(v_fst_2695_) == 0)
{
uint8_t v___x_2696_; 
v___x_2696_ = 0;
return v___x_2696_;
}
else
{
lean_object* v_val_2697_; uint8_t v___x_2698_; 
v_val_2697_ = lean_ctor_get(v_fst_2695_, 0);
lean_inc(v_val_2697_);
lean_dec_ref_known(v_fst_2695_, 1);
v___x_2698_ = lean_unbox(v_val_2697_);
lean_dec(v_val_2697_);
return v___x_2698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___boxed(lean_object* v_00_u03b1_2705_, lean_object* v_00_u03b2_2706_, lean_object* v_cmp_2707_, lean_object* v_t_2708_, lean_object* v_p_2709_){
_start:
{
uint8_t v_res_2710_; lean_object* v_r_2711_; 
v_res_2710_ = l_Std_DTreeMap_any(v_00_u03b1_2705_, v_00_u03b2_2706_, v_cmp_2707_, v_t_2708_, v_p_2709_);
lean_dec_ref(v_cmp_2707_);
v_r_2711_ = lean_box(v_res_2710_);
return v_r_2711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___lam__0(lean_object* v_p_2712_, lean_object* v___x_2713_, lean_object* v___x_2714_, lean_object* v_a_2715_, lean_object* v_b_2716_, lean_object* v_acc_2717_){
_start:
{
lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2718_ = lean_apply_2(v_p_2712_, v_a_2715_, v_b_2716_);
v___x_2719_ = lean_unbox(v___x_2718_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_dec_ref(v___x_2714_);
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2718_);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
lean_ctor_set(v___x_2721_, 1, v___x_2713_);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
else
{
lean_object* v___x_2723_; 
v___x_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2714_);
return v___x_2723_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_2724_, lean_object* v___x_2725_, lean_object* v___x_2726_, lean_object* v_a_2727_, lean_object* v_b_2728_, lean_object* v_acc_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Std_DTreeMap_all___redArg___lam__0(v_p_2724_, v___x_2725_, v___x_2726_, v_a_2727_, v_b_2728_, v_acc_2729_);
lean_dec_ref(v_acc_2729_);
return v_res_2730_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_all___redArg(lean_object* v_t_2731_, lean_object* v_p_2732_){
_start:
{
lean_object* v___y_2734_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___f_2742_; lean_object* v___x_2743_; lean_object* v_a_2744_; 
v___x_2739_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2740_ = lean_box(0);
v___x_2741_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2742_ = lean_alloc_closure((void*)(l_Std_DTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2742_, 0, v_p_2732_);
lean_closure_set(v___f_2742_, 1, v___x_2740_);
lean_closure_set(v___f_2742_, 2, v___x_2741_);
v___x_2743_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2739_, v___f_2742_, v___x_2741_, v_t_2731_);
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec(v___x_2743_);
v___y_2734_ = v_a_2744_;
goto v___jp_2733_;
v___jp_2733_:
{
lean_object* v_fst_2735_; 
v_fst_2735_ = lean_ctor_get(v___y_2734_, 0);
lean_inc(v_fst_2735_);
lean_dec_ref(v___y_2734_);
if (lean_obj_tag(v_fst_2735_) == 0)
{
uint8_t v___x_2736_; 
v___x_2736_ = 1;
return v___x_2736_;
}
else
{
lean_object* v_val_2737_; uint8_t v___x_2738_; 
v_val_2737_ = lean_ctor_get(v_fst_2735_, 0);
lean_inc(v_val_2737_);
lean_dec_ref_known(v_fst_2735_, 1);
v___x_2738_ = lean_unbox(v_val_2737_);
lean_dec(v_val_2737_);
return v___x_2738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___boxed(lean_object* v_t_2745_, lean_object* v_p_2746_){
_start:
{
uint8_t v_res_2747_; lean_object* v_r_2748_; 
v_res_2747_ = l_Std_DTreeMap_all___redArg(v_t_2745_, v_p_2746_);
v_r_2748_ = lean_box(v_res_2747_);
return v_r_2748_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_all(lean_object* v_00_u03b1_2749_, lean_object* v_00_u03b2_2750_, lean_object* v_cmp_2751_, lean_object* v_t_2752_, lean_object* v_p_2753_){
_start:
{
lean_object* v___y_2755_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___f_2763_; lean_object* v___x_2764_; lean_object* v_a_2765_; 
v___x_2760_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2761_ = lean_box(0);
v___x_2762_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2763_ = lean_alloc_closure((void*)(l_Std_DTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2763_, 0, v_p_2753_);
lean_closure_set(v___f_2763_, 1, v___x_2761_);
lean_closure_set(v___f_2763_, 2, v___x_2762_);
v___x_2764_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2760_, v___f_2763_, v___x_2762_, v_t_2752_);
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___y_2755_ = v_a_2765_;
goto v___jp_2754_;
v___jp_2754_:
{
lean_object* v_fst_2756_; 
v_fst_2756_ = lean_ctor_get(v___y_2755_, 0);
lean_inc(v_fst_2756_);
lean_dec_ref(v___y_2755_);
if (lean_obj_tag(v_fst_2756_) == 0)
{
uint8_t v___x_2757_; 
v___x_2757_ = 1;
return v___x_2757_;
}
else
{
lean_object* v_val_2758_; uint8_t v___x_2759_; 
v_val_2758_ = lean_ctor_get(v_fst_2756_, 0);
lean_inc(v_val_2758_);
lean_dec_ref_known(v_fst_2756_, 1);
v___x_2759_ = lean_unbox(v_val_2758_);
lean_dec(v_val_2758_);
return v___x_2759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___boxed(lean_object* v_00_u03b1_2766_, lean_object* v_00_u03b2_2767_, lean_object* v_cmp_2768_, lean_object* v_t_2769_, lean_object* v_p_2770_){
_start:
{
uint8_t v_res_2771_; lean_object* v_r_2772_; 
v_res_2771_ = l_Std_DTreeMap_all(v_00_u03b1_2766_, v_00_u03b2_2767_, v_cmp_2768_, v_t_2769_, v_p_2770_);
lean_dec_ref(v_cmp_2768_);
v_r_2772_ = lean_box(v_res_2771_);
return v_r_2772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg___lam__0(lean_object* v_x1_2773_, lean_object* v_x2_2774_, lean_object* v_x3_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2776_, 0, v_x1_2773_);
lean_ctor_set(v___x_2776_, 1, v_x3_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_2777_, lean_object* v_x2_2778_, lean_object* v_x3_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Std_DTreeMap_keys___redArg___lam__0(v_x1_2777_, v_x2_2778_, v_x3_2779_);
lean_dec(v_x2_2778_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg(lean_object* v_t_2782_){
_start:
{
lean_object* v___f_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___f_2783_ = ((lean_object*)(l_Std_DTreeMap_keys___redArg___closed__0));
v___x_2784_ = lean_box(0);
v___x_2785_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2786_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2785_, v___f_2783_, v___x_2784_, v_t_2782_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys(lean_object* v_00_u03b1_2787_, lean_object* v_00_u03b2_2788_, lean_object* v_cmp_2789_, lean_object* v_t_2790_){
_start:
{
lean_object* v___f_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___f_2791_ = ((lean_object*)(l_Std_DTreeMap_keys___redArg___closed__0));
v___x_2792_ = lean_box(0);
v___x_2793_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2794_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2793_, v___f_2791_, v___x_2792_, v_t_2790_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___boxed(lean_object* v_00_u03b1_2795_, lean_object* v_00_u03b2_2796_, lean_object* v_cmp_2797_, lean_object* v_t_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Std_DTreeMap_keys(v_00_u03b1_2795_, v_00_u03b2_2796_, v_cmp_2797_, v_t_2798_);
lean_dec_ref(v_cmp_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg___lam__0(lean_object* v_l_2800_, lean_object* v_k_2801_, lean_object* v_x_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_array_push(v_l_2800_, v_k_2801_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_2804_, lean_object* v_k_2805_, lean_object* v_x_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Std_DTreeMap_keysArray___redArg___lam__0(v_l_2804_, v_k_2805_, v_x_2806_);
lean_dec(v_x_2806_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg(lean_object* v_t_2809_){
_start:
{
lean_object* v___f_2810_; lean_object* v___y_2812_; 
v___f_2810_ = ((lean_object*)(l_Std_DTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2809_) == 0)
{
lean_object* v_size_2815_; 
v_size_2815_ = lean_ctor_get(v_t_2809_, 0);
lean_inc(v_size_2815_);
v___y_2812_ = v_size_2815_;
goto v___jp_2811_;
}
else
{
lean_object* v___x_2816_; 
v___x_2816_ = lean_unsigned_to_nat(0u);
v___y_2812_ = v___x_2816_;
goto v___jp_2811_;
}
v___jp_2811_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_mk_empty_array_with_capacity(v___y_2812_);
lean_dec(v___y_2812_);
v___x_2814_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2810_, v___x_2813_, v_t_2809_);
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray(lean_object* v_00_u03b1_2817_, lean_object* v_00_u03b2_2818_, lean_object* v_cmp_2819_, lean_object* v_t_2820_){
_start:
{
lean_object* v___f_2821_; lean_object* v___y_2823_; 
v___f_2821_ = ((lean_object*)(l_Std_DTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2820_) == 0)
{
lean_object* v_size_2826_; 
v_size_2826_ = lean_ctor_get(v_t_2820_, 0);
lean_inc(v_size_2826_);
v___y_2823_ = v_size_2826_;
goto v___jp_2822_;
}
else
{
lean_object* v___x_2827_; 
v___x_2827_ = lean_unsigned_to_nat(0u);
v___y_2823_ = v___x_2827_;
goto v___jp_2822_;
}
v___jp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_mk_empty_array_with_capacity(v___y_2823_);
lean_dec(v___y_2823_);
v___x_2825_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2821_, v___x_2824_, v_t_2820_);
return v___x_2825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___boxed(lean_object* v_00_u03b1_2828_, lean_object* v_00_u03b2_2829_, lean_object* v_cmp_2830_, lean_object* v_t_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Std_DTreeMap_keysArray(v_00_u03b1_2828_, v_00_u03b2_2829_, v_cmp_2830_, v_t_2831_);
lean_dec_ref(v_cmp_2830_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg___lam__0(lean_object* v_x1_2833_, lean_object* v_x2_2834_, lean_object* v_x3_2835_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2836_, 0, v_x2_2834_);
lean_ctor_set(v___x_2836_, 1, v_x3_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_2837_, lean_object* v_x2_2838_, lean_object* v_x3_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Std_DTreeMap_values___redArg___lam__0(v_x1_2837_, v_x2_2838_, v_x3_2839_);
lean_dec(v_x1_2837_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg(lean_object* v_t_2842_){
_start:
{
lean_object* v___f_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___f_2843_ = ((lean_object*)(l_Std_DTreeMap_values___redArg___closed__0));
v___x_2844_ = lean_box(0);
v___x_2845_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2846_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2845_, v___f_2843_, v___x_2844_, v_t_2842_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values(lean_object* v_00_u03b1_2847_, lean_object* v_cmp_2848_, lean_object* v_00_u03b2_2849_, lean_object* v_t_2850_){
_start:
{
lean_object* v___f_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___f_2851_ = ((lean_object*)(l_Std_DTreeMap_values___redArg___closed__0));
v___x_2852_ = lean_box(0);
v___x_2853_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2854_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2853_, v___f_2851_, v___x_2852_, v_t_2850_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___boxed(lean_object* v_00_u03b1_2855_, lean_object* v_cmp_2856_, lean_object* v_00_u03b2_2857_, lean_object* v_t_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Std_DTreeMap_values(v_00_u03b1_2855_, v_cmp_2856_, v_00_u03b2_2857_, v_t_2858_);
lean_dec_ref(v_cmp_2856_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_2860_, lean_object* v_x_2861_, lean_object* v_v_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = lean_array_push(v_l_2860_, v_v_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2864_, lean_object* v_x_2865_, lean_object* v_v_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Std_DTreeMap_valuesArray___redArg___lam__0(v_l_2864_, v_x_2865_, v_v_2866_);
lean_dec(v_x_2865_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg(lean_object* v_t_2869_){
_start:
{
lean_object* v___f_2870_; lean_object* v___y_2872_; 
v___f_2870_ = ((lean_object*)(l_Std_DTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2869_) == 0)
{
lean_object* v_size_2875_; 
v_size_2875_ = lean_ctor_get(v_t_2869_, 0);
lean_inc(v_size_2875_);
v___y_2872_ = v_size_2875_;
goto v___jp_2871_;
}
else
{
lean_object* v___x_2876_; 
v___x_2876_ = lean_unsigned_to_nat(0u);
v___y_2872_ = v___x_2876_;
goto v___jp_2871_;
}
v___jp_2871_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = lean_mk_empty_array_with_capacity(v___y_2872_);
lean_dec(v___y_2872_);
v___x_2874_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2870_, v___x_2873_, v_t_2869_);
return v___x_2874_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray(lean_object* v_00_u03b1_2877_, lean_object* v_cmp_2878_, lean_object* v_00_u03b2_2879_, lean_object* v_t_2880_){
_start:
{
lean_object* v___f_2881_; lean_object* v___y_2883_; 
v___f_2881_ = ((lean_object*)(l_Std_DTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2880_) == 0)
{
lean_object* v_size_2886_; 
v_size_2886_ = lean_ctor_get(v_t_2880_, 0);
lean_inc(v_size_2886_);
v___y_2883_ = v_size_2886_;
goto v___jp_2882_;
}
else
{
lean_object* v___x_2887_; 
v___x_2887_ = lean_unsigned_to_nat(0u);
v___y_2883_ = v___x_2887_;
goto v___jp_2882_;
}
v___jp_2882_:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_mk_empty_array_with_capacity(v___y_2883_);
lean_dec(v___y_2883_);
v___x_2885_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2881_, v___x_2884_, v_t_2880_);
return v___x_2885_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_2888_, lean_object* v_cmp_2889_, lean_object* v_00_u03b2_2890_, lean_object* v_t_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Std_DTreeMap_valuesArray(v_00_u03b1_2888_, v_cmp_2889_, v_00_u03b2_2890_, v_t_2891_);
lean_dec_ref(v_cmp_2889_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___redArg___lam__0(lean_object* v_x1_2893_, lean_object* v_x2_2894_, lean_object* v_x3_2895_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v_x1_2893_);
lean_ctor_set(v___x_2896_, 1, v_x2_2894_);
v___x_2897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
lean_ctor_set(v___x_2897_, 1, v_x3_2895_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___redArg(lean_object* v_t_2899_){
_start:
{
lean_object* v___f_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___f_2900_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_2901_ = lean_box(0);
v___x_2902_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2903_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2902_, v___f_2900_, v___x_2901_, v_t_2899_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList(lean_object* v_00_u03b1_2904_, lean_object* v_00_u03b2_2905_, lean_object* v_cmp_2906_, lean_object* v_t_2907_){
_start:
{
lean_object* v___f_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___f_2908_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_2909_ = lean_box(0);
v___x_2910_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2911_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2910_, v___f_2908_, v___x_2909_, v_t_2907_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___boxed(lean_object* v_00_u03b1_2912_, lean_object* v_00_u03b2_2913_, lean_object* v_cmp_2914_, lean_object* v_t_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Std_DTreeMap_toList(v_00_u03b1_2912_, v_00_u03b2_2913_, v_cmp_2914_, v_t_2915_);
lean_dec_ref(v_cmp_2914_);
return v_res_2916_;
}
}
static lean_object* _init_l_Std_DTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_2918_, lean_object* v_a_2919_, lean_object* v_x_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v_fst_2922_; lean_object* v_snd_2923_; lean_object* v_r_2924_; lean_object* v___x_2925_; 
v_fst_2922_ = lean_ctor_get(v_a_2919_, 0);
lean_inc(v_fst_2922_);
v_snd_2923_ = lean_ctor_get(v_a_2919_, 1);
lean_inc(v_snd_2923_);
lean_dec_ref(v_a_2919_);
v_r_2924_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2918_, v_fst_2922_, v_snd_2923_, v___y_2921_);
v___x_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2925_, 0, v_r_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg(lean_object* v_l_2926_, lean_object* v_cmp_2927_){
_start:
{
lean_object* v___f_2928_; lean_object* v___x_2929_; lean_object* v_r_2930_; lean_object* v___x_2931_; 
v___f_2928_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2928_, 0, v_cmp_2927_);
v___x_2929_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2930_ = lean_box(1);
v___x_2931_ = l_List_forIn_x27_loop___redArg(v___x_2929_, v___f_2928_, v_l_2926_, v_r_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg___boxed(lean_object* v_l_2932_, lean_object* v_cmp_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Std_DTreeMap_ofList___redArg(v_l_2932_, v_cmp_2933_);
lean_dec(v_l_2932_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList(lean_object* v_00_u03b1_2935_, lean_object* v_00_u03b2_2936_, lean_object* v_l_2937_, lean_object* v_cmp_2938_){
_start:
{
lean_object* v___f_2939_; lean_object* v___x_2940_; lean_object* v_r_2941_; lean_object* v___x_2942_; 
v___f_2939_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2939_, 0, v_cmp_2938_);
v___x_2940_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2941_ = lean_box(1);
v___x_2942_ = l_List_forIn_x27_loop___redArg(v___x_2940_, v___f_2939_, v_l_2937_, v_r_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___boxed(lean_object* v_00_u03b1_2943_, lean_object* v_00_u03b2_2944_, lean_object* v_l_2945_, lean_object* v_cmp_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Std_DTreeMap_ofList(v_00_u03b1_2943_, v_00_u03b2_2944_, v_l_2945_, v_cmp_2946_);
lean_dec(v_l_2945_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___redArg___lam__0(lean_object* v_l_2948_, lean_object* v_k_2949_, lean_object* v_v_2950_){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v_k_2949_);
lean_ctor_set(v___x_2951_, 1, v_v_2950_);
v___x_2952_ = lean_array_push(v_l_2948_, v___x_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___redArg(lean_object* v_t_2954_){
_start:
{
lean_object* v___f_2955_; lean_object* v___y_2957_; 
v___f_2955_ = ((lean_object*)(l_Std_DTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2954_) == 0)
{
lean_object* v_size_2960_; 
v_size_2960_ = lean_ctor_get(v_t_2954_, 0);
lean_inc(v_size_2960_);
v___y_2957_ = v_size_2960_;
goto v___jp_2956_;
}
else
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_unsigned_to_nat(0u);
v___y_2957_ = v___x_2961_;
goto v___jp_2956_;
}
v___jp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = lean_mk_empty_array_with_capacity(v___y_2957_);
lean_dec(v___y_2957_);
v___x_2959_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2955_, v___x_2958_, v_t_2954_);
return v___x_2959_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray(lean_object* v_00_u03b1_2962_, lean_object* v_00_u03b2_2963_, lean_object* v_cmp_2964_, lean_object* v_t_2965_){
_start:
{
lean_object* v___f_2966_; lean_object* v___y_2968_; 
v___f_2966_ = ((lean_object*)(l_Std_DTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2965_) == 0)
{
lean_object* v_size_2971_; 
v_size_2971_ = lean_ctor_get(v_t_2965_, 0);
lean_inc(v_size_2971_);
v___y_2968_ = v_size_2971_;
goto v___jp_2967_;
}
else
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_unsigned_to_nat(0u);
v___y_2968_ = v___x_2972_;
goto v___jp_2967_;
}
v___jp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_mk_empty_array_with_capacity(v___y_2968_);
lean_dec(v___y_2968_);
v___x_2970_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2966_, v___x_2969_, v_t_2965_);
return v___x_2970_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___boxed(lean_object* v_00_u03b1_2973_, lean_object* v_00_u03b2_2974_, lean_object* v_cmp_2975_, lean_object* v_t_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Std_DTreeMap_toArray(v_00_u03b1_2973_, v_00_u03b2_2974_, v_cmp_2975_, v_t_2976_);
lean_dec_ref(v_cmp_2975_);
return v_res_2977_;
}
}
static lean_object* _init_l_Std_DTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray___redArg(lean_object* v_a_2979_, lean_object* v_cmp_2980_){
_start:
{
lean_object* v___f_2981_; lean_object* v___x_2982_; lean_object* v_r_2983_; size_t v_sz_2984_; size_t v___x_2985_; lean_object* v___x_2986_; 
v___f_2981_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2981_, 0, v_cmp_2980_);
v___x_2982_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2983_ = lean_box(1);
v_sz_2984_ = lean_array_size(v_a_2979_);
v___x_2985_ = ((size_t)0ULL);
v___x_2986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2982_, v_a_2979_, v___f_2981_, v_sz_2984_, v___x_2985_, v_r_2983_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray(lean_object* v_00_u03b1_2987_, lean_object* v_00_u03b2_2988_, lean_object* v_a_2989_, lean_object* v_cmp_2990_){
_start:
{
lean_object* v___f_2991_; lean_object* v___x_2992_; lean_object* v_r_2993_; size_t v_sz_2994_; size_t v___x_2995_; lean_object* v___x_2996_; 
v___f_2991_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2991_, 0, v_cmp_2990_);
v___x_2992_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2993_ = lean_box(1);
v_sz_2994_ = lean_array_size(v_a_2989_);
v___x_2995_ = ((size_t)0ULL);
v___x_2996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2992_, v_a_2989_, v___f_2991_, v_sz_2994_, v___x_2995_, v_r_2993_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_modify___redArg(lean_object* v_cmp_2997_, lean_object* v_t_2998_, lean_object* v_a_2999_, lean_object* v_f_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2997_, v_a_2999_, v_f_3000_, v_t_2998_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_modify(lean_object* v_00_u03b1_3002_, lean_object* v_00_u03b2_3003_, lean_object* v_cmp_3004_, lean_object* v_inst_3005_, lean_object* v_t_3006_, lean_object* v_a_3007_, lean_object* v_f_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3004_, v_a_3007_, v_f_3008_, v_t_3006_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_alter___redArg(lean_object* v_cmp_3010_, lean_object* v_t_3011_, lean_object* v_a_3012_, lean_object* v_f_3013_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3010_, v_a_3012_, v_f_3013_, v_t_3011_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_alter(lean_object* v_00_u03b1_3015_, lean_object* v_00_u03b2_3016_, lean_object* v_cmp_3017_, lean_object* v_inst_3018_, lean_object* v_t_3019_, lean_object* v_a_3020_, lean_object* v_f_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3017_, v_a_3020_, v_f_3021_, v_t_3019_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_3023_, lean_object* v_mergeFn_3024_, lean_object* v_a_3025_, lean_object* v_x_3026_){
_start:
{
if (lean_obj_tag(v_x_3026_) == 0)
{
lean_object* v___x_3027_; 
lean_dec(v_a_3025_);
lean_dec(v_mergeFn_3024_);
v___x_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3027_, 0, v_b_u2082_3023_);
return v___x_3027_;
}
else
{
lean_object* v_val_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3036_; 
v_val_3028_ = lean_ctor_get(v_x_3026_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v_x_3026_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3030_ = v_x_3026_;
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_val_3028_);
lean_dec(v_x_3026_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3032_ = lean_apply_3(v_mergeFn_3024_, v_a_3025_, v_val_3028_, v_b_u2082_3023_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3032_);
v___x_3034_ = v___x_3030_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3037_, lean_object* v_cmp_3038_, lean_object* v_t_3039_, lean_object* v_a_3040_, lean_object* v_b_u2082_3041_){
_start:
{
lean_object* v___f_3042_; lean_object* v___x_3043_; 
lean_inc(v_a_3040_);
v___f_3042_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3042_, 0, v_b_u2082_3041_);
lean_closure_set(v___f_3042_, 1, v_mergeFn_3037_);
lean_closure_set(v___f_3042_, 2, v_a_3040_);
v___x_3043_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3038_, v_a_3040_, v___f_3042_, v_t_3039_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg(lean_object* v_cmp_3044_, lean_object* v_mergeFn_3045_, lean_object* v_t_u2081_3046_, lean_object* v_t_u2082_3047_){
_start:
{
lean_object* v___f_3048_; lean_object* v___x_3049_; 
v___f_3048_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3048_, 0, v_mergeFn_3045_);
lean_closure_set(v___f_3048_, 1, v_cmp_3044_);
v___x_3049_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3048_, v_t_u2081_3046_, v_t_u2082_3047_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith(lean_object* v_00_u03b1_3050_, lean_object* v_00_u03b2_3051_, lean_object* v_cmp_3052_, lean_object* v_inst_3053_, lean_object* v_mergeFn_3054_, lean_object* v_t_u2081_3055_, lean_object* v_t_u2082_3056_){
_start:
{
lean_object* v___f_3057_; lean_object* v___x_3058_; 
v___f_3057_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3057_, 0, v_mergeFn_3054_);
lean_closure_set(v___f_3057_, 1, v_cmp_3052_);
v___x_3058_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3057_, v_t_u2081_3055_, v_t_u2082_3056_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___redArg___lam__0(lean_object* v_x1_3059_, lean_object* v_x2_3060_, lean_object* v_x3_3061_){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3062_, 0, v_x1_3059_);
lean_ctor_set(v___x_3062_, 1, v_x2_3060_);
v___x_3063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set(v___x_3063_, 1, v_x3_3061_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___redArg(lean_object* v_t_3065_){
_start:
{
lean_object* v___f_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___f_3066_ = ((lean_object*)(l_Std_DTreeMap_Const_toList___redArg___closed__0));
v___x_3067_ = lean_box(0);
v___x_3068_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_3069_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3068_, v___f_3066_, v___x_3067_, v_t_3065_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList(lean_object* v_00_u03b1_3070_, lean_object* v_cmp_3071_, lean_object* v_00_u03b2_3072_, lean_object* v_t_3073_){
_start:
{
lean_object* v___f_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___f_3074_ = ((lean_object*)(l_Std_DTreeMap_Const_toList___redArg___closed__0));
v___x_3075_ = lean_box(0);
v___x_3076_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_3077_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3076_, v___f_3074_, v___x_3075_, v_t_3073_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___boxed(lean_object* v_00_u03b1_3078_, lean_object* v_cmp_3079_, lean_object* v_00_u03b2_3080_, lean_object* v_t_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Std_DTreeMap_Const_toList(v_00_u03b1_3078_, v_cmp_3079_, v_00_u03b2_3080_, v_t_3081_);
lean_dec_ref(v_cmp_3079_);
return v_res_3082_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg___lam__0(lean_object* v_cmp_3084_, lean_object* v_a_3085_, lean_object* v_x_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_fst_3088_; lean_object* v_snd_3089_; lean_object* v_r_3090_; lean_object* v___x_3091_; 
v_fst_3088_ = lean_ctor_get(v_a_3085_, 0);
lean_inc(v_fst_3088_);
v_snd_3089_ = lean_ctor_get(v_a_3085_, 1);
lean_inc(v_snd_3089_);
lean_dec_ref(v_a_3085_);
v_r_3090_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3084_, v_fst_3088_, v_snd_3089_, v___y_3087_);
v___x_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3091_, 0, v_r_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg(lean_object* v_l_3092_, lean_object* v_cmp_3093_){
_start:
{
lean_object* v___f_3094_; lean_object* v___x_3095_; lean_object* v_r_3096_; lean_object* v___x_3097_; 
v___f_3094_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3094_, 0, v_cmp_3093_);
v___x_3095_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3096_ = lean_box(1);
v___x_3097_ = l_List_forIn_x27_loop___redArg(v___x_3095_, v___f_3094_, v_l_3092_, v_r_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg___boxed(lean_object* v_l_3098_, lean_object* v_cmp_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_Std_DTreeMap_Const_ofList___redArg(v_l_3098_, v_cmp_3099_);
lean_dec(v_l_3098_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList(lean_object* v_00_u03b1_3101_, lean_object* v_00_u03b2_3102_, lean_object* v_l_3103_, lean_object* v_cmp_3104_){
_start:
{
lean_object* v___f_3105_; lean_object* v___x_3106_; lean_object* v_r_3107_; lean_object* v___x_3108_; 
v___f_3105_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3105_, 0, v_cmp_3104_);
v___x_3106_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3107_ = lean_box(1);
v___x_3108_ = l_List_forIn_x27_loop___redArg(v___x_3106_, v___f_3105_, v_l_3103_, v_r_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___boxed(lean_object* v_00_u03b1_3109_, lean_object* v_00_u03b2_3110_, lean_object* v_l_3111_, lean_object* v_cmp_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Std_DTreeMap_Const_ofList(v_00_u03b1_3109_, v_00_u03b2_3110_, v_l_3111_, v_cmp_3112_);
lean_dec(v_l_3111_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___redArg___lam__0(lean_object* v_acc_3114_, lean_object* v_k_3115_, lean_object* v_v_3116_){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3117_, 0, v_k_3115_);
lean_ctor_set(v___x_3117_, 1, v_v_3116_);
v___x_3118_ = lean_array_push(v_acc_3114_, v___x_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___redArg(lean_object* v_t_3122_){
_start:
{
lean_object* v___f_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___f_3123_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__0));
v___x_3124_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__1));
v___x_3125_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3123_, v___x_3124_, v_t_3122_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray(lean_object* v_00_u03b1_3126_, lean_object* v_cmp_3127_, lean_object* v_00_u03b2_3128_, lean_object* v_t_3129_){
_start:
{
lean_object* v___f_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___f_3130_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__0));
v___x_3131_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__1));
v___x_3132_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3130_, v___x_3131_, v_t_3129_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___boxed(lean_object* v_00_u03b1_3133_, lean_object* v_cmp_3134_, lean_object* v_00_u03b2_3135_, lean_object* v_t_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Std_DTreeMap_Const_toArray(v_00_u03b1_3133_, v_cmp_3134_, v_00_u03b2_3135_, v_t_3136_);
lean_dec_ref(v_cmp_3134_);
return v_res_3137_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray___redArg(lean_object* v_a_3139_, lean_object* v_cmp_3140_){
_start:
{
lean_object* v___f_3141_; lean_object* v___x_3142_; lean_object* v_r_3143_; size_t v_sz_3144_; size_t v___x_3145_; lean_object* v___x_3146_; 
v___f_3141_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3141_, 0, v_cmp_3140_);
v___x_3142_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3143_ = lean_box(1);
v_sz_3144_ = lean_array_size(v_a_3139_);
v___x_3145_ = ((size_t)0ULL);
v___x_3146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3142_, v_a_3139_, v___f_3141_, v_sz_3144_, v___x_3145_, v_r_3143_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray(lean_object* v_00_u03b1_3147_, lean_object* v_00_u03b2_3148_, lean_object* v_a_3149_, lean_object* v_cmp_3150_){
_start:
{
lean_object* v___f_3151_; lean_object* v___x_3152_; lean_object* v_r_3153_; size_t v_sz_3154_; size_t v___x_3155_; lean_object* v___x_3156_; 
v___f_3151_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3151_, 0, v_cmp_3150_);
v___x_3152_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3153_ = lean_box(1);
v_sz_3154_ = lean_array_size(v_a_3149_);
v___x_3155_ = ((size_t)0ULL);
v___x_3156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3152_, v_a_3149_, v___f_3151_, v_sz_3154_, v___x_3155_, v_r_3153_);
return v___x_3156_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_3158_, lean_object* v_a_3159_, lean_object* v_x_3160_, lean_object* v___y_3161_){
_start:
{
uint8_t v___x_3162_; 
lean_inc(v___y_3161_);
lean_inc(v_a_3159_);
lean_inc_ref(v_cmp_3158_);
v___x_3162_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3158_, v_a_3159_, v___y_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3163_ = lean_box(0);
v___x_3164_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3158_, v_a_3159_, v___x_3163_, v___y_3161_);
v___x_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
return v___x_3165_;
}
else
{
lean_object* v___x_3166_; 
lean_dec(v_a_3159_);
lean_dec_ref(v_cmp_3158_);
v___x_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___y_3161_);
return v___x_3166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg(lean_object* v_l_3167_, lean_object* v_cmp_3168_){
_start:
{
lean_object* v___f_3169_; lean_object* v___x_3170_; lean_object* v_r_3171_; lean_object* v___x_3172_; 
v___f_3169_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3169_, 0, v_cmp_3168_);
v___x_3170_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3171_ = lean_box(1);
v___x_3172_ = l_List_forIn_x27_loop___redArg(v___x_3170_, v___f_3169_, v_l_3167_, v_r_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg___boxed(lean_object* v_l_3173_, lean_object* v_cmp_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Std_DTreeMap_Const_unitOfList___redArg(v_l_3173_, v_cmp_3174_);
lean_dec(v_l_3173_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList(lean_object* v_00_u03b1_3176_, lean_object* v_l_3177_, lean_object* v_cmp_3178_){
_start:
{
lean_object* v___f_3179_; lean_object* v___x_3180_; lean_object* v_r_3181_; lean_object* v___x_3182_; 
v___f_3179_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3179_, 0, v_cmp_3178_);
v___x_3180_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3181_ = lean_box(1);
v___x_3182_ = l_List_forIn_x27_loop___redArg(v___x_3180_, v___f_3179_, v_l_3177_, v_r_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___boxed(lean_object* v_00_u03b1_3183_, lean_object* v_l_3184_, lean_object* v_cmp_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Std_DTreeMap_Const_unitOfList(v_00_u03b1_3183_, v_l_3184_, v_cmp_3185_);
lean_dec(v_l_3184_);
return v_res_3186_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray___redArg(lean_object* v_a_3188_, lean_object* v_cmp_3189_){
_start:
{
lean_object* v___f_3190_; lean_object* v___x_3191_; lean_object* v_r_3192_; size_t v_sz_3193_; size_t v___x_3194_; lean_object* v___x_3195_; 
v___f_3190_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3190_, 0, v_cmp_3189_);
v___x_3191_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3192_ = lean_box(1);
v_sz_3193_ = lean_array_size(v_a_3188_);
v___x_3194_ = ((size_t)0ULL);
v___x_3195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3191_, v_a_3188_, v___f_3190_, v_sz_3193_, v___x_3194_, v_r_3192_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray(lean_object* v_00_u03b1_3196_, lean_object* v_a_3197_, lean_object* v_cmp_3198_){
_start:
{
lean_object* v___f_3199_; lean_object* v___x_3200_; lean_object* v_r_3201_; size_t v_sz_3202_; size_t v___x_3203_; lean_object* v___x_3204_; 
v___f_3199_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3199_, 0, v_cmp_3198_);
v___x_3200_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3201_ = lean_box(1);
v_sz_3202_ = lean_array_size(v_a_3197_);
v___x_3203_ = ((size_t)0ULL);
v___x_3204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3200_, v_a_3197_, v___f_3199_, v_sz_3202_, v___x_3203_, v_r_3201_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_modify___redArg(lean_object* v_cmp_3205_, lean_object* v_t_3206_, lean_object* v_a_3207_, lean_object* v_f_3208_){
_start:
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3205_, v_a_3207_, v_f_3208_, v_t_3206_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_modify(lean_object* v_00_u03b1_3210_, lean_object* v_cmp_3211_, lean_object* v_00_u03b2_3212_, lean_object* v_t_3213_, lean_object* v_a_3214_, lean_object* v_f_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3211_, v_a_3214_, v_f_3215_, v_t_3213_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_alter___redArg(lean_object* v_cmp_3217_, lean_object* v_t_3218_, lean_object* v_a_3219_, lean_object* v_f_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3217_, v_a_3219_, v_f_3220_, v_t_3218_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_alter(lean_object* v_00_u03b1_3222_, lean_object* v_cmp_3223_, lean_object* v_00_u03b2_3224_, lean_object* v_t_3225_, lean_object* v_a_3226_, lean_object* v_f_3227_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3223_, v_a_3226_, v_f_3227_, v_t_3225_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3229_, lean_object* v_cmp_3230_, lean_object* v_t_3231_, lean_object* v_a_3232_, lean_object* v_b_u2082_3233_){
_start:
{
lean_object* v___f_3234_; lean_object* v___x_3235_; 
lean_inc(v_a_3232_);
v___f_3234_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3234_, 0, v_b_u2082_3233_);
lean_closure_set(v___f_3234_, 1, v_mergeFn_3229_);
lean_closure_set(v___f_3234_, 2, v_a_3232_);
v___x_3235_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3230_, v_a_3232_, v___f_3234_, v_t_3231_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith___redArg(lean_object* v_cmp_3236_, lean_object* v_mergeFn_3237_, lean_object* v_t_u2081_3238_, lean_object* v_t_u2082_3239_){
_start:
{
lean_object* v___f_3240_; lean_object* v___x_3241_; 
v___f_3240_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3240_, 0, v_mergeFn_3237_);
lean_closure_set(v___f_3240_, 1, v_cmp_3236_);
v___x_3241_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3240_, v_t_u2081_3238_, v_t_u2082_3239_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith(lean_object* v_00_u03b1_3242_, lean_object* v_cmp_3243_, lean_object* v_00_u03b2_3244_, lean_object* v_mergeFn_3245_, lean_object* v_t_u2081_3246_, lean_object* v_t_u2082_3247_){
_start:
{
lean_object* v___f_3248_; lean_object* v___x_3249_; 
v___f_3248_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3248_, 0, v_mergeFn_3245_);
lean_closure_set(v___f_3248_, 1, v_cmp_3243_);
v___x_3249_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3248_, v_t_u2081_3246_, v_t_u2082_3247_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_3250_, lean_object* v_x_3251_, lean_object* v_____s_3252_){
_start:
{
lean_object* v_fst_3253_; lean_object* v_snd_3254_; lean_object* v_r_3255_; lean_object* v___x_3256_; 
v_fst_3253_ = lean_ctor_get(v_x_3251_, 0);
lean_inc(v_fst_3253_);
v_snd_3254_ = lean_ctor_get(v_x_3251_, 1);
lean_inc(v_snd_3254_);
lean_dec_ref(v_x_3251_);
v_r_3255_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3250_, v_fst_3253_, v_snd_3254_, v_____s_3252_);
v___x_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3256_, 0, v_r_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany___redArg(lean_object* v_cmp_3257_, lean_object* v_inst_3258_, lean_object* v_t_3259_, lean_object* v_l_3260_){
_start:
{
lean_object* v___f_3261_; lean_object* v___x_3262_; 
v___f_3261_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3261_, 0, v_cmp_3257_);
v___x_3262_ = lean_apply_4(v_inst_3258_, lean_box(0), v_l_3260_, v_t_3259_, v___f_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany(lean_object* v_00_u03b1_3263_, lean_object* v_00_u03b2_3264_, lean_object* v_cmp_3265_, lean_object* v_00_u03c1_3266_, lean_object* v_inst_3267_, lean_object* v_t_3268_, lean_object* v_l_3269_){
_start:
{
lean_object* v___f_3270_; lean_object* v___x_3271_; 
v___f_3270_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3270_, 0, v_cmp_3265_);
v___x_3271_ = lean_apply_4(v_inst_3267_, lean_box(0), v_l_3269_, v_t_3268_, v___f_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew___redArg___lam__0(lean_object* v_cmp_3272_, lean_object* v_x_3273_, lean_object* v_____s_3274_){
_start:
{
lean_object* v_fst_3275_; lean_object* v_snd_3276_; uint8_t v___x_3277_; 
v_fst_3275_ = lean_ctor_get(v_x_3273_, 0);
lean_inc_n(v_fst_3275_, 2);
v_snd_3276_ = lean_ctor_get(v_x_3273_, 1);
lean_inc(v_snd_3276_);
lean_dec_ref(v_x_3273_);
lean_inc(v_____s_3274_);
lean_inc_ref(v_cmp_3272_);
v___x_3277_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3272_, v_fst_3275_, v_____s_3274_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3272_, v_fst_3275_, v_snd_3276_, v_____s_3274_);
v___x_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
return v___x_3279_;
}
else
{
lean_object* v___x_3280_; 
lean_dec(v_snd_3276_);
lean_dec(v_fst_3275_);
lean_dec_ref(v_cmp_3272_);
v___x_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3280_, 0, v_____s_3274_);
return v___x_3280_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew___redArg(lean_object* v_cmp_3281_, lean_object* v_inst_3282_, lean_object* v_t_3283_, lean_object* v_l_3284_){
_start:
{
lean_object* v___f_3285_; lean_object* v___x_3286_; 
v___f_3285_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertManyIfNew___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3285_, 0, v_cmp_3281_);
v___x_3286_ = lean_apply_4(v_inst_3282_, lean_box(0), v_l_3284_, v_t_3283_, v___f_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew(lean_object* v_00_u03b1_3287_, lean_object* v_00_u03b2_3288_, lean_object* v_cmp_3289_, lean_object* v_00_u03c1_3290_, lean_object* v_inst_3291_, lean_object* v_t_3292_, lean_object* v_l_3293_){
_start:
{
lean_object* v___f_3294_; lean_object* v___x_3295_; 
v___f_3294_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertManyIfNew___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3294_, 0, v_cmp_3289_);
v___x_3295_ = lean_apply_4(v_inst_3291_, lean_box(0), v_l_3293_, v_t_3292_, v___f_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(lean_object* v_cmp_3296_, lean_object* v_k_3297_, lean_object* v_v_3298_, lean_object* v_t_3299_){
_start:
{
if (lean_obj_tag(v_t_3299_) == 0)
{
lean_object* v_size_3300_; lean_object* v_k_3301_; lean_object* v_v_3302_; lean_object* v_l_3303_; lean_object* v_r_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3585_; 
v_size_3300_ = lean_ctor_get(v_t_3299_, 0);
v_k_3301_ = lean_ctor_get(v_t_3299_, 1);
v_v_3302_ = lean_ctor_get(v_t_3299_, 2);
v_l_3303_ = lean_ctor_get(v_t_3299_, 3);
v_r_3304_ = lean_ctor_get(v_t_3299_, 4);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_t_3299_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3306_ = v_t_3299_;
v_isShared_3307_ = v_isSharedCheck_3585_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_r_3304_);
lean_inc(v_l_3303_);
lean_inc(v_v_3302_);
lean_inc(v_k_3301_);
lean_inc(v_size_3300_);
lean_dec(v_t_3299_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3585_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; uint8_t v___x_3309_; 
lean_inc_ref(v_cmp_3296_);
lean_inc(v_k_3301_);
lean_inc(v_k_3297_);
v___x_3308_ = lean_apply_2(v_cmp_3296_, v_k_3297_, v_k_3301_);
v___x_3309_ = lean_unbox(v___x_3308_);
switch(v___x_3309_)
{
case 0:
{
lean_object* v_impl_3310_; lean_object* v___x_3311_; 
lean_dec(v_size_3300_);
v_impl_3310_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3296_, v_k_3297_, v_v_3298_, v_l_3303_);
v___x_3311_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3304_) == 0)
{
lean_object* v_size_3312_; lean_object* v_size_3313_; lean_object* v_k_3314_; lean_object* v_v_3315_; lean_object* v_l_3316_; lean_object* v_r_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v_size_3312_ = lean_ctor_get(v_r_3304_, 0);
v_size_3313_ = lean_ctor_get(v_impl_3310_, 0);
v_k_3314_ = lean_ctor_get(v_impl_3310_, 1);
v_v_3315_ = lean_ctor_get(v_impl_3310_, 2);
v_l_3316_ = lean_ctor_get(v_impl_3310_, 3);
v_r_3317_ = lean_ctor_get(v_impl_3310_, 4);
lean_inc(v_r_3317_);
v___x_3318_ = lean_unsigned_to_nat(3u);
v___x_3319_ = lean_nat_mul(v___x_3318_, v_size_3312_);
v___x_3320_ = lean_nat_dec_lt(v___x_3319_, v_size_3313_);
lean_dec(v___x_3319_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
lean_dec(v_r_3317_);
v___x_3321_ = lean_nat_add(v___x_3311_, v_size_3313_);
v___x_3322_ = lean_nat_add(v___x_3321_, v_size_3312_);
lean_dec(v___x_3321_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 3, v_impl_3310_);
lean_ctor_set(v___x_3306_, 0, v___x_3322_);
v___x_3324_ = v___x_3306_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3325_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3325_, 3, v_impl_3310_);
lean_ctor_set(v_reuseFailAlloc_3325_, 4, v_r_3304_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
else
{
lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3391_; 
lean_inc(v_l_3316_);
lean_inc(v_v_3315_);
lean_inc(v_k_3314_);
lean_inc(v_size_3313_);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_impl_3310_);
if (v_isSharedCheck_3391_ == 0)
{
lean_object* v_unused_3392_; lean_object* v_unused_3393_; lean_object* v_unused_3394_; lean_object* v_unused_3395_; lean_object* v_unused_3396_; 
v_unused_3392_ = lean_ctor_get(v_impl_3310_, 4);
lean_dec(v_unused_3392_);
v_unused_3393_ = lean_ctor_get(v_impl_3310_, 3);
lean_dec(v_unused_3393_);
v_unused_3394_ = lean_ctor_get(v_impl_3310_, 2);
lean_dec(v_unused_3394_);
v_unused_3395_ = lean_ctor_get(v_impl_3310_, 1);
lean_dec(v_unused_3395_);
v_unused_3396_ = lean_ctor_get(v_impl_3310_, 0);
lean_dec(v_unused_3396_);
v___x_3327_ = v_impl_3310_;
v_isShared_3328_ = v_isSharedCheck_3391_;
goto v_resetjp_3326_;
}
else
{
lean_dec(v_impl_3310_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3391_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v_size_3329_; lean_object* v_size_3330_; lean_object* v_k_3331_; lean_object* v_v_3332_; lean_object* v_l_3333_; lean_object* v_r_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v_size_3329_ = lean_ctor_get(v_l_3316_, 0);
v_size_3330_ = lean_ctor_get(v_r_3317_, 0);
v_k_3331_ = lean_ctor_get(v_r_3317_, 1);
v_v_3332_ = lean_ctor_get(v_r_3317_, 2);
v_l_3333_ = lean_ctor_get(v_r_3317_, 3);
v_r_3334_ = lean_ctor_get(v_r_3317_, 4);
v___x_3335_ = lean_unsigned_to_nat(2u);
v___x_3336_ = lean_nat_mul(v___x_3335_, v_size_3329_);
v___x_3337_ = lean_nat_dec_lt(v_size_3330_, v___x_3336_);
lean_dec(v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3366_; 
lean_inc(v_r_3334_);
lean_inc(v_l_3333_);
lean_inc(v_v_3332_);
lean_inc(v_k_3331_);
v_isSharedCheck_3366_ = !lean_is_exclusive(v_r_3317_);
if (v_isSharedCheck_3366_ == 0)
{
lean_object* v_unused_3367_; lean_object* v_unused_3368_; lean_object* v_unused_3369_; lean_object* v_unused_3370_; lean_object* v_unused_3371_; 
v_unused_3367_ = lean_ctor_get(v_r_3317_, 4);
lean_dec(v_unused_3367_);
v_unused_3368_ = lean_ctor_get(v_r_3317_, 3);
lean_dec(v_unused_3368_);
v_unused_3369_ = lean_ctor_get(v_r_3317_, 2);
lean_dec(v_unused_3369_);
v_unused_3370_ = lean_ctor_get(v_r_3317_, 1);
lean_dec(v_unused_3370_);
v_unused_3371_ = lean_ctor_get(v_r_3317_, 0);
lean_dec(v_unused_3371_);
v___x_3339_ = v_r_3317_;
v_isShared_3340_ = v_isSharedCheck_3366_;
goto v_resetjp_3338_;
}
else
{
lean_dec(v_r_3317_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3366_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___x_3354_; lean_object* v___y_3356_; 
v___x_3341_ = lean_nat_add(v___x_3311_, v_size_3313_);
lean_dec(v_size_3313_);
v___x_3342_ = lean_nat_add(v___x_3341_, v_size_3312_);
lean_dec(v___x_3341_);
v___x_3354_ = lean_nat_add(v___x_3311_, v_size_3329_);
if (lean_obj_tag(v_l_3333_) == 0)
{
lean_object* v_size_3364_; 
v_size_3364_ = lean_ctor_get(v_l_3333_, 0);
lean_inc(v_size_3364_);
v___y_3356_ = v_size_3364_;
goto v___jp_3355_;
}
else
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_unsigned_to_nat(0u);
v___y_3356_ = v___x_3365_;
goto v___jp_3355_;
}
v___jp_3343_:
{
lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3347_ = lean_nat_add(v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 4, v_r_3304_);
lean_ctor_set(v___x_3339_, 3, v_r_3334_);
lean_ctor_set(v___x_3339_, 2, v_v_3302_);
lean_ctor_set(v___x_3339_, 1, v_k_3301_);
lean_ctor_set(v___x_3339_, 0, v___x_3347_);
v___x_3349_ = v___x_3339_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3353_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3353_, 3, v_r_3334_);
lean_ctor_set(v_reuseFailAlloc_3353_, 4, v_r_3304_);
v___x_3349_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3351_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 4, v___x_3349_);
lean_ctor_set(v___x_3327_, 3, v___y_3344_);
lean_ctor_set(v___x_3327_, 2, v_v_3332_);
lean_ctor_set(v___x_3327_, 1, v_k_3331_);
lean_ctor_set(v___x_3327_, 0, v___x_3342_);
v___x_3351_ = v___x_3327_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_k_3331_);
lean_ctor_set(v_reuseFailAlloc_3352_, 2, v_v_3332_);
lean_ctor_set(v_reuseFailAlloc_3352_, 3, v___y_3344_);
lean_ctor_set(v_reuseFailAlloc_3352_, 4, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
v___jp_3355_:
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3357_ = lean_nat_add(v___x_3354_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec(v___x_3354_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v_l_3333_);
lean_ctor_set(v___x_3306_, 3, v_l_3316_);
lean_ctor_set(v___x_3306_, 2, v_v_3315_);
lean_ctor_set(v___x_3306_, 1, v_k_3314_);
lean_ctor_set(v___x_3306_, 0, v___x_3357_);
v___x_3359_ = v___x_3306_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_3314_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_3315_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_l_3316_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_l_3333_);
v___x_3359_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_nat_add(v___x_3311_, v_size_3312_);
if (lean_obj_tag(v_r_3334_) == 0)
{
lean_object* v_size_3361_; 
v_size_3361_ = lean_ctor_get(v_r_3334_, 0);
lean_inc(v_size_3361_);
v___y_3344_ = v___x_3359_;
v___y_3345_ = v___x_3360_;
v___y_3346_ = v_size_3361_;
goto v___jp_3343_;
}
else
{
lean_object* v___x_3362_; 
v___x_3362_ = lean_unsigned_to_nat(0u);
v___y_3344_ = v___x_3359_;
v___y_3345_ = v___x_3360_;
v___y_3346_ = v___x_3362_;
goto v___jp_3343_;
}
}
}
}
}
else
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
lean_del_object(v___x_3306_);
v___x_3372_ = lean_nat_add(v___x_3311_, v_size_3313_);
lean_dec(v_size_3313_);
v___x_3373_ = lean_nat_add(v___x_3372_, v_size_3312_);
lean_dec(v___x_3372_);
v___x_3374_ = lean_nat_add(v___x_3311_, v_size_3312_);
v___x_3375_ = lean_nat_add(v___x_3374_, v_size_3330_);
lean_dec(v___x_3374_);
lean_inc_ref(v_r_3304_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 4, v_r_3304_);
lean_ctor_set(v___x_3327_, 3, v_r_3317_);
lean_ctor_set(v___x_3327_, 2, v_v_3302_);
lean_ctor_set(v___x_3327_, 1, v_k_3301_);
lean_ctor_set(v___x_3327_, 0, v___x_3375_);
v___x_3377_ = v___x_3327_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3390_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3390_, 3, v_r_3317_);
lean_ctor_set(v_reuseFailAlloc_3390_, 4, v_r_3304_);
v___x_3377_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
v_isSharedCheck_3384_ = !lean_is_exclusive(v_r_3304_);
if (v_isSharedCheck_3384_ == 0)
{
lean_object* v_unused_3385_; lean_object* v_unused_3386_; lean_object* v_unused_3387_; lean_object* v_unused_3388_; lean_object* v_unused_3389_; 
v_unused_3385_ = lean_ctor_get(v_r_3304_, 4);
lean_dec(v_unused_3385_);
v_unused_3386_ = lean_ctor_get(v_r_3304_, 3);
lean_dec(v_unused_3386_);
v_unused_3387_ = lean_ctor_get(v_r_3304_, 2);
lean_dec(v_unused_3387_);
v_unused_3388_ = lean_ctor_get(v_r_3304_, 1);
lean_dec(v_unused_3388_);
v_unused_3389_ = lean_ctor_get(v_r_3304_, 0);
lean_dec(v_unused_3389_);
v___x_3379_ = v_r_3304_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_dec(v_r_3304_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 4, v___x_3377_);
lean_ctor_set(v___x_3379_, 3, v_l_3316_);
lean_ctor_set(v___x_3379_, 2, v_v_3315_);
lean_ctor_set(v___x_3379_, 1, v_k_3314_);
lean_ctor_set(v___x_3379_, 0, v___x_3373_);
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_k_3314_);
lean_ctor_set(v_reuseFailAlloc_3383_, 2, v_v_3315_);
lean_ctor_set(v_reuseFailAlloc_3383_, 3, v_l_3316_);
lean_ctor_set(v_reuseFailAlloc_3383_, 4, v___x_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3397_; 
v_l_3397_ = lean_ctor_get(v_impl_3310_, 3);
if (lean_obj_tag(v_l_3397_) == 0)
{
lean_object* v_r_3398_; lean_object* v_k_3399_; lean_object* v_v_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3411_; 
lean_inc_ref(v_l_3397_);
v_r_3398_ = lean_ctor_get(v_impl_3310_, 4);
v_k_3399_ = lean_ctor_get(v_impl_3310_, 1);
v_v_3400_ = lean_ctor_get(v_impl_3310_, 2);
v_isSharedCheck_3411_ = !lean_is_exclusive(v_impl_3310_);
if (v_isSharedCheck_3411_ == 0)
{
lean_object* v_unused_3412_; lean_object* v_unused_3413_; 
v_unused_3412_ = lean_ctor_get(v_impl_3310_, 3);
lean_dec(v_unused_3412_);
v_unused_3413_ = lean_ctor_get(v_impl_3310_, 0);
lean_dec(v_unused_3413_);
v___x_3402_ = v_impl_3310_;
v_isShared_3403_ = v_isSharedCheck_3411_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_r_3398_);
lean_inc(v_v_3400_);
lean_inc(v_k_3399_);
lean_dec(v_impl_3310_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3411_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3406_; 
v___x_3404_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3398_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 3, v_r_3398_);
lean_ctor_set(v___x_3402_, 2, v_v_3302_);
lean_ctor_set(v___x_3402_, 1, v_k_3301_);
lean_ctor_set(v___x_3402_, 0, v___x_3311_);
v___x_3406_ = v___x_3402_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3410_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3410_, 3, v_r_3398_);
lean_ctor_set(v_reuseFailAlloc_3410_, 4, v_r_3398_);
v___x_3406_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3408_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3406_);
lean_ctor_set(v___x_3306_, 3, v_l_3397_);
lean_ctor_set(v___x_3306_, 2, v_v_3400_);
lean_ctor_set(v___x_3306_, 1, v_k_3399_);
lean_ctor_set(v___x_3306_, 0, v___x_3404_);
v___x_3408_ = v___x_3306_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3404_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_k_3399_);
lean_ctor_set(v_reuseFailAlloc_3409_, 2, v_v_3400_);
lean_ctor_set(v_reuseFailAlloc_3409_, 3, v_l_3397_);
lean_ctor_set(v_reuseFailAlloc_3409_, 4, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v_r_3414_; 
v_r_3414_ = lean_ctor_get(v_impl_3310_, 4);
lean_inc(v_r_3414_);
if (lean_obj_tag(v_r_3414_) == 0)
{
lean_object* v_k_3415_; lean_object* v_v_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3439_; 
lean_inc(v_l_3397_);
v_k_3415_ = lean_ctor_get(v_impl_3310_, 1);
v_v_3416_ = lean_ctor_get(v_impl_3310_, 2);
v_isSharedCheck_3439_ = !lean_is_exclusive(v_impl_3310_);
if (v_isSharedCheck_3439_ == 0)
{
lean_object* v_unused_3440_; lean_object* v_unused_3441_; lean_object* v_unused_3442_; 
v_unused_3440_ = lean_ctor_get(v_impl_3310_, 4);
lean_dec(v_unused_3440_);
v_unused_3441_ = lean_ctor_get(v_impl_3310_, 3);
lean_dec(v_unused_3441_);
v_unused_3442_ = lean_ctor_get(v_impl_3310_, 0);
lean_dec(v_unused_3442_);
v___x_3418_ = v_impl_3310_;
v_isShared_3419_ = v_isSharedCheck_3439_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_v_3416_);
lean_inc(v_k_3415_);
lean_dec(v_impl_3310_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3439_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v_k_3420_; lean_object* v_v_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3435_; 
v_k_3420_ = lean_ctor_get(v_r_3414_, 1);
v_v_3421_ = lean_ctor_get(v_r_3414_, 2);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_r_3414_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; lean_object* v_unused_3437_; lean_object* v_unused_3438_; 
v_unused_3436_ = lean_ctor_get(v_r_3414_, 4);
lean_dec(v_unused_3436_);
v_unused_3437_ = lean_ctor_get(v_r_3414_, 3);
lean_dec(v_unused_3437_);
v_unused_3438_ = lean_ctor_get(v_r_3414_, 0);
lean_dec(v_unused_3438_);
v___x_3423_ = v_r_3414_;
v_isShared_3424_ = v_isSharedCheck_3435_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_v_3421_);
lean_inc(v_k_3420_);
lean_dec(v_r_3414_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3435_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3425_ = lean_unsigned_to_nat(3u);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 4, v_l_3397_);
lean_ctor_set(v___x_3423_, 3, v_l_3397_);
lean_ctor_set(v___x_3423_, 2, v_v_3416_);
lean_ctor_set(v___x_3423_, 1, v_k_3415_);
lean_ctor_set(v___x_3423_, 0, v___x_3311_);
v___x_3427_ = v___x_3423_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_k_3415_);
lean_ctor_set(v_reuseFailAlloc_3434_, 2, v_v_3416_);
lean_ctor_set(v_reuseFailAlloc_3434_, 3, v_l_3397_);
lean_ctor_set(v_reuseFailAlloc_3434_, 4, v_l_3397_);
v___x_3427_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3429_; 
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 4, v_l_3397_);
lean_ctor_set(v___x_3418_, 2, v_v_3302_);
lean_ctor_set(v___x_3418_, 1, v_k_3301_);
lean_ctor_set(v___x_3418_, 0, v___x_3311_);
v___x_3429_ = v___x_3418_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3433_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3433_, 3, v_l_3397_);
lean_ctor_set(v_reuseFailAlloc_3433_, 4, v_l_3397_);
v___x_3429_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3431_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3429_);
lean_ctor_set(v___x_3306_, 3, v___x_3427_);
lean_ctor_set(v___x_3306_, 2, v_v_3421_);
lean_ctor_set(v___x_3306_, 1, v_k_3420_);
lean_ctor_set(v___x_3306_, 0, v___x_3425_);
v___x_3431_ = v___x_3306_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3425_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_k_3420_);
lean_ctor_set(v_reuseFailAlloc_3432_, 2, v_v_3421_);
lean_ctor_set(v_reuseFailAlloc_3432_, 3, v___x_3427_);
lean_ctor_set(v_reuseFailAlloc_3432_, 4, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
}
else
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = lean_unsigned_to_nat(2u);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v_r_3414_);
lean_ctor_set(v___x_3306_, 3, v_impl_3310_);
lean_ctor_set(v___x_3306_, 0, v___x_3443_);
v___x_3445_ = v___x_3306_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3446_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3446_, 3, v_impl_3310_);
lean_ctor_set(v_reuseFailAlloc_3446_, 4, v_r_3414_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3448_; 
lean_dec(v_v_3302_);
lean_dec(v_k_3301_);
lean_dec_ref(v_cmp_3296_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 2, v_v_3298_);
lean_ctor_set(v___x_3306_, 1, v_k_3297_);
v___x_3448_ = v___x_3306_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_size_3300_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_k_3297_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_v_3298_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v_l_3303_);
lean_ctor_set(v_reuseFailAlloc_3449_, 4, v_r_3304_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
default: 
{
lean_object* v_impl_3450_; lean_object* v___x_3451_; 
lean_dec(v_size_3300_);
v_impl_3450_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3296_, v_k_3297_, v_v_3298_, v_r_3304_);
v___x_3451_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3303_) == 0)
{
lean_object* v_size_3452_; lean_object* v_size_3453_; lean_object* v_k_3454_; lean_object* v_v_3455_; lean_object* v_l_3456_; lean_object* v_r_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; uint8_t v___x_3460_; 
v_size_3452_ = lean_ctor_get(v_l_3303_, 0);
v_size_3453_ = lean_ctor_get(v_impl_3450_, 0);
v_k_3454_ = lean_ctor_get(v_impl_3450_, 1);
v_v_3455_ = lean_ctor_get(v_impl_3450_, 2);
v_l_3456_ = lean_ctor_get(v_impl_3450_, 3);
lean_inc(v_l_3456_);
v_r_3457_ = lean_ctor_get(v_impl_3450_, 4);
v___x_3458_ = lean_unsigned_to_nat(3u);
v___x_3459_ = lean_nat_mul(v___x_3458_, v_size_3452_);
v___x_3460_ = lean_nat_dec_lt(v___x_3459_, v_size_3453_);
lean_dec(v___x_3459_);
if (v___x_3460_ == 0)
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3464_; 
lean_dec(v_l_3456_);
v___x_3461_ = lean_nat_add(v___x_3451_, v_size_3452_);
v___x_3462_ = lean_nat_add(v___x_3461_, v_size_3453_);
lean_dec(v___x_3461_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v_impl_3450_);
lean_ctor_set(v___x_3306_, 0, v___x_3462_);
v___x_3464_ = v___x_3306_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3465_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3465_, 3, v_l_3303_);
lean_ctor_set(v_reuseFailAlloc_3465_, 4, v_impl_3450_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
else
{
lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3529_; 
lean_inc(v_r_3457_);
lean_inc(v_v_3455_);
lean_inc(v_k_3454_);
lean_inc(v_size_3453_);
v_isSharedCheck_3529_ = !lean_is_exclusive(v_impl_3450_);
if (v_isSharedCheck_3529_ == 0)
{
lean_object* v_unused_3530_; lean_object* v_unused_3531_; lean_object* v_unused_3532_; lean_object* v_unused_3533_; lean_object* v_unused_3534_; 
v_unused_3530_ = lean_ctor_get(v_impl_3450_, 4);
lean_dec(v_unused_3530_);
v_unused_3531_ = lean_ctor_get(v_impl_3450_, 3);
lean_dec(v_unused_3531_);
v_unused_3532_ = lean_ctor_get(v_impl_3450_, 2);
lean_dec(v_unused_3532_);
v_unused_3533_ = lean_ctor_get(v_impl_3450_, 1);
lean_dec(v_unused_3533_);
v_unused_3534_ = lean_ctor_get(v_impl_3450_, 0);
lean_dec(v_unused_3534_);
v___x_3467_ = v_impl_3450_;
v_isShared_3468_ = v_isSharedCheck_3529_;
goto v_resetjp_3466_;
}
else
{
lean_dec(v_impl_3450_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3529_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v_size_3469_; lean_object* v_k_3470_; lean_object* v_v_3471_; lean_object* v_l_3472_; lean_object* v_r_3473_; lean_object* v_size_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; uint8_t v___x_3477_; 
v_size_3469_ = lean_ctor_get(v_l_3456_, 0);
v_k_3470_ = lean_ctor_get(v_l_3456_, 1);
v_v_3471_ = lean_ctor_get(v_l_3456_, 2);
v_l_3472_ = lean_ctor_get(v_l_3456_, 3);
v_r_3473_ = lean_ctor_get(v_l_3456_, 4);
v_size_3474_ = lean_ctor_get(v_r_3457_, 0);
v___x_3475_ = lean_unsigned_to_nat(2u);
v___x_3476_ = lean_nat_mul(v___x_3475_, v_size_3474_);
v___x_3477_ = lean_nat_dec_lt(v_size_3469_, v___x_3476_);
lean_dec(v___x_3476_);
if (v___x_3477_ == 0)
{
lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3505_; 
lean_inc(v_r_3473_);
lean_inc(v_l_3472_);
lean_inc(v_v_3471_);
lean_inc(v_k_3470_);
v_isSharedCheck_3505_ = !lean_is_exclusive(v_l_3456_);
if (v_isSharedCheck_3505_ == 0)
{
lean_object* v_unused_3506_; lean_object* v_unused_3507_; lean_object* v_unused_3508_; lean_object* v_unused_3509_; lean_object* v_unused_3510_; 
v_unused_3506_ = lean_ctor_get(v_l_3456_, 4);
lean_dec(v_unused_3506_);
v_unused_3507_ = lean_ctor_get(v_l_3456_, 3);
lean_dec(v_unused_3507_);
v_unused_3508_ = lean_ctor_get(v_l_3456_, 2);
lean_dec(v_unused_3508_);
v_unused_3509_ = lean_ctor_get(v_l_3456_, 1);
lean_dec(v_unused_3509_);
v_unused_3510_ = lean_ctor_get(v_l_3456_, 0);
lean_dec(v_unused_3510_);
v___x_3479_ = v_l_3456_;
v_isShared_3480_ = v_isSharedCheck_3505_;
goto v_resetjp_3478_;
}
else
{
lean_dec(v_l_3456_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3505_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3495_; 
v___x_3481_ = lean_nat_add(v___x_3451_, v_size_3452_);
v___x_3482_ = lean_nat_add(v___x_3481_, v_size_3453_);
lean_dec(v_size_3453_);
if (lean_obj_tag(v_l_3472_) == 0)
{
lean_object* v_size_3503_; 
v_size_3503_ = lean_ctor_get(v_l_3472_, 0);
lean_inc(v_size_3503_);
v___y_3495_ = v_size_3503_;
goto v___jp_3494_;
}
else
{
lean_object* v___x_3504_; 
v___x_3504_ = lean_unsigned_to_nat(0u);
v___y_3495_ = v___x_3504_;
goto v___jp_3494_;
}
v___jp_3483_:
{
lean_object* v___x_3487_; lean_object* v___x_3489_; 
v___x_3487_ = lean_nat_add(v___y_3484_, v___y_3486_);
lean_dec(v___y_3486_);
lean_dec(v___y_3484_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 4, v_r_3457_);
lean_ctor_set(v___x_3479_, 3, v_r_3473_);
lean_ctor_set(v___x_3479_, 2, v_v_3455_);
lean_ctor_set(v___x_3479_, 1, v_k_3454_);
lean_ctor_set(v___x_3479_, 0, v___x_3487_);
v___x_3489_ = v___x_3479_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3487_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v_k_3454_);
lean_ctor_set(v_reuseFailAlloc_3493_, 2, v_v_3455_);
lean_ctor_set(v_reuseFailAlloc_3493_, 3, v_r_3473_);
lean_ctor_set(v_reuseFailAlloc_3493_, 4, v_r_3457_);
v___x_3489_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
lean_object* v___x_3491_; 
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 4, v___x_3489_);
lean_ctor_set(v___x_3467_, 3, v___y_3485_);
lean_ctor_set(v___x_3467_, 2, v_v_3471_);
lean_ctor_set(v___x_3467_, 1, v_k_3470_);
lean_ctor_set(v___x_3467_, 0, v___x_3482_);
v___x_3491_ = v___x_3467_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3482_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_k_3470_);
lean_ctor_set(v_reuseFailAlloc_3492_, 2, v_v_3471_);
lean_ctor_set(v_reuseFailAlloc_3492_, 3, v___y_3485_);
lean_ctor_set(v_reuseFailAlloc_3492_, 4, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
v___jp_3494_:
{
lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3496_ = lean_nat_add(v___x_3481_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec(v___x_3481_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v_l_3472_);
lean_ctor_set(v___x_3306_, 0, v___x_3496_);
v___x_3498_ = v___x_3306_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3496_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3502_, 3, v_l_3303_);
lean_ctor_set(v_reuseFailAlloc_3502_, 4, v_l_3472_);
v___x_3498_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_nat_add(v___x_3451_, v_size_3474_);
if (lean_obj_tag(v_r_3473_) == 0)
{
lean_object* v_size_3500_; 
v_size_3500_ = lean_ctor_get(v_r_3473_, 0);
lean_inc(v_size_3500_);
v___y_3484_ = v___x_3499_;
v___y_3485_ = v___x_3498_;
v___y_3486_ = v_size_3500_;
goto v___jp_3483_;
}
else
{
lean_object* v___x_3501_; 
v___x_3501_ = lean_unsigned_to_nat(0u);
v___y_3484_ = v___x_3499_;
v___y_3485_ = v___x_3498_;
v___y_3486_ = v___x_3501_;
goto v___jp_3483_;
}
}
}
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
lean_del_object(v___x_3306_);
v___x_3511_ = lean_nat_add(v___x_3451_, v_size_3452_);
v___x_3512_ = lean_nat_add(v___x_3511_, v_size_3453_);
lean_dec(v_size_3453_);
v___x_3513_ = lean_nat_add(v___x_3511_, v_size_3469_);
lean_dec(v___x_3511_);
lean_inc_ref(v_l_3303_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 4, v_l_3456_);
lean_ctor_set(v___x_3467_, 3, v_l_3303_);
lean_ctor_set(v___x_3467_, 2, v_v_3302_);
lean_ctor_set(v___x_3467_, 1, v_k_3301_);
lean_ctor_set(v___x_3467_, 0, v___x_3513_);
v___x_3515_ = v___x_3467_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3528_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3528_, 3, v_l_3303_);
lean_ctor_set(v_reuseFailAlloc_3528_, 4, v_l_3456_);
v___x_3515_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
v_isSharedCheck_3522_ = !lean_is_exclusive(v_l_3303_);
if (v_isSharedCheck_3522_ == 0)
{
lean_object* v_unused_3523_; lean_object* v_unused_3524_; lean_object* v_unused_3525_; lean_object* v_unused_3526_; lean_object* v_unused_3527_; 
v_unused_3523_ = lean_ctor_get(v_l_3303_, 4);
lean_dec(v_unused_3523_);
v_unused_3524_ = lean_ctor_get(v_l_3303_, 3);
lean_dec(v_unused_3524_);
v_unused_3525_ = lean_ctor_get(v_l_3303_, 2);
lean_dec(v_unused_3525_);
v_unused_3526_ = lean_ctor_get(v_l_3303_, 1);
lean_dec(v_unused_3526_);
v_unused_3527_ = lean_ctor_get(v_l_3303_, 0);
lean_dec(v_unused_3527_);
v___x_3517_ = v_l_3303_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_dec(v_l_3303_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 4, v_r_3457_);
lean_ctor_set(v___x_3517_, 3, v___x_3515_);
lean_ctor_set(v___x_3517_, 2, v_v_3455_);
lean_ctor_set(v___x_3517_, 1, v_k_3454_);
lean_ctor_set(v___x_3517_, 0, v___x_3512_);
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_k_3454_);
lean_ctor_set(v_reuseFailAlloc_3521_, 2, v_v_3455_);
lean_ctor_set(v_reuseFailAlloc_3521_, 3, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3521_, 4, v_r_3457_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3535_; 
v_l_3535_ = lean_ctor_get(v_impl_3450_, 3);
lean_inc(v_l_3535_);
if (lean_obj_tag(v_l_3535_) == 0)
{
lean_object* v_r_3536_; lean_object* v_k_3537_; lean_object* v_v_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3561_; 
v_r_3536_ = lean_ctor_get(v_impl_3450_, 4);
v_k_3537_ = lean_ctor_get(v_impl_3450_, 1);
v_v_3538_ = lean_ctor_get(v_impl_3450_, 2);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_impl_3450_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; lean_object* v_unused_3563_; 
v_unused_3562_ = lean_ctor_get(v_impl_3450_, 3);
lean_dec(v_unused_3562_);
v_unused_3563_ = lean_ctor_get(v_impl_3450_, 0);
lean_dec(v_unused_3563_);
v___x_3540_ = v_impl_3450_;
v_isShared_3541_ = v_isSharedCheck_3561_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_r_3536_);
lean_inc(v_v_3538_);
lean_inc(v_k_3537_);
lean_dec(v_impl_3450_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3561_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v_k_3542_; lean_object* v_v_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3557_; 
v_k_3542_ = lean_ctor_get(v_l_3535_, 1);
v_v_3543_ = lean_ctor_get(v_l_3535_, 2);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_l_3535_);
if (v_isSharedCheck_3557_ == 0)
{
lean_object* v_unused_3558_; lean_object* v_unused_3559_; lean_object* v_unused_3560_; 
v_unused_3558_ = lean_ctor_get(v_l_3535_, 4);
lean_dec(v_unused_3558_);
v_unused_3559_ = lean_ctor_get(v_l_3535_, 3);
lean_dec(v_unused_3559_);
v_unused_3560_ = lean_ctor_get(v_l_3535_, 0);
lean_dec(v_unused_3560_);
v___x_3545_ = v_l_3535_;
v_isShared_3546_ = v_isSharedCheck_3557_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_v_3543_);
lean_inc(v_k_3542_);
lean_dec(v_l_3535_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3557_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3547_; lean_object* v___x_3549_; 
v___x_3547_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3536_, 2);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 4, v_r_3536_);
lean_ctor_set(v___x_3545_, 3, v_r_3536_);
lean_ctor_set(v___x_3545_, 2, v_v_3302_);
lean_ctor_set(v___x_3545_, 1, v_k_3301_);
lean_ctor_set(v___x_3545_, 0, v___x_3451_);
v___x_3549_ = v___x_3545_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3556_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3556_, 3, v_r_3536_);
lean_ctor_set(v_reuseFailAlloc_3556_, 4, v_r_3536_);
v___x_3549_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3551_; 
lean_inc(v_r_3536_);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 3, v_r_3536_);
lean_ctor_set(v___x_3540_, 0, v___x_3451_);
v___x_3551_ = v___x_3540_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3555_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3555_, 3, v_r_3536_);
lean_ctor_set(v_reuseFailAlloc_3555_, 4, v_r_3536_);
v___x_3551_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3553_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v___x_3551_);
lean_ctor_set(v___x_3306_, 3, v___x_3549_);
lean_ctor_set(v___x_3306_, 2, v_v_3543_);
lean_ctor_set(v___x_3306_, 1, v_k_3542_);
lean_ctor_set(v___x_3306_, 0, v___x_3547_);
v___x_3553_ = v___x_3306_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3547_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_k_3542_);
lean_ctor_set(v_reuseFailAlloc_3554_, 2, v_v_3543_);
lean_ctor_set(v_reuseFailAlloc_3554_, 3, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3554_, 4, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
}
else
{
lean_object* v_r_3564_; 
v_r_3564_ = lean_ctor_get(v_impl_3450_, 4);
lean_inc(v_r_3564_);
if (lean_obj_tag(v_r_3564_) == 0)
{
lean_object* v_k_3565_; lean_object* v_v_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3577_; 
v_k_3565_ = lean_ctor_get(v_impl_3450_, 1);
v_v_3566_ = lean_ctor_get(v_impl_3450_, 2);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_impl_3450_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; lean_object* v_unused_3579_; lean_object* v_unused_3580_; 
v_unused_3578_ = lean_ctor_get(v_impl_3450_, 4);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_impl_3450_, 3);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_impl_3450_, 0);
lean_dec(v_unused_3580_);
v___x_3568_ = v_impl_3450_;
v_isShared_3569_ = v_isSharedCheck_3577_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_v_3566_);
lean_inc(v_k_3565_);
lean_dec(v_impl_3450_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3577_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3570_ = lean_unsigned_to_nat(3u);
if (v_isShared_3569_ == 0)
{
lean_ctor_set(v___x_3568_, 4, v_l_3535_);
lean_ctor_set(v___x_3568_, 2, v_v_3302_);
lean_ctor_set(v___x_3568_, 1, v_k_3301_);
lean_ctor_set(v___x_3568_, 0, v___x_3451_);
v___x_3572_ = v___x_3568_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3576_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3576_, 3, v_l_3535_);
lean_ctor_set(v_reuseFailAlloc_3576_, 4, v_l_3535_);
v___x_3572_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3574_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v_r_3564_);
lean_ctor_set(v___x_3306_, 3, v___x_3572_);
lean_ctor_set(v___x_3306_, 2, v_v_3566_);
lean_ctor_set(v___x_3306_, 1, v_k_3565_);
lean_ctor_set(v___x_3306_, 0, v___x_3570_);
v___x_3574_ = v___x_3306_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_k_3565_);
lean_ctor_set(v_reuseFailAlloc_3575_, 2, v_v_3566_);
lean_ctor_set(v_reuseFailAlloc_3575_, 3, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3575_, 4, v_r_3564_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
else
{
lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3581_ = lean_unsigned_to_nat(2u);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 4, v_impl_3450_);
lean_ctor_set(v___x_3306_, 3, v_r_3564_);
lean_ctor_set(v___x_3306_, 0, v___x_3581_);
v___x_3583_ = v___x_3306_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3584_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3584_, 3, v_r_3564_);
lean_ctor_set(v_reuseFailAlloc_3584_, 4, v_impl_3450_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
lean_dec_ref(v_cmp_3296_);
v___x_3586_ = lean_unsigned_to_nat(1u);
v___x_3587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
lean_ctor_set(v___x_3587_, 1, v_k_3297_);
lean_ctor_set(v___x_3587_, 2, v_v_3298_);
lean_ctor_set(v___x_3587_, 3, v_t_3299_);
lean_ctor_set(v___x_3587_, 4, v_t_3299_);
return v___x_3587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(lean_object* v_cmp_3588_, lean_object* v_init_3589_, lean_object* v_x_3590_){
_start:
{
if (lean_obj_tag(v_x_3590_) == 0)
{
lean_object* v_k_3591_; lean_object* v_v_3592_; lean_object* v_l_3593_; lean_object* v_r_3594_; lean_object* v___x_3595_; lean_object* v_a_3596_; lean_object* v_r_3597_; 
v_k_3591_ = lean_ctor_get(v_x_3590_, 1);
lean_inc(v_k_3591_);
v_v_3592_ = lean_ctor_get(v_x_3590_, 2);
lean_inc(v_v_3592_);
v_l_3593_ = lean_ctor_get(v_x_3590_, 3);
lean_inc(v_l_3593_);
v_r_3594_ = lean_ctor_get(v_x_3590_, 4);
lean_inc(v_r_3594_);
lean_dec_ref_known(v_x_3590_, 5);
lean_inc_ref_n(v_cmp_3588_, 2);
v___x_3595_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3588_, v_init_3589_, v_l_3593_);
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref(v___x_3595_);
v_r_3597_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3588_, v_k_3591_, v_v_3592_, v_a_3596_);
v_init_3589_ = v_r_3597_;
v_x_3590_ = v_r_3594_;
goto _start;
}
else
{
lean_object* v___x_3599_; 
lean_dec_ref(v_cmp_3588_);
v___x_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3599_, 0, v_init_3589_);
return v___x_3599_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(lean_object* v_cmp_3600_, lean_object* v_k_3601_, lean_object* v_t_3602_){
_start:
{
if (lean_obj_tag(v_t_3602_) == 0)
{
lean_object* v_k_3603_; lean_object* v_l_3604_; lean_object* v_r_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v_k_3603_ = lean_ctor_get(v_t_3602_, 1);
lean_inc(v_k_3603_);
v_l_3604_ = lean_ctor_get(v_t_3602_, 3);
lean_inc(v_l_3604_);
v_r_3605_ = lean_ctor_get(v_t_3602_, 4);
lean_inc(v_r_3605_);
lean_dec_ref_known(v_t_3602_, 5);
lean_inc_ref(v_cmp_3600_);
lean_inc(v_k_3601_);
v___x_3606_ = lean_apply_2(v_cmp_3600_, v_k_3601_, v_k_3603_);
v___x_3607_ = lean_unbox(v___x_3606_);
switch(v___x_3607_)
{
case 0:
{
lean_dec(v_r_3605_);
v_t_3602_ = v_l_3604_;
goto _start;
}
case 1:
{
uint8_t v___x_3609_; 
lean_dec(v_r_3605_);
lean_dec(v_l_3604_);
lean_dec(v_k_3601_);
lean_dec_ref(v_cmp_3600_);
v___x_3609_ = 1;
return v___x_3609_;
}
default: 
{
lean_dec(v_l_3604_);
v_t_3602_ = v_r_3605_;
goto _start;
}
}
}
else
{
uint8_t v___x_3611_; 
lean_dec(v_k_3601_);
lean_dec_ref(v_cmp_3600_);
v___x_3611_ = 0;
return v___x_3611_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_3612_, lean_object* v_k_3613_, lean_object* v_t_3614_){
_start:
{
uint8_t v_res_3615_; lean_object* v_r_3616_; 
v_res_3615_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3612_, v_k_3613_, v_t_3614_);
v_r_3616_ = lean_box(v_res_3615_);
return v_r_3616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(lean_object* v_cmp_3617_, lean_object* v_init_3618_, lean_object* v_x_3619_){
_start:
{
if (lean_obj_tag(v_x_3619_) == 0)
{
lean_object* v_k_3620_; lean_object* v_v_3621_; lean_object* v_l_3622_; lean_object* v_r_3623_; lean_object* v___x_3624_; lean_object* v_a_3625_; uint8_t v___x_3626_; 
v_k_3620_ = lean_ctor_get(v_x_3619_, 1);
lean_inc_n(v_k_3620_, 2);
v_v_3621_ = lean_ctor_get(v_x_3619_, 2);
lean_inc(v_v_3621_);
v_l_3622_ = lean_ctor_get(v_x_3619_, 3);
lean_inc(v_l_3622_);
v_r_3623_ = lean_ctor_get(v_x_3619_, 4);
lean_inc(v_r_3623_);
lean_dec_ref_known(v_x_3619_, 5);
lean_inc_ref_n(v_cmp_3617_, 2);
v___x_3624_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3617_, v_init_3618_, v_l_3622_);
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc_n(v_a_3625_, 2);
lean_dec_ref(v___x_3624_);
v___x_3626_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3617_, v_k_3620_, v_a_3625_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; 
lean_inc_ref(v_cmp_3617_);
v___x_3627_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3617_, v_k_3620_, v_v_3621_, v_a_3625_);
v_init_3618_ = v___x_3627_;
v_x_3619_ = v_r_3623_;
goto _start;
}
else
{
lean_dec(v_v_3621_);
lean_dec(v_k_3620_);
v_init_3618_ = v_a_3625_;
v_x_3619_ = v_r_3623_;
goto _start;
}
}
else
{
lean_object* v___x_3630_; 
lean_dec_ref(v_cmp_3617_);
v___x_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3630_, 0, v_init_3618_);
return v___x_3630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object* v_cmp_3631_, lean_object* v_t_u2081_3632_, lean_object* v_t_u2082_3633_){
_start:
{
lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3643_; 
if (lean_obj_tag(v_t_u2081_3632_) == 0)
{
lean_object* v_size_3646_; 
v_size_3646_ = lean_ctor_get(v_t_u2081_3632_, 0);
lean_inc(v_size_3646_);
v___y_3643_ = v_size_3646_;
goto v___jp_3642_;
}
else
{
lean_object* v___x_3647_; 
v___x_3647_ = lean_unsigned_to_nat(0u);
v___y_3643_ = v___x_3647_;
goto v___jp_3642_;
}
v___jp_3634_:
{
uint8_t v___x_3637_; 
v___x_3637_ = lean_nat_dec_le(v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec(v___y_3635_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; lean_object* v_a_3639_; 
v___x_3638_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3631_, v_t_u2081_3632_, v_t_u2082_3633_);
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref(v___x_3638_);
return v_a_3639_;
}
else
{
lean_object* v___x_3640_; lean_object* v_a_3641_; 
v___x_3640_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3631_, v_t_u2082_3633_, v_t_u2081_3632_);
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref(v___x_3640_);
return v_a_3641_;
}
}
v___jp_3642_:
{
if (lean_obj_tag(v_t_u2082_3633_) == 0)
{
lean_object* v_size_3644_; 
v_size_3644_ = lean_ctor_get(v_t_u2082_3633_, 0);
lean_inc(v_size_3644_);
v___y_3635_ = v___y_3643_;
v___y_3636_ = v_size_3644_;
goto v___jp_3634_;
}
else
{
lean_object* v___x_3645_; 
v___x_3645_ = lean_unsigned_to_nat(0u);
v___y_3635_ = v___y_3643_;
v___y_3636_ = v___x_3645_;
goto v___jp_3634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_union___redArg(lean_object* v_cmp_3648_, lean_object* v_t_u2081_3649_, lean_object* v_t_u2082_3650_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3648_, v_t_u2081_3649_, v_t_u2082_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_union(lean_object* v_00_u03b1_3652_, lean_object* v_00_u03b2_3653_, lean_object* v_cmp_3654_, lean_object* v_t_u2081_3655_, lean_object* v_t_u2082_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3654_, v_t_u2081_3655_, v_t_u2082_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0(lean_object* v_00_u03b1_3658_, lean_object* v_cmp_3659_, lean_object* v_00_u03b2_3660_, lean_object* v_t_u2081_3661_, lean_object* v_t_u2082_3662_, lean_object* v_h_u2081_3663_, lean_object* v_h_u2082_3664_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3659_, v_t_u2081_3661_, v_t_u2082_3662_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0(lean_object* v_00_u03b1_3666_, lean_object* v_cmp_3667_, lean_object* v_00_u03b2_3668_, lean_object* v_k_3669_, lean_object* v_v_3670_, lean_object* v_t_3671_, lean_object* v_hl_3672_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3667_, v_k_3669_, v_v_3670_, v_t_3671_);
return v___x_3673_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1(lean_object* v_00_u03b1_3674_, lean_object* v_cmp_3675_, lean_object* v_00_u03b2_3676_, lean_object* v_k_3677_, lean_object* v_t_3678_){
_start:
{
uint8_t v___x_3679_; 
v___x_3679_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3675_, v_k_3677_, v_t_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3680_, lean_object* v_cmp_3681_, lean_object* v_00_u03b2_3682_, lean_object* v_k_3683_, lean_object* v_t_3684_){
_start:
{
uint8_t v_res_3685_; lean_object* v_r_3686_; 
v_res_3685_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1(v_00_u03b1_3680_, v_cmp_3681_, v_00_u03b2_3682_, v_k_3683_, v_t_3684_);
v_r_3686_ = lean_box(v_res_3685_);
return v_r_3686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2(lean_object* v_00_u03b1_3687_, lean_object* v_00_u03b2_3688_, lean_object* v_cmp_3689_, lean_object* v_init_3690_, lean_object* v_x_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3689_, v_init_3690_, v_x_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3(lean_object* v_00_u03b1_3693_, lean_object* v_00_u03b2_3694_, lean_object* v_cmp_3695_, lean_object* v_init_3696_, lean_object* v_x_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3695_, v_init_3696_, v_x_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instUnion___redArg(lean_object* v_cmp_3699_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_alloc_closure((void*)(l_Std_DTreeMap_union), 5, 3);
lean_closure_set(v___x_3700_, 0, lean_box(0));
lean_closure_set(v___x_3700_, 1, lean_box(0));
lean_closure_set(v___x_3700_, 2, v_cmp_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instUnion(lean_object* v_00_u03b1_3701_, lean_object* v_00_u03b2_3702_, lean_object* v_cmp_3703_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = lean_alloc_closure((void*)(l_Std_DTreeMap_union), 5, 3);
lean_closure_set(v___x_3704_, 0, lean_box(0));
lean_closure_set(v___x_3704_, 1, lean_box(0));
lean_closure_set(v___x_3704_, 2, v_cmp_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(lean_object* v_cmp_3705_, lean_object* v_m_u2082_3706_, lean_object* v_t_3707_){
_start:
{
if (lean_obj_tag(v_t_3707_) == 0)
{
lean_object* v_k_3708_; lean_object* v_v_3709_; lean_object* v_l_3710_; lean_object* v_r_3711_; uint8_t v___x_3712_; 
v_k_3708_ = lean_ctor_get(v_t_3707_, 1);
lean_inc_n(v_k_3708_, 2);
v_v_3709_ = lean_ctor_get(v_t_3707_, 2);
lean_inc(v_v_3709_);
v_l_3710_ = lean_ctor_get(v_t_3707_, 3);
lean_inc(v_l_3710_);
v_r_3711_ = lean_ctor_get(v_t_3707_, 4);
lean_inc(v_r_3711_);
lean_dec_ref_known(v_t_3707_, 5);
lean_inc(v_m_u2082_3706_);
lean_inc_ref(v_cmp_3705_);
v___x_3712_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3705_, v_k_3708_, v_m_u2082_3706_);
if (v___x_3712_ == 0)
{
lean_object* v_impl_3713_; lean_object* v_impl_3714_; lean_object* v___x_3715_; 
lean_dec(v_v_3709_);
lean_dec(v_k_3708_);
lean_inc(v_m_u2082_3706_);
lean_inc_ref(v_cmp_3705_);
v_impl_3713_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3705_, v_m_u2082_3706_, v_l_3710_);
v_impl_3714_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3705_, v_m_u2082_3706_, v_r_3711_);
v___x_3715_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_3713_, v_impl_3714_);
return v___x_3715_;
}
else
{
lean_object* v_impl_3716_; lean_object* v_impl_3717_; lean_object* v___x_3718_; 
lean_inc(v_m_u2082_3706_);
lean_inc_ref(v_cmp_3705_);
v_impl_3716_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3705_, v_m_u2082_3706_, v_l_3710_);
v_impl_3717_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3705_, v_m_u2082_3706_, v_r_3711_);
v___x_3718_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_3708_, v_v_3709_, v_impl_3716_, v_impl_3717_);
return v___x_3718_;
}
}
else
{
lean_dec(v_m_u2082_3706_);
lean_dec_ref(v_cmp_3705_);
return v_t_3707_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_3719_, lean_object* v_t_3720_, lean_object* v_k_3721_){
_start:
{
if (lean_obj_tag(v_t_3720_) == 0)
{
lean_object* v_k_3722_; lean_object* v_v_3723_; lean_object* v_l_3724_; lean_object* v_r_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; 
v_k_3722_ = lean_ctor_get(v_t_3720_, 1);
lean_inc_n(v_k_3722_, 2);
v_v_3723_ = lean_ctor_get(v_t_3720_, 2);
lean_inc(v_v_3723_);
v_l_3724_ = lean_ctor_get(v_t_3720_, 3);
lean_inc(v_l_3724_);
v_r_3725_ = lean_ctor_get(v_t_3720_, 4);
lean_inc(v_r_3725_);
lean_dec_ref_known(v_t_3720_, 5);
lean_inc_ref(v_cmp_3719_);
lean_inc(v_k_3721_);
v___x_3726_ = lean_apply_2(v_cmp_3719_, v_k_3721_, v_k_3722_);
v___x_3727_ = lean_unbox(v___x_3726_);
switch(v___x_3727_)
{
case 0:
{
lean_dec(v_r_3725_);
lean_dec(v_v_3723_);
lean_dec(v_k_3722_);
v_t_3720_ = v_l_3724_;
goto _start;
}
case 1:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
lean_dec(v_r_3725_);
lean_dec(v_l_3724_);
lean_dec(v_k_3721_);
lean_dec_ref(v_cmp_3719_);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v_k_3722_);
lean_ctor_set(v___x_3729_, 1, v_v_3723_);
v___x_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
return v___x_3730_;
}
default: 
{
lean_dec(v_l_3724_);
lean_dec(v_v_3723_);
lean_dec(v_k_3722_);
v_t_3720_ = v_r_3725_;
goto _start;
}
}
}
else
{
lean_object* v___x_3732_; 
lean_dec(v_k_3721_);
lean_dec_ref(v_cmp_3719_);
v___x_3732_ = lean_box(0);
return v___x_3732_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_cmp_3733_, lean_object* v_m_u2081_3734_, lean_object* v_init_3735_, lean_object* v_x_3736_){
_start:
{
if (lean_obj_tag(v_x_3736_) == 0)
{
lean_object* v_k_3737_; lean_object* v_l_3738_; lean_object* v_r_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v_k_3737_ = lean_ctor_get(v_x_3736_, 1);
lean_inc(v_k_3737_);
v_l_3738_ = lean_ctor_get(v_x_3736_, 3);
lean_inc(v_l_3738_);
v_r_3739_ = lean_ctor_get(v_x_3736_, 4);
lean_inc(v_r_3739_);
lean_dec_ref_known(v_x_3736_, 5);
lean_inc_n(v_m_u2081_3734_, 2);
lean_inc_ref_n(v_cmp_3733_, 2);
v___x_3740_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3733_, v_m_u2081_3734_, v_init_3735_, v_l_3738_);
v___x_3741_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3733_, v_m_u2081_3734_, v_k_3737_);
if (lean_obj_tag(v___x_3741_) == 0)
{
v_init_3735_ = v___x_3740_;
v_x_3736_ = v_r_3739_;
goto _start;
}
else
{
lean_object* v_val_3743_; lean_object* v_fst_3744_; lean_object* v_snd_3745_; lean_object* v_impl_3746_; 
v_val_3743_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_val_3743_);
lean_dec_ref_known(v___x_3741_, 1);
v_fst_3744_ = lean_ctor_get(v_val_3743_, 0);
lean_inc(v_fst_3744_);
v_snd_3745_ = lean_ctor_get(v_val_3743_, 1);
lean_inc(v_snd_3745_);
lean_dec(v_val_3743_);
lean_inc_ref(v_cmp_3733_);
v_impl_3746_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3733_, v_fst_3744_, v_snd_3745_, v___x_3740_);
v_init_3735_ = v_impl_3746_;
v_x_3736_ = v_r_3739_;
goto _start;
}
}
else
{
lean_dec(v_m_u2081_3734_);
lean_dec_ref(v_cmp_3733_);
return v_init_3735_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(lean_object* v_cmp_3748_, lean_object* v_m_u2081_3749_, lean_object* v_m_u2082_3750_){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3751_ = lean_box(1);
v___x_3752_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3748_, v_m_u2081_3749_, v___x_3751_, v_m_u2082_3750_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(lean_object* v_cmp_3753_, lean_object* v_m_u2081_3754_, lean_object* v_m_u2082_3755_){
_start:
{
lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3763_; 
if (lean_obj_tag(v_m_u2081_3754_) == 0)
{
lean_object* v_size_3766_; 
v_size_3766_ = lean_ctor_get(v_m_u2081_3754_, 0);
lean_inc(v_size_3766_);
v___y_3763_ = v_size_3766_;
goto v___jp_3762_;
}
else
{
lean_object* v___x_3767_; 
v___x_3767_ = lean_unsigned_to_nat(0u);
v___y_3763_ = v___x_3767_;
goto v___jp_3762_;
}
v___jp_3756_:
{
uint8_t v___x_3759_; 
v___x_3759_ = lean_nat_dec_le(v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec(v___y_3757_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; 
v___x_3760_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(v_cmp_3753_, v_m_u2081_3754_, v_m_u2082_3755_);
return v___x_3760_;
}
else
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3753_, v_m_u2082_3755_, v_m_u2081_3754_);
return v___x_3761_;
}
}
v___jp_3762_:
{
if (lean_obj_tag(v_m_u2082_3755_) == 0)
{
lean_object* v_size_3764_; 
v_size_3764_ = lean_ctor_get(v_m_u2082_3755_, 0);
lean_inc(v_size_3764_);
v___y_3757_ = v___y_3763_;
v___y_3758_ = v_size_3764_;
goto v___jp_3756_;
}
else
{
lean_object* v___x_3765_; 
v___x_3765_ = lean_unsigned_to_nat(0u);
v___y_3757_ = v___y_3763_;
v___y_3758_ = v___x_3765_;
goto v___jp_3756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_inter___redArg(lean_object* v_cmp_3768_, lean_object* v_t_u2081_3769_, lean_object* v_t_u2082_3770_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3768_, v_t_u2081_3769_, v_t_u2082_3770_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_inter(lean_object* v_00_u03b1_3772_, lean_object* v_00_u03b2_3773_, lean_object* v_cmp_3774_, lean_object* v_t_u2081_3775_, lean_object* v_t_u2082_3776_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3774_, v_t_u2081_3775_, v_t_u2082_3776_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0(lean_object* v_00_u03b1_3778_, lean_object* v_cmp_3779_, lean_object* v_00_u03b2_3780_, lean_object* v_m_u2081_3781_, lean_object* v_m_u2082_3782_, lean_object* v_h_u2081_3783_){
_start:
{
lean_object* v___x_3784_; 
v___x_3784_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3779_, v_m_u2081_3781_, v_m_u2082_3782_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0(lean_object* v_00_u03b1_3785_, lean_object* v_cmp_3786_, lean_object* v_00_u03b2_3787_, lean_object* v_m_u2081_3788_, lean_object* v_m_u2082_3789_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(v_cmp_3786_, v_m_u2081_3788_, v_m_u2082_3789_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1(lean_object* v_00_u03b1_3791_, lean_object* v_00_u03b2_3792_, lean_object* v_cmp_3793_, lean_object* v_m_u2082_3794_, lean_object* v_t_3795_, lean_object* v_hl_3796_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3793_, v_m_u2082_3794_, v_t_3795_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3798_, lean_object* v_cmp_3799_, lean_object* v_00_u03b2_3800_, lean_object* v_t_3801_, lean_object* v_k_3802_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3799_, v_t_3801_, v_k_3802_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2___redArg(lean_object* v_cmp_3804_, lean_object* v_m_u2081_3805_, lean_object* v_init_3806_, lean_object* v_t_3807_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3804_, v_m_u2081_3805_, v_init_3806_, v_t_3807_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3809_, lean_object* v_00_u03b2_3810_, lean_object* v_cmp_3811_, lean_object* v_m_u2081_3812_, lean_object* v_init_3813_, lean_object* v_t_3814_){
_start:
{
lean_object* v___x_3815_; 
v___x_3815_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3811_, v_m_u2081_3812_, v_init_3813_, v_t_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_3816_, lean_object* v_00_u03b2_3817_, lean_object* v_cmp_3818_, lean_object* v_m_u2081_3819_, lean_object* v_init_3820_, lean_object* v_x_3821_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3818_, v_m_u2081_3819_, v_init_3820_, v_x_3821_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInter___redArg(lean_object* v_cmp_3823_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_alloc_closure((void*)(l_Std_DTreeMap_inter), 5, 3);
lean_closure_set(v___x_3824_, 0, lean_box(0));
lean_closure_set(v___x_3824_, 1, lean_box(0));
lean_closure_set(v___x_3824_, 2, v_cmp_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInter(lean_object* v_00_u03b1_3825_, lean_object* v_00_u03b2_3826_, lean_object* v_cmp_3827_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_alloc_closure((void*)(l_Std_DTreeMap_inter), 5, 3);
lean_closure_set(v___x_3828_, 0, lean_box(0));
lean_closure_set(v___x_3828_, 1, lean_box(0));
lean_closure_set(v___x_3828_, 2, v_cmp_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_beq___redArg(lean_object* v_cmp_3829_, lean_object* v_inst_3830_, lean_object* v_t_u2081_3831_, lean_object* v_t_u2082_3832_){
_start:
{
uint8_t v___x_3833_; 
v___x_3833_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3829_, v_inst_3830_, v_t_u2081_3831_, v_t_u2082_3832_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_beq___redArg___boxed(lean_object* v_cmp_3834_, lean_object* v_inst_3835_, lean_object* v_t_u2081_3836_, lean_object* v_t_u2082_3837_){
_start:
{
uint8_t v_res_3838_; lean_object* v_r_3839_; 
v_res_3838_ = l_Std_DTreeMap_beq___redArg(v_cmp_3834_, v_inst_3835_, v_t_u2081_3836_, v_t_u2082_3837_);
v_r_3839_ = lean_box(v_res_3838_);
return v_r_3839_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_beq(lean_object* v_00_u03b1_3840_, lean_object* v_00_u03b2_3841_, lean_object* v_cmp_3842_, lean_object* v_inst_3843_, lean_object* v_inst_3844_, lean_object* v_t_u2081_3845_, lean_object* v_t_u2082_3846_){
_start:
{
uint8_t v___x_3847_; 
v___x_3847_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3842_, v_inst_3844_, v_t_u2081_3845_, v_t_u2082_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_beq___boxed(lean_object* v_00_u03b1_3848_, lean_object* v_00_u03b2_3849_, lean_object* v_cmp_3850_, lean_object* v_inst_3851_, lean_object* v_inst_3852_, lean_object* v_t_u2081_3853_, lean_object* v_t_u2082_3854_){
_start:
{
uint8_t v_res_3855_; lean_object* v_r_3856_; 
v_res_3855_ = l_Std_DTreeMap_beq(v_00_u03b1_3848_, v_00_u03b2_3849_, v_cmp_3850_, v_inst_3851_, v_inst_3852_, v_t_u2081_3853_, v_t_u2082_3854_);
v_r_3856_ = lean_box(v_res_3855_);
return v_r_3856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instBEqOfLawfulEqCmp___redArg(lean_object* v_cmp_3857_, lean_object* v_inst_3858_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = lean_alloc_closure((void*)(l_Std_DTreeMap_beq___boxed), 7, 5);
lean_closure_set(v___x_3859_, 0, lean_box(0));
lean_closure_set(v___x_3859_, 1, lean_box(0));
lean_closure_set(v___x_3859_, 2, v_cmp_3857_);
lean_closure_set(v___x_3859_, 3, lean_box(0));
lean_closure_set(v___x_3859_, 4, v_inst_3858_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instBEqOfLawfulEqCmp(lean_object* v_00_u03b1_3860_, lean_object* v_00_u03b2_3861_, lean_object* v_cmp_3862_, lean_object* v_inst_3863_, lean_object* v_inst_3864_){
_start:
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_alloc_closure((void*)(l_Std_DTreeMap_beq___boxed), 7, 5);
lean_closure_set(v___x_3865_, 0, lean_box(0));
lean_closure_set(v___x_3865_, 1, lean_box(0));
lean_closure_set(v___x_3865_, 2, v_cmp_3862_);
lean_closure_set(v___x_3865_, 3, lean_box(0));
lean_closure_set(v___x_3865_, 4, v_inst_3864_);
return v___x_3865_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___redArg(lean_object* v_cmp_3866_, lean_object* v_inst_3867_, lean_object* v_t_u2081_3868_, lean_object* v_t_u2082_3869_){
_start:
{
uint8_t v___x_3870_; 
v___x_3870_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3866_, v_inst_3867_, v_t_u2081_3868_, v_t_u2082_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___redArg___boxed(lean_object* v_cmp_3871_, lean_object* v_inst_3872_, lean_object* v_t_u2081_3873_, lean_object* v_t_u2082_3874_){
_start:
{
uint8_t v_res_3875_; lean_object* v_r_3876_; 
v_res_3875_ = l_Std_DTreeMap_Const_beq___redArg(v_cmp_3871_, v_inst_3872_, v_t_u2081_3873_, v_t_u2082_3874_);
v_r_3876_ = lean_box(v_res_3875_);
return v_r_3876_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq(lean_object* v_00_u03b1_3877_, lean_object* v_cmp_3878_, lean_object* v_00_u03b2_3879_, lean_object* v_inst_3880_, lean_object* v_t_u2081_3881_, lean_object* v_t_u2082_3882_){
_start:
{
uint8_t v___x_3883_; 
v___x_3883_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3878_, v_inst_3880_, v_t_u2081_3881_, v_t_u2082_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___boxed(lean_object* v_00_u03b1_3884_, lean_object* v_cmp_3885_, lean_object* v_00_u03b2_3886_, lean_object* v_inst_3887_, lean_object* v_t_u2081_3888_, lean_object* v_t_u2082_3889_){
_start:
{
uint8_t v_res_3890_; lean_object* v_r_3891_; 
v_res_3890_ = l_Std_DTreeMap_Const_beq(v_00_u03b1_3884_, v_cmp_3885_, v_00_u03b2_3886_, v_inst_3887_, v_t_u2081_3888_, v_t_u2082_3889_);
v_r_3891_ = lean_box(v_res_3890_);
return v_r_3891_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(lean_object* v_cmp_3892_, lean_object* v_k_3893_, lean_object* v_t_3894_){
_start:
{
if (lean_obj_tag(v_t_3894_) == 0)
{
lean_object* v_k_3895_; lean_object* v_v_3896_; lean_object* v_l_3897_; lean_object* v_r_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_4553_; 
v_k_3895_ = lean_ctor_get(v_t_3894_, 1);
v_v_3896_ = lean_ctor_get(v_t_3894_, 2);
v_l_3897_ = lean_ctor_get(v_t_3894_, 3);
v_r_3898_ = lean_ctor_get(v_t_3894_, 4);
v_isSharedCheck_4553_ = !lean_is_exclusive(v_t_3894_);
if (v_isSharedCheck_4553_ == 0)
{
lean_object* v_unused_4554_; 
v_unused_4554_ = lean_ctor_get(v_t_3894_, 0);
lean_dec(v_unused_4554_);
v___x_3900_ = v_t_3894_;
v_isShared_3901_ = v_isSharedCheck_4553_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_r_3898_);
lean_inc(v_l_3897_);
lean_inc(v_v_3896_);
lean_inc(v_k_3895_);
lean_dec(v_t_3894_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_4553_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; uint8_t v___x_3903_; 
lean_inc_ref(v_cmp_3892_);
lean_inc(v_k_3895_);
lean_inc(v_k_3893_);
v___x_3902_ = lean_apply_2(v_cmp_3892_, v_k_3893_, v_k_3895_);
v___x_3903_ = lean_unbox(v___x_3902_);
switch(v___x_3903_)
{
case 0:
{
lean_object* v_impl_3904_; lean_object* v___x_3905_; 
v_impl_3904_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_3892_, v_k_3893_, v_l_3897_);
v___x_3905_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3904_) == 0)
{
if (lean_obj_tag(v_r_3898_) == 0)
{
lean_object* v_size_3906_; lean_object* v_size_3907_; lean_object* v_k_3908_; lean_object* v_v_3909_; lean_object* v_l_3910_; lean_object* v_r_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; 
v_size_3906_ = lean_ctor_get(v_impl_3904_, 0);
v_size_3907_ = lean_ctor_get(v_r_3898_, 0);
v_k_3908_ = lean_ctor_get(v_r_3898_, 1);
v_v_3909_ = lean_ctor_get(v_r_3898_, 2);
v_l_3910_ = lean_ctor_get(v_r_3898_, 3);
lean_inc(v_l_3910_);
v_r_3911_ = lean_ctor_get(v_r_3898_, 4);
v___x_3912_ = lean_unsigned_to_nat(3u);
v___x_3913_ = lean_nat_mul(v___x_3912_, v_size_3906_);
v___x_3914_ = lean_nat_dec_lt(v___x_3913_, v_size_3907_);
lean_dec(v___x_3913_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3918_; 
lean_dec(v_l_3910_);
v___x_3915_ = lean_nat_add(v___x_3905_, v_size_3906_);
v___x_3916_ = lean_nat_add(v___x_3915_, v_size_3907_);
lean_dec(v___x_3915_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 3, v_impl_3904_);
lean_ctor_set(v___x_3900_, 0, v___x_3916_);
v___x_3918_ = v___x_3900_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_3919_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_3919_, 3, v_impl_3904_);
lean_ctor_set(v_reuseFailAlloc_3919_, 4, v_r_3898_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
else
{
lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3983_; 
lean_inc(v_r_3911_);
lean_inc(v_v_3909_);
lean_inc(v_k_3908_);
lean_inc(v_size_3907_);
v_isSharedCheck_3983_ = !lean_is_exclusive(v_r_3898_);
if (v_isSharedCheck_3983_ == 0)
{
lean_object* v_unused_3984_; lean_object* v_unused_3985_; lean_object* v_unused_3986_; lean_object* v_unused_3987_; lean_object* v_unused_3988_; 
v_unused_3984_ = lean_ctor_get(v_r_3898_, 4);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_r_3898_, 3);
lean_dec(v_unused_3985_);
v_unused_3986_ = lean_ctor_get(v_r_3898_, 2);
lean_dec(v_unused_3986_);
v_unused_3987_ = lean_ctor_get(v_r_3898_, 1);
lean_dec(v_unused_3987_);
v_unused_3988_ = lean_ctor_get(v_r_3898_, 0);
lean_dec(v_unused_3988_);
v___x_3921_ = v_r_3898_;
v_isShared_3922_ = v_isSharedCheck_3983_;
goto v_resetjp_3920_;
}
else
{
lean_dec(v_r_3898_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3983_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v_size_3923_; lean_object* v_k_3924_; lean_object* v_v_3925_; lean_object* v_l_3926_; lean_object* v_r_3927_; lean_object* v_size_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; uint8_t v___x_3931_; 
v_size_3923_ = lean_ctor_get(v_l_3910_, 0);
v_k_3924_ = lean_ctor_get(v_l_3910_, 1);
v_v_3925_ = lean_ctor_get(v_l_3910_, 2);
v_l_3926_ = lean_ctor_get(v_l_3910_, 3);
v_r_3927_ = lean_ctor_get(v_l_3910_, 4);
v_size_3928_ = lean_ctor_get(v_r_3911_, 0);
v___x_3929_ = lean_unsigned_to_nat(2u);
v___x_3930_ = lean_nat_mul(v___x_3929_, v_size_3928_);
v___x_3931_ = lean_nat_dec_lt(v_size_3923_, v___x_3930_);
lean_dec(v___x_3930_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3959_; 
lean_inc(v_r_3927_);
lean_inc(v_l_3926_);
lean_inc(v_v_3925_);
lean_inc(v_k_3924_);
v_isSharedCheck_3959_ = !lean_is_exclusive(v_l_3910_);
if (v_isSharedCheck_3959_ == 0)
{
lean_object* v_unused_3960_; lean_object* v_unused_3961_; lean_object* v_unused_3962_; lean_object* v_unused_3963_; lean_object* v_unused_3964_; 
v_unused_3960_ = lean_ctor_get(v_l_3910_, 4);
lean_dec(v_unused_3960_);
v_unused_3961_ = lean_ctor_get(v_l_3910_, 3);
lean_dec(v_unused_3961_);
v_unused_3962_ = lean_ctor_get(v_l_3910_, 2);
lean_dec(v_unused_3962_);
v_unused_3963_ = lean_ctor_get(v_l_3910_, 1);
lean_dec(v_unused_3963_);
v_unused_3964_ = lean_ctor_get(v_l_3910_, 0);
lean_dec(v_unused_3964_);
v___x_3933_ = v_l_3910_;
v_isShared_3934_ = v_isSharedCheck_3959_;
goto v_resetjp_3932_;
}
else
{
lean_dec(v_l_3910_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3959_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3949_; 
v___x_3935_ = lean_nat_add(v___x_3905_, v_size_3906_);
v___x_3936_ = lean_nat_add(v___x_3935_, v_size_3907_);
lean_dec(v_size_3907_);
if (lean_obj_tag(v_l_3926_) == 0)
{
lean_object* v_size_3957_; 
v_size_3957_ = lean_ctor_get(v_l_3926_, 0);
lean_inc(v_size_3957_);
v___y_3949_ = v_size_3957_;
goto v___jp_3948_;
}
else
{
lean_object* v___x_3958_; 
v___x_3958_ = lean_unsigned_to_nat(0u);
v___y_3949_ = v___x_3958_;
goto v___jp_3948_;
}
v___jp_3937_:
{
lean_object* v___x_3941_; lean_object* v___x_3943_; 
v___x_3941_ = lean_nat_add(v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec(v___y_3939_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 4, v_r_3911_);
lean_ctor_set(v___x_3933_, 3, v_r_3927_);
lean_ctor_set(v___x_3933_, 2, v_v_3909_);
lean_ctor_set(v___x_3933_, 1, v_k_3908_);
lean_ctor_set(v___x_3933_, 0, v___x_3941_);
v___x_3943_ = v___x_3933_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3941_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v_k_3908_);
lean_ctor_set(v_reuseFailAlloc_3947_, 2, v_v_3909_);
lean_ctor_set(v_reuseFailAlloc_3947_, 3, v_r_3927_);
lean_ctor_set(v_reuseFailAlloc_3947_, 4, v_r_3911_);
v___x_3943_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
lean_object* v___x_3945_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v___x_3943_);
lean_ctor_set(v___x_3921_, 3, v___y_3938_);
lean_ctor_set(v___x_3921_, 2, v_v_3925_);
lean_ctor_set(v___x_3921_, 1, v_k_3924_);
lean_ctor_set(v___x_3921_, 0, v___x_3936_);
v___x_3945_ = v___x_3921_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_k_3924_);
lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_v_3925_);
lean_ctor_set(v_reuseFailAlloc_3946_, 3, v___y_3938_);
lean_ctor_set(v_reuseFailAlloc_3946_, 4, v___x_3943_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
v___jp_3948_:
{
lean_object* v___x_3950_; lean_object* v___x_3952_; 
v___x_3950_ = lean_nat_add(v___x_3935_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec(v___x_3935_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v_l_3926_);
lean_ctor_set(v___x_3900_, 3, v_impl_3904_);
lean_ctor_set(v___x_3900_, 0, v___x_3950_);
v___x_3952_ = v___x_3900_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3950_);
lean_ctor_set(v_reuseFailAlloc_3956_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_3956_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_3956_, 3, v_impl_3904_);
lean_ctor_set(v_reuseFailAlloc_3956_, 4, v_l_3926_);
v___x_3952_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
lean_object* v___x_3953_; 
v___x_3953_ = lean_nat_add(v___x_3905_, v_size_3928_);
if (lean_obj_tag(v_r_3927_) == 0)
{
lean_object* v_size_3954_; 
v_size_3954_ = lean_ctor_get(v_r_3927_, 0);
lean_inc(v_size_3954_);
v___y_3938_ = v___x_3952_;
v___y_3939_ = v___x_3953_;
v___y_3940_ = v_size_3954_;
goto v___jp_3937_;
}
else
{
lean_object* v___x_3955_; 
v___x_3955_ = lean_unsigned_to_nat(0u);
v___y_3938_ = v___x_3952_;
v___y_3939_ = v___x_3953_;
v___y_3940_ = v___x_3955_;
goto v___jp_3937_;
}
}
}
}
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3969_; 
lean_del_object(v___x_3900_);
v___x_3965_ = lean_nat_add(v___x_3905_, v_size_3906_);
v___x_3966_ = lean_nat_add(v___x_3965_, v_size_3907_);
lean_dec(v_size_3907_);
v___x_3967_ = lean_nat_add(v___x_3965_, v_size_3923_);
lean_dec(v___x_3965_);
lean_inc_ref(v_impl_3904_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v_l_3910_);
lean_ctor_set(v___x_3921_, 3, v_impl_3904_);
lean_ctor_set(v___x_3921_, 2, v_v_3896_);
lean_ctor_set(v___x_3921_, 1, v_k_3895_);
lean_ctor_set(v___x_3921_, 0, v___x_3967_);
v___x_3969_ = v___x_3921_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3967_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_3982_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_3982_, 3, v_impl_3904_);
lean_ctor_set(v_reuseFailAlloc_3982_, 4, v_l_3910_);
v___x_3969_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
v_isSharedCheck_3976_ = !lean_is_exclusive(v_impl_3904_);
if (v_isSharedCheck_3976_ == 0)
{
lean_object* v_unused_3977_; lean_object* v_unused_3978_; lean_object* v_unused_3979_; lean_object* v_unused_3980_; lean_object* v_unused_3981_; 
v_unused_3977_ = lean_ctor_get(v_impl_3904_, 4);
lean_dec(v_unused_3977_);
v_unused_3978_ = lean_ctor_get(v_impl_3904_, 3);
lean_dec(v_unused_3978_);
v_unused_3979_ = lean_ctor_get(v_impl_3904_, 2);
lean_dec(v_unused_3979_);
v_unused_3980_ = lean_ctor_get(v_impl_3904_, 1);
lean_dec(v_unused_3980_);
v_unused_3981_ = lean_ctor_get(v_impl_3904_, 0);
lean_dec(v_unused_3981_);
v___x_3971_ = v_impl_3904_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_dec(v_impl_3904_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 4, v_r_3911_);
lean_ctor_set(v___x_3971_, 3, v___x_3969_);
lean_ctor_set(v___x_3971_, 2, v_v_3909_);
lean_ctor_set(v___x_3971_, 1, v_k_3908_);
lean_ctor_set(v___x_3971_, 0, v___x_3966_);
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3966_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v_k_3908_);
lean_ctor_set(v_reuseFailAlloc_3975_, 2, v_v_3909_);
lean_ctor_set(v_reuseFailAlloc_3975_, 3, v___x_3969_);
lean_ctor_set(v_reuseFailAlloc_3975_, 4, v_r_3911_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3989_; lean_object* v___x_3990_; lean_object* v___x_3992_; 
v_size_3989_ = lean_ctor_get(v_impl_3904_, 0);
v___x_3990_ = lean_nat_add(v___x_3905_, v_size_3989_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 3, v_impl_3904_);
lean_ctor_set(v___x_3900_, 0, v___x_3990_);
v___x_3992_ = v___x_3900_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3990_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_3993_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_3993_, 3, v_impl_3904_);
lean_ctor_set(v_reuseFailAlloc_3993_, 4, v_r_3898_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
else
{
if (lean_obj_tag(v_r_3898_) == 0)
{
lean_object* v_l_3994_; 
v_l_3994_ = lean_ctor_get(v_r_3898_, 3);
lean_inc(v_l_3994_);
if (lean_obj_tag(v_l_3994_) == 0)
{
lean_object* v_r_3995_; 
v_r_3995_ = lean_ctor_get(v_r_3898_, 4);
lean_inc(v_r_3995_);
if (lean_obj_tag(v_r_3995_) == 0)
{
lean_object* v_size_3996_; lean_object* v_k_3997_; lean_object* v_v_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4011_; 
v_size_3996_ = lean_ctor_get(v_r_3898_, 0);
v_k_3997_ = lean_ctor_get(v_r_3898_, 1);
v_v_3998_ = lean_ctor_get(v_r_3898_, 2);
v_isSharedCheck_4011_ = !lean_is_exclusive(v_r_3898_);
if (v_isSharedCheck_4011_ == 0)
{
lean_object* v_unused_4012_; lean_object* v_unused_4013_; 
v_unused_4012_ = lean_ctor_get(v_r_3898_, 4);
lean_dec(v_unused_4012_);
v_unused_4013_ = lean_ctor_get(v_r_3898_, 3);
lean_dec(v_unused_4013_);
v___x_4000_ = v_r_3898_;
v_isShared_4001_ = v_isSharedCheck_4011_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_v_3998_);
lean_inc(v_k_3997_);
lean_inc(v_size_3996_);
lean_dec(v_r_3898_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4011_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v_size_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4006_; 
v_size_4002_ = lean_ctor_get(v_l_3994_, 0);
v___x_4003_ = lean_nat_add(v___x_3905_, v_size_3996_);
lean_dec(v_size_3996_);
v___x_4004_ = lean_nat_add(v___x_3905_, v_size_4002_);
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 4, v_l_3994_);
lean_ctor_set(v___x_4000_, 3, v_impl_3904_);
lean_ctor_set(v___x_4000_, 2, v_v_3896_);
lean_ctor_set(v___x_4000_, 1, v_k_3895_);
lean_ctor_set(v___x_4000_, 0, v___x_4004_);
v___x_4006_ = v___x_4000_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4004_);
lean_ctor_set(v_reuseFailAlloc_4010_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4010_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4010_, 3, v_impl_3904_);
lean_ctor_set(v_reuseFailAlloc_4010_, 4, v_l_3994_);
v___x_4006_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
lean_object* v___x_4008_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v_r_3995_);
lean_ctor_set(v___x_3900_, 3, v___x_4006_);
lean_ctor_set(v___x_3900_, 2, v_v_3998_);
lean_ctor_set(v___x_3900_, 1, v_k_3997_);
lean_ctor_set(v___x_3900_, 0, v___x_4003_);
v___x_4008_ = v___x_3900_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_4003_);
lean_ctor_set(v_reuseFailAlloc_4009_, 1, v_k_3997_);
lean_ctor_set(v_reuseFailAlloc_4009_, 2, v_v_3998_);
lean_ctor_set(v_reuseFailAlloc_4009_, 3, v___x_4006_);
lean_ctor_set(v_reuseFailAlloc_4009_, 4, v_r_3995_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
else
{
lean_object* v_k_4014_; lean_object* v_v_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4038_; 
v_k_4014_ = lean_ctor_get(v_r_3898_, 1);
v_v_4015_ = lean_ctor_get(v_r_3898_, 2);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_r_3898_);
if (v_isSharedCheck_4038_ == 0)
{
lean_object* v_unused_4039_; lean_object* v_unused_4040_; lean_object* v_unused_4041_; 
v_unused_4039_ = lean_ctor_get(v_r_3898_, 4);
lean_dec(v_unused_4039_);
v_unused_4040_ = lean_ctor_get(v_r_3898_, 3);
lean_dec(v_unused_4040_);
v_unused_4041_ = lean_ctor_get(v_r_3898_, 0);
lean_dec(v_unused_4041_);
v___x_4017_ = v_r_3898_;
v_isShared_4018_ = v_isSharedCheck_4038_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_v_4015_);
lean_inc(v_k_4014_);
lean_dec(v_r_3898_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4038_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v_k_4019_; lean_object* v_v_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4034_; 
v_k_4019_ = lean_ctor_get(v_l_3994_, 1);
v_v_4020_ = lean_ctor_get(v_l_3994_, 2);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_l_3994_);
if (v_isSharedCheck_4034_ == 0)
{
lean_object* v_unused_4035_; lean_object* v_unused_4036_; lean_object* v_unused_4037_; 
v_unused_4035_ = lean_ctor_get(v_l_3994_, 4);
lean_dec(v_unused_4035_);
v_unused_4036_ = lean_ctor_get(v_l_3994_, 3);
lean_dec(v_unused_4036_);
v_unused_4037_ = lean_ctor_get(v_l_3994_, 0);
lean_dec(v_unused_4037_);
v___x_4022_ = v_l_3994_;
v_isShared_4023_ = v_isSharedCheck_4034_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_v_4020_);
lean_inc(v_k_4019_);
lean_dec(v_l_3994_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4034_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4026_; 
v___x_4024_ = lean_unsigned_to_nat(3u);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 4, v_r_3995_);
lean_ctor_set(v___x_4022_, 3, v_r_3995_);
lean_ctor_set(v___x_4022_, 2, v_v_3896_);
lean_ctor_set(v___x_4022_, 1, v_k_3895_);
lean_ctor_set(v___x_4022_, 0, v___x_3905_);
v___x_4026_ = v___x_4022_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4033_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4033_, 3, v_r_3995_);
lean_ctor_set(v_reuseFailAlloc_4033_, 4, v_r_3995_);
v___x_4026_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
lean_object* v___x_4028_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 3, v_r_3995_);
lean_ctor_set(v___x_4017_, 0, v___x_3905_);
v___x_4028_ = v___x_4017_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_4032_, 1, v_k_4014_);
lean_ctor_set(v_reuseFailAlloc_4032_, 2, v_v_4015_);
lean_ctor_set(v_reuseFailAlloc_4032_, 3, v_r_3995_);
lean_ctor_set(v_reuseFailAlloc_4032_, 4, v_r_3995_);
v___x_4028_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4030_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v___x_4028_);
lean_ctor_set(v___x_3900_, 3, v___x_4026_);
lean_ctor_set(v___x_3900_, 2, v_v_4020_);
lean_ctor_set(v___x_3900_, 1, v_k_4019_);
lean_ctor_set(v___x_3900_, 0, v___x_4024_);
v___x_4030_ = v___x_3900_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4024_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v_k_4019_);
lean_ctor_set(v_reuseFailAlloc_4031_, 2, v_v_4020_);
lean_ctor_set(v_reuseFailAlloc_4031_, 3, v___x_4026_);
lean_ctor_set(v_reuseFailAlloc_4031_, 4, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_4042_; 
v_r_4042_ = lean_ctor_get(v_r_3898_, 4);
lean_inc(v_r_4042_);
if (lean_obj_tag(v_r_4042_) == 0)
{
lean_object* v_k_4043_; lean_object* v_v_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4055_; 
v_k_4043_ = lean_ctor_get(v_r_3898_, 1);
v_v_4044_ = lean_ctor_get(v_r_3898_, 2);
v_isSharedCheck_4055_ = !lean_is_exclusive(v_r_3898_);
if (v_isSharedCheck_4055_ == 0)
{
lean_object* v_unused_4056_; lean_object* v_unused_4057_; lean_object* v_unused_4058_; 
v_unused_4056_ = lean_ctor_get(v_r_3898_, 4);
lean_dec(v_unused_4056_);
v_unused_4057_ = lean_ctor_get(v_r_3898_, 3);
lean_dec(v_unused_4057_);
v_unused_4058_ = lean_ctor_get(v_r_3898_, 0);
lean_dec(v_unused_4058_);
v___x_4046_ = v_r_3898_;
v_isShared_4047_ = v_isSharedCheck_4055_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_v_4044_);
lean_inc(v_k_4043_);
lean_dec(v_r_3898_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4055_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4048_; lean_object* v___x_4050_; 
v___x_4048_ = lean_unsigned_to_nat(3u);
if (v_isShared_4047_ == 0)
{
lean_ctor_set(v___x_4046_, 4, v_l_3994_);
lean_ctor_set(v___x_4046_, 2, v_v_3896_);
lean_ctor_set(v___x_4046_, 1, v_k_3895_);
lean_ctor_set(v___x_4046_, 0, v___x_3905_);
v___x_4050_ = v___x_4046_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4054_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4054_, 3, v_l_3994_);
lean_ctor_set(v_reuseFailAlloc_4054_, 4, v_l_3994_);
v___x_4050_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4052_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v_r_4042_);
lean_ctor_set(v___x_3900_, 3, v___x_4050_);
lean_ctor_set(v___x_3900_, 2, v_v_4044_);
lean_ctor_set(v___x_3900_, 1, v_k_4043_);
lean_ctor_set(v___x_3900_, 0, v___x_4048_);
v___x_4052_ = v___x_3900_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4048_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_k_4043_);
lean_ctor_set(v_reuseFailAlloc_4053_, 2, v_v_4044_);
lean_ctor_set(v_reuseFailAlloc_4053_, 3, v___x_4050_);
lean_ctor_set(v_reuseFailAlloc_4053_, 4, v_r_4042_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
else
{
lean_object* v_size_4059_; lean_object* v_k_4060_; lean_object* v_v_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4072_; 
v_size_4059_ = lean_ctor_get(v_r_3898_, 0);
v_k_4060_ = lean_ctor_get(v_r_3898_, 1);
v_v_4061_ = lean_ctor_get(v_r_3898_, 2);
v_isSharedCheck_4072_ = !lean_is_exclusive(v_r_3898_);
if (v_isSharedCheck_4072_ == 0)
{
lean_object* v_unused_4073_; lean_object* v_unused_4074_; 
v_unused_4073_ = lean_ctor_get(v_r_3898_, 4);
lean_dec(v_unused_4073_);
v_unused_4074_ = lean_ctor_get(v_r_3898_, 3);
lean_dec(v_unused_4074_);
v___x_4063_ = v_r_3898_;
v_isShared_4064_ = v_isSharedCheck_4072_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_v_4061_);
lean_inc(v_k_4060_);
lean_inc(v_size_4059_);
lean_dec(v_r_3898_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4072_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 3, v_r_4042_);
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_size_4059_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v_k_4060_);
lean_ctor_set(v_reuseFailAlloc_4071_, 2, v_v_4061_);
lean_ctor_set(v_reuseFailAlloc_4071_, 3, v_r_4042_);
lean_ctor_set(v_reuseFailAlloc_4071_, 4, v_r_4042_);
v___x_4066_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
lean_object* v___x_4067_; lean_object* v___x_4069_; 
v___x_4067_ = lean_unsigned_to_nat(2u);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v___x_4066_);
lean_ctor_set(v___x_3900_, 3, v_r_4042_);
lean_ctor_set(v___x_3900_, 0, v___x_4067_);
v___x_4069_ = v___x_3900_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4070_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4070_, 3, v_r_4042_);
lean_ctor_set(v_reuseFailAlloc_4070_, 4, v___x_4066_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
}
else
{
lean_object* v___x_4076_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 3, v_r_3898_);
lean_ctor_set(v___x_3900_, 0, v___x_3905_);
v___x_4076_ = v___x_3900_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4077_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4077_, 3, v_r_3898_);
lean_ctor_set(v_reuseFailAlloc_4077_, 4, v_r_3898_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3900_);
lean_dec(v_v_3896_);
lean_dec(v_k_3895_);
lean_dec(v_k_3893_);
lean_dec_ref(v_cmp_3892_);
if (lean_obj_tag(v_l_3897_) == 0)
{
if (lean_obj_tag(v_r_3898_) == 0)
{
lean_object* v_size_4078_; lean_object* v_k_4079_; lean_object* v_v_4080_; lean_object* v_l_4081_; lean_object* v_r_4082_; lean_object* v_size_4083_; lean_object* v_k_4084_; lean_object* v_v_4085_; lean_object* v_l_4086_; lean_object* v_r_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; 
v_size_4078_ = lean_ctor_get(v_l_3897_, 0);
v_k_4079_ = lean_ctor_get(v_l_3897_, 1);
v_v_4080_ = lean_ctor_get(v_l_3897_, 2);
v_l_4081_ = lean_ctor_get(v_l_3897_, 3);
v_r_4082_ = lean_ctor_get(v_l_3897_, 4);
lean_inc(v_r_4082_);
v_size_4083_ = lean_ctor_get(v_r_3898_, 0);
v_k_4084_ = lean_ctor_get(v_r_3898_, 1);
v_v_4085_ = lean_ctor_get(v_r_3898_, 2);
v_l_4086_ = lean_ctor_get(v_r_3898_, 3);
lean_inc(v_l_4086_);
v_r_4087_ = lean_ctor_get(v_r_3898_, 4);
v___x_4088_ = lean_unsigned_to_nat(1u);
v___x_4089_ = lean_nat_dec_lt(v_size_4078_, v_size_4083_);
if (v___x_4089_ == 0)
{
lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4225_; 
lean_inc(v_l_4081_);
lean_inc(v_v_4080_);
lean_inc(v_k_4079_);
v_isSharedCheck_4225_ = !lean_is_exclusive(v_l_3897_);
if (v_isSharedCheck_4225_ == 0)
{
lean_object* v_unused_4226_; lean_object* v_unused_4227_; lean_object* v_unused_4228_; lean_object* v_unused_4229_; lean_object* v_unused_4230_; 
v_unused_4226_ = lean_ctor_get(v_l_3897_, 4);
lean_dec(v_unused_4226_);
v_unused_4227_ = lean_ctor_get(v_l_3897_, 3);
lean_dec(v_unused_4227_);
v_unused_4228_ = lean_ctor_get(v_l_3897_, 2);
lean_dec(v_unused_4228_);
v_unused_4229_ = lean_ctor_get(v_l_3897_, 1);
lean_dec(v_unused_4229_);
v_unused_4230_ = lean_ctor_get(v_l_3897_, 0);
lean_dec(v_unused_4230_);
v___x_4091_ = v_l_3897_;
v_isShared_4092_ = v_isSharedCheck_4225_;
goto v_resetjp_4090_;
}
else
{
lean_dec(v_l_3897_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4225_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4093_; lean_object* v_tree_4094_; 
v___x_4093_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_4079_, v_v_4080_, v_l_4081_, v_r_4082_);
v_tree_4094_ = lean_ctor_get(v___x_4093_, 2);
if (lean_obj_tag(v_tree_4094_) == 0)
{
lean_object* v_k_4095_; lean_object* v_v_4096_; lean_object* v_size_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; uint8_t v___x_4100_; 
lean_inc_ref(v_tree_4094_);
v_k_4095_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_k_4095_);
v_v_4096_ = lean_ctor_get(v___x_4093_, 1);
lean_inc(v_v_4096_);
lean_dec_ref(v___x_4093_);
v_size_4097_ = lean_ctor_get(v_tree_4094_, 0);
v___x_4098_ = lean_unsigned_to_nat(3u);
v___x_4099_ = lean_nat_mul(v___x_4098_, v_size_4097_);
v___x_4100_ = lean_nat_dec_lt(v___x_4099_, v_size_4083_);
lean_dec(v___x_4099_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4104_; 
lean_dec(v_l_4086_);
v___x_4101_ = lean_nat_add(v___x_4088_, v_size_4097_);
v___x_4102_ = lean_nat_add(v___x_4101_, v_size_4083_);
lean_dec(v___x_4101_);
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 4, v_r_3898_);
lean_ctor_set(v___x_4091_, 3, v_tree_4094_);
lean_ctor_set(v___x_4091_, 2, v_v_4096_);
lean_ctor_set(v___x_4091_, 1, v_k_4095_);
lean_ctor_set(v___x_4091_, 0, v___x_4102_);
v___x_4104_ = v___x_4091_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4102_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v_k_4095_);
lean_ctor_set(v_reuseFailAlloc_4105_, 2, v_v_4096_);
lean_ctor_set(v_reuseFailAlloc_4105_, 3, v_tree_4094_);
lean_ctor_set(v_reuseFailAlloc_4105_, 4, v_r_3898_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
else
{
lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4160_; 
lean_inc(v_r_4087_);
lean_inc(v_v_4085_);
lean_inc(v_k_4084_);
lean_inc(v_size_4083_);
v_isSharedCheck_4160_ = !lean_is_exclusive(v_r_3898_);
if (v_isSharedCheck_4160_ == 0)
{
lean_object* v_unused_4161_; lean_object* v_unused_4162_; lean_object* v_unused_4163_; lean_object* v_unused_4164_; lean_object* v_unused_4165_; 
v_unused_4161_ = lean_ctor_get(v_r_3898_, 4);
lean_dec(v_unused_4161_);
v_unused_4162_ = lean_ctor_get(v_r_3898_, 3);
lean_dec(v_unused_4162_);
v_unused_4163_ = lean_ctor_get(v_r_3898_, 2);
lean_dec(v_unused_4163_);
v_unused_4164_ = lean_ctor_get(v_r_3898_, 1);
lean_dec(v_unused_4164_);
v_unused_4165_ = lean_ctor_get(v_r_3898_, 0);
lean_dec(v_unused_4165_);
v___x_4107_ = v_r_3898_;
v_isShared_4108_ = v_isSharedCheck_4160_;
goto v_resetjp_4106_;
}
else
{
lean_dec(v_r_3898_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4160_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v_size_4109_; lean_object* v_k_4110_; lean_object* v_v_4111_; lean_object* v_l_4112_; lean_object* v_r_4113_; lean_object* v_size_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; uint8_t v___x_4117_; 
v_size_4109_ = lean_ctor_get(v_l_4086_, 0);
v_k_4110_ = lean_ctor_get(v_l_4086_, 1);
v_v_4111_ = lean_ctor_get(v_l_4086_, 2);
v_l_4112_ = lean_ctor_get(v_l_4086_, 3);
v_r_4113_ = lean_ctor_get(v_l_4086_, 4);
v_size_4114_ = lean_ctor_get(v_r_4087_, 0);
v___x_4115_ = lean_unsigned_to_nat(2u);
v___x_4116_ = lean_nat_mul(v___x_4115_, v_size_4114_);
v___x_4117_ = lean_nat_dec_lt(v_size_4109_, v___x_4116_);
lean_dec(v___x_4116_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4145_; 
lean_inc(v_r_4113_);
lean_inc(v_l_4112_);
lean_inc(v_v_4111_);
lean_inc(v_k_4110_);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_l_4086_);
if (v_isSharedCheck_4145_ == 0)
{
lean_object* v_unused_4146_; lean_object* v_unused_4147_; lean_object* v_unused_4148_; lean_object* v_unused_4149_; lean_object* v_unused_4150_; 
v_unused_4146_ = lean_ctor_get(v_l_4086_, 4);
lean_dec(v_unused_4146_);
v_unused_4147_ = lean_ctor_get(v_l_4086_, 3);
lean_dec(v_unused_4147_);
v_unused_4148_ = lean_ctor_get(v_l_4086_, 2);
lean_dec(v_unused_4148_);
v_unused_4149_ = lean_ctor_get(v_l_4086_, 1);
lean_dec(v_unused_4149_);
v_unused_4150_ = lean_ctor_get(v_l_4086_, 0);
lean_dec(v_unused_4150_);
v___x_4119_ = v_l_4086_;
v_isShared_4120_ = v_isSharedCheck_4145_;
goto v_resetjp_4118_;
}
else
{
lean_dec(v_l_4086_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4145_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4135_; 
v___x_4121_ = lean_nat_add(v___x_4088_, v_size_4097_);
v___x_4122_ = lean_nat_add(v___x_4121_, v_size_4083_);
lean_dec(v_size_4083_);
if (lean_obj_tag(v_l_4112_) == 0)
{
lean_object* v_size_4143_; 
v_size_4143_ = lean_ctor_get(v_l_4112_, 0);
lean_inc(v_size_4143_);
v___y_4135_ = v_size_4143_;
goto v___jp_4134_;
}
else
{
lean_object* v___x_4144_; 
v___x_4144_ = lean_unsigned_to_nat(0u);
v___y_4135_ = v___x_4144_;
goto v___jp_4134_;
}
v___jp_4123_:
{
lean_object* v___x_4127_; lean_object* v___x_4129_; 
v___x_4127_ = lean_nat_add(v___y_4125_, v___y_4126_);
lean_dec(v___y_4126_);
lean_dec(v___y_4125_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 4, v_r_4087_);
lean_ctor_set(v___x_4119_, 3, v_r_4113_);
lean_ctor_set(v___x_4119_, 2, v_v_4085_);
lean_ctor_set(v___x_4119_, 1, v_k_4084_);
lean_ctor_set(v___x_4119_, 0, v___x_4127_);
v___x_4129_ = v___x_4119_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4127_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v_k_4084_);
lean_ctor_set(v_reuseFailAlloc_4133_, 2, v_v_4085_);
lean_ctor_set(v_reuseFailAlloc_4133_, 3, v_r_4113_);
lean_ctor_set(v_reuseFailAlloc_4133_, 4, v_r_4087_);
v___x_4129_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
lean_object* v___x_4131_; 
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 4, v___x_4129_);
lean_ctor_set(v___x_4107_, 3, v___y_4124_);
lean_ctor_set(v___x_4107_, 2, v_v_4111_);
lean_ctor_set(v___x_4107_, 1, v_k_4110_);
lean_ctor_set(v___x_4107_, 0, v___x_4122_);
v___x_4131_ = v___x_4107_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4122_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v_k_4110_);
lean_ctor_set(v_reuseFailAlloc_4132_, 2, v_v_4111_);
lean_ctor_set(v_reuseFailAlloc_4132_, 3, v___y_4124_);
lean_ctor_set(v_reuseFailAlloc_4132_, 4, v___x_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
v___jp_4134_:
{
lean_object* v___x_4136_; lean_object* v___x_4138_; 
v___x_4136_ = lean_nat_add(v___x_4121_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec(v___x_4121_);
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 4, v_l_4112_);
lean_ctor_set(v___x_4091_, 3, v_tree_4094_);
lean_ctor_set(v___x_4091_, 2, v_v_4096_);
lean_ctor_set(v___x_4091_, 1, v_k_4095_);
lean_ctor_set(v___x_4091_, 0, v___x_4136_);
v___x_4138_ = v___x_4091_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4136_);
lean_ctor_set(v_reuseFailAlloc_4142_, 1, v_k_4095_);
lean_ctor_set(v_reuseFailAlloc_4142_, 2, v_v_4096_);
lean_ctor_set(v_reuseFailAlloc_4142_, 3, v_tree_4094_);
lean_ctor_set(v_reuseFailAlloc_4142_, 4, v_l_4112_);
v___x_4138_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
lean_object* v___x_4139_; 
v___x_4139_ = lean_nat_add(v___x_4088_, v_size_4114_);
if (lean_obj_tag(v_r_4113_) == 0)
{
lean_object* v_size_4140_; 
v_size_4140_ = lean_ctor_get(v_r_4113_, 0);
lean_inc(v_size_4140_);
v___y_4124_ = v___x_4138_;
v___y_4125_ = v___x_4139_;
v___y_4126_ = v_size_4140_;
goto v___jp_4123_;
}
else
{
lean_object* v___x_4141_; 
v___x_4141_ = lean_unsigned_to_nat(0u);
v___y_4124_ = v___x_4138_;
v___y_4125_ = v___x_4139_;
v___y_4126_ = v___x_4141_;
goto v___jp_4123_;
}
}
}
}
}
else
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4155_; 
v___x_4151_ = lean_nat_add(v___x_4088_, v_size_4097_);
v___x_4152_ = lean_nat_add(v___x_4151_, v_size_4083_);
lean_dec(v_size_4083_);
v___x_4153_ = lean_nat_add(v___x_4151_, v_size_4109_);
lean_dec(v___x_4151_);
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 4, v_l_4086_);
lean_ctor_set(v___x_4107_, 3, v_tree_4094_);
lean_ctor_set(v___x_4107_, 2, v_v_4096_);
lean_ctor_set(v___x_4107_, 1, v_k_4095_);
lean_ctor_set(v___x_4107_, 0, v___x_4153_);
v___x_4155_ = v___x_4107_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4153_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v_k_4095_);
lean_ctor_set(v_reuseFailAlloc_4159_, 2, v_v_4096_);
lean_ctor_set(v_reuseFailAlloc_4159_, 3, v_tree_4094_);
lean_ctor_set(v_reuseFailAlloc_4159_, 4, v_l_4086_);
v___x_4155_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
lean_object* v___x_4157_; 
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 4, v_r_4087_);
lean_ctor_set(v___x_4091_, 3, v___x_4155_);
lean_ctor_set(v___x_4091_, 2, v_v_4085_);
lean_ctor_set(v___x_4091_, 1, v_k_4084_);
lean_ctor_set(v___x_4091_, 0, v___x_4152_);
v___x_4157_ = v___x_4091_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4152_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v_k_4084_);
lean_ctor_set(v_reuseFailAlloc_4158_, 2, v_v_4085_);
lean_ctor_set(v_reuseFailAlloc_4158_, 3, v___x_4155_);
lean_ctor_set(v_reuseFailAlloc_4158_, 4, v_r_4087_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
}
}
else
{
lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4219_; 
lean_inc(v_r_4087_);
lean_inc(v_v_4085_);
lean_inc(v_k_4084_);
lean_inc(v_size_4083_);
v_isSharedCheck_4219_ = !lean_is_exclusive(v_r_3898_);
if (v_isSharedCheck_4219_ == 0)
{
lean_object* v_unused_4220_; lean_object* v_unused_4221_; lean_object* v_unused_4222_; lean_object* v_unused_4223_; lean_object* v_unused_4224_; 
v_unused_4220_ = lean_ctor_get(v_r_3898_, 4);
lean_dec(v_unused_4220_);
v_unused_4221_ = lean_ctor_get(v_r_3898_, 3);
lean_dec(v_unused_4221_);
v_unused_4222_ = lean_ctor_get(v_r_3898_, 2);
lean_dec(v_unused_4222_);
v_unused_4223_ = lean_ctor_get(v_r_3898_, 1);
lean_dec(v_unused_4223_);
v_unused_4224_ = lean_ctor_get(v_r_3898_, 0);
lean_dec(v_unused_4224_);
v___x_4167_ = v_r_3898_;
v_isShared_4168_ = v_isSharedCheck_4219_;
goto v_resetjp_4166_;
}
else
{
lean_dec(v_r_3898_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4219_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
if (lean_obj_tag(v_l_4086_) == 0)
{
if (lean_obj_tag(v_r_4087_) == 0)
{
lean_object* v_k_4169_; lean_object* v_v_4170_; lean_object* v_size_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
lean_inc(v_tree_4094_);
v_k_4169_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_k_4169_);
v_v_4170_ = lean_ctor_get(v___x_4093_, 1);
lean_inc(v_v_4170_);
lean_dec_ref(v___x_4093_);
v_size_4171_ = lean_ctor_get(v_l_4086_, 0);
v___x_4172_ = lean_nat_add(v___x_4088_, v_size_4083_);
lean_dec(v_size_4083_);
v___x_4173_ = lean_nat_add(v___x_4088_, v_size_4171_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 4, v_l_4086_);
lean_ctor_set(v___x_4167_, 3, v_tree_4094_);
lean_ctor_set(v___x_4167_, 2, v_v_4170_);
lean_ctor_set(v___x_4167_, 1, v_k_4169_);
lean_ctor_set(v___x_4167_, 0, v___x_4173_);
v___x_4175_ = v___x_4167_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4173_);
lean_ctor_set(v_reuseFailAlloc_4179_, 1, v_k_4169_);
lean_ctor_set(v_reuseFailAlloc_4179_, 2, v_v_4170_);
lean_ctor_set(v_reuseFailAlloc_4179_, 3, v_tree_4094_);
lean_ctor_set(v_reuseFailAlloc_4179_, 4, v_l_4086_);
v___x_4175_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
lean_object* v___x_4177_; 
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 4, v_r_4087_);
lean_ctor_set(v___x_4091_, 3, v___x_4175_);
lean_ctor_set(v___x_4091_, 2, v_v_4085_);
lean_ctor_set(v___x_4091_, 1, v_k_4084_);
lean_ctor_set(v___x_4091_, 0, v___x_4172_);
v___x_4177_ = v___x_4091_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4172_);
lean_ctor_set(v_reuseFailAlloc_4178_, 1, v_k_4084_);
lean_ctor_set(v_reuseFailAlloc_4178_, 2, v_v_4085_);
lean_ctor_set(v_reuseFailAlloc_4178_, 3, v___x_4175_);
lean_ctor_set(v_reuseFailAlloc_4178_, 4, v_r_4087_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
else
{
lean_object* v_k_4180_; lean_object* v_v_4181_; lean_object* v_k_4182_; lean_object* v_v_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4197_; 
lean_dec(v_size_4083_);
v_k_4180_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_k_4180_);
v_v_4181_ = lean_ctor_get(v___x_4093_, 1);
lean_inc(v_v_4181_);
lean_dec_ref(v___x_4093_);
v_k_4182_ = lean_ctor_get(v_l_4086_, 1);
v_v_4183_ = lean_ctor_get(v_l_4086_, 2);
v_isSharedCheck_4197_ = !lean_is_exclusive(v_l_4086_);
if (v_isSharedCheck_4197_ == 0)
{
lean_object* v_unused_4198_; lean_object* v_unused_4199_; lean_object* v_unused_4200_; 
v_unused_4198_ = lean_ctor_get(v_l_4086_, 4);
lean_dec(v_unused_4198_);
v_unused_4199_ = lean_ctor_get(v_l_4086_, 3);
lean_dec(v_unused_4199_);
v_unused_4200_ = lean_ctor_get(v_l_4086_, 0);
lean_dec(v_unused_4200_);
v___x_4185_ = v_l_4086_;
v_isShared_4186_ = v_isSharedCheck_4197_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_v_4183_);
lean_inc(v_k_4182_);
lean_dec(v_l_4086_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4197_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4189_; 
v___x_4187_ = lean_unsigned_to_nat(3u);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 4, v_r_4087_);
lean_ctor_set(v___x_4185_, 3, v_r_4087_);
lean_ctor_set(v___x_4185_, 2, v_v_4181_);
lean_ctor_set(v___x_4185_, 1, v_k_4180_);
lean_ctor_set(v___x_4185_, 0, v___x_4088_);
v___x_4189_ = v___x_4185_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4088_);
lean_ctor_set(v_reuseFailAlloc_4196_, 1, v_k_4180_);
lean_ctor_set(v_reuseFailAlloc_4196_, 2, v_v_4181_);
lean_ctor_set(v_reuseFailAlloc_4196_, 3, v_r_4087_);
lean_ctor_set(v_reuseFailAlloc_4196_, 4, v_r_4087_);
v___x_4189_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
lean_object* v___x_4191_; 
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 3, v_r_4087_);
lean_ctor_set(v___x_4167_, 0, v___x_4088_);
v___x_4191_ = v___x_4167_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4088_);
lean_ctor_set(v_reuseFailAlloc_4195_, 1, v_k_4084_);
lean_ctor_set(v_reuseFailAlloc_4195_, 2, v_v_4085_);
lean_ctor_set(v_reuseFailAlloc_4195_, 3, v_r_4087_);
lean_ctor_set(v_reuseFailAlloc_4195_, 4, v_r_4087_);
v___x_4191_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4193_; 
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 4, v___x_4191_);
lean_ctor_set(v___x_4091_, 3, v___x_4189_);
lean_ctor_set(v___x_4091_, 2, v_v_4183_);
lean_ctor_set(v___x_4091_, 1, v_k_4182_);
lean_ctor_set(v___x_4091_, 0, v___x_4187_);
v___x_4193_ = v___x_4091_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4187_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v_k_4182_);
lean_ctor_set(v_reuseFailAlloc_4194_, 2, v_v_4183_);
lean_ctor_set(v_reuseFailAlloc_4194_, 3, v___x_4189_);
lean_ctor_set(v_reuseFailAlloc_4194_, 4, v___x_4191_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4087_) == 0)
{
lean_object* v_k_4201_; lean_object* v_v_4202_; lean_object* v___x_4203_; lean_object* v___x_4205_; 
lean_dec(v_size_4083_);
v_k_4201_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_k_4201_);
v_v_4202_ = lean_ctor_get(v___x_4093_, 1);
lean_inc(v_v_4202_);
lean_dec_ref(v___x_4093_);
v___x_4203_ = lean_unsigned_to_nat(3u);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 4, v_l_4086_);
lean_ctor_set(v___x_4167_, 2, v_v_4202_);
lean_ctor_set(v___x_4167_, 1, v_k_4201_);
lean_ctor_set(v___x_4167_, 0, v___x_4088_);
v___x_4205_ = v___x_4167_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4088_);
lean_ctor_set(v_reuseFailAlloc_4209_, 1, v_k_4201_);
lean_ctor_set(v_reuseFailAlloc_4209_, 2, v_v_4202_);
lean_ctor_set(v_reuseFailAlloc_4209_, 3, v_l_4086_);
lean_ctor_set(v_reuseFailAlloc_4209_, 4, v_l_4086_);
v___x_4205_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
lean_object* v___x_4207_; 
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 4, v_r_4087_);
lean_ctor_set(v___x_4091_, 3, v___x_4205_);
lean_ctor_set(v___x_4091_, 2, v_v_4085_);
lean_ctor_set(v___x_4091_, 1, v_k_4084_);
lean_ctor_set(v___x_4091_, 0, v___x_4203_);
v___x_4207_ = v___x_4091_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4203_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v_k_4084_);
lean_ctor_set(v_reuseFailAlloc_4208_, 2, v_v_4085_);
lean_ctor_set(v_reuseFailAlloc_4208_, 3, v___x_4205_);
lean_ctor_set(v_reuseFailAlloc_4208_, 4, v_r_4087_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
else
{
lean_object* v_k_4210_; lean_object* v_v_4211_; lean_object* v___x_4213_; 
v_k_4210_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_k_4210_);
v_v_4211_ = lean_ctor_get(v___x_4093_, 1);
lean_inc(v_v_4211_);
lean_dec_ref(v___x_4093_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 3, v_r_4087_);
v___x_4213_ = v___x_4167_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_size_4083_);
lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_k_4084_);
lean_ctor_set(v_reuseFailAlloc_4218_, 2, v_v_4085_);
lean_ctor_set(v_reuseFailAlloc_4218_, 3, v_r_4087_);
lean_ctor_set(v_reuseFailAlloc_4218_, 4, v_r_4087_);
v___x_4213_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
lean_object* v___x_4214_; lean_object* v___x_4216_; 
v___x_4214_ = lean_unsigned_to_nat(2u);
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 4, v___x_4213_);
lean_ctor_set(v___x_4091_, 3, v_r_4087_);
lean_ctor_set(v___x_4091_, 2, v_v_4211_);
lean_ctor_set(v___x_4091_, 1, v_k_4210_);
lean_ctor_set(v___x_4091_, 0, v___x_4214_);
v___x_4216_ = v___x_4091_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4214_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_k_4210_);
lean_ctor_set(v_reuseFailAlloc_4217_, 2, v_v_4211_);
lean_ctor_set(v_reuseFailAlloc_4217_, 3, v_r_4087_);
lean_ctor_set(v_reuseFailAlloc_4217_, 4, v___x_4213_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4383_; 
lean_inc(v_r_4087_);
lean_inc(v_v_4085_);
lean_inc(v_k_4084_);
v_isSharedCheck_4383_ = !lean_is_exclusive(v_r_3898_);
if (v_isSharedCheck_4383_ == 0)
{
lean_object* v_unused_4384_; lean_object* v_unused_4385_; lean_object* v_unused_4386_; lean_object* v_unused_4387_; lean_object* v_unused_4388_; 
v_unused_4384_ = lean_ctor_get(v_r_3898_, 4);
lean_dec(v_unused_4384_);
v_unused_4385_ = lean_ctor_get(v_r_3898_, 3);
lean_dec(v_unused_4385_);
v_unused_4386_ = lean_ctor_get(v_r_3898_, 2);
lean_dec(v_unused_4386_);
v_unused_4387_ = lean_ctor_get(v_r_3898_, 1);
lean_dec(v_unused_4387_);
v_unused_4388_ = lean_ctor_get(v_r_3898_, 0);
lean_dec(v_unused_4388_);
v___x_4232_ = v_r_3898_;
v_isShared_4233_ = v_isSharedCheck_4383_;
goto v_resetjp_4231_;
}
else
{
lean_dec(v_r_3898_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4383_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4234_; lean_object* v_tree_4235_; 
v___x_4234_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_4084_, v_v_4085_, v_l_4086_, v_r_4087_);
v_tree_4235_ = lean_ctor_get(v___x_4234_, 2);
lean_inc(v_tree_4235_);
if (lean_obj_tag(v_tree_4235_) == 0)
{
lean_object* v_k_4236_; lean_object* v_v_4237_; lean_object* v_size_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; 
v_k_4236_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_k_4236_);
v_v_4237_ = lean_ctor_get(v___x_4234_, 1);
lean_inc(v_v_4237_);
lean_dec_ref(v___x_4234_);
v_size_4238_ = lean_ctor_get(v_tree_4235_, 0);
v___x_4239_ = lean_unsigned_to_nat(3u);
v___x_4240_ = lean_nat_mul(v___x_4239_, v_size_4238_);
v___x_4241_ = lean_nat_dec_lt(v___x_4240_, v_size_4078_);
lean_dec(v___x_4240_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4245_; 
lean_dec(v_r_4082_);
v___x_4242_ = lean_nat_add(v___x_4088_, v_size_4078_);
v___x_4243_ = lean_nat_add(v___x_4242_, v_size_4238_);
lean_dec(v___x_4242_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 4, v_tree_4235_);
lean_ctor_set(v___x_4232_, 3, v_l_3897_);
lean_ctor_set(v___x_4232_, 2, v_v_4237_);
lean_ctor_set(v___x_4232_, 1, v_k_4236_);
lean_ctor_set(v___x_4232_, 0, v___x_4243_);
v___x_4245_ = v___x_4232_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4243_);
lean_ctor_set(v_reuseFailAlloc_4246_, 1, v_k_4236_);
lean_ctor_set(v_reuseFailAlloc_4246_, 2, v_v_4237_);
lean_ctor_set(v_reuseFailAlloc_4246_, 3, v_l_3897_);
lean_ctor_set(v_reuseFailAlloc_4246_, 4, v_tree_4235_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
else
{
lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4312_; 
lean_inc(v_l_4081_);
lean_inc(v_v_4080_);
lean_inc(v_k_4079_);
lean_inc(v_size_4078_);
v_isSharedCheck_4312_ = !lean_is_exclusive(v_l_3897_);
if (v_isSharedCheck_4312_ == 0)
{
lean_object* v_unused_4313_; lean_object* v_unused_4314_; lean_object* v_unused_4315_; lean_object* v_unused_4316_; lean_object* v_unused_4317_; 
v_unused_4313_ = lean_ctor_get(v_l_3897_, 4);
lean_dec(v_unused_4313_);
v_unused_4314_ = lean_ctor_get(v_l_3897_, 3);
lean_dec(v_unused_4314_);
v_unused_4315_ = lean_ctor_get(v_l_3897_, 2);
lean_dec(v_unused_4315_);
v_unused_4316_ = lean_ctor_get(v_l_3897_, 1);
lean_dec(v_unused_4316_);
v_unused_4317_ = lean_ctor_get(v_l_3897_, 0);
lean_dec(v_unused_4317_);
v___x_4248_ = v_l_3897_;
v_isShared_4249_ = v_isSharedCheck_4312_;
goto v_resetjp_4247_;
}
else
{
lean_dec(v_l_3897_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4312_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v_size_4250_; lean_object* v_size_4251_; lean_object* v_k_4252_; lean_object* v_v_4253_; lean_object* v_l_4254_; lean_object* v_r_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; uint8_t v___x_4258_; 
v_size_4250_ = lean_ctor_get(v_l_4081_, 0);
v_size_4251_ = lean_ctor_get(v_r_4082_, 0);
v_k_4252_ = lean_ctor_get(v_r_4082_, 1);
v_v_4253_ = lean_ctor_get(v_r_4082_, 2);
v_l_4254_ = lean_ctor_get(v_r_4082_, 3);
v_r_4255_ = lean_ctor_get(v_r_4082_, 4);
v___x_4256_ = lean_unsigned_to_nat(2u);
v___x_4257_ = lean_nat_mul(v___x_4256_, v_size_4250_);
v___x_4258_ = lean_nat_dec_lt(v_size_4251_, v___x_4257_);
lean_dec(v___x_4257_);
if (v___x_4258_ == 0)
{
lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4296_; 
lean_inc(v_r_4255_);
lean_inc(v_l_4254_);
lean_inc(v_v_4253_);
lean_inc(v_k_4252_);
lean_del_object(v___x_4248_);
v_isSharedCheck_4296_ = !lean_is_exclusive(v_r_4082_);
if (v_isSharedCheck_4296_ == 0)
{
lean_object* v_unused_4297_; lean_object* v_unused_4298_; lean_object* v_unused_4299_; lean_object* v_unused_4300_; lean_object* v_unused_4301_; 
v_unused_4297_ = lean_ctor_get(v_r_4082_, 4);
lean_dec(v_unused_4297_);
v_unused_4298_ = lean_ctor_get(v_r_4082_, 3);
lean_dec(v_unused_4298_);
v_unused_4299_ = lean_ctor_get(v_r_4082_, 2);
lean_dec(v_unused_4299_);
v_unused_4300_ = lean_ctor_get(v_r_4082_, 1);
lean_dec(v_unused_4300_);
v_unused_4301_ = lean_ctor_get(v_r_4082_, 0);
lean_dec(v_unused_4301_);
v___x_4260_ = v_r_4082_;
v_isShared_4261_ = v_isSharedCheck_4296_;
goto v_resetjp_4259_;
}
else
{
lean_dec(v_r_4082_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4296_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___x_4284_; lean_object* v___y_4286_; 
v___x_4262_ = lean_nat_add(v___x_4088_, v_size_4078_);
lean_dec(v_size_4078_);
v___x_4263_ = lean_nat_add(v___x_4262_, v_size_4238_);
lean_dec(v___x_4262_);
v___x_4284_ = lean_nat_add(v___x_4088_, v_size_4250_);
if (lean_obj_tag(v_l_4254_) == 0)
{
lean_object* v_size_4294_; 
v_size_4294_ = lean_ctor_get(v_l_4254_, 0);
lean_inc(v_size_4294_);
v___y_4286_ = v_size_4294_;
goto v___jp_4285_;
}
else
{
lean_object* v___x_4295_; 
v___x_4295_ = lean_unsigned_to_nat(0u);
v___y_4286_ = v___x_4295_;
goto v___jp_4285_;
}
v___jp_4264_:
{
lean_object* v___x_4268_; lean_object* v___x_4270_; 
v___x_4268_ = lean_nat_add(v___y_4266_, v___y_4267_);
lean_dec(v___y_4267_);
lean_dec(v___y_4266_);
lean_inc_ref(v_tree_4235_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 4, v_tree_4235_);
lean_ctor_set(v___x_4260_, 3, v_r_4255_);
lean_ctor_set(v___x_4260_, 2, v_v_4237_);
lean_ctor_set(v___x_4260_, 1, v_k_4236_);
lean_ctor_set(v___x_4260_, 0, v___x_4268_);
v___x_4270_ = v___x_4260_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4268_);
lean_ctor_set(v_reuseFailAlloc_4283_, 1, v_k_4236_);
lean_ctor_set(v_reuseFailAlloc_4283_, 2, v_v_4237_);
lean_ctor_set(v_reuseFailAlloc_4283_, 3, v_r_4255_);
lean_ctor_set(v_reuseFailAlloc_4283_, 4, v_tree_4235_);
v___x_4270_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
v_isSharedCheck_4277_ = !lean_is_exclusive(v_tree_4235_);
if (v_isSharedCheck_4277_ == 0)
{
lean_object* v_unused_4278_; lean_object* v_unused_4279_; lean_object* v_unused_4280_; lean_object* v_unused_4281_; lean_object* v_unused_4282_; 
v_unused_4278_ = lean_ctor_get(v_tree_4235_, 4);
lean_dec(v_unused_4278_);
v_unused_4279_ = lean_ctor_get(v_tree_4235_, 3);
lean_dec(v_unused_4279_);
v_unused_4280_ = lean_ctor_get(v_tree_4235_, 2);
lean_dec(v_unused_4280_);
v_unused_4281_ = lean_ctor_get(v_tree_4235_, 1);
lean_dec(v_unused_4281_);
v_unused_4282_ = lean_ctor_get(v_tree_4235_, 0);
lean_dec(v_unused_4282_);
v___x_4272_ = v_tree_4235_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_dec(v_tree_4235_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 4, v___x_4270_);
lean_ctor_set(v___x_4272_, 3, v___y_4265_);
lean_ctor_set(v___x_4272_, 2, v_v_4253_);
lean_ctor_set(v___x_4272_, 1, v_k_4252_);
lean_ctor_set(v___x_4272_, 0, v___x_4263_);
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v___x_4263_);
lean_ctor_set(v_reuseFailAlloc_4276_, 1, v_k_4252_);
lean_ctor_set(v_reuseFailAlloc_4276_, 2, v_v_4253_);
lean_ctor_set(v_reuseFailAlloc_4276_, 3, v___y_4265_);
lean_ctor_set(v_reuseFailAlloc_4276_, 4, v___x_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
v___jp_4285_:
{
lean_object* v___x_4287_; lean_object* v___x_4289_; 
v___x_4287_ = lean_nat_add(v___x_4284_, v___y_4286_);
lean_dec(v___y_4286_);
lean_dec(v___x_4284_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 4, v_l_4254_);
lean_ctor_set(v___x_4232_, 3, v_l_4081_);
lean_ctor_set(v___x_4232_, 2, v_v_4080_);
lean_ctor_set(v___x_4232_, 1, v_k_4079_);
lean_ctor_set(v___x_4232_, 0, v___x_4287_);
v___x_4289_ = v___x_4232_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4287_);
lean_ctor_set(v_reuseFailAlloc_4293_, 1, v_k_4079_);
lean_ctor_set(v_reuseFailAlloc_4293_, 2, v_v_4080_);
lean_ctor_set(v_reuseFailAlloc_4293_, 3, v_l_4081_);
lean_ctor_set(v_reuseFailAlloc_4293_, 4, v_l_4254_);
v___x_4289_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
lean_object* v___x_4290_; 
v___x_4290_ = lean_nat_add(v___x_4088_, v_size_4238_);
if (lean_obj_tag(v_r_4255_) == 0)
{
lean_object* v_size_4291_; 
v_size_4291_ = lean_ctor_get(v_r_4255_, 0);
lean_inc(v_size_4291_);
v___y_4265_ = v___x_4289_;
v___y_4266_ = v___x_4290_;
v___y_4267_ = v_size_4291_;
goto v___jp_4264_;
}
else
{
lean_object* v___x_4292_; 
v___x_4292_ = lean_unsigned_to_nat(0u);
v___y_4265_ = v___x_4289_;
v___y_4266_ = v___x_4290_;
v___y_4267_ = v___x_4292_;
goto v___jp_4264_;
}
}
}
}
}
else
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4307_; 
v___x_4302_ = lean_nat_add(v___x_4088_, v_size_4078_);
lean_dec(v_size_4078_);
v___x_4303_ = lean_nat_add(v___x_4302_, v_size_4238_);
lean_dec(v___x_4302_);
v___x_4304_ = lean_nat_add(v___x_4088_, v_size_4238_);
v___x_4305_ = lean_nat_add(v___x_4304_, v_size_4251_);
lean_dec(v___x_4304_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 4, v_tree_4235_);
lean_ctor_set(v___x_4232_, 3, v_r_4082_);
lean_ctor_set(v___x_4232_, 2, v_v_4237_);
lean_ctor_set(v___x_4232_, 1, v_k_4236_);
lean_ctor_set(v___x_4232_, 0, v___x_4305_);
v___x_4307_ = v___x_4232_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4305_);
lean_ctor_set(v_reuseFailAlloc_4311_, 1, v_k_4236_);
lean_ctor_set(v_reuseFailAlloc_4311_, 2, v_v_4237_);
lean_ctor_set(v_reuseFailAlloc_4311_, 3, v_r_4082_);
lean_ctor_set(v_reuseFailAlloc_4311_, 4, v_tree_4235_);
v___x_4307_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
lean_object* v___x_4309_; 
if (v_isShared_4249_ == 0)
{
lean_ctor_set(v___x_4248_, 4, v___x_4307_);
lean_ctor_set(v___x_4248_, 0, v___x_4303_);
v___x_4309_ = v___x_4248_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4303_);
lean_ctor_set(v_reuseFailAlloc_4310_, 1, v_k_4079_);
lean_ctor_set(v_reuseFailAlloc_4310_, 2, v_v_4080_);
lean_ctor_set(v_reuseFailAlloc_4310_, 3, v_l_4081_);
lean_ctor_set(v_reuseFailAlloc_4310_, 4, v___x_4307_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_4081_) == 0)
{
lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4341_; 
lean_inc_ref(v_l_4081_);
lean_inc(v_v_4080_);
lean_inc(v_k_4079_);
lean_inc(v_size_4078_);
v_isSharedCheck_4341_ = !lean_is_exclusive(v_l_3897_);
if (v_isSharedCheck_4341_ == 0)
{
lean_object* v_unused_4342_; lean_object* v_unused_4343_; lean_object* v_unused_4344_; lean_object* v_unused_4345_; lean_object* v_unused_4346_; 
v_unused_4342_ = lean_ctor_get(v_l_3897_, 4);
lean_dec(v_unused_4342_);
v_unused_4343_ = lean_ctor_get(v_l_3897_, 3);
lean_dec(v_unused_4343_);
v_unused_4344_ = lean_ctor_get(v_l_3897_, 2);
lean_dec(v_unused_4344_);
v_unused_4345_ = lean_ctor_get(v_l_3897_, 1);
lean_dec(v_unused_4345_);
v_unused_4346_ = lean_ctor_get(v_l_3897_, 0);
lean_dec(v_unused_4346_);
v___x_4319_ = v_l_3897_;
v_isShared_4320_ = v_isSharedCheck_4341_;
goto v_resetjp_4318_;
}
else
{
lean_dec(v_l_3897_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4341_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
if (lean_obj_tag(v_r_4082_) == 0)
{
lean_object* v_k_4321_; lean_object* v_v_4322_; lean_object* v_size_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4327_; 
v_k_4321_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_k_4321_);
v_v_4322_ = lean_ctor_get(v___x_4234_, 1);
lean_inc(v_v_4322_);
lean_dec_ref(v___x_4234_);
v_size_4323_ = lean_ctor_get(v_r_4082_, 0);
v___x_4324_ = lean_nat_add(v___x_4088_, v_size_4078_);
lean_dec(v_size_4078_);
v___x_4325_ = lean_nat_add(v___x_4088_, v_size_4323_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 4, v_tree_4235_);
lean_ctor_set(v___x_4232_, 3, v_r_4082_);
lean_ctor_set(v___x_4232_, 2, v_v_4322_);
lean_ctor_set(v___x_4232_, 1, v_k_4321_);
lean_ctor_set(v___x_4232_, 0, v___x_4325_);
v___x_4327_ = v___x_4232_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4325_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v_k_4321_);
lean_ctor_set(v_reuseFailAlloc_4331_, 2, v_v_4322_);
lean_ctor_set(v_reuseFailAlloc_4331_, 3, v_r_4082_);
lean_ctor_set(v_reuseFailAlloc_4331_, 4, v_tree_4235_);
v___x_4327_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
lean_object* v___x_4329_; 
if (v_isShared_4320_ == 0)
{
lean_ctor_set(v___x_4319_, 4, v___x_4327_);
lean_ctor_set(v___x_4319_, 0, v___x_4324_);
v___x_4329_ = v___x_4319_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4324_);
lean_ctor_set(v_reuseFailAlloc_4330_, 1, v_k_4079_);
lean_ctor_set(v_reuseFailAlloc_4330_, 2, v_v_4080_);
lean_ctor_set(v_reuseFailAlloc_4330_, 3, v_l_4081_);
lean_ctor_set(v_reuseFailAlloc_4330_, 4, v___x_4327_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
else
{
lean_object* v_k_4332_; lean_object* v_v_4333_; lean_object* v___x_4334_; lean_object* v___x_4336_; 
lean_dec(v_size_4078_);
v_k_4332_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_k_4332_);
v_v_4333_ = lean_ctor_get(v___x_4234_, 1);
lean_inc(v_v_4333_);
lean_dec_ref(v___x_4234_);
v___x_4334_ = lean_unsigned_to_nat(3u);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 4, v_r_4082_);
lean_ctor_set(v___x_4232_, 3, v_r_4082_);
lean_ctor_set(v___x_4232_, 2, v_v_4333_);
lean_ctor_set(v___x_4232_, 1, v_k_4332_);
lean_ctor_set(v___x_4232_, 0, v___x_4088_);
v___x_4336_ = v___x_4232_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4088_);
lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_k_4332_);
lean_ctor_set(v_reuseFailAlloc_4340_, 2, v_v_4333_);
lean_ctor_set(v_reuseFailAlloc_4340_, 3, v_r_4082_);
lean_ctor_set(v_reuseFailAlloc_4340_, 4, v_r_4082_);
v___x_4336_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
lean_object* v___x_4338_; 
if (v_isShared_4320_ == 0)
{
lean_ctor_set(v___x_4319_, 4, v___x_4336_);
lean_ctor_set(v___x_4319_, 0, v___x_4334_);
v___x_4338_ = v___x_4319_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v___x_4334_);
lean_ctor_set(v_reuseFailAlloc_4339_, 1, v_k_4079_);
lean_ctor_set(v_reuseFailAlloc_4339_, 2, v_v_4080_);
lean_ctor_set(v_reuseFailAlloc_4339_, 3, v_l_4081_);
lean_ctor_set(v_reuseFailAlloc_4339_, 4, v___x_4336_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4082_) == 0)
{
lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4371_; 
lean_inc(v_l_4081_);
lean_inc(v_v_4080_);
lean_inc(v_k_4079_);
v_isSharedCheck_4371_ = !lean_is_exclusive(v_l_3897_);
if (v_isSharedCheck_4371_ == 0)
{
lean_object* v_unused_4372_; lean_object* v_unused_4373_; lean_object* v_unused_4374_; lean_object* v_unused_4375_; lean_object* v_unused_4376_; 
v_unused_4372_ = lean_ctor_get(v_l_3897_, 4);
lean_dec(v_unused_4372_);
v_unused_4373_ = lean_ctor_get(v_l_3897_, 3);
lean_dec(v_unused_4373_);
v_unused_4374_ = lean_ctor_get(v_l_3897_, 2);
lean_dec(v_unused_4374_);
v_unused_4375_ = lean_ctor_get(v_l_3897_, 1);
lean_dec(v_unused_4375_);
v_unused_4376_ = lean_ctor_get(v_l_3897_, 0);
lean_dec(v_unused_4376_);
v___x_4348_ = v_l_3897_;
v_isShared_4349_ = v_isSharedCheck_4371_;
goto v_resetjp_4347_;
}
else
{
lean_dec(v_l_3897_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4371_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v_k_4350_; lean_object* v_v_4351_; lean_object* v_k_4352_; lean_object* v_v_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4367_; 
v_k_4350_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_k_4350_);
v_v_4351_ = lean_ctor_get(v___x_4234_, 1);
lean_inc(v_v_4351_);
lean_dec_ref(v___x_4234_);
v_k_4352_ = lean_ctor_get(v_r_4082_, 1);
v_v_4353_ = lean_ctor_get(v_r_4082_, 2);
v_isSharedCheck_4367_ = !lean_is_exclusive(v_r_4082_);
if (v_isSharedCheck_4367_ == 0)
{
lean_object* v_unused_4368_; lean_object* v_unused_4369_; lean_object* v_unused_4370_; 
v_unused_4368_ = lean_ctor_get(v_r_4082_, 4);
lean_dec(v_unused_4368_);
v_unused_4369_ = lean_ctor_get(v_r_4082_, 3);
lean_dec(v_unused_4369_);
v_unused_4370_ = lean_ctor_get(v_r_4082_, 0);
lean_dec(v_unused_4370_);
v___x_4355_ = v_r_4082_;
v_isShared_4356_ = v_isSharedCheck_4367_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_v_4353_);
lean_inc(v_k_4352_);
lean_dec(v_r_4082_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4367_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4357_; lean_object* v___x_4359_; 
v___x_4357_ = lean_unsigned_to_nat(3u);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 4, v_l_4081_);
lean_ctor_set(v___x_4355_, 3, v_l_4081_);
lean_ctor_set(v___x_4355_, 2, v_v_4080_);
lean_ctor_set(v___x_4355_, 1, v_k_4079_);
lean_ctor_set(v___x_4355_, 0, v___x_4088_);
v___x_4359_ = v___x_4355_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v___x_4088_);
lean_ctor_set(v_reuseFailAlloc_4366_, 1, v_k_4079_);
lean_ctor_set(v_reuseFailAlloc_4366_, 2, v_v_4080_);
lean_ctor_set(v_reuseFailAlloc_4366_, 3, v_l_4081_);
lean_ctor_set(v_reuseFailAlloc_4366_, 4, v_l_4081_);
v___x_4359_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
lean_object* v___x_4361_; 
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 4, v_l_4081_);
lean_ctor_set(v___x_4232_, 3, v_l_4081_);
lean_ctor_set(v___x_4232_, 2, v_v_4351_);
lean_ctor_set(v___x_4232_, 1, v_k_4350_);
lean_ctor_set(v___x_4232_, 0, v___x_4088_);
v___x_4361_ = v___x_4232_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4088_);
lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_k_4350_);
lean_ctor_set(v_reuseFailAlloc_4365_, 2, v_v_4351_);
lean_ctor_set(v_reuseFailAlloc_4365_, 3, v_l_4081_);
lean_ctor_set(v_reuseFailAlloc_4365_, 4, v_l_4081_);
v___x_4361_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4363_; 
if (v_isShared_4349_ == 0)
{
lean_ctor_set(v___x_4348_, 4, v___x_4361_);
lean_ctor_set(v___x_4348_, 3, v___x_4359_);
lean_ctor_set(v___x_4348_, 2, v_v_4353_);
lean_ctor_set(v___x_4348_, 1, v_k_4352_);
lean_ctor_set(v___x_4348_, 0, v___x_4357_);
v___x_4363_ = v___x_4348_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4357_);
lean_ctor_set(v_reuseFailAlloc_4364_, 1, v_k_4352_);
lean_ctor_set(v_reuseFailAlloc_4364_, 2, v_v_4353_);
lean_ctor_set(v_reuseFailAlloc_4364_, 3, v___x_4359_);
lean_ctor_set(v_reuseFailAlloc_4364_, 4, v___x_4361_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
}
}
else
{
lean_object* v_k_4377_; lean_object* v_v_4378_; lean_object* v___x_4379_; lean_object* v___x_4381_; 
v_k_4377_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_k_4377_);
v_v_4378_ = lean_ctor_get(v___x_4234_, 1);
lean_inc(v_v_4378_);
lean_dec_ref(v___x_4234_);
v___x_4379_ = lean_unsigned_to_nat(2u);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 4, v_r_4082_);
lean_ctor_set(v___x_4232_, 3, v_l_3897_);
lean_ctor_set(v___x_4232_, 2, v_v_4378_);
lean_ctor_set(v___x_4232_, 1, v_k_4377_);
lean_ctor_set(v___x_4232_, 0, v___x_4379_);
v___x_4381_ = v___x_4232_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_k_4377_);
lean_ctor_set(v_reuseFailAlloc_4382_, 2, v_v_4378_);
lean_ctor_set(v_reuseFailAlloc_4382_, 3, v_l_3897_);
lean_ctor_set(v_reuseFailAlloc_4382_, 4, v_r_4082_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
}
}
}
else
{
return v_l_3897_;
}
}
else
{
return v_r_3898_;
}
}
default: 
{
lean_object* v_impl_4389_; lean_object* v___x_4390_; 
v_impl_4389_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_3892_, v_k_3893_, v_r_3898_);
v___x_4390_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_4389_) == 0)
{
if (lean_obj_tag(v_l_3897_) == 0)
{
lean_object* v_size_4391_; lean_object* v_size_4392_; lean_object* v_k_4393_; lean_object* v_v_4394_; lean_object* v_l_4395_; lean_object* v_r_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; uint8_t v___x_4399_; 
v_size_4391_ = lean_ctor_get(v_impl_4389_, 0);
v_size_4392_ = lean_ctor_get(v_l_3897_, 0);
v_k_4393_ = lean_ctor_get(v_l_3897_, 1);
v_v_4394_ = lean_ctor_get(v_l_3897_, 2);
v_l_4395_ = lean_ctor_get(v_l_3897_, 3);
v_r_4396_ = lean_ctor_get(v_l_3897_, 4);
lean_inc(v_r_4396_);
v___x_4397_ = lean_unsigned_to_nat(3u);
v___x_4398_ = lean_nat_mul(v___x_4397_, v_size_4391_);
v___x_4399_ = lean_nat_dec_lt(v___x_4398_, v_size_4392_);
lean_dec(v___x_4398_);
if (v___x_4399_ == 0)
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4403_; 
lean_dec(v_r_4396_);
v___x_4400_ = lean_nat_add(v___x_4390_, v_size_4392_);
v___x_4401_ = lean_nat_add(v___x_4400_, v_size_4391_);
lean_dec(v___x_4400_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v_impl_4389_);
lean_ctor_set(v___x_3900_, 0, v___x_4401_);
v___x_4403_ = v___x_3900_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4401_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4404_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4404_, 3, v_l_3897_);
lean_ctor_set(v_reuseFailAlloc_4404_, 4, v_impl_4389_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
else
{
lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4470_; 
lean_inc(v_l_4395_);
lean_inc(v_v_4394_);
lean_inc(v_k_4393_);
lean_inc(v_size_4392_);
v_isSharedCheck_4470_ = !lean_is_exclusive(v_l_3897_);
if (v_isSharedCheck_4470_ == 0)
{
lean_object* v_unused_4471_; lean_object* v_unused_4472_; lean_object* v_unused_4473_; lean_object* v_unused_4474_; lean_object* v_unused_4475_; 
v_unused_4471_ = lean_ctor_get(v_l_3897_, 4);
lean_dec(v_unused_4471_);
v_unused_4472_ = lean_ctor_get(v_l_3897_, 3);
lean_dec(v_unused_4472_);
v_unused_4473_ = lean_ctor_get(v_l_3897_, 2);
lean_dec(v_unused_4473_);
v_unused_4474_ = lean_ctor_get(v_l_3897_, 1);
lean_dec(v_unused_4474_);
v_unused_4475_ = lean_ctor_get(v_l_3897_, 0);
lean_dec(v_unused_4475_);
v___x_4406_ = v_l_3897_;
v_isShared_4407_ = v_isSharedCheck_4470_;
goto v_resetjp_4405_;
}
else
{
lean_dec(v_l_3897_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4470_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v_size_4408_; lean_object* v_size_4409_; lean_object* v_k_4410_; lean_object* v_v_4411_; lean_object* v_l_4412_; lean_object* v_r_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; uint8_t v___x_4416_; 
v_size_4408_ = lean_ctor_get(v_l_4395_, 0);
v_size_4409_ = lean_ctor_get(v_r_4396_, 0);
v_k_4410_ = lean_ctor_get(v_r_4396_, 1);
v_v_4411_ = lean_ctor_get(v_r_4396_, 2);
v_l_4412_ = lean_ctor_get(v_r_4396_, 3);
v_r_4413_ = lean_ctor_get(v_r_4396_, 4);
v___x_4414_ = lean_unsigned_to_nat(2u);
v___x_4415_ = lean_nat_mul(v___x_4414_, v_size_4408_);
v___x_4416_ = lean_nat_dec_lt(v_size_4409_, v___x_4415_);
lean_dec(v___x_4415_);
if (v___x_4416_ == 0)
{
lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4445_; 
lean_inc(v_r_4413_);
lean_inc(v_l_4412_);
lean_inc(v_v_4411_);
lean_inc(v_k_4410_);
v_isSharedCheck_4445_ = !lean_is_exclusive(v_r_4396_);
if (v_isSharedCheck_4445_ == 0)
{
lean_object* v_unused_4446_; lean_object* v_unused_4447_; lean_object* v_unused_4448_; lean_object* v_unused_4449_; lean_object* v_unused_4450_; 
v_unused_4446_ = lean_ctor_get(v_r_4396_, 4);
lean_dec(v_unused_4446_);
v_unused_4447_ = lean_ctor_get(v_r_4396_, 3);
lean_dec(v_unused_4447_);
v_unused_4448_ = lean_ctor_get(v_r_4396_, 2);
lean_dec(v_unused_4448_);
v_unused_4449_ = lean_ctor_get(v_r_4396_, 1);
lean_dec(v_unused_4449_);
v_unused_4450_ = lean_ctor_get(v_r_4396_, 0);
lean_dec(v_unused_4450_);
v___x_4418_ = v_r_4396_;
v_isShared_4419_ = v_isSharedCheck_4445_;
goto v_resetjp_4417_;
}
else
{
lean_dec(v_r_4396_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4445_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___x_4433_; lean_object* v___y_4435_; 
v___x_4420_ = lean_nat_add(v___x_4390_, v_size_4392_);
lean_dec(v_size_4392_);
v___x_4421_ = lean_nat_add(v___x_4420_, v_size_4391_);
lean_dec(v___x_4420_);
v___x_4433_ = lean_nat_add(v___x_4390_, v_size_4408_);
if (lean_obj_tag(v_l_4412_) == 0)
{
lean_object* v_size_4443_; 
v_size_4443_ = lean_ctor_get(v_l_4412_, 0);
lean_inc(v_size_4443_);
v___y_4435_ = v_size_4443_;
goto v___jp_4434_;
}
else
{
lean_object* v___x_4444_; 
v___x_4444_ = lean_unsigned_to_nat(0u);
v___y_4435_ = v___x_4444_;
goto v___jp_4434_;
}
v___jp_4422_:
{
lean_object* v___x_4426_; lean_object* v___x_4428_; 
v___x_4426_ = lean_nat_add(v___y_4424_, v___y_4425_);
lean_dec(v___y_4425_);
lean_dec(v___y_4424_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 4, v_impl_4389_);
lean_ctor_set(v___x_4418_, 3, v_r_4413_);
lean_ctor_set(v___x_4418_, 2, v_v_3896_);
lean_ctor_set(v___x_4418_, 1, v_k_3895_);
lean_ctor_set(v___x_4418_, 0, v___x_4426_);
v___x_4428_ = v___x_4418_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4426_);
lean_ctor_set(v_reuseFailAlloc_4432_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4432_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4432_, 3, v_r_4413_);
lean_ctor_set(v_reuseFailAlloc_4432_, 4, v_impl_4389_);
v___x_4428_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
lean_object* v___x_4430_; 
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 4, v___x_4428_);
lean_ctor_set(v___x_4406_, 3, v___y_4423_);
lean_ctor_set(v___x_4406_, 2, v_v_4411_);
lean_ctor_set(v___x_4406_, 1, v_k_4410_);
lean_ctor_set(v___x_4406_, 0, v___x_4421_);
v___x_4430_ = v___x_4406_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4421_);
lean_ctor_set(v_reuseFailAlloc_4431_, 1, v_k_4410_);
lean_ctor_set(v_reuseFailAlloc_4431_, 2, v_v_4411_);
lean_ctor_set(v_reuseFailAlloc_4431_, 3, v___y_4423_);
lean_ctor_set(v_reuseFailAlloc_4431_, 4, v___x_4428_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
v___jp_4434_:
{
lean_object* v___x_4436_; lean_object* v___x_4438_; 
v___x_4436_ = lean_nat_add(v___x_4433_, v___y_4435_);
lean_dec(v___y_4435_);
lean_dec(v___x_4433_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v_l_4412_);
lean_ctor_set(v___x_3900_, 3, v_l_4395_);
lean_ctor_set(v___x_3900_, 2, v_v_4394_);
lean_ctor_set(v___x_3900_, 1, v_k_4393_);
lean_ctor_set(v___x_3900_, 0, v___x_4436_);
v___x_4438_ = v___x_3900_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4436_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v_k_4393_);
lean_ctor_set(v_reuseFailAlloc_4442_, 2, v_v_4394_);
lean_ctor_set(v_reuseFailAlloc_4442_, 3, v_l_4395_);
lean_ctor_set(v_reuseFailAlloc_4442_, 4, v_l_4412_);
v___x_4438_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
lean_object* v___x_4439_; 
v___x_4439_ = lean_nat_add(v___x_4390_, v_size_4391_);
if (lean_obj_tag(v_r_4413_) == 0)
{
lean_object* v_size_4440_; 
v_size_4440_ = lean_ctor_get(v_r_4413_, 0);
lean_inc(v_size_4440_);
v___y_4423_ = v___x_4438_;
v___y_4424_ = v___x_4439_;
v___y_4425_ = v_size_4440_;
goto v___jp_4422_;
}
else
{
lean_object* v___x_4441_; 
v___x_4441_ = lean_unsigned_to_nat(0u);
v___y_4423_ = v___x_4438_;
v___y_4424_ = v___x_4439_;
v___y_4425_ = v___x_4441_;
goto v___jp_4422_;
}
}
}
}
}
else
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4456_; 
lean_del_object(v___x_3900_);
v___x_4451_ = lean_nat_add(v___x_4390_, v_size_4392_);
lean_dec(v_size_4392_);
v___x_4452_ = lean_nat_add(v___x_4451_, v_size_4391_);
lean_dec(v___x_4451_);
v___x_4453_ = lean_nat_add(v___x_4390_, v_size_4391_);
v___x_4454_ = lean_nat_add(v___x_4453_, v_size_4409_);
lean_dec(v___x_4453_);
lean_inc_ref(v_impl_4389_);
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 4, v_impl_4389_);
lean_ctor_set(v___x_4406_, 3, v_r_4396_);
lean_ctor_set(v___x_4406_, 2, v_v_3896_);
lean_ctor_set(v___x_4406_, 1, v_k_3895_);
lean_ctor_set(v___x_4406_, 0, v___x_4454_);
v___x_4456_ = v___x_4406_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4454_);
lean_ctor_set(v_reuseFailAlloc_4469_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4469_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4469_, 3, v_r_4396_);
lean_ctor_set(v_reuseFailAlloc_4469_, 4, v_impl_4389_);
v___x_4456_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4463_; 
v_isSharedCheck_4463_ = !lean_is_exclusive(v_impl_4389_);
if (v_isSharedCheck_4463_ == 0)
{
lean_object* v_unused_4464_; lean_object* v_unused_4465_; lean_object* v_unused_4466_; lean_object* v_unused_4467_; lean_object* v_unused_4468_; 
v_unused_4464_ = lean_ctor_get(v_impl_4389_, 4);
lean_dec(v_unused_4464_);
v_unused_4465_ = lean_ctor_get(v_impl_4389_, 3);
lean_dec(v_unused_4465_);
v_unused_4466_ = lean_ctor_get(v_impl_4389_, 2);
lean_dec(v_unused_4466_);
v_unused_4467_ = lean_ctor_get(v_impl_4389_, 1);
lean_dec(v_unused_4467_);
v_unused_4468_ = lean_ctor_get(v_impl_4389_, 0);
lean_dec(v_unused_4468_);
v___x_4458_ = v_impl_4389_;
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
else
{
lean_dec(v_impl_4389_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4461_; 
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 4, v___x_4456_);
lean_ctor_set(v___x_4458_, 3, v_l_4395_);
lean_ctor_set(v___x_4458_, 2, v_v_4394_);
lean_ctor_set(v___x_4458_, 1, v_k_4393_);
lean_ctor_set(v___x_4458_, 0, v___x_4452_);
v___x_4461_ = v___x_4458_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4452_);
lean_ctor_set(v_reuseFailAlloc_4462_, 1, v_k_4393_);
lean_ctor_set(v_reuseFailAlloc_4462_, 2, v_v_4394_);
lean_ctor_set(v_reuseFailAlloc_4462_, 3, v_l_4395_);
lean_ctor_set(v_reuseFailAlloc_4462_, 4, v___x_4456_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_4476_; lean_object* v___x_4477_; lean_object* v___x_4479_; 
v_size_4476_ = lean_ctor_get(v_impl_4389_, 0);
v___x_4477_ = lean_nat_add(v___x_4390_, v_size_4476_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v_impl_4389_);
lean_ctor_set(v___x_3900_, 0, v___x_4477_);
v___x_4479_ = v___x_3900_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4480_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4480_, 3, v_l_3897_);
lean_ctor_set(v_reuseFailAlloc_4480_, 4, v_impl_4389_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
else
{
if (lean_obj_tag(v_l_3897_) == 0)
{
lean_object* v_l_4481_; 
v_l_4481_ = lean_ctor_get(v_l_3897_, 3);
if (lean_obj_tag(v_l_4481_) == 0)
{
lean_object* v_r_4482_; 
lean_inc_ref(v_l_4481_);
v_r_4482_ = lean_ctor_get(v_l_3897_, 4);
lean_inc(v_r_4482_);
if (lean_obj_tag(v_r_4482_) == 0)
{
lean_object* v_size_4483_; lean_object* v_k_4484_; lean_object* v_v_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4498_; 
v_size_4483_ = lean_ctor_get(v_l_3897_, 0);
v_k_4484_ = lean_ctor_get(v_l_3897_, 1);
v_v_4485_ = lean_ctor_get(v_l_3897_, 2);
v_isSharedCheck_4498_ = !lean_is_exclusive(v_l_3897_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; lean_object* v_unused_4500_; 
v_unused_4499_ = lean_ctor_get(v_l_3897_, 4);
lean_dec(v_unused_4499_);
v_unused_4500_ = lean_ctor_get(v_l_3897_, 3);
lean_dec(v_unused_4500_);
v___x_4487_ = v_l_3897_;
v_isShared_4488_ = v_isSharedCheck_4498_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_v_4485_);
lean_inc(v_k_4484_);
lean_inc(v_size_4483_);
lean_dec(v_l_3897_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4498_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v_size_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4493_; 
v_size_4489_ = lean_ctor_get(v_r_4482_, 0);
v___x_4490_ = lean_nat_add(v___x_4390_, v_size_4483_);
lean_dec(v_size_4483_);
v___x_4491_ = lean_nat_add(v___x_4390_, v_size_4489_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 4, v_impl_4389_);
lean_ctor_set(v___x_4487_, 3, v_r_4482_);
lean_ctor_set(v___x_4487_, 2, v_v_3896_);
lean_ctor_set(v___x_4487_, 1, v_k_3895_);
lean_ctor_set(v___x_4487_, 0, v___x_4491_);
v___x_4493_ = v___x_4487_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4491_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4497_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4497_, 3, v_r_4482_);
lean_ctor_set(v_reuseFailAlloc_4497_, 4, v_impl_4389_);
v___x_4493_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4495_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v___x_4493_);
lean_ctor_set(v___x_3900_, 3, v_l_4481_);
lean_ctor_set(v___x_3900_, 2, v_v_4485_);
lean_ctor_set(v___x_3900_, 1, v_k_4484_);
lean_ctor_set(v___x_3900_, 0, v___x_4490_);
v___x_4495_ = v___x_3900_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4490_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v_k_4484_);
lean_ctor_set(v_reuseFailAlloc_4496_, 2, v_v_4485_);
lean_ctor_set(v_reuseFailAlloc_4496_, 3, v_l_4481_);
lean_ctor_set(v_reuseFailAlloc_4496_, 4, v___x_4493_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
else
{
lean_object* v_k_4501_; lean_object* v_v_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4513_; 
v_k_4501_ = lean_ctor_get(v_l_3897_, 1);
v_v_4502_ = lean_ctor_get(v_l_3897_, 2);
v_isSharedCheck_4513_ = !lean_is_exclusive(v_l_3897_);
if (v_isSharedCheck_4513_ == 0)
{
lean_object* v_unused_4514_; lean_object* v_unused_4515_; lean_object* v_unused_4516_; 
v_unused_4514_ = lean_ctor_get(v_l_3897_, 4);
lean_dec(v_unused_4514_);
v_unused_4515_ = lean_ctor_get(v_l_3897_, 3);
lean_dec(v_unused_4515_);
v_unused_4516_ = lean_ctor_get(v_l_3897_, 0);
lean_dec(v_unused_4516_);
v___x_4504_ = v_l_3897_;
v_isShared_4505_ = v_isSharedCheck_4513_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_v_4502_);
lean_inc(v_k_4501_);
lean_dec(v_l_3897_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4513_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4506_ = lean_unsigned_to_nat(3u);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 3, v_r_4482_);
lean_ctor_set(v___x_4504_, 2, v_v_3896_);
lean_ctor_set(v___x_4504_, 1, v_k_3895_);
lean_ctor_set(v___x_4504_, 0, v___x_4390_);
v___x_4508_ = v___x_4504_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4390_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4512_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4512_, 3, v_r_4482_);
lean_ctor_set(v_reuseFailAlloc_4512_, 4, v_r_4482_);
v___x_4508_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4510_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v___x_4508_);
lean_ctor_set(v___x_3900_, 3, v_l_4481_);
lean_ctor_set(v___x_3900_, 2, v_v_4502_);
lean_ctor_set(v___x_3900_, 1, v_k_4501_);
lean_ctor_set(v___x_3900_, 0, v___x_4506_);
v___x_4510_ = v___x_3900_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4506_);
lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_k_4501_);
lean_ctor_set(v_reuseFailAlloc_4511_, 2, v_v_4502_);
lean_ctor_set(v_reuseFailAlloc_4511_, 3, v_l_4481_);
lean_ctor_set(v_reuseFailAlloc_4511_, 4, v___x_4508_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
}
else
{
lean_object* v_r_4517_; 
v_r_4517_ = lean_ctor_get(v_l_3897_, 4);
lean_inc(v_r_4517_);
if (lean_obj_tag(v_r_4517_) == 0)
{
lean_object* v_k_4518_; lean_object* v_v_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4542_; 
lean_inc(v_l_4481_);
v_k_4518_ = lean_ctor_get(v_l_3897_, 1);
v_v_4519_ = lean_ctor_get(v_l_3897_, 2);
v_isSharedCheck_4542_ = !lean_is_exclusive(v_l_3897_);
if (v_isSharedCheck_4542_ == 0)
{
lean_object* v_unused_4543_; lean_object* v_unused_4544_; lean_object* v_unused_4545_; 
v_unused_4543_ = lean_ctor_get(v_l_3897_, 4);
lean_dec(v_unused_4543_);
v_unused_4544_ = lean_ctor_get(v_l_3897_, 3);
lean_dec(v_unused_4544_);
v_unused_4545_ = lean_ctor_get(v_l_3897_, 0);
lean_dec(v_unused_4545_);
v___x_4521_ = v_l_3897_;
v_isShared_4522_ = v_isSharedCheck_4542_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_v_4519_);
lean_inc(v_k_4518_);
lean_dec(v_l_3897_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4542_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v_k_4523_; lean_object* v_v_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4538_; 
v_k_4523_ = lean_ctor_get(v_r_4517_, 1);
v_v_4524_ = lean_ctor_get(v_r_4517_, 2);
v_isSharedCheck_4538_ = !lean_is_exclusive(v_r_4517_);
if (v_isSharedCheck_4538_ == 0)
{
lean_object* v_unused_4539_; lean_object* v_unused_4540_; lean_object* v_unused_4541_; 
v_unused_4539_ = lean_ctor_get(v_r_4517_, 4);
lean_dec(v_unused_4539_);
v_unused_4540_ = lean_ctor_get(v_r_4517_, 3);
lean_dec(v_unused_4540_);
v_unused_4541_ = lean_ctor_get(v_r_4517_, 0);
lean_dec(v_unused_4541_);
v___x_4526_ = v_r_4517_;
v_isShared_4527_ = v_isSharedCheck_4538_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_v_4524_);
lean_inc(v_k_4523_);
lean_dec(v_r_4517_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4538_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4528_; lean_object* v___x_4530_; 
v___x_4528_ = lean_unsigned_to_nat(3u);
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 4, v_l_4481_);
lean_ctor_set(v___x_4526_, 3, v_l_4481_);
lean_ctor_set(v___x_4526_, 2, v_v_4519_);
lean_ctor_set(v___x_4526_, 1, v_k_4518_);
lean_ctor_set(v___x_4526_, 0, v___x_4390_);
v___x_4530_ = v___x_4526_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4390_);
lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_k_4518_);
lean_ctor_set(v_reuseFailAlloc_4537_, 2, v_v_4519_);
lean_ctor_set(v_reuseFailAlloc_4537_, 3, v_l_4481_);
lean_ctor_set(v_reuseFailAlloc_4537_, 4, v_l_4481_);
v___x_4530_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
lean_object* v___x_4532_; 
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 4, v_l_4481_);
lean_ctor_set(v___x_4521_, 2, v_v_3896_);
lean_ctor_set(v___x_4521_, 1, v_k_3895_);
lean_ctor_set(v___x_4521_, 0, v___x_4390_);
v___x_4532_ = v___x_4521_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4390_);
lean_ctor_set(v_reuseFailAlloc_4536_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4536_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4536_, 3, v_l_4481_);
lean_ctor_set(v_reuseFailAlloc_4536_, 4, v_l_4481_);
v___x_4532_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
lean_object* v___x_4534_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v___x_4532_);
lean_ctor_set(v___x_3900_, 3, v___x_4530_);
lean_ctor_set(v___x_3900_, 2, v_v_4524_);
lean_ctor_set(v___x_3900_, 1, v_k_4523_);
lean_ctor_set(v___x_3900_, 0, v___x_4528_);
v___x_4534_ = v___x_3900_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4528_);
lean_ctor_set(v_reuseFailAlloc_4535_, 1, v_k_4523_);
lean_ctor_set(v_reuseFailAlloc_4535_, 2, v_v_4524_);
lean_ctor_set(v_reuseFailAlloc_4535_, 3, v___x_4530_);
lean_ctor_set(v_reuseFailAlloc_4535_, 4, v___x_4532_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
}
}
}
else
{
lean_object* v___x_4546_; lean_object* v___x_4548_; 
v___x_4546_ = lean_unsigned_to_nat(2u);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v_r_4517_);
lean_ctor_set(v___x_3900_, 0, v___x_4546_);
v___x_4548_ = v___x_3900_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4546_);
lean_ctor_set(v_reuseFailAlloc_4549_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4549_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4549_, 3, v_l_3897_);
lean_ctor_set(v_reuseFailAlloc_4549_, 4, v_r_4517_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
else
{
lean_object* v___x_4551_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v_l_3897_);
lean_ctor_set(v___x_3900_, 0, v___x_4390_);
v___x_4551_ = v___x_3900_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4390_);
lean_ctor_set(v_reuseFailAlloc_4552_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_4552_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_4552_, 3, v_l_3897_);
lean_ctor_set(v_reuseFailAlloc_4552_, 4, v_l_3897_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_3893_);
lean_dec_ref(v_cmp_3892_);
return v_t_3894_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(lean_object* v_cmp_4555_, lean_object* v_init_4556_, lean_object* v_x_4557_){
_start:
{
if (lean_obj_tag(v_x_4557_) == 0)
{
lean_object* v_k_4558_; lean_object* v_l_4559_; lean_object* v_r_4560_; lean_object* v___x_4561_; lean_object* v_a_4562_; lean_object* v_r_4563_; 
v_k_4558_ = lean_ctor_get(v_x_4557_, 1);
lean_inc(v_k_4558_);
v_l_4559_ = lean_ctor_get(v_x_4557_, 3);
lean_inc(v_l_4559_);
v_r_4560_ = lean_ctor_get(v_x_4557_, 4);
lean_inc(v_r_4560_);
lean_dec_ref_known(v_x_4557_, 5);
lean_inc_ref_n(v_cmp_4555_, 2);
v___x_4561_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4555_, v_init_4556_, v_l_4559_);
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_a_4562_);
lean_dec_ref(v___x_4561_);
v_r_4563_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_4555_, v_k_4558_, v_a_4562_);
v_init_4556_ = v_r_4563_;
v_x_4557_ = v_r_4560_;
goto _start;
}
else
{
lean_object* v___x_4565_; 
lean_dec_ref(v_cmp_4555_);
v___x_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4565_, 0, v_init_4556_);
return v___x_4565_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(lean_object* v_cmp_4566_, lean_object* v_t_u2082_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v_t_4570_){
_start:
{
if (lean_obj_tag(v_t_4570_) == 0)
{
lean_object* v_k_4571_; lean_object* v_v_4572_; lean_object* v_l_4573_; lean_object* v_r_4574_; uint8_t v___x_4579_; 
v_k_4571_ = lean_ctor_get(v_t_4570_, 1);
lean_inc_n(v_k_4571_, 2);
v_v_4572_ = lean_ctor_get(v_t_4570_, 2);
lean_inc(v_v_4572_);
v_l_4573_ = lean_ctor_get(v_t_4570_, 3);
lean_inc(v_l_4573_);
v_r_4574_ = lean_ctor_get(v_t_4570_, 4);
lean_inc(v_r_4574_);
lean_dec_ref_known(v_t_4570_, 5);
lean_inc(v_t_u2082_4567_);
lean_inc_ref(v_cmp_4566_);
v___x_4579_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_4566_, v_k_4571_, v_t_u2082_4567_);
if (v___x_4579_ == 0)
{
uint8_t v___x_4580_; 
v___x_4580_ = lean_nat_dec_le(v___y_4568_, v___y_4569_);
if (v___x_4580_ == 0)
{
lean_dec(v_v_4572_);
lean_dec(v_k_4571_);
goto v___jp_4575_;
}
else
{
lean_object* v_impl_4581_; lean_object* v_impl_4582_; lean_object* v___x_4583_; 
lean_inc(v_t_u2082_4567_);
lean_inc_ref(v_cmp_4566_);
v_impl_4581_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4566_, v_t_u2082_4567_, v___y_4568_, v___y_4569_, v_l_4573_);
v_impl_4582_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4566_, v_t_u2082_4567_, v___y_4568_, v___y_4569_, v_r_4574_);
v___x_4583_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_4571_, v_v_4572_, v_impl_4581_, v_impl_4582_);
return v___x_4583_;
}
}
else
{
lean_dec(v_v_4572_);
lean_dec(v_k_4571_);
goto v___jp_4575_;
}
v___jp_4575_:
{
lean_object* v_impl_4576_; lean_object* v_impl_4577_; lean_object* v___x_4578_; 
lean_inc(v_t_u2082_4567_);
lean_inc_ref(v_cmp_4566_);
v_impl_4576_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4566_, v_t_u2082_4567_, v___y_4568_, v___y_4569_, v_l_4573_);
v_impl_4577_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4566_, v_t_u2082_4567_, v___y_4568_, v___y_4569_, v_r_4574_);
v___x_4578_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_4576_, v_impl_4577_);
return v___x_4578_;
}
}
else
{
lean_dec(v_t_u2082_4567_);
lean_dec_ref(v_cmp_4566_);
return v_t_4570_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg___boxed(lean_object* v_cmp_4584_, lean_object* v_t_u2082_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v_t_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4584_, v_t_u2082_4585_, v___y_4586_, v___y_4587_, v_t_4588_);
lean_dec(v___y_4587_);
lean_dec(v___y_4586_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object* v_cmp_4590_, lean_object* v_t_u2081_4591_, lean_object* v_t_u2082_4592_){
_start:
{
lean_object* v___y_4594_; lean_object* v___y_4595_; lean_object* v___y_4601_; 
if (lean_obj_tag(v_t_u2081_4591_) == 0)
{
lean_object* v_size_4604_; 
v_size_4604_ = lean_ctor_get(v_t_u2081_4591_, 0);
lean_inc(v_size_4604_);
v___y_4601_ = v_size_4604_;
goto v___jp_4600_;
}
else
{
lean_object* v___x_4605_; 
v___x_4605_ = lean_unsigned_to_nat(0u);
v___y_4601_ = v___x_4605_;
goto v___jp_4600_;
}
v___jp_4593_:
{
uint8_t v___x_4596_; 
v___x_4596_ = lean_nat_dec_le(v___y_4594_, v___y_4595_);
if (v___x_4596_ == 0)
{
lean_object* v___x_4597_; lean_object* v_a_4598_; 
lean_dec(v___y_4595_);
lean_dec(v___y_4594_);
v___x_4597_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4590_, v_t_u2081_4591_, v_t_u2082_4592_);
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref(v___x_4597_);
return v_a_4598_;
}
else
{
lean_object* v___x_4599_; 
v___x_4599_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4590_, v_t_u2082_4592_, v___y_4594_, v___y_4595_, v_t_u2081_4591_);
lean_dec(v___y_4595_);
lean_dec(v___y_4594_);
return v___x_4599_;
}
}
v___jp_4600_:
{
if (lean_obj_tag(v_t_u2082_4592_) == 0)
{
lean_object* v_size_4602_; 
v_size_4602_ = lean_ctor_get(v_t_u2082_4592_, 0);
lean_inc(v_size_4602_);
v___y_4594_ = v___y_4601_;
v___y_4595_ = v_size_4602_;
goto v___jp_4593_;
}
else
{
lean_object* v___x_4603_; 
v___x_4603_ = lean_unsigned_to_nat(0u);
v___y_4594_ = v___y_4601_;
v___y_4595_ = v___x_4603_;
goto v___jp_4593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff___redArg(lean_object* v_cmp_4606_, lean_object* v_t_u2081_4607_, lean_object* v_t_u2082_4608_){
_start:
{
lean_object* v___x_4609_; 
v___x_4609_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4606_, v_t_u2081_4607_, v_t_u2082_4608_);
return v___x_4609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff(lean_object* v_00_u03b1_4610_, lean_object* v_00_u03b2_4611_, lean_object* v_cmp_4612_, lean_object* v_t_u2081_4613_, lean_object* v_t_u2082_4614_){
_start:
{
lean_object* v___x_4615_; 
v___x_4615_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4612_, v_t_u2081_4613_, v_t_u2082_4614_);
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0(lean_object* v_00_u03b1_4616_, lean_object* v_cmp_4617_, lean_object* v_00_u03b2_4618_, lean_object* v_t_u2081_4619_, lean_object* v_t_u2082_4620_, lean_object* v_h_u2081_4621_){
_start:
{
lean_object* v___x_4622_; 
v___x_4622_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4617_, v_t_u2081_4619_, v_t_u2082_4620_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0(lean_object* v_00_u03b1_4623_, lean_object* v_cmp_4624_, lean_object* v_00_u03b2_4625_, lean_object* v_k_4626_, lean_object* v_t_4627_, lean_object* v_h_4628_){
_start:
{
lean_object* v___x_4629_; 
v___x_4629_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_4624_, v_k_4626_, v_t_4627_);
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1(lean_object* v_00_u03b1_4630_, lean_object* v_00_u03b2_4631_, lean_object* v_cmp_4632_, lean_object* v_init_4633_, lean_object* v_x_4634_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4632_, v_init_4633_, v_x_4634_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2(lean_object* v_00_u03b1_4636_, lean_object* v_00_u03b2_4637_, lean_object* v_cmp_4638_, lean_object* v_t_u2082_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v_t_4642_, lean_object* v_hl_4643_){
_start:
{
lean_object* v___x_4644_; 
v___x_4644_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4638_, v_t_u2082_4639_, v___y_4640_, v___y_4641_, v_t_4642_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4645_, lean_object* v_00_u03b2_4646_, lean_object* v_cmp_4647_, lean_object* v_t_u2082_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v_t_4651_, lean_object* v_hl_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2(v_00_u03b1_4645_, v_00_u03b2_4646_, v_cmp_4647_, v_t_u2082_4648_, v___y_4649_, v___y_4650_, v_t_4651_, v_hl_4652_);
lean_dec(v___y_4650_);
lean_dec(v___y_4649_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSDiff___redArg(lean_object* v_cmp_4654_){
_start:
{
lean_object* v___x_4655_; 
v___x_4655_ = lean_alloc_closure((void*)(l_Std_DTreeMap_diff), 5, 3);
lean_closure_set(v___x_4655_, 0, lean_box(0));
lean_closure_set(v___x_4655_, 1, lean_box(0));
lean_closure_set(v___x_4655_, 2, v_cmp_4654_);
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSDiff(lean_object* v_00_u03b1_4656_, lean_object* v_00_u03b2_4657_, lean_object* v_cmp_4658_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = lean_alloc_closure((void*)(l_Std_DTreeMap_diff), 5, 3);
lean_closure_set(v___x_4659_, 0, lean_box(0));
lean_closure_set(v___x_4659_, 1, lean_box(0));
lean_closure_set(v___x_4659_, 2, v_cmp_4658_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_4660_, lean_object* v_a_4661_, lean_object* v_____s_4662_){
_start:
{
lean_object* v_r_4663_; lean_object* v___x_4664_; 
v_r_4663_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_4660_, v_a_4661_, v_____s_4662_);
v___x_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4664_, 0, v_r_4663_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany___redArg(lean_object* v_cmp_4665_, lean_object* v_inst_4666_, lean_object* v_t_4667_, lean_object* v_l_4668_){
_start:
{
lean_object* v___f_4669_; lean_object* v___x_4670_; 
v___f_4669_ = lean_alloc_closure((void*)(l_Std_DTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4669_, 0, v_cmp_4665_);
v___x_4670_ = lean_apply_4(v_inst_4666_, lean_box(0), v_l_4668_, v_t_4667_, v___f_4669_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany(lean_object* v_00_u03b1_4671_, lean_object* v_00_u03b2_4672_, lean_object* v_cmp_4673_, lean_object* v_00_u03c1_4674_, lean_object* v_inst_4675_, lean_object* v_t_4676_, lean_object* v_l_4677_){
_start:
{
lean_object* v___f_4678_; lean_object* v___x_4679_; 
v___f_4678_ = lean_alloc_closure((void*)(l_Std_DTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4678_, 0, v_cmp_4673_);
v___x_4679_ = lean_apply_4(v_inst_4675_, lean_box(0), v_l_4677_, v_t_4676_, v___f_4678_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany___redArg___lam__0(lean_object* v_cmp_4680_, lean_object* v_x_4681_, lean_object* v_____s_4682_){
_start:
{
lean_object* v_fst_4683_; lean_object* v_snd_4684_; lean_object* v_r_4685_; lean_object* v___x_4686_; 
v_fst_4683_ = lean_ctor_get(v_x_4681_, 0);
lean_inc(v_fst_4683_);
v_snd_4684_ = lean_ctor_get(v_x_4681_, 1);
lean_inc(v_snd_4684_);
lean_dec_ref(v_x_4681_);
v_r_4685_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4680_, v_fst_4683_, v_snd_4684_, v_____s_4682_);
v___x_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4686_, 0, v_r_4685_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany___redArg(lean_object* v_cmp_4687_, lean_object* v_inst_4688_, lean_object* v_t_4689_, lean_object* v_l_4690_){
_start:
{
lean_object* v___f_4691_; lean_object* v___x_4692_; 
v___f_4691_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4691_, 0, v_cmp_4687_);
v___x_4692_ = lean_apply_4(v_inst_4688_, lean_box(0), v_l_4690_, v_t_4689_, v___f_4691_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany(lean_object* v_00_u03b1_4693_, lean_object* v_cmp_4694_, lean_object* v_00_u03b2_4695_, lean_object* v_00_u03c1_4696_, lean_object* v_inst_4697_, lean_object* v_t_4698_, lean_object* v_l_4699_){
_start:
{
lean_object* v___f_4700_; lean_object* v___x_4701_; 
v___f_4700_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4700_, 0, v_cmp_4694_);
v___x_4701_ = lean_apply_4(v_inst_4697_, lean_box(0), v_l_4699_, v_t_4698_, v___f_4700_);
return v___x_4701_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_4702_, lean_object* v_a_4703_, lean_object* v_____s_4704_){
_start:
{
uint8_t v___x_4705_; 
lean_inc(v_____s_4704_);
lean_inc(v_a_4703_);
lean_inc_ref(v_cmp_4702_);
v___x_4705_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4702_, v_a_4703_, v_____s_4704_);
if (v___x_4705_ == 0)
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4706_ = lean_box(0);
v___x_4707_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4702_, v_a_4703_, v___x_4706_, v_____s_4704_);
v___x_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4708_, 0, v___x_4707_);
return v___x_4708_;
}
else
{
lean_object* v___x_4709_; 
lean_dec(v_a_4703_);
lean_dec_ref(v_cmp_4702_);
v___x_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4709_, 0, v_____s_4704_);
return v___x_4709_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_4710_, lean_object* v_inst_4711_, lean_object* v_t_4712_, lean_object* v_l_4713_){
_start:
{
lean_object* v___f_4714_; lean_object* v___x_4715_; 
v___f_4714_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4714_, 0, v_cmp_4710_);
v___x_4715_ = lean_apply_4(v_inst_4711_, lean_box(0), v_l_4713_, v_t_4712_, v___f_4714_);
return v___x_4715_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_4716_, lean_object* v_cmp_4717_, lean_object* v_00_u03c1_4718_, lean_object* v_inst_4719_, lean_object* v_t_4720_, lean_object* v_l_4721_){
_start:
{
lean_object* v___f_4722_; lean_object* v___x_4723_; 
v___f_4722_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4722_, 0, v_cmp_4717_);
v___x_4723_ = lean_apply_4(v_inst_4719_, lean_box(0), v_l_4721_, v_t_4720_, v___f_4722_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1(lean_object* v___f_4727_, lean_object* v___x_4728_, lean_object* v_m_4729_, lean_object* v_prec_4730_){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4731_ = ((lean_object*)(l_Std_DTreeMap_instRepr___redArg___lam__1___closed__1));
v___x_4732_ = lean_box(0);
v___x_4733_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_4734_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_4733_, v___f_4727_, v___x_4732_, v_m_4729_);
v___x_4735_ = l_List_repr___redArg(v___x_4728_, v___x_4734_);
v___x_4736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4736_, 0, v___x_4731_);
lean_ctor_set(v___x_4736_, 1, v___x_4735_);
v___x_4737_ = l_Repr_addAppParen(v___x_4736_, v_prec_4730_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1___boxed(lean_object* v___f_4738_, lean_object* v___x_4739_, lean_object* v_m_4740_, lean_object* v_prec_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_Std_DTreeMap_instRepr___redArg___lam__1(v___f_4738_, v___x_4739_, v_m_4740_, v_prec_4741_);
lean_dec(v_prec_4741_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg(lean_object* v_inst_4743_, lean_object* v_inst_4744_){
_start:
{
lean_object* v___f_4745_; lean_object* v___x_4746_; lean_object* v___f_4747_; 
v___f_4745_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_4746_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_4746_, 0, lean_box(0));
lean_closure_set(v___x_4746_, 1, lean_box(0));
lean_closure_set(v___x_4746_, 2, v_inst_4743_);
lean_closure_set(v___x_4746_, 3, v_inst_4744_);
v___f_4747_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4747_, 0, v___f_4745_);
lean_closure_set(v___f_4747_, 1, v___x_4746_);
return v___f_4747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr(lean_object* v_00_u03b1_4748_, lean_object* v_00_u03b2_4749_, lean_object* v_cmp_4750_, lean_object* v_inst_4751_, lean_object* v_inst_4752_){
_start:
{
lean_object* v___x_4753_; 
v___x_4753_ = l_Std_DTreeMap_instRepr___redArg(v_inst_4751_, v_inst_4752_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___boxed(lean_object* v_00_u03b1_4754_, lean_object* v_00_u03b2_4755_, lean_object* v_cmp_4756_, lean_object* v_inst_4757_, lean_object* v_inst_4758_){
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l_Std_DTreeMap_instRepr(v_00_u03b1_4754_, v_00_u03b2_4755_, v_cmp_4756_, v_inst_4757_, v_inst_4758_);
lean_dec_ref(v_cmp_4756_);
return v_res_4759_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_DTreeMap___auto__1 = _init_l_Std_DTreeMap___auto__1();
lean_mark_persistent(l_Std_DTreeMap___auto__1);
l_Std_DTreeMap_ofList___auto__1 = _init_l_Std_DTreeMap_ofList___auto__1();
lean_mark_persistent(l_Std_DTreeMap_ofList___auto__1);
l_Std_DTreeMap_ofArray___auto__1 = _init_l_Std_DTreeMap_ofArray___auto__1();
lean_mark_persistent(l_Std_DTreeMap_ofArray___auto__1);
l_Std_DTreeMap_Const_ofList___auto__1 = _init_l_Std_DTreeMap_Const_ofList___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Const_ofList___auto__1);
l_Std_DTreeMap_Const_ofArray___auto__1 = _init_l_Std_DTreeMap_Const_ofArray___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Const_ofArray___auto__1);
l_Std_DTreeMap_Const_unitOfList___auto__1 = _init_l_Std_DTreeMap_Const_unitOfList___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Const_unitOfList___auto__1);
l_Std_DTreeMap_Const_unitOfArray___auto__1 = _init_l_Std_DTreeMap_Const_unitOfArray___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Const_unitOfArray___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Internal_WF_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
