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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg(lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__15;
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__16;
static const lean_ctor_object l_Std_DTreeMap___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
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
static lean_once_cell_t l_Std_DTreeMap___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_DTreeMap___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__15(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__14));
v___x_34_ = lean_string_utf8_byte_size(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__16(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__15, &l_Std_DTreeMap___auto__1___closed__15_once, _init_l_Std_DTreeMap___auto__1___closed__15);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__14));
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_35_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_41_ = lean_box(0);
v___x_42_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__17));
v___x_43_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__16, &l_Std_DTreeMap___auto__1___closed__16_once, _init_l_Std_DTreeMap___auto__1___closed__16);
v___x_44_ = lean_box(2);
v___x_45_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
lean_ctor_set(v___x_45_, 2, v___x_42_);
lean_ctor_set(v___x_45_, 3, v___x_41_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__18, &l_Std_DTreeMap___auto__1___closed__18_once, _init_l_Std_DTreeMap___auto__1___closed__18);
v___x_47_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__13, &l_Std_DTreeMap___auto__1___closed__13_once, _init_l_Std_DTreeMap___auto__1___closed__13);
v___x_48_ = lean_array_push(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__19, &l_Std_DTreeMap___auto__1___closed__19_once, _init_l_Std_DTreeMap___auto__1___closed__19);
v___x_50_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__11));
v___x_51_ = lean_box(2);
v___x_52_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__21(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__20, &l_Std_DTreeMap___auto__1___closed__20_once, _init_l_Std_DTreeMap___auto__1___closed__20);
v___x_54_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__5));
v___x_55_ = lean_array_push(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__22(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__21, &l_Std_DTreeMap___auto__1___closed__21_once, _init_l_Std_DTreeMap___auto__1___closed__21);
v___x_57_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__9));
v___x_58_ = lean_box(2);
v___x_59_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__23(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__22, &l_Std_DTreeMap___auto__1___closed__22_once, _init_l_Std_DTreeMap___auto__1___closed__22);
v___x_61_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__24(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__23, &l_Std_DTreeMap___auto__1___closed__23_once, _init_l_Std_DTreeMap___auto__1___closed__23);
v___x_64_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__7));
v___x_65_ = lean_box(2);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__25(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__24, &l_Std_DTreeMap___auto__1___closed__24_once, _init_l_Std_DTreeMap___auto__1___closed__24);
v___x_68_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__5));
v___x_69_ = lean_array_push(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1___closed__26(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
v___x_71_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__4));
v___x_72_ = lean_box(2);
v___x_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_70_);
return v___x_73_;
}
}
static lean_object* _init_l_Std_DTreeMap___auto__1(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall(lean_object* v_00_u03b1_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(0);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_cmp_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(1);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty___boxed(lean_object* v_00_u03b1_81_, lean_object* v_00_u03b2_82_, lean_object* v_cmp_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_DTreeMap_empty(v_00_u03b1_81_, v_00_u03b2_82_, v_cmp_83_);
lean_dec_ref(v_cmp_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_cmp_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(1);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b2_90_, lean_object* v_cmp_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_DTreeMap_instEmptyCollection(v_00_u03b1_89_, v_00_u03b2_90_, v_cmp_91_);
lean_dec_ref(v_cmp_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_cmp_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(1);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited___boxed(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_cmp_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_DTreeMap_instInhabited(v_00_u03b1_97_, v_00_u03b2_98_, v_cmp_99_);
lean_dec_ref(v_cmp_99_);
return v_res_100_;
}
}
static lean_object* _init_l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3));
v___x_139_ = l_String_toRawSubstring_x27(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1(lean_object* v_x_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__3));
lean_inc(v_x_157_);
v___x_161_ = l_Lean_Syntax_isOfKind(v_x_157_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec_ref(v_a_158_);
lean_dec(v_x_157_);
v___x_162_ = lean_box(1);
v___x_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_a_159_);
return v___x_163_;
}
else
{
lean_object* v_quotContext_164_; lean_object* v_currMacroScope_165_; lean_object* v_ref_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_quotContext_164_ = lean_ctor_get(v_a_158_, 1);
lean_inc(v_quotContext_164_);
v_currMacroScope_165_ = lean_ctor_get(v_a_158_, 2);
lean_inc(v_currMacroScope_165_);
v_ref_166_ = lean_ctor_get(v_a_158_, 5);
lean_inc(v_ref_166_);
lean_dec_ref(v_a_158_);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = l_Lean_Syntax_getArg(v_x_157_, v___x_167_);
v___x_169_ = lean_unsigned_to_nat(2u);
v___x_170_ = l_Lean_Syntax_getArg(v_x_157_, v___x_169_);
lean_dec(v_x_157_);
v___x_171_ = 0;
v___x_172_ = l_Lean_SourceInfo_fromRef(v_ref_166_, v___x_171_);
lean_dec(v_ref_166_);
v___x_173_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2));
v___x_174_ = lean_obj_once(&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4, &l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4_once, _init_l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4);
v___x_175_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__5));
v___x_176_ = l_Lean_addMacroScope(v_quotContext_164_, v___x_175_, v_currMacroScope_165_);
v___x_177_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__10));
lean_inc(v___x_172_);
v___x_178_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_178_, 0, v___x_172_);
lean_ctor_set(v___x_178_, 1, v___x_174_);
lean_ctor_set(v___x_178_, 2, v___x_176_);
lean_ctor_set(v___x_178_, 3, v___x_177_);
v___x_179_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__9));
lean_inc(v___x_172_);
v___x_180_ = l_Lean_Syntax_node2(v___x_172_, v___x_179_, v___x_168_, v___x_170_);
v___x_181_ = l_Lean_Syntax_node2(v___x_172_, v___x_173_, v___x_178_, v___x_180_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_a_159_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(lean_object* v_x_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2));
lean_inc(v_x_186_);
v___x_190_ = l_Lean_Syntax_isOfKind(v_x_186_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v_x_186_);
v___x_191_ = lean_box(0);
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_a_188_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = l_Lean_Syntax_getArg(v_x_186_, v___x_193_);
v___x_195_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__1));
lean_inc(v___x_194_);
v___x_196_ = l_Lean_Syntax_isOfKind(v___x_194_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v___x_194_);
lean_dec(v_x_186_);
v___x_197_ = lean_box(0);
v___x_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v_a_188_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = l_Lean_Syntax_getArg(v_x_186_, v___x_199_);
lean_dec(v_x_186_);
v___x_201_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_200_);
v___x_202_ = l_Lean_Syntax_matchesNull(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v___x_200_);
lean_dec(v___x_194_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_a_188_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_ref_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_205_ = l_Lean_Syntax_getArg(v___x_200_, v___x_193_);
v___x_206_ = l_Lean_Syntax_getArg(v___x_200_, v___x_199_);
lean_dec(v___x_200_);
v_ref_207_ = l_Lean_replaceRef(v___x_194_, v_a_187_);
lean_dec(v___x_194_);
v___x_208_ = 0;
v___x_209_ = l_Lean_SourceInfo_fromRef(v_ref_207_, v___x_208_);
lean_dec(v_ref_207_);
v___x_210_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__3));
v___x_211_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__6));
lean_inc(v___x_209_);
v___x_212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_209_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = l_Lean_Syntax_node3(v___x_209_, v___x_210_, v___x_205_, v___x_212_, v___x_206_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v_a_188_);
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___boxed(lean_object* v_x_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(v_x_215_, v_a_216_, v_a_217_);
lean_dec(v_a_216_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insert___redArg(lean_object* v_cmp_219_, lean_object* v_t_220_, lean_object* v_a_221_, lean_object* v_b_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_219_, v_a_221_, v_b_222_, v_t_220_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insert(lean_object* v_00_u03b1_224_, lean_object* v_00_u03b2_225_, lean_object* v_cmp_226_, lean_object* v_t_227_, lean_object* v_a_228_, lean_object* v_b_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_226_, v_a_228_, v_b_229_, v_t_227_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma___redArg___lam__0(lean_object* v_cmp_231_, lean_object* v_e_232_){
_start:
{
lean_object* v_fst_233_; lean_object* v_snd_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_fst_233_ = lean_ctor_get(v_e_232_, 0);
lean_inc(v_fst_233_);
v_snd_234_ = lean_ctor_get(v_e_232_, 1);
lean_inc(v_snd_234_);
lean_dec_ref(v_e_232_);
v___x_235_ = lean_box(1);
v___x_236_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_231_, v_fst_233_, v_snd_234_, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma___redArg(lean_object* v_cmp_237_){
_start:
{
lean_object* v___f_238_; 
v___f_238_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_238_, 0, v_cmp_237_);
return v___f_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma(lean_object* v_00_u03b1_239_, lean_object* v_00_u03b2_240_, lean_object* v_cmp_241_){
_start:
{
lean_object* v___f_242_; 
v___f_242_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_242_, 0, v_cmp_241_);
return v___f_242_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma___redArg___lam__0(lean_object* v_cmp_243_, lean_object* v_e_244_, lean_object* v_s_245_){
_start:
{
lean_object* v_fst_246_; lean_object* v_snd_247_; lean_object* v___x_248_; 
v_fst_246_ = lean_ctor_get(v_e_244_, 0);
lean_inc(v_fst_246_);
v_snd_247_ = lean_ctor_get(v_e_244_, 1);
lean_inc(v_snd_247_);
lean_dec_ref(v_e_244_);
v___x_248_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_243_, v_fst_246_, v_snd_247_, v_s_245_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma___redArg(lean_object* v_cmp_249_){
_start:
{
lean_object* v___f_250_; 
v___f_250_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_250_, 0, v_cmp_249_);
return v___f_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma(lean_object* v_00_u03b1_251_, lean_object* v_00_u03b2_252_, lean_object* v_cmp_253_){
_start:
{
lean_object* v___f_254_; 
v___f_254_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_254_, 0, v_cmp_253_);
return v___f_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertIfNew___redArg(lean_object* v_cmp_255_, lean_object* v_t_256_, lean_object* v_a_257_, lean_object* v_b_258_){
_start:
{
uint8_t v___x_259_; 
lean_inc(v_t_256_);
lean_inc(v_a_257_);
lean_inc_ref(v_cmp_255_);
v___x_259_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_255_, v_a_257_, v_t_256_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
v___x_260_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_255_, v_a_257_, v_b_258_, v_t_256_);
return v___x_260_;
}
else
{
lean_dec(v_b_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_cmp_255_);
return v_t_256_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertIfNew(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_cmp_263_, lean_object* v_t_264_, lean_object* v_a_265_, lean_object* v_b_266_){
_start:
{
uint8_t v___x_267_; 
lean_inc(v_t_264_);
lean_inc(v_a_265_);
lean_inc_ref(v_cmp_263_);
v___x_267_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_263_, v_a_265_, v_t_264_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_263_, v_a_265_, v_b_266_, v_t_264_);
return v___x_268_;
}
else
{
lean_dec(v_b_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_cmp_263_);
return v_t_264_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsert___redArg(lean_object* v_cmp_269_, lean_object* v_t_270_, lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
lean_object* v_sz_273_; lean_object* v_m_274_; lean_object* v___y_276_; 
v_sz_273_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_270_);
v_m_274_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_269_, v_a_271_, v_b_272_, v_t_270_);
if (lean_obj_tag(v_m_274_) == 0)
{
lean_object* v_size_280_; 
v_size_280_ = lean_ctor_get(v_m_274_, 0);
lean_inc(v_size_280_);
v___y_276_ = v_size_280_;
goto v___jp_275_;
}
else
{
lean_object* v___x_281_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___y_276_ = v___x_281_;
goto v___jp_275_;
}
v___jp_275_:
{
uint8_t v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_nat_dec_eq(v_sz_273_, v___y_276_);
lean_dec(v___y_276_);
lean_dec(v_sz_273_);
v___x_278_ = lean_box(v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_m_274_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsert(lean_object* v_00_u03b1_282_, lean_object* v_00_u03b2_283_, lean_object* v_cmp_284_, lean_object* v_t_285_, lean_object* v_a_286_, lean_object* v_b_287_){
_start:
{
lean_object* v_sz_288_; lean_object* v_m_289_; lean_object* v___y_291_; 
v_sz_288_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_285_);
v_m_289_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_284_, v_a_286_, v_b_287_, v_t_285_);
if (lean_obj_tag(v_m_289_) == 0)
{
lean_object* v_size_295_; 
v_size_295_ = lean_ctor_get(v_m_289_, 0);
lean_inc(v_size_295_);
v___y_291_ = v_size_295_;
goto v___jp_290_;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v___y_291_ = v___x_296_;
goto v___jp_290_;
}
v___jp_290_:
{
uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_nat_dec_eq(v_sz_288_, v___y_291_);
lean_dec(v___y_291_);
lean_dec(v_sz_288_);
v___x_293_ = lean_box(v___x_292_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_m_289_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_297_, lean_object* v_t_298_, lean_object* v_a_299_, lean_object* v_b_300_){
_start:
{
uint8_t v___x_301_; 
lean_inc(v_t_298_);
lean_inc(v_a_299_);
lean_inc_ref(v_cmp_297_);
v___x_301_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_297_, v_a_299_, v_t_298_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_297_, v_a_299_, v_b_300_, v_t_298_);
v___x_303_ = lean_box(v___x_301_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v_b_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_cmp_297_);
v___x_305_ = lean_box(v___x_301_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v_t_298_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_307_, lean_object* v_00_u03b2_308_, lean_object* v_cmp_309_, lean_object* v_t_310_, lean_object* v_a_311_, lean_object* v_b_312_){
_start:
{
uint8_t v___x_313_; 
lean_inc(v_t_310_);
lean_inc(v_a_311_);
lean_inc_ref(v_cmp_309_);
v___x_313_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_309_, v_a_311_, v_t_310_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_309_, v_a_311_, v_b_312_, v_t_310_);
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
lean_dec_ref(v_cmp_309_);
v___x_317_ = lean_box(v___x_313_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v_t_310_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_319_, lean_object* v_t_320_, lean_object* v_a_321_, lean_object* v_b_322_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_cmp_331_, lean_object* v_inst_332_, lean_object* v_t_333_, lean_object* v_a_334_, lean_object* v_b_335_){
_start:
{
lean_object* v___x_336_; 
lean_inc(v_a_334_);
lean_inc(v_t_333_);
lean_inc_ref(v_cmp_331_);
v___x_336_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_331_, v_t_333_, v_a_334_);
if (lean_obj_tag(v___x_336_) == 0)
{
uint8_t v___x_337_; 
lean_inc(v_t_333_);
lean_inc(v_a_334_);
lean_inc_ref(v_cmp_331_);
v___x_337_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_331_, v_a_334_, v_t_333_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_331_, v_a_334_, v_b_335_, v_t_333_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_336_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
return v___x_339_;
}
else
{
lean_object* v___x_340_; 
lean_dec(v_b_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_cmp_331_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_336_);
lean_ctor_set(v___x_340_, 1, v_t_333_);
return v___x_340_;
}
}
else
{
lean_object* v___x_341_; 
lean_dec(v_b_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_cmp_331_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_336_);
lean_ctor_set(v___x_341_, 1, v_t_333_);
return v___x_341_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_contains___redArg(lean_object* v_cmp_342_, lean_object* v_t_343_, lean_object* v_a_344_){
_start:
{
uint8_t v___x_345_; 
v___x_345_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_342_, v_a_344_, v_t_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_contains___redArg___boxed(lean_object* v_cmp_346_, lean_object* v_t_347_, lean_object* v_a_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Std_DTreeMap_contains___redArg(v_cmp_346_, v_t_347_, v_a_348_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_contains(lean_object* v_00_u03b1_351_, lean_object* v_00_u03b2_352_, lean_object* v_cmp_353_, lean_object* v_t_354_, lean_object* v_a_355_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_353_, v_a_355_, v_t_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_contains___boxed(lean_object* v_00_u03b1_357_, lean_object* v_00_u03b2_358_, lean_object* v_cmp_359_, lean_object* v_t_360_, lean_object* v_a_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Std_DTreeMap_contains(v_00_u03b1_357_, v_00_u03b2_358_, v_cmp_359_, v_t_360_, v_a_361_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership(lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_cmp_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_box(0);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___boxed(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_cmp_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Std_DTreeMap_instMembership(v_00_u03b1_368_, v_00_u03b2_369_, v_cmp_370_);
lean_dec_ref(v_cmp_370_);
return v_res_371_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableMem___redArg(lean_object* v_cmp_372_, lean_object* v_m_373_, lean_object* v_a_374_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_372_, v_a_374_, v_m_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_376_, lean_object* v_m_377_, lean_object* v_a_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = l_Std_DTreeMap_instDecidableMem___redArg(v_cmp_376_, v_m_377_, v_a_378_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableMem(lean_object* v_00_u03b1_381_, lean_object* v_00_u03b2_382_, lean_object* v_cmp_383_, lean_object* v_m_384_, lean_object* v_a_385_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_383_, v_a_385_, v_m_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_387_, lean_object* v_00_u03b2_388_, lean_object* v_cmp_389_, lean_object* v_m_390_, lean_object* v_a_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Std_DTreeMap_instDecidableMem(v_00_u03b1_387_, v_00_u03b2_388_, v_cmp_389_, v_m_390_, v_a_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___redArg(lean_object* v_t_394_){
_start:
{
if (lean_obj_tag(v_t_394_) == 0)
{
lean_object* v_size_395_; 
v_size_395_ = lean_ctor_get(v_t_394_, 0);
lean_inc(v_size_395_);
return v_size_395_;
}
else
{
lean_object* v___x_396_; 
v___x_396_ = lean_unsigned_to_nat(0u);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___redArg___boxed(lean_object* v_t_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_DTreeMap_size___redArg(v_t_397_);
lean_dec(v_t_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size(lean_object* v_00_u03b1_399_, lean_object* v_00_u03b2_400_, lean_object* v_cmp_401_, lean_object* v_t_402_){
_start:
{
if (lean_obj_tag(v_t_402_) == 0)
{
lean_object* v_size_403_; 
v_size_403_ = lean_ctor_get(v_t_402_, 0);
lean_inc(v_size_403_);
return v_size_403_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = lean_unsigned_to_nat(0u);
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___boxed(lean_object* v_00_u03b1_405_, lean_object* v_00_u03b2_406_, lean_object* v_cmp_407_, lean_object* v_t_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_DTreeMap_size(v_00_u03b1_405_, v_00_u03b2_406_, v_cmp_407_, v_t_408_);
lean_dec(v_t_408_);
lean_dec_ref(v_cmp_407_);
return v_res_409_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_isEmpty___redArg(lean_object* v_t_410_){
_start:
{
if (lean_obj_tag(v_t_410_) == 0)
{
uint8_t v___x_411_; 
v___x_411_ = 0;
return v___x_411_;
}
else
{
uint8_t v___x_412_; 
v___x_412_ = 1;
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isEmpty___redArg___boxed(lean_object* v_t_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Std_DTreeMap_isEmpty___redArg(v_t_413_);
lean_dec(v_t_413_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_isEmpty(lean_object* v_00_u03b1_416_, lean_object* v_00_u03b2_417_, lean_object* v_cmp_418_, lean_object* v_t_419_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_422_, lean_object* v_00_u03b2_423_, lean_object* v_cmp_424_, lean_object* v_t_425_){
_start:
{
uint8_t v_res_426_; lean_object* v_r_427_; 
v_res_426_ = l_Std_DTreeMap_isEmpty(v_00_u03b1_422_, v_00_u03b2_423_, v_cmp_424_, v_t_425_);
lean_dec(v_t_425_);
lean_dec_ref(v_cmp_424_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_erase___redArg(lean_object* v_cmp_428_, lean_object* v_t_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_428_, v_a_430_, v_t_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_erase(lean_object* v_00_u03b1_432_, lean_object* v_00_u03b2_433_, lean_object* v_cmp_434_, lean_object* v_t_435_, lean_object* v_a_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_434_, v_a_436_, v_t_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x3f___redArg(lean_object* v_cmp_438_, lean_object* v_t_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_438_, v_t_439_, v_a_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x3f(lean_object* v_00_u03b1_442_, lean_object* v_00_u03b2_443_, lean_object* v_cmp_444_, lean_object* v_inst_445_, lean_object* v_t_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_444_, v_t_446_, v_a_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get___redArg(lean_object* v_cmp_449_, lean_object* v_t_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_449_, v_t_450_, v_a_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get(lean_object* v_00_u03b1_453_, lean_object* v_00_u03b2_454_, lean_object* v_cmp_455_, lean_object* v_inst_456_, lean_object* v_t_457_, lean_object* v_a_458_, lean_object* v_h_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_455_, v_t_457_, v_a_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___redArg(lean_object* v_cmp_461_, lean_object* v_t_462_, lean_object* v_a_463_, lean_object* v_inst_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_461_, v_t_462_, v_a_463_, v_inst_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21(lean_object* v_00_u03b1_466_, lean_object* v_00_u03b2_467_, lean_object* v_cmp_468_, lean_object* v_inst_469_, lean_object* v_t_470_, lean_object* v_a_471_, lean_object* v_inst_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_468_, v_t_470_, v_a_471_, v_inst_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg(lean_object* v_cmp_474_, lean_object* v_t_475_, lean_object* v_a_476_, lean_object* v_fallback_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_474_, v_t_475_, v_a_476_, v_fallback_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg___boxed(lean_object* v_cmp_479_, lean_object* v_t_480_, lean_object* v_a_481_, lean_object* v_fallback_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_DTreeMap_getD___redArg(v_cmp_479_, v_t_480_, v_a_481_, v_fallback_482_);
lean_dec(v_fallback_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_cmp_486_, lean_object* v_inst_487_, lean_object* v_t_488_, lean_object* v_a_489_, lean_object* v_fallback_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_486_, v_t_488_, v_a_489_, v_fallback_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___boxed(lean_object* v_00_u03b1_492_, lean_object* v_00_u03b2_493_, lean_object* v_cmp_494_, lean_object* v_inst_495_, lean_object* v_t_496_, lean_object* v_a_497_, lean_object* v_fallback_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_DTreeMap_getD(v_00_u03b1_492_, v_00_u03b2_493_, v_cmp_494_, v_inst_495_, v_t_496_, v_a_497_, v_fallback_498_);
lean_dec(v_fallback_498_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f___redArg(lean_object* v_cmp_500_, lean_object* v_t_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_500_, v_t_501_, v_a_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f(lean_object* v_00_u03b1_504_, lean_object* v_00_u03b2_505_, lean_object* v_cmp_506_, lean_object* v_t_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_506_, v_t_507_, v_a_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey___redArg(lean_object* v_cmp_510_, lean_object* v_t_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_510_, v_t_511_, v_a_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey(lean_object* v_00_u03b1_514_, lean_object* v_00_u03b2_515_, lean_object* v_cmp_516_, lean_object* v_t_517_, lean_object* v_a_518_, lean_object* v_h_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_516_, v_t_517_, v_a_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___redArg(lean_object* v_cmp_521_, lean_object* v_inst_522_, lean_object* v_t_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_521_, v_t_523_, v_a_524_, v_inst_522_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21(lean_object* v_00_u03b1_526_, lean_object* v_00_u03b2_527_, lean_object* v_cmp_528_, lean_object* v_inst_529_, lean_object* v_t_530_, lean_object* v_a_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_528_, v_t_530_, v_a_531_, v_inst_529_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___redArg(lean_object* v_cmp_533_, lean_object* v_t_534_, lean_object* v_a_535_, lean_object* v_fallback_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_533_, v_t_534_, v_a_535_, v_fallback_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_538_, lean_object* v_t_539_, lean_object* v_a_540_, lean_object* v_fallback_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_DTreeMap_getKeyD___redArg(v_cmp_538_, v_t_539_, v_a_540_, v_fallback_541_);
lean_dec(v_fallback_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD(lean_object* v_00_u03b1_543_, lean_object* v_00_u03b2_544_, lean_object* v_cmp_545_, lean_object* v_t_546_, lean_object* v_a_547_, lean_object* v_fallback_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_545_, v_t_546_, v_a_547_, v_fallback_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_550_, lean_object* v_00_u03b2_551_, lean_object* v_cmp_552_, lean_object* v_t_553_, lean_object* v_a_554_, lean_object* v_fallback_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_DTreeMap_getKeyD(v_00_u03b1_550_, v_00_u03b2_551_, v_cmp_552_, v_t_553_, v_a_554_, v_fallback_555_);
lean_dec(v_fallback_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x3f___redArg(lean_object* v_cmp_557_, lean_object* v_t_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_557_, v_t_558_, v_a_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x3f(lean_object* v_00_u03b1_561_, lean_object* v_00_u03b2_562_, lean_object* v_cmp_563_, lean_object* v_t_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_563_, v_t_564_, v_a_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry___redArg(lean_object* v_cmp_567_, lean_object* v_t_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_567_, v_t_568_, v_a_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_cmp_573_, lean_object* v_t_574_, lean_object* v_a_575_, lean_object* v_h_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_573_, v_t_574_, v_a_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___redArg(lean_object* v_cmp_578_, lean_object* v_t_579_, lean_object* v_a_580_, lean_object* v_fallback_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_578_, v_t_579_, v_a_580_, v_fallback_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___redArg___boxed(lean_object* v_cmp_583_, lean_object* v_t_584_, lean_object* v_a_585_, lean_object* v_fallback_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_DTreeMap_getEntryD___redArg(v_cmp_583_, v_t_584_, v_a_585_, v_fallback_586_);
lean_dec_ref(v_fallback_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_cmp_590_, lean_object* v_t_591_, lean_object* v_a_592_, lean_object* v_fallback_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_590_, v_t_591_, v_a_592_, v_fallback_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___boxed(lean_object* v_00_u03b1_595_, lean_object* v_00_u03b2_596_, lean_object* v_cmp_597_, lean_object* v_t_598_, lean_object* v_a_599_, lean_object* v_fallback_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_DTreeMap_getEntryD(v_00_u03b1_595_, v_00_u03b2_596_, v_cmp_597_, v_t_598_, v_a_599_, v_fallback_600_);
lean_dec_ref(v_fallback_600_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___redArg(lean_object* v_cmp_602_, lean_object* v_inst_603_, lean_object* v_t_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_602_, v_inst_603_, v_t_604_, v_a_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21(lean_object* v_00_u03b1_607_, lean_object* v_00_u03b2_608_, lean_object* v_cmp_609_, lean_object* v_inst_610_, lean_object* v_t_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_609_, v_inst_610_, v_t_611_, v_a_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___redArg(lean_object* v_t_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_DTreeMap_minEntry_x3f___redArg(v_t_616_);
lean_dec(v_t_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f(lean_object* v_00_u03b1_618_, lean_object* v_00_u03b2_619_, lean_object* v_cmp_620_, lean_object* v_t_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_623_, lean_object* v_00_u03b2_624_, lean_object* v_cmp_625_, lean_object* v_t_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_DTreeMap_minEntry_x3f(v_00_u03b1_623_, v_00_u03b2_624_, v_cmp_625_, v_t_626_);
lean_dec(v_t_626_);
lean_dec_ref(v_cmp_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___redArg(lean_object* v_t_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___redArg___boxed(lean_object* v_t_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std_DTreeMap_minEntry___redArg(v_t_630_);
lean_dec(v_t_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry(lean_object* v_00_u03b1_632_, lean_object* v_00_u03b2_633_, lean_object* v_cmp_634_, lean_object* v_t_635_, lean_object* v_h_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_635_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___boxed(lean_object* v_00_u03b1_638_, lean_object* v_00_u03b2_639_, lean_object* v_cmp_640_, lean_object* v_t_641_, lean_object* v_h_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_DTreeMap_minEntry(v_00_u03b1_638_, v_00_u03b2_639_, v_cmp_640_, v_t_641_, v_h_642_);
lean_dec(v_t_641_);
lean_dec_ref(v_cmp_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___redArg(lean_object* v_inst_644_, lean_object* v_t_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_644_, v_t_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_647_, lean_object* v_t_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Std_DTreeMap_minEntry_x21___redArg(v_inst_647_, v_t_648_);
lean_dec(v_t_648_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21(lean_object* v_00_u03b1_650_, lean_object* v_00_u03b2_651_, lean_object* v_cmp_652_, lean_object* v_inst_653_, lean_object* v_t_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_653_, v_t_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_656_, lean_object* v_00_u03b2_657_, lean_object* v_cmp_658_, lean_object* v_inst_659_, lean_object* v_t_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_DTreeMap_minEntry_x21(v_00_u03b1_656_, v_00_u03b2_657_, v_cmp_658_, v_inst_659_, v_t_660_);
lean_dec(v_t_660_);
lean_dec_ref(v_cmp_658_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___redArg(lean_object* v_t_662_, lean_object* v_fallback_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_662_, v_fallback_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___redArg___boxed(lean_object* v_t_665_, lean_object* v_fallback_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Std_DTreeMap_minEntryD___redArg(v_t_665_, v_fallback_666_);
lean_dec_ref(v_fallback_666_);
lean_dec(v_t_665_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD(lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_cmp_670_, lean_object* v_t_671_, lean_object* v_fallback_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_671_, v_fallback_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_cmp_676_, lean_object* v_t_677_, lean_object* v_fallback_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Std_DTreeMap_minEntryD(v_00_u03b1_674_, v_00_u03b2_675_, v_cmp_676_, v_t_677_, v_fallback_678_);
lean_dec_ref(v_fallback_678_);
lean_dec(v_t_677_);
lean_dec_ref(v_cmp_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___redArg(lean_object* v_t_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_DTreeMap_maxEntry_x3f___redArg(v_t_682_);
lean_dec(v_t_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_684_, lean_object* v_00_u03b2_685_, lean_object* v_cmp_686_, lean_object* v_t_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_689_, lean_object* v_00_u03b2_690_, lean_object* v_cmp_691_, lean_object* v_t_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_DTreeMap_maxEntry_x3f(v_00_u03b1_689_, v_00_u03b2_690_, v_cmp_691_, v_t_692_);
lean_dec(v_t_692_);
lean_dec_ref(v_cmp_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___redArg(lean_object* v_t_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___redArg___boxed(lean_object* v_t_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_DTreeMap_maxEntry___redArg(v_t_696_);
lean_dec(v_t_696_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_cmp_700_, lean_object* v_t_701_, lean_object* v_h_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_701_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_704_, lean_object* v_00_u03b2_705_, lean_object* v_cmp_706_, lean_object* v_t_707_, lean_object* v_h_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_DTreeMap_maxEntry(v_00_u03b1_704_, v_00_u03b2_705_, v_cmp_706_, v_t_707_, v_h_708_);
lean_dec(v_t_707_);
lean_dec_ref(v_cmp_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___redArg(lean_object* v_inst_710_, lean_object* v_t_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_710_, v_t_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_713_, lean_object* v_t_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_DTreeMap_maxEntry_x21___redArg(v_inst_713_, v_t_714_);
lean_dec(v_t_714_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21(lean_object* v_00_u03b1_716_, lean_object* v_00_u03b2_717_, lean_object* v_cmp_718_, lean_object* v_inst_719_, lean_object* v_t_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_719_, v_t_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_722_, lean_object* v_00_u03b2_723_, lean_object* v_cmp_724_, lean_object* v_inst_725_, lean_object* v_t_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_DTreeMap_maxEntry_x21(v_00_u03b1_722_, v_00_u03b2_723_, v_cmp_724_, v_inst_725_, v_t_726_);
lean_dec(v_t_726_);
lean_dec_ref(v_cmp_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___redArg(lean_object* v_t_728_, lean_object* v_fallback_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_728_, v_fallback_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_731_, lean_object* v_fallback_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Std_DTreeMap_maxEntryD___redArg(v_t_731_, v_fallback_732_);
lean_dec_ref(v_fallback_732_);
lean_dec(v_t_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD(lean_object* v_00_u03b1_734_, lean_object* v_00_u03b2_735_, lean_object* v_cmp_736_, lean_object* v_t_737_, lean_object* v_fallback_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_737_, v_fallback_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_740_, lean_object* v_00_u03b2_741_, lean_object* v_cmp_742_, lean_object* v_t_743_, lean_object* v_fallback_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Std_DTreeMap_maxEntryD(v_00_u03b1_740_, v_00_u03b2_741_, v_cmp_742_, v_t_743_, v_fallback_744_);
lean_dec_ref(v_fallback_744_);
lean_dec(v_t_743_);
lean_dec_ref(v_cmp_742_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___redArg(lean_object* v_t_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_DTreeMap_minKey_x3f___redArg(v_t_748_);
lean_dec(v_t_748_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f(lean_object* v_00_u03b1_750_, lean_object* v_00_u03b2_751_, lean_object* v_cmp_752_, lean_object* v_t_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_755_, lean_object* v_00_u03b2_756_, lean_object* v_cmp_757_, lean_object* v_t_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_DTreeMap_minKey_x3f(v_00_u03b1_755_, v_00_u03b2_756_, v_cmp_757_, v_t_758_);
lean_dec(v_t_758_);
lean_dec_ref(v_cmp_757_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___redArg(lean_object* v_t_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___redArg___boxed(lean_object* v_t_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_DTreeMap_minKey___redArg(v_t_762_);
lean_dec(v_t_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey(lean_object* v_00_u03b1_764_, lean_object* v_00_u03b2_765_, lean_object* v_cmp_766_, lean_object* v_t_767_, lean_object* v_h_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___boxed(lean_object* v_00_u03b1_770_, lean_object* v_00_u03b2_771_, lean_object* v_cmp_772_, lean_object* v_t_773_, lean_object* v_h_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_DTreeMap_minKey(v_00_u03b1_770_, v_00_u03b2_771_, v_cmp_772_, v_t_773_, v_h_774_);
lean_dec(v_t_773_);
lean_dec_ref(v_cmp_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___redArg(lean_object* v_inst_776_, lean_object* v_t_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_776_, v_t_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_779_, lean_object* v_t_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Std_DTreeMap_minKey_x21___redArg(v_inst_779_, v_t_780_);
lean_dec(v_t_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21(lean_object* v_00_u03b1_782_, lean_object* v_00_u03b2_783_, lean_object* v_cmp_784_, lean_object* v_inst_785_, lean_object* v_t_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_785_, v_t_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_788_, lean_object* v_00_u03b2_789_, lean_object* v_cmp_790_, lean_object* v_inst_791_, lean_object* v_t_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_DTreeMap_minKey_x21(v_00_u03b1_788_, v_00_u03b2_789_, v_cmp_790_, v_inst_791_, v_t_792_);
lean_dec(v_t_792_);
lean_dec_ref(v_cmp_790_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___redArg(lean_object* v_t_794_, lean_object* v_fallback_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_794_, v_fallback_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___redArg___boxed(lean_object* v_t_797_, lean_object* v_fallback_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Std_DTreeMap_minKeyD___redArg(v_t_797_, v_fallback_798_);
lean_dec(v_fallback_798_);
lean_dec(v_t_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD(lean_object* v_00_u03b1_800_, lean_object* v_00_u03b2_801_, lean_object* v_cmp_802_, lean_object* v_t_803_, lean_object* v_fallback_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_803_, v_fallback_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_806_, lean_object* v_00_u03b2_807_, lean_object* v_cmp_808_, lean_object* v_t_809_, lean_object* v_fallback_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Std_DTreeMap_minKeyD(v_00_u03b1_806_, v_00_u03b2_807_, v_cmp_808_, v_t_809_, v_fallback_810_);
lean_dec(v_fallback_810_);
lean_dec(v_t_809_);
lean_dec_ref(v_cmp_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___redArg(lean_object* v_t_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_DTreeMap_maxKey_x3f___redArg(v_t_814_);
lean_dec(v_t_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_cmp_818_, lean_object* v_t_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_821_, lean_object* v_00_u03b2_822_, lean_object* v_cmp_823_, lean_object* v_t_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_DTreeMap_maxKey_x3f(v_00_u03b1_821_, v_00_u03b2_822_, v_cmp_823_, v_t_824_);
lean_dec(v_t_824_);
lean_dec_ref(v_cmp_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___redArg(lean_object* v_t_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___redArg___boxed(lean_object* v_t_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_DTreeMap_maxKey___redArg(v_t_828_);
lean_dec(v_t_828_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey(lean_object* v_00_u03b1_830_, lean_object* v_00_u03b2_831_, lean_object* v_cmp_832_, lean_object* v_t_833_, lean_object* v_h_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___boxed(lean_object* v_00_u03b1_836_, lean_object* v_00_u03b2_837_, lean_object* v_cmp_838_, lean_object* v_t_839_, lean_object* v_h_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_DTreeMap_maxKey(v_00_u03b1_836_, v_00_u03b2_837_, v_cmp_838_, v_t_839_, v_h_840_);
lean_dec(v_t_839_);
lean_dec_ref(v_cmp_838_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___redArg(lean_object* v_inst_842_, lean_object* v_t_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_842_, v_t_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_845_, lean_object* v_t_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_DTreeMap_maxKey_x21___redArg(v_inst_845_, v_t_846_);
lean_dec(v_t_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21(lean_object* v_00_u03b1_848_, lean_object* v_00_u03b2_849_, lean_object* v_cmp_850_, lean_object* v_inst_851_, lean_object* v_t_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_851_, v_t_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_854_, lean_object* v_00_u03b2_855_, lean_object* v_cmp_856_, lean_object* v_inst_857_, lean_object* v_t_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_DTreeMap_maxKey_x21(v_00_u03b1_854_, v_00_u03b2_855_, v_cmp_856_, v_inst_857_, v_t_858_);
lean_dec(v_t_858_);
lean_dec_ref(v_cmp_856_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___redArg(lean_object* v_t_860_, lean_object* v_fallback_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_860_, v_fallback_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_863_, lean_object* v_fallback_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_DTreeMap_maxKeyD___redArg(v_t_863_, v_fallback_864_);
lean_dec(v_fallback_864_);
lean_dec(v_t_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD(lean_object* v_00_u03b1_866_, lean_object* v_00_u03b2_867_, lean_object* v_cmp_868_, lean_object* v_t_869_, lean_object* v_fallback_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_869_, v_fallback_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_872_, lean_object* v_00_u03b2_873_, lean_object* v_cmp_874_, lean_object* v_t_875_, lean_object* v_fallback_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_DTreeMap_maxKeyD(v_00_u03b1_872_, v_00_u03b2_873_, v_cmp_874_, v_t_875_, v_fallback_876_);
lean_dec(v_fallback_876_);
lean_dec(v_t_875_);
lean_dec_ref(v_cmp_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_878_, lean_object* v_n_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_878_, v_n_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_881_, lean_object* v_n_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Std_DTreeMap_entryAtIdx_x3f___redArg(v_t_881_, v_n_882_);
lean_dec(v_t_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_884_, lean_object* v_00_u03b2_885_, lean_object* v_cmp_886_, lean_object* v_t_887_, lean_object* v_n_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_887_, v_n_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_890_, lean_object* v_00_u03b2_891_, lean_object* v_cmp_892_, lean_object* v_t_893_, lean_object* v_n_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_DTreeMap_entryAtIdx_x3f(v_00_u03b1_890_, v_00_u03b2_891_, v_cmp_892_, v_t_893_, v_n_894_);
lean_dec(v_t_893_);
lean_dec_ref(v_cmp_892_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___redArg(lean_object* v_t_896_, lean_object* v_n_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_896_, v_n_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_899_, lean_object* v_n_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_DTreeMap_entryAtIdx___redArg(v_t_899_, v_n_900_);
lean_dec(v_t_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_cmp_904_, lean_object* v_t_905_, lean_object* v_n_906_, lean_object* v_h_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_905_, v_n_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_909_, lean_object* v_00_u03b2_910_, lean_object* v_cmp_911_, lean_object* v_t_912_, lean_object* v_n_913_, lean_object* v_h_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Std_DTreeMap_entryAtIdx(v_00_u03b1_909_, v_00_u03b2_910_, v_cmp_911_, v_t_912_, v_n_913_, v_h_914_);
lean_dec(v_t_912_);
lean_dec_ref(v_cmp_911_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_916_, lean_object* v_t_917_, lean_object* v_n_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_916_, v_t_917_, v_n_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_920_, lean_object* v_t_921_, lean_object* v_n_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_DTreeMap_entryAtIdx_x21___redArg(v_inst_920_, v_t_921_, v_n_922_);
lean_dec(v_t_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_cmp_926_, lean_object* v_inst_927_, lean_object* v_t_928_, lean_object* v_n_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_927_, v_t_928_, v_n_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_931_, lean_object* v_00_u03b2_932_, lean_object* v_cmp_933_, lean_object* v_inst_934_, lean_object* v_t_935_, lean_object* v_n_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_DTreeMap_entryAtIdx_x21(v_00_u03b1_931_, v_00_u03b2_932_, v_cmp_933_, v_inst_934_, v_t_935_, v_n_936_);
lean_dec(v_t_935_);
lean_dec_ref(v_cmp_933_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___redArg(lean_object* v_t_938_, lean_object* v_n_939_, lean_object* v_fallback_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_938_, v_n_939_, v_fallback_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_942_, lean_object* v_n_943_, lean_object* v_fallback_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_DTreeMap_entryAtIdxD___redArg(v_t_942_, v_n_943_, v_fallback_944_);
lean_dec_ref(v_fallback_944_);
lean_dec(v_t_942_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_cmp_948_, lean_object* v_t_949_, lean_object* v_n_950_, lean_object* v_fallback_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_949_, v_n_950_, v_fallback_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_953_, lean_object* v_00_u03b2_954_, lean_object* v_cmp_955_, lean_object* v_t_956_, lean_object* v_n_957_, lean_object* v_fallback_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Std_DTreeMap_entryAtIdxD(v_00_u03b1_953_, v_00_u03b2_954_, v_cmp_955_, v_t_956_, v_n_957_, v_fallback_958_);
lean_dec_ref(v_fallback_958_);
lean_dec(v_t_956_);
lean_dec_ref(v_cmp_955_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_960_, lean_object* v_n_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_960_, v_n_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_963_, lean_object* v_n_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_DTreeMap_keyAtIdx_x3f___redArg(v_t_963_, v_n_964_);
lean_dec(v_t_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_966_, lean_object* v_00_u03b2_967_, lean_object* v_cmp_968_, lean_object* v_t_969_, lean_object* v_n_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_969_, v_n_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_972_, lean_object* v_00_u03b2_973_, lean_object* v_cmp_974_, lean_object* v_t_975_, lean_object* v_n_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_DTreeMap_keyAtIdx_x3f(v_00_u03b1_972_, v_00_u03b2_973_, v_cmp_974_, v_t_975_, v_n_976_);
lean_dec(v_t_975_);
lean_dec_ref(v_cmp_974_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___redArg(lean_object* v_t_978_, lean_object* v_n_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_978_, v_n_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_981_, lean_object* v_n_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Std_DTreeMap_keyAtIdx___redArg(v_t_981_, v_n_982_);
lean_dec(v_t_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx(lean_object* v_00_u03b1_984_, lean_object* v_00_u03b2_985_, lean_object* v_cmp_986_, lean_object* v_t_987_, lean_object* v_n_988_, lean_object* v_h_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_987_, v_n_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_991_, lean_object* v_00_u03b2_992_, lean_object* v_cmp_993_, lean_object* v_t_994_, lean_object* v_n_995_, lean_object* v_h_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Std_DTreeMap_keyAtIdx(v_00_u03b1_991_, v_00_u03b2_992_, v_cmp_993_, v_t_994_, v_n_995_, v_h_996_);
lean_dec(v_t_994_);
lean_dec_ref(v_cmp_993_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_998_, lean_object* v_t_999_, lean_object* v_n_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_998_, v_t_999_, v_n_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_1002_, lean_object* v_t_1003_, lean_object* v_n_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Std_DTreeMap_keyAtIdx_x21___redArg(v_inst_1002_, v_t_1003_, v_n_1004_);
lean_dec(v_t_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_1006_, lean_object* v_00_u03b2_1007_, lean_object* v_cmp_1008_, lean_object* v_inst_1009_, lean_object* v_t_1010_, lean_object* v_n_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1009_, v_t_1010_, v_n_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_1013_, lean_object* v_00_u03b2_1014_, lean_object* v_cmp_1015_, lean_object* v_inst_1016_, lean_object* v_t_1017_, lean_object* v_n_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Std_DTreeMap_keyAtIdx_x21(v_00_u03b1_1013_, v_00_u03b2_1014_, v_cmp_1015_, v_inst_1016_, v_t_1017_, v_n_1018_);
lean_dec(v_t_1017_);
lean_dec_ref(v_cmp_1015_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___redArg(lean_object* v_t_1020_, lean_object* v_n_1021_, lean_object* v_fallback_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1020_, v_n_1021_, v_fallback_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_1024_, lean_object* v_n_1025_, lean_object* v_fallback_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Std_DTreeMap_keyAtIdxD___redArg(v_t_1024_, v_n_1025_, v_fallback_1026_);
lean_dec(v_fallback_1026_);
lean_dec(v_t_1024_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD(lean_object* v_00_u03b1_1028_, lean_object* v_00_u03b2_1029_, lean_object* v_cmp_1030_, lean_object* v_t_1031_, lean_object* v_n_1032_, lean_object* v_fallback_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1031_, v_n_1032_, v_fallback_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_1035_, lean_object* v_00_u03b2_1036_, lean_object* v_cmp_1037_, lean_object* v_t_1038_, lean_object* v_n_1039_, lean_object* v_fallback_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_DTreeMap_keyAtIdxD(v_00_u03b1_1035_, v_00_u03b2_1036_, v_cmp_1037_, v_t_1038_, v_n_1039_, v_fallback_1040_);
lean_dec(v_fallback_1040_);
lean_dec(v_t_1038_);
lean_dec_ref(v_cmp_1037_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1042_, lean_object* v_t_1043_, lean_object* v_k_1044_){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_box(0);
v___x_1046_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1042_, v_k_1044_, v___x_1045_, v_t_1043_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1047_, lean_object* v_00_u03b2_1048_, lean_object* v_cmp_1049_, lean_object* v_t_1050_, lean_object* v_k_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1049_, v_k_1051_, v___x_1052_, v_t_1050_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1054_, lean_object* v_t_1055_, lean_object* v_k_1056_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1054_, v_k_1056_, v___x_1057_, v_t_1055_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1059_, lean_object* v_00_u03b2_1060_, lean_object* v_cmp_1061_, lean_object* v_t_1062_, lean_object* v_k_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1061_, v_k_1063_, v___x_1064_, v_t_1062_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1066_, lean_object* v_t_1067_, lean_object* v_k_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_box(0);
v___x_1070_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1066_, v_k_1068_, v___x_1069_, v_t_1067_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1071_, lean_object* v_00_u03b2_1072_, lean_object* v_cmp_1073_, lean_object* v_t_1074_, lean_object* v_k_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1073_, v_k_1075_, v___x_1076_, v_t_1074_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1078_, lean_object* v_t_1079_, lean_object* v_k_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_box(0);
v___x_1082_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1078_, v_k_1080_, v___x_1081_, v_t_1079_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1083_, lean_object* v_00_u03b2_1084_, lean_object* v_cmp_1085_, lean_object* v_t_1086_, lean_object* v_k_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1085_, v_k_1087_, v___x_1088_, v_t_1086_);
return v___x_1089_;
}
}
static lean_object* _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1093_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1094_ = lean_unsigned_to_nat(14u);
v___x_1095_ = lean_unsigned_to_nat(22u);
v___x_1096_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1097_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1098_ = l_mkPanicMessageWithDecl(v___x_1097_, v___x_1096_, v___x_1095_, v___x_1094_, v___x_1093_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1099_, lean_object* v_inst_1100_, lean_object* v_t_1101_, lean_object* v_k_1102_){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_box(0);
v___x_1104_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1099_, v_k_1102_, v___x_1103_, v_t_1101_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1106_ = l_panic___redArg(v_inst_1100_, v___x_1105_);
return v___x_1106_;
}
else
{
lean_object* v_val_1107_; 
lean_dec_ref(v_inst_1100_);
v_val_1107_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_val_1107_);
lean_dec_ref(v___x_1104_);
return v_val_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1108_, lean_object* v_00_u03b2_1109_, lean_object* v_cmp_1110_, lean_object* v_inst_1111_, lean_object* v_t_1112_, lean_object* v_k_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_box(0);
v___x_1115_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1110_, v_k_1113_, v___x_1114_, v_t_1112_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1117_ = l_panic___redArg(v_inst_1111_, v___x_1116_);
return v___x_1117_;
}
else
{
lean_object* v_val_1118_; 
lean_dec_ref(v_inst_1111_);
v_val_1118_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_val_1118_);
lean_dec_ref(v___x_1115_);
return v_val_1118_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1119_, lean_object* v_inst_1120_, lean_object* v_t_1121_, lean_object* v_k_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_box(0);
v___x_1124_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1119_, v_k_1122_, v___x_1123_, v_t_1121_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1126_ = l_panic___redArg(v_inst_1120_, v___x_1125_);
return v___x_1126_;
}
else
{
lean_object* v_val_1127_; 
lean_dec_ref(v_inst_1120_);
v_val_1127_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_val_1127_);
lean_dec_ref(v___x_1124_);
return v_val_1127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1128_, lean_object* v_00_u03b2_1129_, lean_object* v_cmp_1130_, lean_object* v_inst_1131_, lean_object* v_t_1132_, lean_object* v_k_1133_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_box(0);
v___x_1135_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1130_, v_k_1133_, v___x_1134_, v_t_1132_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1137_ = l_panic___redArg(v_inst_1131_, v___x_1136_);
return v___x_1137_;
}
else
{
lean_object* v_val_1138_; 
lean_dec_ref(v_inst_1131_);
v_val_1138_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_val_1138_);
lean_dec_ref(v___x_1135_);
return v_val_1138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1139_, lean_object* v_inst_1140_, lean_object* v_t_1141_, lean_object* v_k_1142_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_box(0);
v___x_1144_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1139_, v_k_1142_, v___x_1143_, v_t_1141_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1146_ = l_panic___redArg(v_inst_1140_, v___x_1145_);
return v___x_1146_;
}
else
{
lean_object* v_val_1147_; 
lean_dec_ref(v_inst_1140_);
v_val_1147_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_val_1147_);
lean_dec_ref(v___x_1144_);
return v_val_1147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1148_, lean_object* v_00_u03b2_1149_, lean_object* v_cmp_1150_, lean_object* v_inst_1151_, lean_object* v_t_1152_, lean_object* v_k_1153_){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_box(0);
v___x_1155_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1150_, v_k_1153_, v___x_1154_, v_t_1152_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1157_ = l_panic___redArg(v_inst_1151_, v___x_1156_);
return v___x_1157_;
}
else
{
lean_object* v_val_1158_; 
lean_dec_ref(v_inst_1151_);
v_val_1158_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_val_1158_);
lean_dec_ref(v___x_1155_);
return v_val_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1159_, lean_object* v_inst_1160_, lean_object* v_t_1161_, lean_object* v_k_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_box(0);
v___x_1164_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1159_, v_k_1162_, v___x_1163_, v_t_1161_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1166_ = l_panic___redArg(v_inst_1160_, v___x_1165_);
return v___x_1166_;
}
else
{
lean_object* v_val_1167_; 
lean_dec_ref(v_inst_1160_);
v_val_1167_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_val_1167_);
lean_dec_ref(v___x_1164_);
return v_val_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1168_, lean_object* v_00_u03b2_1169_, lean_object* v_cmp_1170_, lean_object* v_inst_1171_, lean_object* v_t_1172_, lean_object* v_k_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_box(0);
v___x_1175_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1170_, v_k_1173_, v___x_1174_, v_t_1172_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1177_ = l_panic___redArg(v_inst_1171_, v___x_1176_);
return v___x_1177_;
}
else
{
lean_object* v_val_1178_; 
lean_dec_ref(v_inst_1171_);
v_val_1178_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_val_1178_);
lean_dec_ref(v___x_1175_);
return v_val_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___redArg(lean_object* v_cmp_1179_, lean_object* v_t_1180_, lean_object* v_k_1181_, lean_object* v_fallback_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_box(0);
v___x_1184_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1179_, v_k_1181_, v___x_1183_, v_t_1180_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_inc_ref(v_fallback_1182_);
return v_fallback_1182_;
}
else
{
lean_object* v_val_1185_; 
v_val_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_val_1185_);
lean_dec_ref(v___x_1184_);
return v_val_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1186_, lean_object* v_t_1187_, lean_object* v_k_1188_, lean_object* v_fallback_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Std_DTreeMap_getEntryGED___redArg(v_cmp_1186_, v_t_1187_, v_k_1188_, v_fallback_1189_);
lean_dec_ref(v_fallback_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED(lean_object* v_00_u03b1_1191_, lean_object* v_00_u03b2_1192_, lean_object* v_cmp_1193_, lean_object* v_t_1194_, lean_object* v_k_1195_, lean_object* v_fallback_1196_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_box(0);
v___x_1198_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1193_, v_k_1195_, v___x_1197_, v_t_1194_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_inc_ref(v_fallback_1196_);
return v_fallback_1196_;
}
else
{
lean_object* v_val_1199_; 
v_val_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_val_1199_);
lean_dec_ref(v___x_1198_);
return v_val_1199_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1200_, lean_object* v_00_u03b2_1201_, lean_object* v_cmp_1202_, lean_object* v_t_1203_, lean_object* v_k_1204_, lean_object* v_fallback_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Std_DTreeMap_getEntryGED(v_00_u03b1_1200_, v_00_u03b2_1201_, v_cmp_1202_, v_t_1203_, v_k_1204_, v_fallback_1205_);
lean_dec_ref(v_fallback_1205_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1207_, lean_object* v_t_1208_, lean_object* v_k_1209_, lean_object* v_fallback_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1207_, v_k_1209_, v___x_1211_, v_t_1208_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_inc_ref(v_fallback_1210_);
return v_fallback_1210_;
}
else
{
lean_object* v_val_1213_; 
v_val_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_val_1213_);
lean_dec_ref(v___x_1212_);
return v_val_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1214_, lean_object* v_t_1215_, lean_object* v_k_1216_, lean_object* v_fallback_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Std_DTreeMap_getEntryGTD___redArg(v_cmp_1214_, v_t_1215_, v_k_1216_, v_fallback_1217_);
lean_dec_ref(v_fallback_1217_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD(lean_object* v_00_u03b1_1219_, lean_object* v_00_u03b2_1220_, lean_object* v_cmp_1221_, lean_object* v_t_1222_, lean_object* v_k_1223_, lean_object* v_fallback_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1221_, v_k_1223_, v___x_1225_, v_t_1222_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_inc_ref(v_fallback_1224_);
return v_fallback_1224_;
}
else
{
lean_object* v_val_1227_; 
v_val_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_val_1227_);
lean_dec_ref(v___x_1226_);
return v_val_1227_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_00_u03b2_1229_, lean_object* v_cmp_1230_, lean_object* v_t_1231_, lean_object* v_k_1232_, lean_object* v_fallback_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Std_DTreeMap_getEntryGTD(v_00_u03b1_1228_, v_00_u03b2_1229_, v_cmp_1230_, v_t_1231_, v_k_1232_, v_fallback_1233_);
lean_dec_ref(v_fallback_1233_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___redArg(lean_object* v_cmp_1235_, lean_object* v_t_1236_, lean_object* v_k_1237_, lean_object* v_fallback_1238_){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_box(0);
v___x_1240_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1235_, v_k_1237_, v___x_1239_, v_t_1236_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_inc_ref(v_fallback_1238_);
return v_fallback_1238_;
}
else
{
lean_object* v_val_1241_; 
v_val_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_val_1241_);
lean_dec_ref(v___x_1240_);
return v_val_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1242_, lean_object* v_t_1243_, lean_object* v_k_1244_, lean_object* v_fallback_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Std_DTreeMap_getEntryLED___redArg(v_cmp_1242_, v_t_1243_, v_k_1244_, v_fallback_1245_);
lean_dec_ref(v_fallback_1245_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED(lean_object* v_00_u03b1_1247_, lean_object* v_00_u03b2_1248_, lean_object* v_cmp_1249_, lean_object* v_t_1250_, lean_object* v_k_1251_, lean_object* v_fallback_1252_){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_box(0);
v___x_1254_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1249_, v_k_1251_, v___x_1253_, v_t_1250_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_inc_ref(v_fallback_1252_);
return v_fallback_1252_;
}
else
{
lean_object* v_val_1255_; 
v_val_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_val_1255_);
lean_dec_ref(v___x_1254_);
return v_val_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_00_u03b2_1257_, lean_object* v_cmp_1258_, lean_object* v_t_1259_, lean_object* v_k_1260_, lean_object* v_fallback_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Std_DTreeMap_getEntryLED(v_00_u03b1_1256_, v_00_u03b2_1257_, v_cmp_1258_, v_t_1259_, v_k_1260_, v_fallback_1261_);
lean_dec_ref(v_fallback_1261_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1263_, lean_object* v_t_1264_, lean_object* v_k_1265_, lean_object* v_fallback_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_box(0);
v___x_1268_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1263_, v_k_1265_, v___x_1267_, v_t_1264_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_inc_ref(v_fallback_1266_);
return v_fallback_1266_;
}
else
{
lean_object* v_val_1269_; 
v_val_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_val_1269_);
lean_dec_ref(v___x_1268_);
return v_val_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1270_, lean_object* v_t_1271_, lean_object* v_k_1272_, lean_object* v_fallback_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Std_DTreeMap_getEntryLTD___redArg(v_cmp_1270_, v_t_1271_, v_k_1272_, v_fallback_1273_);
lean_dec_ref(v_fallback_1273_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD(lean_object* v_00_u03b1_1275_, lean_object* v_00_u03b2_1276_, lean_object* v_cmp_1277_, lean_object* v_t_1278_, lean_object* v_k_1279_, lean_object* v_fallback_1280_){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_box(0);
v___x_1282_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1277_, v_k_1279_, v___x_1281_, v_t_1278_);
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
lean_dec_ref(v___x_1282_);
return v_val_1283_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_00_u03b2_1285_, lean_object* v_cmp_1286_, lean_object* v_t_1287_, lean_object* v_k_1288_, lean_object* v_fallback_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Std_DTreeMap_getEntryLTD(v_00_u03b1_1284_, v_00_u03b2_1285_, v_cmp_1286_, v_t_1287_, v_k_1288_, v_fallback_1289_);
lean_dec_ref(v_fallback_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1291_, lean_object* v_t_1292_, lean_object* v_k_1293_){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_box(0);
v___x_1295_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1291_, v_k_1293_, v___x_1294_, v_t_1292_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1296_, lean_object* v_00_u03b2_1297_, lean_object* v_cmp_1298_, lean_object* v_t_1299_, lean_object* v_k_1300_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_box(0);
v___x_1302_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1298_, v_k_1300_, v___x_1301_, v_t_1299_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1303_, lean_object* v_t_1304_, lean_object* v_k_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1303_, v_k_1305_, v___x_1306_, v_t_1304_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1308_, lean_object* v_00_u03b2_1309_, lean_object* v_cmp_1310_, lean_object* v_t_1311_, lean_object* v_k_1312_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_box(0);
v___x_1314_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1310_, v_k_1312_, v___x_1313_, v_t_1311_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1315_, lean_object* v_t_1316_, lean_object* v_k_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_box(0);
v___x_1319_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1315_, v_k_1317_, v___x_1318_, v_t_1316_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1320_, lean_object* v_00_u03b2_1321_, lean_object* v_cmp_1322_, lean_object* v_t_1323_, lean_object* v_k_1324_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_box(0);
v___x_1326_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1322_, v_k_1324_, v___x_1325_, v_t_1323_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1327_, lean_object* v_t_1328_, lean_object* v_k_1329_){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_box(0);
v___x_1331_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1327_, v_k_1329_, v___x_1330_, v_t_1328_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1332_, lean_object* v_00_u03b2_1333_, lean_object* v_cmp_1334_, lean_object* v_t_1335_, lean_object* v_k_1336_){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_box(0);
v___x_1338_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1334_, v_k_1336_, v___x_1337_, v_t_1335_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1339_, lean_object* v_inst_1340_, lean_object* v_t_1341_, lean_object* v_k_1342_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_box(0);
v___x_1344_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1339_, v_k_1342_, v___x_1343_, v_t_1341_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1346_ = l_panic___redArg(v_inst_1340_, v___x_1345_);
return v___x_1346_;
}
else
{
lean_object* v_val_1347_; 
lean_dec(v_inst_1340_);
v_val_1347_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_val_1347_);
lean_dec_ref(v___x_1344_);
return v_val_1347_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1348_, lean_object* v_00_u03b2_1349_, lean_object* v_cmp_1350_, lean_object* v_inst_1351_, lean_object* v_t_1352_, lean_object* v_k_1353_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1350_, v_k_1353_, v___x_1354_, v_t_1352_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1357_ = l_panic___redArg(v_inst_1351_, v___x_1356_);
return v___x_1357_;
}
else
{
lean_object* v_val_1358_; 
lean_dec(v_inst_1351_);
v_val_1358_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_val_1358_);
lean_dec_ref(v___x_1355_);
return v_val_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1359_, lean_object* v_inst_1360_, lean_object* v_t_1361_, lean_object* v_k_1362_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_box(0);
v___x_1364_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1359_, v_k_1362_, v___x_1363_, v_t_1361_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1366_ = l_panic___redArg(v_inst_1360_, v___x_1365_);
return v___x_1366_;
}
else
{
lean_object* v_val_1367_; 
lean_dec(v_inst_1360_);
v_val_1367_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_val_1367_);
lean_dec_ref(v___x_1364_);
return v_val_1367_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1368_, lean_object* v_00_u03b2_1369_, lean_object* v_cmp_1370_, lean_object* v_inst_1371_, lean_object* v_t_1372_, lean_object* v_k_1373_){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1370_, v_k_1373_, v___x_1374_, v_t_1372_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1377_ = l_panic___redArg(v_inst_1371_, v___x_1376_);
return v___x_1377_;
}
else
{
lean_object* v_val_1378_; 
lean_dec(v_inst_1371_);
v_val_1378_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_val_1378_);
lean_dec_ref(v___x_1375_);
return v_val_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1379_, lean_object* v_inst_1380_, lean_object* v_t_1381_, lean_object* v_k_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1379_, v_k_1382_, v___x_1383_, v_t_1381_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1386_ = l_panic___redArg(v_inst_1380_, v___x_1385_);
return v___x_1386_;
}
else
{
lean_object* v_val_1387_; 
lean_dec(v_inst_1380_);
v_val_1387_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_val_1387_);
lean_dec_ref(v___x_1384_);
return v_val_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1388_, lean_object* v_00_u03b2_1389_, lean_object* v_cmp_1390_, lean_object* v_inst_1391_, lean_object* v_t_1392_, lean_object* v_k_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1390_, v_k_1393_, v___x_1394_, v_t_1392_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1397_ = l_panic___redArg(v_inst_1391_, v___x_1396_);
return v___x_1397_;
}
else
{
lean_object* v_val_1398_; 
lean_dec(v_inst_1391_);
v_val_1398_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_val_1398_);
lean_dec_ref(v___x_1395_);
return v_val_1398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1399_, lean_object* v_inst_1400_, lean_object* v_t_1401_, lean_object* v_k_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_box(0);
v___x_1404_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1399_, v_k_1402_, v___x_1403_, v_t_1401_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1406_ = l_panic___redArg(v_inst_1400_, v___x_1405_);
return v___x_1406_;
}
else
{
lean_object* v_val_1407_; 
lean_dec(v_inst_1400_);
v_val_1407_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_val_1407_);
lean_dec_ref(v___x_1404_);
return v_val_1407_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1408_, lean_object* v_00_u03b2_1409_, lean_object* v_cmp_1410_, lean_object* v_inst_1411_, lean_object* v_t_1412_, lean_object* v_k_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1410_, v_k_1413_, v___x_1414_, v_t_1412_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1417_ = l_panic___redArg(v_inst_1411_, v___x_1416_);
return v___x_1417_;
}
else
{
lean_object* v_val_1418_; 
lean_dec(v_inst_1411_);
v_val_1418_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_val_1418_);
lean_dec_ref(v___x_1415_);
return v_val_1418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___redArg(lean_object* v_cmp_1419_, lean_object* v_t_1420_, lean_object* v_k_1421_, lean_object* v_fallback_1422_){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_box(0);
v___x_1424_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1419_, v_k_1421_, v___x_1423_, v_t_1420_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_inc(v_fallback_1422_);
return v_fallback_1422_;
}
else
{
lean_object* v_val_1425_; 
v_val_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_val_1425_);
lean_dec_ref(v___x_1424_);
return v_val_1425_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1426_, lean_object* v_t_1427_, lean_object* v_k_1428_, lean_object* v_fallback_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Std_DTreeMap_getKeyGED___redArg(v_cmp_1426_, v_t_1427_, v_k_1428_, v_fallback_1429_);
lean_dec(v_fallback_1429_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED(lean_object* v_00_u03b1_1431_, lean_object* v_00_u03b2_1432_, lean_object* v_cmp_1433_, lean_object* v_t_1434_, lean_object* v_k_1435_, lean_object* v_fallback_1436_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_box(0);
v___x_1438_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1433_, v_k_1435_, v___x_1437_, v_t_1434_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_inc(v_fallback_1436_);
return v_fallback_1436_;
}
else
{
lean_object* v_val_1439_; 
v_val_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_val_1439_);
lean_dec_ref(v___x_1438_);
return v_val_1439_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1440_, lean_object* v_00_u03b2_1441_, lean_object* v_cmp_1442_, lean_object* v_t_1443_, lean_object* v_k_1444_, lean_object* v_fallback_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Std_DTreeMap_getKeyGED(v_00_u03b1_1440_, v_00_u03b2_1441_, v_cmp_1442_, v_t_1443_, v_k_1444_, v_fallback_1445_);
lean_dec(v_fallback_1445_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1447_, lean_object* v_t_1448_, lean_object* v_k_1449_, lean_object* v_fallback_1450_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_box(0);
v___x_1452_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1447_, v_k_1449_, v___x_1451_, v_t_1448_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_inc(v_fallback_1450_);
return v_fallback_1450_;
}
else
{
lean_object* v_val_1453_; 
v_val_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_val_1453_);
lean_dec_ref(v___x_1452_);
return v_val_1453_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1454_, lean_object* v_t_1455_, lean_object* v_k_1456_, lean_object* v_fallback_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Std_DTreeMap_getKeyGTD___redArg(v_cmp_1454_, v_t_1455_, v_k_1456_, v_fallback_1457_);
lean_dec(v_fallback_1457_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD(lean_object* v_00_u03b1_1459_, lean_object* v_00_u03b2_1460_, lean_object* v_cmp_1461_, lean_object* v_t_1462_, lean_object* v_k_1463_, lean_object* v_fallback_1464_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_box(0);
v___x_1466_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1461_, v_k_1463_, v___x_1465_, v_t_1462_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_inc(v_fallback_1464_);
return v_fallback_1464_;
}
else
{
lean_object* v_val_1467_; 
v_val_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_val_1467_);
lean_dec_ref(v___x_1466_);
return v_val_1467_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1468_, lean_object* v_00_u03b2_1469_, lean_object* v_cmp_1470_, lean_object* v_t_1471_, lean_object* v_k_1472_, lean_object* v_fallback_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Std_DTreeMap_getKeyGTD(v_00_u03b1_1468_, v_00_u03b2_1469_, v_cmp_1470_, v_t_1471_, v_k_1472_, v_fallback_1473_);
lean_dec(v_fallback_1473_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___redArg(lean_object* v_cmp_1475_, lean_object* v_t_1476_, lean_object* v_k_1477_, lean_object* v_fallback_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_box(0);
v___x_1480_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1475_, v_k_1477_, v___x_1479_, v_t_1476_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_inc(v_fallback_1478_);
return v_fallback_1478_;
}
else
{
lean_object* v_val_1481_; 
v_val_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_val_1481_);
lean_dec_ref(v___x_1480_);
return v_val_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1482_, lean_object* v_t_1483_, lean_object* v_k_1484_, lean_object* v_fallback_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Std_DTreeMap_getKeyLED___redArg(v_cmp_1482_, v_t_1483_, v_k_1484_, v_fallback_1485_);
lean_dec(v_fallback_1485_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED(lean_object* v_00_u03b1_1487_, lean_object* v_00_u03b2_1488_, lean_object* v_cmp_1489_, lean_object* v_t_1490_, lean_object* v_k_1491_, lean_object* v_fallback_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1489_, v_k_1491_, v___x_1493_, v_t_1490_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_inc(v_fallback_1492_);
return v_fallback_1492_;
}
else
{
lean_object* v_val_1495_; 
v_val_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_val_1495_);
lean_dec_ref(v___x_1494_);
return v_val_1495_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1496_, lean_object* v_00_u03b2_1497_, lean_object* v_cmp_1498_, lean_object* v_t_1499_, lean_object* v_k_1500_, lean_object* v_fallback_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Std_DTreeMap_getKeyLED(v_00_u03b1_1496_, v_00_u03b2_1497_, v_cmp_1498_, v_t_1499_, v_k_1500_, v_fallback_1501_);
lean_dec(v_fallback_1501_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1503_, lean_object* v_t_1504_, lean_object* v_k_1505_, lean_object* v_fallback_1506_){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_box(0);
v___x_1508_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1503_, v_k_1505_, v___x_1507_, v_t_1504_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_inc(v_fallback_1506_);
return v_fallback_1506_;
}
else
{
lean_object* v_val_1509_; 
v_val_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_val_1509_);
lean_dec_ref(v___x_1508_);
return v_val_1509_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1510_, lean_object* v_t_1511_, lean_object* v_k_1512_, lean_object* v_fallback_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Std_DTreeMap_getKeyLTD___redArg(v_cmp_1510_, v_t_1511_, v_k_1512_, v_fallback_1513_);
lean_dec(v_fallback_1513_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD(lean_object* v_00_u03b1_1515_, lean_object* v_00_u03b2_1516_, lean_object* v_cmp_1517_, lean_object* v_t_1518_, lean_object* v_k_1519_, lean_object* v_fallback_1520_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_box(0);
v___x_1522_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1517_, v_k_1519_, v___x_1521_, v_t_1518_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_inc(v_fallback_1520_);
return v_fallback_1520_;
}
else
{
lean_object* v_val_1523_; 
v_val_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_val_1523_);
lean_dec_ref(v___x_1522_);
return v_val_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1524_, lean_object* v_00_u03b2_1525_, lean_object* v_cmp_1526_, lean_object* v_t_1527_, lean_object* v_k_1528_, lean_object* v_fallback_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Std_DTreeMap_getKeyLTD(v_00_u03b1_1524_, v_00_u03b2_1525_, v_cmp_1526_, v_t_1527_, v_k_1528_, v_fallback_1529_);
lean_dec(v_fallback_1529_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1531_, lean_object* v_t_1532_, lean_object* v_a_1533_, lean_object* v_b_1534_){
_start:
{
lean_object* v___x_1535_; 
lean_inc(v_a_1533_);
lean_inc(v_t_1532_);
lean_inc_ref(v_cmp_1531_);
v___x_1535_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1531_, v_t_1532_, v_a_1533_);
if (lean_obj_tag(v___x_1535_) == 0)
{
uint8_t v___x_1536_; 
lean_inc(v_t_1532_);
lean_inc(v_a_1533_);
lean_inc_ref(v_cmp_1531_);
v___x_1536_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1531_, v_a_1533_, v_t_1532_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1531_, v_a_1533_, v_b_1534_, v_t_1532_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1535_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; 
lean_dec(v_b_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_cmp_1531_);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1535_);
lean_ctor_set(v___x_1539_, 1, v_t_1532_);
return v___x_1539_;
}
}
else
{
lean_object* v___x_1540_; 
lean_dec(v_b_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_cmp_1531_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1535_);
lean_ctor_set(v___x_1540_, 1, v_t_1532_);
return v___x_1540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1541_, lean_object* v_cmp_1542_, lean_object* v_00_u03b2_1543_, lean_object* v_t_1544_, lean_object* v_a_1545_, lean_object* v_b_1546_){
_start:
{
lean_object* v___x_1547_; 
lean_inc(v_a_1545_);
lean_inc(v_t_1544_);
lean_inc_ref(v_cmp_1542_);
v___x_1547_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1542_, v_t_1544_, v_a_1545_);
if (lean_obj_tag(v___x_1547_) == 0)
{
uint8_t v___x_1548_; 
lean_inc(v_t_1544_);
lean_inc(v_a_1545_);
lean_inc_ref(v_cmp_1542_);
v___x_1548_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1542_, v_a_1545_, v_t_1544_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1542_, v_a_1545_, v_b_1546_, v_t_1544_);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1547_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; 
lean_dec(v_b_1546_);
lean_dec(v_a_1545_);
lean_dec_ref(v_cmp_1542_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1547_);
lean_ctor_set(v___x_1551_, 1, v_t_1544_);
return v___x_1551_;
}
}
else
{
lean_object* v___x_1552_; 
lean_dec(v_b_1546_);
lean_dec(v_a_1545_);
lean_dec_ref(v_cmp_1542_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1547_);
lean_ctor_set(v___x_1552_, 1, v_t_1544_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x3f___redArg(lean_object* v_cmp_1553_, lean_object* v_t_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1553_, v_t_1554_, v_a_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x3f(lean_object* v_00_u03b1_1557_, lean_object* v_cmp_1558_, lean_object* v_00_u03b2_1559_, lean_object* v_t_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1558_, v_t_1560_, v_a_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get___redArg(lean_object* v_cmp_1563_, lean_object* v_t_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1563_, v_t_1564_, v_a_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get(lean_object* v_00_u03b1_1567_, lean_object* v_cmp_1568_, lean_object* v_00_u03b2_1569_, lean_object* v_t_1570_, lean_object* v_a_1571_, lean_object* v_h_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1568_, v_t_1570_, v_a_1571_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___redArg(lean_object* v_cmp_1574_, lean_object* v_inst_1575_, lean_object* v_t_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1574_, v_inst_1575_, v_t_1576_, v_a_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21(lean_object* v_00_u03b1_1579_, lean_object* v_cmp_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_inst_1582_, lean_object* v_t_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1580_, v_inst_1582_, v_t_1583_, v_a_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___redArg(lean_object* v_cmp_1586_, lean_object* v_t_1587_, lean_object* v_a_1588_, lean_object* v_fallback_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1586_, v_t_1587_, v_a_1588_, v_fallback_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___redArg___boxed(lean_object* v_cmp_1591_, lean_object* v_t_1592_, lean_object* v_a_1593_, lean_object* v_fallback_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Std_DTreeMap_Const_getD___redArg(v_cmp_1591_, v_t_1592_, v_a_1593_, v_fallback_1594_);
lean_dec(v_fallback_1594_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD(lean_object* v_00_u03b1_1596_, lean_object* v_cmp_1597_, lean_object* v_00_u03b2_1598_, lean_object* v_t_1599_, lean_object* v_a_1600_, lean_object* v_fallback_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1597_, v_t_1599_, v_a_1600_, v_fallback_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___boxed(lean_object* v_00_u03b1_1603_, lean_object* v_cmp_1604_, lean_object* v_00_u03b2_1605_, lean_object* v_t_1606_, lean_object* v_a_1607_, lean_object* v_fallback_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Std_DTreeMap_Const_getD(v_00_u03b1_1603_, v_cmp_1604_, v_00_u03b2_1605_, v_t_1606_, v_a_1607_, v_fallback_1608_);
lean_dec(v_fallback_1608_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___redArg(lean_object* v_t_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Std_DTreeMap_Const_minEntry_x3f___redArg(v_t_1612_);
lean_dec(v_t_1612_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f(lean_object* v_00_u03b1_1614_, lean_object* v_cmp_1615_, lean_object* v_00_u03b2_1616_, lean_object* v_t_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1619_, lean_object* v_cmp_1620_, lean_object* v_00_u03b2_1621_, lean_object* v_t_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Std_DTreeMap_Const_minEntry_x3f(v_00_u03b1_1619_, v_cmp_1620_, v_00_u03b2_1621_, v_t_1622_);
lean_dec(v_t_1622_);
lean_dec_ref(v_cmp_1620_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___redArg(lean_object* v_t_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___redArg___boxed(lean_object* v_t_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Std_DTreeMap_Const_minEntry___redArg(v_t_1626_);
lean_dec(v_t_1626_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry(lean_object* v_00_u03b1_1628_, lean_object* v_cmp_1629_, lean_object* v_00_u03b2_1630_, lean_object* v_t_1631_, lean_object* v_h_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___boxed(lean_object* v_00_u03b1_1634_, lean_object* v_cmp_1635_, lean_object* v_00_u03b2_1636_, lean_object* v_t_1637_, lean_object* v_h_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Std_DTreeMap_Const_minEntry(v_00_u03b1_1634_, v_cmp_1635_, v_00_u03b2_1636_, v_t_1637_, v_h_1638_);
lean_dec(v_t_1637_);
lean_dec_ref(v_cmp_1635_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___redArg(lean_object* v_inst_1640_, lean_object* v_t_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1640_, v_t_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1643_, lean_object* v_t_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Std_DTreeMap_Const_minEntry_x21___redArg(v_inst_1643_, v_t_1644_);
lean_dec(v_t_1644_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21(lean_object* v_00_u03b1_1646_, lean_object* v_cmp_1647_, lean_object* v_00_u03b2_1648_, lean_object* v_inst_1649_, lean_object* v_t_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1649_, v_t_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1652_, lean_object* v_cmp_1653_, lean_object* v_00_u03b2_1654_, lean_object* v_inst_1655_, lean_object* v_t_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Std_DTreeMap_Const_minEntry_x21(v_00_u03b1_1652_, v_cmp_1653_, v_00_u03b2_1654_, v_inst_1655_, v_t_1656_);
lean_dec(v_t_1656_);
lean_dec_ref(v_cmp_1653_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___redArg(lean_object* v_t_1658_, lean_object* v_fallback_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1658_, v_fallback_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___redArg___boxed(lean_object* v_t_1661_, lean_object* v_fallback_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Std_DTreeMap_Const_minEntryD___redArg(v_t_1661_, v_fallback_1662_);
lean_dec_ref(v_fallback_1662_);
lean_dec(v_t_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD(lean_object* v_00_u03b1_1664_, lean_object* v_cmp_1665_, lean_object* v_00_u03b2_1666_, lean_object* v_t_1667_, lean_object* v_fallback_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1667_, v_fallback_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___boxed(lean_object* v_00_u03b1_1670_, lean_object* v_cmp_1671_, lean_object* v_00_u03b2_1672_, lean_object* v_t_1673_, lean_object* v_fallback_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Std_DTreeMap_Const_minEntryD(v_00_u03b1_1670_, v_cmp_1671_, v_00_u03b2_1672_, v_t_1673_, v_fallback_1674_);
lean_dec_ref(v_fallback_1674_);
lean_dec(v_t_1673_);
lean_dec_ref(v_cmp_1671_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___redArg(lean_object* v_t_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Std_DTreeMap_Const_maxEntry_x3f___redArg(v_t_1678_);
lean_dec(v_t_1678_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f(lean_object* v_00_u03b1_1680_, lean_object* v_cmp_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_t_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1685_, lean_object* v_cmp_1686_, lean_object* v_00_u03b2_1687_, lean_object* v_t_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Std_DTreeMap_Const_maxEntry_x3f(v_00_u03b1_1685_, v_cmp_1686_, v_00_u03b2_1687_, v_t_1688_);
lean_dec(v_t_1688_);
lean_dec_ref(v_cmp_1686_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___redArg(lean_object* v_t_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___redArg___boxed(lean_object* v_t_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Std_DTreeMap_Const_maxEntry___redArg(v_t_1692_);
lean_dec(v_t_1692_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry(lean_object* v_00_u03b1_1694_, lean_object* v_cmp_1695_, lean_object* v_00_u03b2_1696_, lean_object* v_t_1697_, lean_object* v_h_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1697_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_cmp_1701_, lean_object* v_00_u03b2_1702_, lean_object* v_t_1703_, lean_object* v_h_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Std_DTreeMap_Const_maxEntry(v_00_u03b1_1700_, v_cmp_1701_, v_00_u03b2_1702_, v_t_1703_, v_h_1704_);
lean_dec(v_t_1703_);
lean_dec_ref(v_cmp_1701_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___redArg(lean_object* v_inst_1706_, lean_object* v_t_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1706_, v_t_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_1709_, lean_object* v_t_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Std_DTreeMap_Const_maxEntry_x21___redArg(v_inst_1709_, v_t_1710_);
lean_dec(v_t_1710_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21(lean_object* v_00_u03b1_1712_, lean_object* v_cmp_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_inst_1715_, lean_object* v_t_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1715_, v_t_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_1718_, lean_object* v_cmp_1719_, lean_object* v_00_u03b2_1720_, lean_object* v_inst_1721_, lean_object* v_t_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Std_DTreeMap_Const_maxEntry_x21(v_00_u03b1_1718_, v_cmp_1719_, v_00_u03b2_1720_, v_inst_1721_, v_t_1722_);
lean_dec(v_t_1722_);
lean_dec_ref(v_cmp_1719_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___redArg(lean_object* v_t_1724_, lean_object* v_fallback_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1724_, v_fallback_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___redArg___boxed(lean_object* v_t_1727_, lean_object* v_fallback_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Std_DTreeMap_Const_maxEntryD___redArg(v_t_1727_, v_fallback_1728_);
lean_dec_ref(v_fallback_1728_);
lean_dec(v_t_1727_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD(lean_object* v_00_u03b1_1730_, lean_object* v_cmp_1731_, lean_object* v_00_u03b2_1732_, lean_object* v_t_1733_, lean_object* v_fallback_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1733_, v_fallback_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___boxed(lean_object* v_00_u03b1_1736_, lean_object* v_cmp_1737_, lean_object* v_00_u03b2_1738_, lean_object* v_t_1739_, lean_object* v_fallback_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Std_DTreeMap_Const_maxEntryD(v_00_u03b1_1736_, v_cmp_1737_, v_00_u03b2_1738_, v_t_1739_, v_fallback_1740_);
lean_dec_ref(v_fallback_1740_);
lean_dec(v_t_1739_);
lean_dec_ref(v_cmp_1737_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(lean_object* v_t_1742_, lean_object* v_n_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1742_, v_n_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_1745_, lean_object* v_n_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(v_t_1745_, v_n_1746_);
lean_dec(v_t_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_1748_, lean_object* v_cmp_1749_, lean_object* v_00_u03b2_1750_, lean_object* v_t_1751_, lean_object* v_n_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1751_, v_n_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1754_, lean_object* v_cmp_1755_, lean_object* v_00_u03b2_1756_, lean_object* v_t_1757_, lean_object* v_n_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Std_DTreeMap_Const_entryAtIdx_x3f(v_00_u03b1_1754_, v_cmp_1755_, v_00_u03b2_1756_, v_t_1757_, v_n_1758_);
lean_dec(v_t_1757_);
lean_dec_ref(v_cmp_1755_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___redArg(lean_object* v_t_1760_, lean_object* v_n_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_1760_, v_n_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___redArg___boxed(lean_object* v_t_1763_, lean_object* v_n_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Std_DTreeMap_Const_entryAtIdx___redArg(v_t_1763_, v_n_1764_);
lean_dec(v_t_1763_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx(lean_object* v_00_u03b1_1766_, lean_object* v_cmp_1767_, lean_object* v_00_u03b2_1768_, lean_object* v_t_1769_, lean_object* v_n_1770_, lean_object* v_h_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_1769_, v_n_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_1773_, lean_object* v_cmp_1774_, lean_object* v_00_u03b2_1775_, lean_object* v_t_1776_, lean_object* v_n_1777_, lean_object* v_h_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Std_DTreeMap_Const_entryAtIdx(v_00_u03b1_1773_, v_cmp_1774_, v_00_u03b2_1775_, v_t_1776_, v_n_1777_, v_h_1778_);
lean_dec(v_t_1776_);
lean_dec_ref(v_cmp_1774_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(lean_object* v_inst_1780_, lean_object* v_t_1781_, lean_object* v_n_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1780_, v_t_1781_, v_n_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_1784_, lean_object* v_t_1785_, lean_object* v_n_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(v_inst_1784_, v_t_1785_, v_n_1786_);
lean_dec(v_t_1785_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21(lean_object* v_00_u03b1_1788_, lean_object* v_cmp_1789_, lean_object* v_00_u03b2_1790_, lean_object* v_inst_1791_, lean_object* v_t_1792_, lean_object* v_n_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1791_, v_t_1792_, v_n_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_1795_, lean_object* v_cmp_1796_, lean_object* v_00_u03b2_1797_, lean_object* v_inst_1798_, lean_object* v_t_1799_, lean_object* v_n_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Std_DTreeMap_Const_entryAtIdx_x21(v_00_u03b1_1795_, v_cmp_1796_, v_00_u03b2_1797_, v_inst_1798_, v_t_1799_, v_n_1800_);
lean_dec(v_t_1799_);
lean_dec_ref(v_cmp_1796_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___redArg(lean_object* v_t_1802_, lean_object* v_n_1803_, lean_object* v_fallback_1804_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1802_, v_n_1803_, v_fallback_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_1806_, lean_object* v_n_1807_, lean_object* v_fallback_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Std_DTreeMap_Const_entryAtIdxD___redArg(v_t_1806_, v_n_1807_, v_fallback_1808_);
lean_dec_ref(v_fallback_1808_);
lean_dec(v_t_1806_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD(lean_object* v_00_u03b1_1810_, lean_object* v_cmp_1811_, lean_object* v_00_u03b2_1812_, lean_object* v_t_1813_, lean_object* v_n_1814_, lean_object* v_fallback_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1813_, v_n_1814_, v_fallback_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_1817_, lean_object* v_cmp_1818_, lean_object* v_00_u03b2_1819_, lean_object* v_t_1820_, lean_object* v_n_1821_, lean_object* v_fallback_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Std_DTreeMap_Const_entryAtIdxD(v_00_u03b1_1817_, v_cmp_1818_, v_00_u03b2_1819_, v_t_1820_, v_n_1821_, v_fallback_1822_);
lean_dec_ref(v_fallback_1822_);
lean_dec(v_t_1820_);
lean_dec_ref(v_cmp_1818_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_1824_, lean_object* v_t_1825_, lean_object* v_k_1826_){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_box(0);
v___x_1828_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1824_, v_k_1826_, v___x_1827_, v_t_1825_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x3f(lean_object* v_00_u03b1_1829_, lean_object* v_cmp_1830_, lean_object* v_00_u03b2_1831_, lean_object* v_t_1832_, lean_object* v_k_1833_){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_box(0);
v___x_1835_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1830_, v_k_1833_, v___x_1834_, v_t_1832_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_1836_, lean_object* v_t_1837_, lean_object* v_k_1838_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_box(0);
v___x_1840_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1836_, v_k_1838_, v___x_1839_, v_t_1837_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x3f(lean_object* v_00_u03b1_1841_, lean_object* v_cmp_1842_, lean_object* v_00_u03b2_1843_, lean_object* v_t_1844_, lean_object* v_k_1845_){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_box(0);
v___x_1847_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1842_, v_k_1845_, v___x_1846_, v_t_1844_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_1848_, lean_object* v_t_1849_, lean_object* v_k_1850_){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_box(0);
v___x_1852_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1848_, v_k_1850_, v___x_1851_, v_t_1849_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x3f(lean_object* v_00_u03b1_1853_, lean_object* v_cmp_1854_, lean_object* v_00_u03b2_1855_, lean_object* v_t_1856_, lean_object* v_k_1857_){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = lean_box(0);
v___x_1859_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1854_, v_k_1857_, v___x_1858_, v_t_1856_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_1860_, lean_object* v_t_1861_, lean_object* v_k_1862_){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_box(0);
v___x_1864_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1860_, v_k_1862_, v___x_1863_, v_t_1861_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x3f(lean_object* v_00_u03b1_1865_, lean_object* v_cmp_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_t_1868_, lean_object* v_k_1869_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_box(0);
v___x_1871_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1866_, v_k_1869_, v___x_1870_, v_t_1868_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___redArg(lean_object* v_cmp_1872_, lean_object* v_inst_1873_, lean_object* v_t_1874_, lean_object* v_k_1875_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_box(0);
v___x_1877_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1872_, v_k_1875_, v___x_1876_, v_t_1874_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1879_ = l_panic___redArg(v_inst_1873_, v___x_1878_);
return v___x_1879_;
}
else
{
lean_object* v_val_1880_; 
lean_dec_ref(v_inst_1873_);
v_val_1880_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_val_1880_);
lean_dec_ref(v___x_1877_);
return v_val_1880_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21(lean_object* v_00_u03b1_1881_, lean_object* v_cmp_1882_, lean_object* v_00_u03b2_1883_, lean_object* v_inst_1884_, lean_object* v_t_1885_, lean_object* v_k_1886_){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_box(0);
v___x_1888_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1882_, v_k_1886_, v___x_1887_, v_t_1885_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1890_ = l_panic___redArg(v_inst_1884_, v___x_1889_);
return v___x_1890_;
}
else
{
lean_object* v_val_1891_; 
lean_dec_ref(v_inst_1884_);
v_val_1891_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_val_1891_);
lean_dec_ref(v___x_1888_);
return v_val_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___redArg(lean_object* v_cmp_1892_, lean_object* v_inst_1893_, lean_object* v_t_1894_, lean_object* v_k_1895_){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_box(0);
v___x_1897_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1892_, v_k_1895_, v___x_1896_, v_t_1894_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1899_ = l_panic___redArg(v_inst_1893_, v___x_1898_);
return v___x_1899_;
}
else
{
lean_object* v_val_1900_; 
lean_dec_ref(v_inst_1893_);
v_val_1900_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_val_1900_);
lean_dec_ref(v___x_1897_);
return v_val_1900_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21(lean_object* v_00_u03b1_1901_, lean_object* v_cmp_1902_, lean_object* v_00_u03b2_1903_, lean_object* v_inst_1904_, lean_object* v_t_1905_, lean_object* v_k_1906_){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_box(0);
v___x_1908_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1902_, v_k_1906_, v___x_1907_, v_t_1905_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1910_ = l_panic___redArg(v_inst_1904_, v___x_1909_);
return v___x_1910_;
}
else
{
lean_object* v_val_1911_; 
lean_dec_ref(v_inst_1904_);
v_val_1911_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_val_1911_);
lean_dec_ref(v___x_1908_);
return v_val_1911_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___redArg(lean_object* v_cmp_1912_, lean_object* v_inst_1913_, lean_object* v_t_1914_, lean_object* v_k_1915_){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_box(0);
v___x_1917_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1912_, v_k_1915_, v___x_1916_, v_t_1914_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1919_ = l_panic___redArg(v_inst_1913_, v___x_1918_);
return v___x_1919_;
}
else
{
lean_object* v_val_1920_; 
lean_dec_ref(v_inst_1913_);
v_val_1920_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_val_1920_);
lean_dec_ref(v___x_1917_);
return v_val_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21(lean_object* v_00_u03b1_1921_, lean_object* v_cmp_1922_, lean_object* v_00_u03b2_1923_, lean_object* v_inst_1924_, lean_object* v_t_1925_, lean_object* v_k_1926_){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_box(0);
v___x_1928_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1922_, v_k_1926_, v___x_1927_, v_t_1925_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1930_ = l_panic___redArg(v_inst_1924_, v___x_1929_);
return v___x_1930_;
}
else
{
lean_object* v_val_1931_; 
lean_dec_ref(v_inst_1924_);
v_val_1931_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_val_1931_);
lean_dec_ref(v___x_1928_);
return v_val_1931_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___redArg(lean_object* v_cmp_1932_, lean_object* v_inst_1933_, lean_object* v_t_1934_, lean_object* v_k_1935_){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_box(0);
v___x_1937_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1932_, v_k_1935_, v___x_1936_, v_t_1934_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1939_ = l_panic___redArg(v_inst_1933_, v___x_1938_);
return v___x_1939_;
}
else
{
lean_object* v_val_1940_; 
lean_dec_ref(v_inst_1933_);
v_val_1940_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_val_1940_);
lean_dec_ref(v___x_1937_);
return v_val_1940_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21(lean_object* v_00_u03b1_1941_, lean_object* v_cmp_1942_, lean_object* v_00_u03b2_1943_, lean_object* v_inst_1944_, lean_object* v_t_1945_, lean_object* v_k_1946_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_box(0);
v___x_1948_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1942_, v_k_1946_, v___x_1947_, v_t_1945_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1950_ = l_panic___redArg(v_inst_1944_, v___x_1949_);
return v___x_1950_;
}
else
{
lean_object* v_val_1951_; 
lean_dec_ref(v_inst_1944_);
v_val_1951_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_val_1951_);
lean_dec_ref(v___x_1948_);
return v_val_1951_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___redArg(lean_object* v_cmp_1952_, lean_object* v_t_1953_, lean_object* v_k_1954_, lean_object* v_fallback_1955_){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = lean_box(0);
v___x_1957_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1952_, v_k_1954_, v___x_1956_, v_t_1953_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_inc_ref(v_fallback_1955_);
return v_fallback_1955_;
}
else
{
lean_object* v_val_1958_; 
v_val_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_val_1958_);
lean_dec_ref(v___x_1957_);
return v_val_1958_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_1959_, lean_object* v_t_1960_, lean_object* v_k_1961_, lean_object* v_fallback_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Std_DTreeMap_Const_getEntryGED___redArg(v_cmp_1959_, v_t_1960_, v_k_1961_, v_fallback_1962_);
lean_dec_ref(v_fallback_1962_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED(lean_object* v_00_u03b1_1964_, lean_object* v_cmp_1965_, lean_object* v_00_u03b2_1966_, lean_object* v_t_1967_, lean_object* v_k_1968_, lean_object* v_fallback_1969_){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_box(0);
v___x_1971_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1965_, v_k_1968_, v___x_1970_, v_t_1967_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_inc_ref(v_fallback_1969_);
return v_fallback_1969_;
}
else
{
lean_object* v_val_1972_; 
v_val_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_val_1972_);
lean_dec_ref(v___x_1971_);
return v_val_1972_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___boxed(lean_object* v_00_u03b1_1973_, lean_object* v_cmp_1974_, lean_object* v_00_u03b2_1975_, lean_object* v_t_1976_, lean_object* v_k_1977_, lean_object* v_fallback_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Std_DTreeMap_Const_getEntryGED(v_00_u03b1_1973_, v_cmp_1974_, v_00_u03b2_1975_, v_t_1976_, v_k_1977_, v_fallback_1978_);
lean_dec_ref(v_fallback_1978_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___redArg(lean_object* v_cmp_1980_, lean_object* v_t_1981_, lean_object* v_k_1982_, lean_object* v_fallback_1983_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_box(0);
v___x_1985_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1980_, v_k_1982_, v___x_1984_, v_t_1981_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_inc_ref(v_fallback_1983_);
return v_fallback_1983_;
}
else
{
lean_object* v_val_1986_; 
v_val_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_val_1986_);
lean_dec_ref(v___x_1985_);
return v_val_1986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_1987_, lean_object* v_t_1988_, lean_object* v_k_1989_, lean_object* v_fallback_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Std_DTreeMap_Const_getEntryGTD___redArg(v_cmp_1987_, v_t_1988_, v_k_1989_, v_fallback_1990_);
lean_dec_ref(v_fallback_1990_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD(lean_object* v_00_u03b1_1992_, lean_object* v_cmp_1993_, lean_object* v_00_u03b2_1994_, lean_object* v_t_1995_, lean_object* v_k_1996_, lean_object* v_fallback_1997_){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_box(0);
v___x_1999_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1993_, v_k_1996_, v___x_1998_, v_t_1995_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_inc_ref(v_fallback_1997_);
return v_fallback_1997_;
}
else
{
lean_object* v_val_2000_; 
v_val_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_val_2000_);
lean_dec_ref(v___x_1999_);
return v_val_2000_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2001_, lean_object* v_cmp_2002_, lean_object* v_00_u03b2_2003_, lean_object* v_t_2004_, lean_object* v_k_2005_, lean_object* v_fallback_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Std_DTreeMap_Const_getEntryGTD(v_00_u03b1_2001_, v_cmp_2002_, v_00_u03b2_2003_, v_t_2004_, v_k_2005_, v_fallback_2006_);
lean_dec_ref(v_fallback_2006_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___redArg(lean_object* v_cmp_2008_, lean_object* v_t_2009_, lean_object* v_k_2010_, lean_object* v_fallback_2011_){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_box(0);
v___x_2013_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2008_, v_k_2010_, v___x_2012_, v_t_2009_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_inc_ref(v_fallback_2011_);
return v_fallback_2011_;
}
else
{
lean_object* v_val_2014_; 
v_val_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_val_2014_);
lean_dec_ref(v___x_2013_);
return v_val_2014_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2015_, lean_object* v_t_2016_, lean_object* v_k_2017_, lean_object* v_fallback_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Std_DTreeMap_Const_getEntryLED___redArg(v_cmp_2015_, v_t_2016_, v_k_2017_, v_fallback_2018_);
lean_dec_ref(v_fallback_2018_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED(lean_object* v_00_u03b1_2020_, lean_object* v_cmp_2021_, lean_object* v_00_u03b2_2022_, lean_object* v_t_2023_, lean_object* v_k_2024_, lean_object* v_fallback_2025_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = lean_box(0);
v___x_2027_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2021_, v_k_2024_, v___x_2026_, v_t_2023_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_inc_ref(v_fallback_2025_);
return v_fallback_2025_;
}
else
{
lean_object* v_val_2028_; 
v_val_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_val_2028_);
lean_dec_ref(v___x_2027_);
return v_val_2028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2029_, lean_object* v_cmp_2030_, lean_object* v_00_u03b2_2031_, lean_object* v_t_2032_, lean_object* v_k_2033_, lean_object* v_fallback_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Std_DTreeMap_Const_getEntryLED(v_00_u03b1_2029_, v_cmp_2030_, v_00_u03b2_2031_, v_t_2032_, v_k_2033_, v_fallback_2034_);
lean_dec_ref(v_fallback_2034_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___redArg(lean_object* v_cmp_2036_, lean_object* v_t_2037_, lean_object* v_k_2038_, lean_object* v_fallback_2039_){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = lean_box(0);
v___x_2041_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2036_, v_k_2038_, v___x_2040_, v_t_2037_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_inc_ref(v_fallback_2039_);
return v_fallback_2039_;
}
else
{
lean_object* v_val_2042_; 
v_val_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_val_2042_);
lean_dec_ref(v___x_2041_);
return v_val_2042_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2043_, lean_object* v_t_2044_, lean_object* v_k_2045_, lean_object* v_fallback_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Std_DTreeMap_Const_getEntryLTD___redArg(v_cmp_2043_, v_t_2044_, v_k_2045_, v_fallback_2046_);
lean_dec_ref(v_fallback_2046_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD(lean_object* v_00_u03b1_2048_, lean_object* v_cmp_2049_, lean_object* v_00_u03b2_2050_, lean_object* v_t_2051_, lean_object* v_k_2052_, lean_object* v_fallback_2053_){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_box(0);
v___x_2055_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2049_, v_k_2052_, v___x_2054_, v_t_2051_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_inc_ref(v_fallback_2053_);
return v_fallback_2053_;
}
else
{
lean_object* v_val_2056_; 
v_val_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_val_2056_);
lean_dec_ref(v___x_2055_);
return v_val_2056_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2057_, lean_object* v_cmp_2058_, lean_object* v_00_u03b2_2059_, lean_object* v_t_2060_, lean_object* v_k_2061_, lean_object* v_fallback_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Std_DTreeMap_Const_getEntryLTD(v_00_u03b1_2057_, v_cmp_2058_, v_00_u03b2_2059_, v_t_2060_, v_k_2061_, v_fallback_2062_);
lean_dec_ref(v_fallback_2062_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter___redArg(lean_object* v_f_2064_, lean_object* v_t_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2064_, v_t_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter(lean_object* v_00_u03b1_2067_, lean_object* v_00_u03b2_2068_, lean_object* v_cmp_2069_, lean_object* v_f_2070_, lean_object* v_t_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2070_, v_t_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter___boxed(lean_object* v_00_u03b1_2073_, lean_object* v_00_u03b2_2074_, lean_object* v_cmp_2075_, lean_object* v_f_2076_, lean_object* v_t_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Std_DTreeMap_filter(v_00_u03b1_2073_, v_00_u03b2_2074_, v_cmp_2075_, v_f_2076_, v_t_2077_);
lean_dec_ref(v_cmp_2075_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM___redArg(lean_object* v_inst_2079_, lean_object* v_f_2080_, lean_object* v_init_2081_, lean_object* v_t_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2079_, v_f_2080_, v_init_2081_, v_t_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM(lean_object* v_00_u03b1_2084_, lean_object* v_00_u03b2_2085_, lean_object* v_cmp_2086_, lean_object* v_00_u03b4_2087_, lean_object* v_m_2088_, lean_object* v_inst_2089_, lean_object* v_f_2090_, lean_object* v_init_2091_, lean_object* v_t_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2089_, v_f_2090_, v_init_2091_, v_t_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM___boxed(lean_object* v_00_u03b1_2094_, lean_object* v_00_u03b2_2095_, lean_object* v_cmp_2096_, lean_object* v_00_u03b4_2097_, lean_object* v_m_2098_, lean_object* v_inst_2099_, lean_object* v_f_2100_, lean_object* v_init_2101_, lean_object* v_t_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Std_DTreeMap_foldlM(v_00_u03b1_2094_, v_00_u03b2_2095_, v_cmp_2096_, v_00_u03b4_2097_, v_m_2098_, v_inst_2099_, v_f_2100_, v_init_2101_, v_t_2102_);
lean_dec_ref(v_cmp_2096_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl___redArg(lean_object* v_f_2104_, lean_object* v_init_2105_, lean_object* v_t_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2104_, v_init_2105_, v_t_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl(lean_object* v_00_u03b1_2108_, lean_object* v_00_u03b2_2109_, lean_object* v_cmp_2110_, lean_object* v_00_u03b4_2111_, lean_object* v_f_2112_, lean_object* v_init_2113_, lean_object* v_t_2114_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2112_, v_init_2113_, v_t_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_00_u03b2_2117_, lean_object* v_cmp_2118_, lean_object* v_00_u03b4_2119_, lean_object* v_f_2120_, lean_object* v_init_2121_, lean_object* v_t_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Std_DTreeMap_foldl(v_00_u03b1_2116_, v_00_u03b2_2117_, v_cmp_2118_, v_00_u03b4_2119_, v_f_2120_, v_init_2121_, v_t_2122_);
lean_dec_ref(v_cmp_2118_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM___redArg(lean_object* v_inst_2124_, lean_object* v_f_2125_, lean_object* v_init_2126_, lean_object* v_t_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2124_, v_f_2125_, v_init_2126_, v_t_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM(lean_object* v_00_u03b1_2129_, lean_object* v_00_u03b2_2130_, lean_object* v_cmp_2131_, lean_object* v_00_u03b4_2132_, lean_object* v_m_2133_, lean_object* v_inst_2134_, lean_object* v_f_2135_, lean_object* v_init_2136_, lean_object* v_t_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2134_, v_f_2135_, v_init_2136_, v_t_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM___boxed(lean_object* v_00_u03b1_2139_, lean_object* v_00_u03b2_2140_, lean_object* v_cmp_2141_, lean_object* v_00_u03b4_2142_, lean_object* v_m_2143_, lean_object* v_inst_2144_, lean_object* v_f_2145_, lean_object* v_init_2146_, lean_object* v_t_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Std_DTreeMap_foldrM(v_00_u03b1_2139_, v_00_u03b2_2140_, v_cmp_2141_, v_00_u03b4_2142_, v_m_2143_, v_inst_2144_, v_f_2145_, v_init_2146_, v_t_2147_);
lean_dec_ref(v_cmp_2141_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___redArg___lam__0(lean_object* v_f_2149_, lean_object* v_x1_2150_, lean_object* v_x2_2151_, lean_object* v_x3_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_apply_3(v_f_2149_, v_x1_2150_, v_x2_2151_, v_x3_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___redArg(lean_object* v_f_2173_, lean_object* v_init_2174_, lean_object* v_t_2175_){
_start:
{
lean_object* v___f_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___f_2176_ = lean_alloc_closure((void*)(l_Std_DTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2176_, 0, v_f_2173_);
v___x_2177_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2178_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2177_, v___f_2176_, v_init_2174_, v_t_2175_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr(lean_object* v_00_u03b1_2179_, lean_object* v_00_u03b2_2180_, lean_object* v_cmp_2181_, lean_object* v_00_u03b4_2182_, lean_object* v_f_2183_, lean_object* v_init_2184_, lean_object* v_t_2185_){
_start:
{
lean_object* v___f_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___f_2186_ = lean_alloc_closure((void*)(l_Std_DTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2186_, 0, v_f_2183_);
v___x_2187_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2188_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2187_, v___f_2186_, v_init_2184_, v_t_2185_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___boxed(lean_object* v_00_u03b1_2189_, lean_object* v_00_u03b2_2190_, lean_object* v_cmp_2191_, lean_object* v_00_u03b4_2192_, lean_object* v_f_2193_, lean_object* v_init_2194_, lean_object* v_t_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Std_DTreeMap_foldr(v_00_u03b1_2189_, v_00_u03b2_2190_, v_cmp_2191_, v_00_u03b4_2192_, v_f_2193_, v_init_2194_, v_t_2195_);
lean_dec_ref(v_cmp_2191_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition___redArg___lam__0(lean_object* v_f_2197_, lean_object* v_cmp_2198_, lean_object* v_x_2199_, lean_object* v_a_2200_, lean_object* v_b_2201_){
_start:
{
lean_object* v_fst_2202_; lean_object* v_snd_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2217_; 
v_fst_2202_ = lean_ctor_get(v_x_2199_, 0);
v_snd_2203_ = lean_ctor_get(v_x_2199_, 1);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_x_2199_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2205_ = v_x_2199_;
v_isShared_2206_ = v_isSharedCheck_2217_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_snd_2203_);
lean_inc(v_fst_2202_);
lean_dec(v_x_2199_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2217_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
lean_inc(v_b_2201_);
lean_inc(v_a_2200_);
v___x_2207_ = lean_apply_2(v_f_2197_, v_a_2200_, v_b_2201_);
v___x_2208_ = lean_unbox(v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2209_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2198_, v_a_2200_, v_b_2201_, v_snd_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 1, v___x_2209_);
v___x_2211_ = v___x_2205_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_fst_2202_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2213_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2198_, v_a_2200_, v_b_2201_, v_fst_2202_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2213_);
v___x_2215_ = v___x_2205_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_snd_2203_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition___redArg(lean_object* v_cmp_2220_, lean_object* v_f_2221_, lean_object* v_t_2222_){
_start:
{
lean_object* v___f_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___f_2223_ = lean_alloc_closure((void*)(l_Std_DTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2223_, 0, v_f_2221_);
lean_closure_set(v___f_2223_, 1, v_cmp_2220_);
v___x_2224_ = ((lean_object*)(l_Std_DTreeMap_partition___redArg___closed__0));
v___x_2225_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2223_, v___x_2224_, v_t_2222_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition(lean_object* v_00_u03b1_2226_, lean_object* v_00_u03b2_2227_, lean_object* v_cmp_2228_, lean_object* v_f_2229_, lean_object* v_t_2230_){
_start:
{
lean_object* v___f_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___f_2231_ = lean_alloc_closure((void*)(l_Std_DTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2231_, 0, v_f_2229_);
lean_closure_set(v___f_2231_, 1, v_cmp_2228_);
v___x_2232_ = ((lean_object*)(l_Std_DTreeMap_partition___redArg___closed__0));
v___x_2233_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2231_, v___x_2232_, v_t_2230_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___redArg___lam__0(lean_object* v_f_2234_, lean_object* v_x_2235_, lean_object* v_k_2236_, lean_object* v_v_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = lean_apply_2(v_f_2234_, v_k_2236_, v_v_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___redArg(lean_object* v_inst_2239_, lean_object* v_f_2240_, lean_object* v_t_2241_){
_start:
{
lean_object* v___f_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___f_2242_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2242_, 0, v_f_2240_);
v___x_2243_ = lean_box(0);
v___x_2244_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2239_, v___f_2242_, v___x_2243_, v_t_2241_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM(lean_object* v_00_u03b1_2245_, lean_object* v_00_u03b2_2246_, lean_object* v_cmp_2247_, lean_object* v_m_2248_, lean_object* v_inst_2249_, lean_object* v_f_2250_, lean_object* v_t_2251_){
_start:
{
lean_object* v___f_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___f_2252_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2252_, 0, v_f_2250_);
v___x_2253_ = lean_box(0);
v___x_2254_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2249_, v___f_2252_, v___x_2253_, v_t_2251_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___boxed(lean_object* v_00_u03b1_2255_, lean_object* v_00_u03b2_2256_, lean_object* v_cmp_2257_, lean_object* v_m_2258_, lean_object* v_inst_2259_, lean_object* v_f_2260_, lean_object* v_t_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Std_DTreeMap_forM(v_00_u03b1_2255_, v_00_u03b2_2256_, v_cmp_2257_, v_m_2258_, v_inst_2259_, v_f_2260_, v_t_2261_);
lean_dec_ref(v_cmp_2257_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___redArg___lam__0(lean_object* v_toPure_2263_, lean_object* v_____do__lift_2264_){
_start:
{
lean_object* v_a_2265_; lean_object* v___x_2266_; 
v_a_2265_ = lean_ctor_get(v_____do__lift_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref(v_____do__lift_2264_);
v___x_2266_ = lean_apply_2(v_toPure_2263_, lean_box(0), v_a_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___redArg(lean_object* v_inst_2267_, lean_object* v_f_2268_, lean_object* v_init_2269_, lean_object* v_t_2270_){
_start:
{
lean_object* v_toApplicative_2271_; lean_object* v_toBind_2272_; lean_object* v_toPure_2273_; lean_object* v___x_2274_; lean_object* v___f_2275_; lean_object* v___x_2276_; 
v_toApplicative_2271_ = lean_ctor_get(v_inst_2267_, 0);
v_toBind_2272_ = lean_ctor_get(v_inst_2267_, 1);
lean_inc(v_toBind_2272_);
v_toPure_2273_ = lean_ctor_get(v_toApplicative_2271_, 1);
lean_inc(v_toPure_2273_);
v___x_2274_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2267_, v_f_2268_, v_init_2269_, v_t_2270_);
v___f_2275_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2275_, 0, v_toPure_2273_);
v___x_2276_ = lean_apply_4(v_toBind_2272_, lean_box(0), lean_box(0), v___x_2274_, v___f_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn(lean_object* v_00_u03b1_2277_, lean_object* v_00_u03b2_2278_, lean_object* v_cmp_2279_, lean_object* v_00_u03b4_2280_, lean_object* v_m_2281_, lean_object* v_inst_2282_, lean_object* v_f_2283_, lean_object* v_init_2284_, lean_object* v_t_2285_){
_start:
{
lean_object* v_toApplicative_2286_; lean_object* v_toBind_2287_; lean_object* v_toPure_2288_; lean_object* v___x_2289_; lean_object* v___f_2290_; lean_object* v___x_2291_; 
v_toApplicative_2286_ = lean_ctor_get(v_inst_2282_, 0);
v_toBind_2287_ = lean_ctor_get(v_inst_2282_, 1);
lean_inc(v_toBind_2287_);
v_toPure_2288_ = lean_ctor_get(v_toApplicative_2286_, 1);
lean_inc(v_toPure_2288_);
v___x_2289_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2282_, v_f_2283_, v_init_2284_, v_t_2285_);
v___f_2290_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2290_, 0, v_toPure_2288_);
v___x_2291_ = lean_apply_4(v_toBind_2287_, lean_box(0), lean_box(0), v___x_2289_, v___f_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___boxed(lean_object* v_00_u03b1_2292_, lean_object* v_00_u03b2_2293_, lean_object* v_cmp_2294_, lean_object* v_00_u03b4_2295_, lean_object* v_m_2296_, lean_object* v_inst_2297_, lean_object* v_f_2298_, lean_object* v_init_2299_, lean_object* v_t_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Std_DTreeMap_forIn(v_00_u03b1_2292_, v_00_u03b2_2293_, v_cmp_2294_, v_00_u03b4_2295_, v_m_2296_, v_inst_2297_, v_f_2298_, v_init_2299_, v_t_2300_);
lean_dec_ref(v_cmp_2294_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_2302_, lean_object* v_x_2303_, lean_object* v_k_2304_, lean_object* v_v_2305_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2306_, 0, v_k_2304_);
lean_ctor_set(v___x_2306_, 1, v_v_2305_);
v___x_2307_ = lean_apply_1(v_f_2302_, v___x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1(lean_object* v_inst_2308_, lean_object* v_t_2309_, lean_object* v_f_2310_){
_start:
{
lean_object* v___f_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___f_2311_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2311_, 0, v_f_2310_);
v___x_2312_ = lean_box(0);
v___x_2313_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2308_, v___f_2311_, v___x_2312_, v_t_2309_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg(lean_object* v_inst_2314_){
_start:
{
lean_object* v___f_2315_; 
v___f_2315_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2315_, 0, v_inst_2314_);
return v___f_2315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad(lean_object* v_00_u03b1_2316_, lean_object* v_00_u03b2_2317_, lean_object* v_cmp_2318_, lean_object* v_m_2319_, lean_object* v_inst_2320_){
_start:
{
lean_object* v___f_2321_; 
v___f_2321_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2321_, 0, v_inst_2320_);
return v___f_2321_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___boxed(lean_object* v_00_u03b1_2322_, lean_object* v_00_u03b2_2323_, lean_object* v_cmp_2324_, lean_object* v_m_2325_, lean_object* v_inst_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Std_DTreeMap_instForMSigmaOfMonad(v_00_u03b1_2322_, v_00_u03b2_2323_, v_cmp_2324_, v_m_2325_, v_inst_2326_);
lean_dec_ref(v_cmp_2324_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_2328_, lean_object* v_a_2329_, lean_object* v_b_2330_, lean_object* v_acc_2331_){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2332_, 0, v_a_2329_);
lean_ctor_set(v___x_2332_, 1, v_b_2330_);
v___x_2333_ = lean_apply_2(v_f_2328_, v___x_2332_, v_acc_2331_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_2334_, lean_object* v_00_u03b2_2335_, lean_object* v_m_2336_, lean_object* v_init_2337_, lean_object* v_f_2338_){
_start:
{
lean_object* v_toApplicative_2339_; lean_object* v_toBind_2340_; lean_object* v_toPure_2341_; lean_object* v___f_2342_; lean_object* v___x_2343_; lean_object* v___f_2344_; lean_object* v___x_2345_; 
v_toApplicative_2339_ = lean_ctor_get(v_inst_2334_, 0);
v_toBind_2340_ = lean_ctor_get(v_inst_2334_, 1);
lean_inc(v_toBind_2340_);
v_toPure_2341_ = lean_ctor_get(v_toApplicative_2339_, 1);
lean_inc(v_toPure_2341_);
v___f_2342_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2342_, 0, v_f_2338_);
v___x_2343_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2334_, v___f_2342_, v_init_2337_, v_m_2336_);
v___f_2344_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2344_, 0, v_toPure_2341_);
v___x_2345_ = lean_apply_4(v_toBind_2340_, lean_box(0), lean_box(0), v___x_2343_, v___f_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg(lean_object* v_inst_2346_){
_start:
{
lean_object* v___f_2347_; 
v___f_2347_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2347_, 0, v_inst_2346_);
return v___f_2347_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad(lean_object* v_00_u03b1_2348_, lean_object* v_00_u03b2_2349_, lean_object* v_cmp_2350_, lean_object* v_m_2351_, lean_object* v_inst_2352_){
_start:
{
lean_object* v___f_2353_; 
v___f_2353_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2353_, 0, v_inst_2352_);
return v___f_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___boxed(lean_object* v_00_u03b1_2354_, lean_object* v_00_u03b2_2355_, lean_object* v_cmp_2356_, lean_object* v_m_2357_, lean_object* v_inst_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Std_DTreeMap_instForInSigmaOfMonad(v_00_u03b1_2354_, v_00_u03b2_2355_, v_cmp_2356_, v_m_2357_, v_inst_2358_);
lean_dec_ref(v_cmp_2356_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2360_, lean_object* v_x_2361_, lean_object* v_k_2362_, lean_object* v_v_2363_){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2364_, 0, v_k_2362_);
lean_ctor_set(v___x_2364_, 1, v_v_2363_);
v___x_2365_ = lean_apply_1(v_f_2360_, v___x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___redArg(lean_object* v_inst_2366_, lean_object* v_f_2367_, lean_object* v_t_2368_){
_start:
{
lean_object* v___f_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___f_2369_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2369_, 0, v_f_2367_);
v___x_2370_ = lean_box(0);
v___x_2371_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2366_, v___f_2369_, v___x_2370_, v_t_2368_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried(lean_object* v_00_u03b1_2372_, lean_object* v_cmp_2373_, lean_object* v_m_2374_, lean_object* v_inst_2375_, lean_object* v_00_u03b2_2376_, lean_object* v_f_2377_, lean_object* v_t_2378_){
_start:
{
lean_object* v___f_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___f_2379_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2379_, 0, v_f_2377_);
v___x_2380_ = lean_box(0);
v___x_2381_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2375_, v___f_2379_, v___x_2380_, v_t_2378_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2382_, lean_object* v_cmp_2383_, lean_object* v_m_2384_, lean_object* v_inst_2385_, lean_object* v_00_u03b2_2386_, lean_object* v_f_2387_, lean_object* v_t_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Std_DTreeMap_Const_forMUncurried(v_00_u03b1_2382_, v_cmp_2383_, v_m_2384_, v_inst_2385_, v_00_u03b2_2386_, v_f_2387_, v_t_2388_);
lean_dec_ref(v_cmp_2383_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2390_, lean_object* v_a_2391_, lean_object* v_b_2392_, lean_object* v_acc_2393_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2394_, 0, v_a_2391_);
lean_ctor_set(v___x_2394_, 1, v_b_2392_);
v___x_2395_ = lean_apply_2(v_f_2390_, v___x_2394_, v_acc_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___redArg(lean_object* v_inst_2396_, lean_object* v_f_2397_, lean_object* v_init_2398_, lean_object* v_t_2399_){
_start:
{
lean_object* v_toApplicative_2400_; lean_object* v_toBind_2401_; lean_object* v_toPure_2402_; lean_object* v___f_2403_; lean_object* v___x_2404_; lean_object* v___f_2405_; lean_object* v___x_2406_; 
v_toApplicative_2400_ = lean_ctor_get(v_inst_2396_, 0);
v_toBind_2401_ = lean_ctor_get(v_inst_2396_, 1);
lean_inc(v_toBind_2401_);
v_toPure_2402_ = lean_ctor_get(v_toApplicative_2400_, 1);
lean_inc(v_toPure_2402_);
v___f_2403_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2403_, 0, v_f_2397_);
v___x_2404_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2396_, v___f_2403_, v_init_2398_, v_t_2399_);
v___f_2405_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2405_, 0, v_toPure_2402_);
v___x_2406_ = lean_apply_4(v_toBind_2401_, lean_box(0), lean_box(0), v___x_2404_, v___f_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried(lean_object* v_00_u03b1_2407_, lean_object* v_cmp_2408_, lean_object* v_00_u03b4_2409_, lean_object* v_m_2410_, lean_object* v_inst_2411_, lean_object* v_00_u03b2_2412_, lean_object* v_f_2413_, lean_object* v_init_2414_, lean_object* v_t_2415_){
_start:
{
lean_object* v_toApplicative_2416_; lean_object* v_toBind_2417_; lean_object* v_toPure_2418_; lean_object* v___f_2419_; lean_object* v___x_2420_; lean_object* v___f_2421_; lean_object* v___x_2422_; 
v_toApplicative_2416_ = lean_ctor_get(v_inst_2411_, 0);
v_toBind_2417_ = lean_ctor_get(v_inst_2411_, 1);
lean_inc(v_toBind_2417_);
v_toPure_2418_ = lean_ctor_get(v_toApplicative_2416_, 1);
lean_inc(v_toPure_2418_);
v___f_2419_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2419_, 0, v_f_2413_);
v___x_2420_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2411_, v___f_2419_, v_init_2414_, v_t_2415_);
v___f_2421_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2421_, 0, v_toPure_2418_);
v___x_2422_ = lean_apply_4(v_toBind_2417_, lean_box(0), lean_box(0), v___x_2420_, v___f_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2423_, lean_object* v_cmp_2424_, lean_object* v_00_u03b4_2425_, lean_object* v_m_2426_, lean_object* v_inst_2427_, lean_object* v_00_u03b2_2428_, lean_object* v_f_2429_, lean_object* v_init_2430_, lean_object* v_t_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Std_DTreeMap_Const_forInUncurried(v_00_u03b1_2423_, v_cmp_2424_, v_00_u03b4_2425_, v_m_2426_, v_inst_2427_, v_00_u03b2_2428_, v_f_2429_, v_init_2430_, v_t_2431_);
lean_dec_ref(v_cmp_2424_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___lam__0(lean_object* v_p_2433_, lean_object* v___x_2434_, lean_object* v___x_2435_, lean_object* v_a_2436_, lean_object* v_b_2437_, lean_object* v_acc_2438_){
_start:
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = lean_apply_2(v_p_2433_, v_a_2436_, v_b_2437_);
v___x_2440_ = lean_unbox(v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2434_);
return v___x_2441_;
}
else
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
lean_dec_ref(v___x_2434_);
v___x_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2439_);
v___x_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v___x_2435_);
v___x_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
return v___x_2444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2445_, lean_object* v___x_2446_, lean_object* v___x_2447_, lean_object* v_a_2448_, lean_object* v_b_2449_, lean_object* v_acc_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Std_DTreeMap_any___redArg___lam__0(v_p_2445_, v___x_2446_, v___x_2447_, v_a_2448_, v_b_2449_, v_acc_2450_);
lean_dec_ref(v_acc_2450_);
return v_res_2451_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_any___redArg(lean_object* v_t_2455_, lean_object* v_p_2456_){
_start:
{
lean_object* v___y_2458_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___f_2466_; lean_object* v___x_2467_; lean_object* v_a_2468_; 
v___x_2463_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2464_ = lean_box(0);
v___x_2465_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2466_ = lean_alloc_closure((void*)(l_Std_DTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2466_, 0, v_p_2456_);
lean_closure_set(v___f_2466_, 1, v___x_2465_);
lean_closure_set(v___f_2466_, 2, v___x_2464_);
v___x_2467_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2463_, v___f_2466_, v___x_2465_, v_t_2455_);
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___y_2458_ = v_a_2468_;
goto v___jp_2457_;
v___jp_2457_:
{
lean_object* v_fst_2459_; 
v_fst_2459_ = lean_ctor_get(v___y_2458_, 0);
lean_inc(v_fst_2459_);
lean_dec_ref(v___y_2458_);
if (lean_obj_tag(v_fst_2459_) == 0)
{
uint8_t v___x_2460_; 
v___x_2460_ = 0;
return v___x_2460_;
}
else
{
lean_object* v_val_2461_; uint8_t v___x_2462_; 
v_val_2461_ = lean_ctor_get(v_fst_2459_, 0);
lean_inc(v_val_2461_);
lean_dec_ref(v_fst_2459_);
v___x_2462_ = lean_unbox(v_val_2461_);
lean_dec(v_val_2461_);
return v___x_2462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___boxed(lean_object* v_t_2469_, lean_object* v_p_2470_){
_start:
{
uint8_t v_res_2471_; lean_object* v_r_2472_; 
v_res_2471_ = l_Std_DTreeMap_any___redArg(v_t_2469_, v_p_2470_);
v_r_2472_ = lean_box(v_res_2471_);
return v_r_2472_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_any(lean_object* v_00_u03b1_2473_, lean_object* v_00_u03b2_2474_, lean_object* v_cmp_2475_, lean_object* v_t_2476_, lean_object* v_p_2477_){
_start:
{
lean_object* v___y_2479_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___f_2487_; lean_object* v___x_2488_; lean_object* v_a_2489_; 
v___x_2484_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2485_ = lean_box(0);
v___x_2486_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2487_ = lean_alloc_closure((void*)(l_Std_DTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2487_, 0, v_p_2477_);
lean_closure_set(v___f_2487_, 1, v___x_2486_);
lean_closure_set(v___f_2487_, 2, v___x_2485_);
v___x_2488_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2484_, v___f_2487_, v___x_2486_, v_t_2476_);
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___y_2479_ = v_a_2489_;
goto v___jp_2478_;
v___jp_2478_:
{
lean_object* v_fst_2480_; 
v_fst_2480_ = lean_ctor_get(v___y_2479_, 0);
lean_inc(v_fst_2480_);
lean_dec_ref(v___y_2479_);
if (lean_obj_tag(v_fst_2480_) == 0)
{
uint8_t v___x_2481_; 
v___x_2481_ = 0;
return v___x_2481_;
}
else
{
lean_object* v_val_2482_; uint8_t v___x_2483_; 
v_val_2482_ = lean_ctor_get(v_fst_2480_, 0);
lean_inc(v_val_2482_);
lean_dec_ref(v_fst_2480_);
v___x_2483_ = lean_unbox(v_val_2482_);
lean_dec(v_val_2482_);
return v___x_2483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___boxed(lean_object* v_00_u03b1_2490_, lean_object* v_00_u03b2_2491_, lean_object* v_cmp_2492_, lean_object* v_t_2493_, lean_object* v_p_2494_){
_start:
{
uint8_t v_res_2495_; lean_object* v_r_2496_; 
v_res_2495_ = l_Std_DTreeMap_any(v_00_u03b1_2490_, v_00_u03b2_2491_, v_cmp_2492_, v_t_2493_, v_p_2494_);
lean_dec_ref(v_cmp_2492_);
v_r_2496_ = lean_box(v_res_2495_);
return v_r_2496_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___lam__0(lean_object* v_p_2497_, lean_object* v___x_2498_, lean_object* v___x_2499_, lean_object* v_a_2500_, lean_object* v_b_2501_, lean_object* v_acc_2502_){
_start:
{
lean_object* v___x_2503_; uint8_t v___x_2504_; 
v___x_2503_ = lean_apply_2(v_p_2497_, v_a_2500_, v_b_2501_);
v___x_2504_ = lean_unbox(v___x_2503_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec_ref(v___x_2499_);
v___x_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
v___x_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v___x_2498_);
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
else
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2499_);
return v___x_2508_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_2509_, lean_object* v___x_2510_, lean_object* v___x_2511_, lean_object* v_a_2512_, lean_object* v_b_2513_, lean_object* v_acc_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Std_DTreeMap_all___redArg___lam__0(v_p_2509_, v___x_2510_, v___x_2511_, v_a_2512_, v_b_2513_, v_acc_2514_);
lean_dec_ref(v_acc_2514_);
return v_res_2515_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_all___redArg(lean_object* v_t_2516_, lean_object* v_p_2517_){
_start:
{
lean_object* v___y_2519_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; lean_object* v_a_2529_; 
v___x_2524_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2525_ = lean_box(0);
v___x_2526_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2527_ = lean_alloc_closure((void*)(l_Std_DTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2527_, 0, v_p_2517_);
lean_closure_set(v___f_2527_, 1, v___x_2525_);
lean_closure_set(v___f_2527_, 2, v___x_2526_);
v___x_2528_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2524_, v___f_2527_, v___x_2526_, v_t_2516_);
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___y_2519_ = v_a_2529_;
goto v___jp_2518_;
v___jp_2518_:
{
lean_object* v_fst_2520_; 
v_fst_2520_ = lean_ctor_get(v___y_2519_, 0);
lean_inc(v_fst_2520_);
lean_dec_ref(v___y_2519_);
if (lean_obj_tag(v_fst_2520_) == 0)
{
uint8_t v___x_2521_; 
v___x_2521_ = 1;
return v___x_2521_;
}
else
{
lean_object* v_val_2522_; uint8_t v___x_2523_; 
v_val_2522_ = lean_ctor_get(v_fst_2520_, 0);
lean_inc(v_val_2522_);
lean_dec_ref(v_fst_2520_);
v___x_2523_ = lean_unbox(v_val_2522_);
lean_dec(v_val_2522_);
return v___x_2523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___boxed(lean_object* v_t_2530_, lean_object* v_p_2531_){
_start:
{
uint8_t v_res_2532_; lean_object* v_r_2533_; 
v_res_2532_ = l_Std_DTreeMap_all___redArg(v_t_2530_, v_p_2531_);
v_r_2533_ = lean_box(v_res_2532_);
return v_r_2533_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_all(lean_object* v_00_u03b1_2534_, lean_object* v_00_u03b2_2535_, lean_object* v_cmp_2536_, lean_object* v_t_2537_, lean_object* v_p_2538_){
_start:
{
lean_object* v___y_2540_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___f_2548_; lean_object* v___x_2549_; lean_object* v_a_2550_; 
v___x_2545_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2546_ = lean_box(0);
v___x_2547_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2548_ = lean_alloc_closure((void*)(l_Std_DTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2548_, 0, v_p_2538_);
lean_closure_set(v___f_2548_, 1, v___x_2546_);
lean_closure_set(v___f_2548_, 2, v___x_2547_);
v___x_2549_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2545_, v___f_2548_, v___x_2547_, v_t_2537_);
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___y_2540_ = v_a_2550_;
goto v___jp_2539_;
v___jp_2539_:
{
lean_object* v_fst_2541_; 
v_fst_2541_ = lean_ctor_get(v___y_2540_, 0);
lean_inc(v_fst_2541_);
lean_dec_ref(v___y_2540_);
if (lean_obj_tag(v_fst_2541_) == 0)
{
uint8_t v___x_2542_; 
v___x_2542_ = 1;
return v___x_2542_;
}
else
{
lean_object* v_val_2543_; uint8_t v___x_2544_; 
v_val_2543_ = lean_ctor_get(v_fst_2541_, 0);
lean_inc(v_val_2543_);
lean_dec_ref(v_fst_2541_);
v___x_2544_ = lean_unbox(v_val_2543_);
lean_dec(v_val_2543_);
return v___x_2544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___boxed(lean_object* v_00_u03b1_2551_, lean_object* v_00_u03b2_2552_, lean_object* v_cmp_2553_, lean_object* v_t_2554_, lean_object* v_p_2555_){
_start:
{
uint8_t v_res_2556_; lean_object* v_r_2557_; 
v_res_2556_ = l_Std_DTreeMap_all(v_00_u03b1_2551_, v_00_u03b2_2552_, v_cmp_2553_, v_t_2554_, v_p_2555_);
lean_dec_ref(v_cmp_2553_);
v_r_2557_ = lean_box(v_res_2556_);
return v_r_2557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg___lam__0(lean_object* v_x1_2558_, lean_object* v_x2_2559_, lean_object* v_x3_2560_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2561_, 0, v_x1_2558_);
lean_ctor_set(v___x_2561_, 1, v_x3_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_2562_, lean_object* v_x2_2563_, lean_object* v_x3_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Std_DTreeMap_keys___redArg___lam__0(v_x1_2562_, v_x2_2563_, v_x3_2564_);
lean_dec(v_x2_2563_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg(lean_object* v_t_2567_){
_start:
{
lean_object* v___f_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___f_2568_ = ((lean_object*)(l_Std_DTreeMap_keys___redArg___closed__0));
v___x_2569_ = lean_box(0);
v___x_2570_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2571_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2570_, v___f_2568_, v___x_2569_, v_t_2567_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys(lean_object* v_00_u03b1_2572_, lean_object* v_00_u03b2_2573_, lean_object* v_cmp_2574_, lean_object* v_t_2575_){
_start:
{
lean_object* v___f_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___f_2576_ = ((lean_object*)(l_Std_DTreeMap_keys___redArg___closed__0));
v___x_2577_ = lean_box(0);
v___x_2578_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2579_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2578_, v___f_2576_, v___x_2577_, v_t_2575_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___boxed(lean_object* v_00_u03b1_2580_, lean_object* v_00_u03b2_2581_, lean_object* v_cmp_2582_, lean_object* v_t_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Std_DTreeMap_keys(v_00_u03b1_2580_, v_00_u03b2_2581_, v_cmp_2582_, v_t_2583_);
lean_dec_ref(v_cmp_2582_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg___lam__0(lean_object* v_l_2585_, lean_object* v_k_2586_, lean_object* v_x_2587_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_array_push(v_l_2585_, v_k_2586_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_2589_, lean_object* v_k_2590_, lean_object* v_x_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Std_DTreeMap_keysArray___redArg___lam__0(v_l_2589_, v_k_2590_, v_x_2591_);
lean_dec(v_x_2591_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg(lean_object* v_t_2594_){
_start:
{
lean_object* v___f_2595_; lean_object* v___y_2597_; 
v___f_2595_ = ((lean_object*)(l_Std_DTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2594_) == 0)
{
lean_object* v_size_2600_; 
v_size_2600_ = lean_ctor_get(v_t_2594_, 0);
lean_inc(v_size_2600_);
v___y_2597_ = v_size_2600_;
goto v___jp_2596_;
}
else
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_unsigned_to_nat(0u);
v___y_2597_ = v___x_2601_;
goto v___jp_2596_;
}
v___jp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_mk_empty_array_with_capacity(v___y_2597_);
lean_dec(v___y_2597_);
v___x_2599_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2595_, v___x_2598_, v_t_2594_);
return v___x_2599_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray(lean_object* v_00_u03b1_2602_, lean_object* v_00_u03b2_2603_, lean_object* v_cmp_2604_, lean_object* v_t_2605_){
_start:
{
lean_object* v___f_2606_; lean_object* v___y_2608_; 
v___f_2606_ = ((lean_object*)(l_Std_DTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2605_) == 0)
{
lean_object* v_size_2611_; 
v_size_2611_ = lean_ctor_get(v_t_2605_, 0);
lean_inc(v_size_2611_);
v___y_2608_ = v_size_2611_;
goto v___jp_2607_;
}
else
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_unsigned_to_nat(0u);
v___y_2608_ = v___x_2612_;
goto v___jp_2607_;
}
v___jp_2607_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_mk_empty_array_with_capacity(v___y_2608_);
lean_dec(v___y_2608_);
v___x_2610_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2606_, v___x_2609_, v_t_2605_);
return v___x_2610_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___boxed(lean_object* v_00_u03b1_2613_, lean_object* v_00_u03b2_2614_, lean_object* v_cmp_2615_, lean_object* v_t_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Std_DTreeMap_keysArray(v_00_u03b1_2613_, v_00_u03b2_2614_, v_cmp_2615_, v_t_2616_);
lean_dec_ref(v_cmp_2615_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg___lam__0(lean_object* v_x1_2618_, lean_object* v_x2_2619_, lean_object* v_x3_2620_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2621_, 0, v_x2_2619_);
lean_ctor_set(v___x_2621_, 1, v_x3_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_2622_, lean_object* v_x2_2623_, lean_object* v_x3_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Std_DTreeMap_values___redArg___lam__0(v_x1_2622_, v_x2_2623_, v_x3_2624_);
lean_dec(v_x1_2622_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg(lean_object* v_t_2627_){
_start:
{
lean_object* v___f_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___f_2628_ = ((lean_object*)(l_Std_DTreeMap_values___redArg___closed__0));
v___x_2629_ = lean_box(0);
v___x_2630_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2631_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2630_, v___f_2628_, v___x_2629_, v_t_2627_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values(lean_object* v_00_u03b1_2632_, lean_object* v_cmp_2633_, lean_object* v_00_u03b2_2634_, lean_object* v_t_2635_){
_start:
{
lean_object* v___f_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___f_2636_ = ((lean_object*)(l_Std_DTreeMap_values___redArg___closed__0));
v___x_2637_ = lean_box(0);
v___x_2638_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2639_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2638_, v___f_2636_, v___x_2637_, v_t_2635_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_cmp_2641_, lean_object* v_00_u03b2_2642_, lean_object* v_t_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Std_DTreeMap_values(v_00_u03b1_2640_, v_cmp_2641_, v_00_u03b2_2642_, v_t_2643_);
lean_dec_ref(v_cmp_2641_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_2645_, lean_object* v_x_2646_, lean_object* v_v_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_array_push(v_l_2645_, v_v_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2649_, lean_object* v_x_2650_, lean_object* v_v_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Std_DTreeMap_valuesArray___redArg___lam__0(v_l_2649_, v_x_2650_, v_v_2651_);
lean_dec(v_x_2650_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg(lean_object* v_t_2654_){
_start:
{
lean_object* v___f_2655_; lean_object* v___y_2657_; 
v___f_2655_ = ((lean_object*)(l_Std_DTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2654_) == 0)
{
lean_object* v_size_2660_; 
v_size_2660_ = lean_ctor_get(v_t_2654_, 0);
lean_inc(v_size_2660_);
v___y_2657_ = v_size_2660_;
goto v___jp_2656_;
}
else
{
lean_object* v___x_2661_; 
v___x_2661_ = lean_unsigned_to_nat(0u);
v___y_2657_ = v___x_2661_;
goto v___jp_2656_;
}
v___jp_2656_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_mk_empty_array_with_capacity(v___y_2657_);
lean_dec(v___y_2657_);
v___x_2659_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2655_, v___x_2658_, v_t_2654_);
return v___x_2659_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray(lean_object* v_00_u03b1_2662_, lean_object* v_cmp_2663_, lean_object* v_00_u03b2_2664_, lean_object* v_t_2665_){
_start:
{
lean_object* v___f_2666_; lean_object* v___y_2668_; 
v___f_2666_ = ((lean_object*)(l_Std_DTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2665_) == 0)
{
lean_object* v_size_2671_; 
v_size_2671_ = lean_ctor_get(v_t_2665_, 0);
lean_inc(v_size_2671_);
v___y_2668_ = v_size_2671_;
goto v___jp_2667_;
}
else
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_unsigned_to_nat(0u);
v___y_2668_ = v___x_2672_;
goto v___jp_2667_;
}
v___jp_2667_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = lean_mk_empty_array_with_capacity(v___y_2668_);
lean_dec(v___y_2668_);
v___x_2670_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2666_, v___x_2669_, v_t_2665_);
return v___x_2670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_2673_, lean_object* v_cmp_2674_, lean_object* v_00_u03b2_2675_, lean_object* v_t_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Std_DTreeMap_valuesArray(v_00_u03b1_2673_, v_cmp_2674_, v_00_u03b2_2675_, v_t_2676_);
lean_dec_ref(v_cmp_2674_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___redArg___lam__0(lean_object* v_x1_2678_, lean_object* v_x2_2679_, lean_object* v_x3_2680_){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v_x1_2678_);
lean_ctor_set(v___x_2681_, 1, v_x2_2679_);
v___x_2682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
lean_ctor_set(v___x_2682_, 1, v_x3_2680_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___redArg(lean_object* v_t_2684_){
_start:
{
lean_object* v___f_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___f_2685_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_2686_ = lean_box(0);
v___x_2687_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2688_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2687_, v___f_2685_, v___x_2686_, v_t_2684_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList(lean_object* v_00_u03b1_2689_, lean_object* v_00_u03b2_2690_, lean_object* v_cmp_2691_, lean_object* v_t_2692_){
_start:
{
lean_object* v___f_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___f_2693_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_2694_ = lean_box(0);
v___x_2695_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2696_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2695_, v___f_2693_, v___x_2694_, v_t_2692_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___boxed(lean_object* v_00_u03b1_2697_, lean_object* v_00_u03b2_2698_, lean_object* v_cmp_2699_, lean_object* v_t_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Std_DTreeMap_toList(v_00_u03b1_2697_, v_00_u03b2_2698_, v_cmp_2699_, v_t_2700_);
lean_dec_ref(v_cmp_2699_);
return v_res_2701_;
}
}
static lean_object* _init_l_Std_DTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_2703_, lean_object* v_a_2704_, lean_object* v_x_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_fst_2707_; lean_object* v_snd_2708_; lean_object* v_r_2709_; lean_object* v___x_2710_; 
v_fst_2707_ = lean_ctor_get(v_a_2704_, 0);
lean_inc(v_fst_2707_);
v_snd_2708_ = lean_ctor_get(v_a_2704_, 1);
lean_inc(v_snd_2708_);
lean_dec_ref(v_a_2704_);
v_r_2709_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2703_, v_fst_2707_, v_snd_2708_, v___y_2706_);
v___x_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2710_, 0, v_r_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg(lean_object* v_l_2711_, lean_object* v_cmp_2712_){
_start:
{
lean_object* v___f_2713_; lean_object* v___x_2714_; lean_object* v_r_2715_; lean_object* v___x_2716_; 
v___f_2713_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2713_, 0, v_cmp_2712_);
v___x_2714_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2715_ = lean_box(1);
v___x_2716_ = l_List_forIn_x27_loop___redArg(v___x_2714_, v___f_2713_, v_l_2711_, v_r_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList(lean_object* v_00_u03b1_2717_, lean_object* v_00_u03b2_2718_, lean_object* v_l_2719_, lean_object* v_cmp_2720_){
_start:
{
lean_object* v___f_2721_; lean_object* v___x_2722_; lean_object* v_r_2723_; lean_object* v___x_2724_; 
v___f_2721_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2721_, 0, v_cmp_2720_);
v___x_2722_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2723_ = lean_box(1);
v___x_2724_ = l_List_forIn_x27_loop___redArg(v___x_2722_, v___f_2721_, v_l_2719_, v_r_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___redArg___lam__0(lean_object* v_l_2725_, lean_object* v_k_2726_, lean_object* v_v_2727_){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2728_, 0, v_k_2726_);
lean_ctor_set(v___x_2728_, 1, v_v_2727_);
v___x_2729_ = lean_array_push(v_l_2725_, v___x_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___redArg(lean_object* v_t_2731_){
_start:
{
lean_object* v___f_2732_; lean_object* v___y_2734_; 
v___f_2732_ = ((lean_object*)(l_Std_DTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2731_) == 0)
{
lean_object* v_size_2737_; 
v_size_2737_ = lean_ctor_get(v_t_2731_, 0);
lean_inc(v_size_2737_);
v___y_2734_ = v_size_2737_;
goto v___jp_2733_;
}
else
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_unsigned_to_nat(0u);
v___y_2734_ = v___x_2738_;
goto v___jp_2733_;
}
v___jp_2733_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = lean_mk_empty_array_with_capacity(v___y_2734_);
lean_dec(v___y_2734_);
v___x_2736_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2732_, v___x_2735_, v_t_2731_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray(lean_object* v_00_u03b1_2739_, lean_object* v_00_u03b2_2740_, lean_object* v_cmp_2741_, lean_object* v_t_2742_){
_start:
{
lean_object* v___f_2743_; lean_object* v___y_2745_; 
v___f_2743_ = ((lean_object*)(l_Std_DTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2742_) == 0)
{
lean_object* v_size_2748_; 
v_size_2748_ = lean_ctor_get(v_t_2742_, 0);
lean_inc(v_size_2748_);
v___y_2745_ = v_size_2748_;
goto v___jp_2744_;
}
else
{
lean_object* v___x_2749_; 
v___x_2749_ = lean_unsigned_to_nat(0u);
v___y_2745_ = v___x_2749_;
goto v___jp_2744_;
}
v___jp_2744_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = lean_mk_empty_array_with_capacity(v___y_2745_);
lean_dec(v___y_2745_);
v___x_2747_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2743_, v___x_2746_, v_t_2742_);
return v___x_2747_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___boxed(lean_object* v_00_u03b1_2750_, lean_object* v_00_u03b2_2751_, lean_object* v_cmp_2752_, lean_object* v_t_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Std_DTreeMap_toArray(v_00_u03b1_2750_, v_00_u03b2_2751_, v_cmp_2752_, v_t_2753_);
lean_dec_ref(v_cmp_2752_);
return v_res_2754_;
}
}
static lean_object* _init_l_Std_DTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray___redArg(lean_object* v_a_2756_, lean_object* v_cmp_2757_){
_start:
{
lean_object* v___f_2758_; lean_object* v___x_2759_; lean_object* v_r_2760_; size_t v_sz_2761_; size_t v___x_2762_; lean_object* v___x_2763_; 
v___f_2758_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2758_, 0, v_cmp_2757_);
v___x_2759_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2760_ = lean_box(1);
v_sz_2761_ = lean_array_size(v_a_2756_);
v___x_2762_ = ((size_t)0ULL);
v___x_2763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2759_, v_a_2756_, v___f_2758_, v_sz_2761_, v___x_2762_, v_r_2760_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray(lean_object* v_00_u03b1_2764_, lean_object* v_00_u03b2_2765_, lean_object* v_a_2766_, lean_object* v_cmp_2767_){
_start:
{
lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v_r_2770_; size_t v_sz_2771_; size_t v___x_2772_; lean_object* v___x_2773_; 
v___f_2768_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2768_, 0, v_cmp_2767_);
v___x_2769_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2770_ = lean_box(1);
v_sz_2771_ = lean_array_size(v_a_2766_);
v___x_2772_ = ((size_t)0ULL);
v___x_2773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2769_, v_a_2766_, v___f_2768_, v_sz_2771_, v___x_2772_, v_r_2770_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_modify___redArg(lean_object* v_cmp_2774_, lean_object* v_t_2775_, lean_object* v_a_2776_, lean_object* v_f_2777_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2774_, v_a_2776_, v_f_2777_, v_t_2775_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_modify(lean_object* v_00_u03b1_2779_, lean_object* v_00_u03b2_2780_, lean_object* v_cmp_2781_, lean_object* v_inst_2782_, lean_object* v_t_2783_, lean_object* v_a_2784_, lean_object* v_f_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2781_, v_a_2784_, v_f_2785_, v_t_2783_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_alter___redArg(lean_object* v_cmp_2787_, lean_object* v_t_2788_, lean_object* v_a_2789_, lean_object* v_f_2790_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_2787_, v_a_2789_, v_f_2790_, v_t_2788_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_alter(lean_object* v_00_u03b1_2792_, lean_object* v_00_u03b2_2793_, lean_object* v_cmp_2794_, lean_object* v_inst_2795_, lean_object* v_t_2796_, lean_object* v_a_2797_, lean_object* v_f_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_2794_, v_a_2797_, v_f_2798_, v_t_2796_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2800_, lean_object* v_mergeFn_2801_, lean_object* v_a_2802_, lean_object* v_x_2803_){
_start:
{
if (lean_obj_tag(v_x_2803_) == 0)
{
lean_object* v___x_2804_; 
lean_dec(v_a_2802_);
lean_dec(v_mergeFn_2801_);
v___x_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_b_u2082_2800_);
return v___x_2804_;
}
else
{
lean_object* v_val_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2813_; 
v_val_2805_ = lean_ctor_get(v_x_2803_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_x_2803_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2807_ = v_x_2803_;
v_isShared_2808_ = v_isSharedCheck_2813_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_val_2805_);
lean_dec(v_x_2803_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2813_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2809_ = lean_apply_3(v_mergeFn_2801_, v_a_2802_, v_val_2805_, v_b_u2082_2800_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2809_);
v___x_2811_ = v___x_2807_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2814_, lean_object* v_cmp_2815_, lean_object* v_t_2816_, lean_object* v_a_2817_, lean_object* v_b_u2082_2818_){
_start:
{
lean_object* v___f_2819_; lean_object* v___x_2820_; 
lean_inc(v_a_2817_);
v___f_2819_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2819_, 0, v_b_u2082_2818_);
lean_closure_set(v___f_2819_, 1, v_mergeFn_2814_);
lean_closure_set(v___f_2819_, 2, v_a_2817_);
v___x_2820_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_2815_, v_a_2817_, v___f_2819_, v_t_2816_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg(lean_object* v_cmp_2821_, lean_object* v_mergeFn_2822_, lean_object* v_t_u2081_2823_, lean_object* v_t_u2082_2824_){
_start:
{
lean_object* v___f_2825_; lean_object* v___x_2826_; 
v___f_2825_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2825_, 0, v_mergeFn_2822_);
lean_closure_set(v___f_2825_, 1, v_cmp_2821_);
v___x_2826_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2825_, v_t_u2081_2823_, v_t_u2082_2824_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith(lean_object* v_00_u03b1_2827_, lean_object* v_00_u03b2_2828_, lean_object* v_cmp_2829_, lean_object* v_inst_2830_, lean_object* v_mergeFn_2831_, lean_object* v_t_u2081_2832_, lean_object* v_t_u2082_2833_){
_start:
{
lean_object* v___f_2834_; lean_object* v___x_2835_; 
v___f_2834_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2834_, 0, v_mergeFn_2831_);
lean_closure_set(v___f_2834_, 1, v_cmp_2829_);
v___x_2835_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2834_, v_t_u2081_2832_, v_t_u2082_2833_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___redArg___lam__0(lean_object* v_x1_2836_, lean_object* v_x2_2837_, lean_object* v_x3_2838_){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2839_, 0, v_x1_2836_);
lean_ctor_set(v___x_2839_, 1, v_x2_2837_);
v___x_2840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v_x3_2838_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___redArg(lean_object* v_t_2842_){
_start:
{
lean_object* v___f_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___f_2843_ = ((lean_object*)(l_Std_DTreeMap_Const_toList___redArg___closed__0));
v___x_2844_ = lean_box(0);
v___x_2845_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2846_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2845_, v___f_2843_, v___x_2844_, v_t_2842_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList(lean_object* v_00_u03b1_2847_, lean_object* v_cmp_2848_, lean_object* v_00_u03b2_2849_, lean_object* v_t_2850_){
_start:
{
lean_object* v___f_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___f_2851_ = ((lean_object*)(l_Std_DTreeMap_Const_toList___redArg___closed__0));
v___x_2852_ = lean_box(0);
v___x_2853_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2854_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2853_, v___f_2851_, v___x_2852_, v_t_2850_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___boxed(lean_object* v_00_u03b1_2855_, lean_object* v_cmp_2856_, lean_object* v_00_u03b2_2857_, lean_object* v_t_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Std_DTreeMap_Const_toList(v_00_u03b1_2855_, v_cmp_2856_, v_00_u03b2_2857_, v_t_2858_);
lean_dec_ref(v_cmp_2856_);
return v_res_2859_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg___lam__0(lean_object* v_cmp_2861_, lean_object* v_a_2862_, lean_object* v_x_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_fst_2865_; lean_object* v_snd_2866_; lean_object* v_r_2867_; lean_object* v___x_2868_; 
v_fst_2865_ = lean_ctor_get(v_a_2862_, 0);
lean_inc(v_fst_2865_);
v_snd_2866_ = lean_ctor_get(v_a_2862_, 1);
lean_inc(v_snd_2866_);
lean_dec_ref(v_a_2862_);
v_r_2867_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2861_, v_fst_2865_, v_snd_2866_, v___y_2864_);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v_r_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg(lean_object* v_l_2869_, lean_object* v_cmp_2870_){
_start:
{
lean_object* v___f_2871_; lean_object* v___x_2872_; lean_object* v_r_2873_; lean_object* v___x_2874_; 
v___f_2871_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2871_, 0, v_cmp_2870_);
v___x_2872_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2873_ = lean_box(1);
v___x_2874_ = l_List_forIn_x27_loop___redArg(v___x_2872_, v___f_2871_, v_l_2869_, v_r_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList(lean_object* v_00_u03b1_2875_, lean_object* v_00_u03b2_2876_, lean_object* v_l_2877_, lean_object* v_cmp_2878_){
_start:
{
lean_object* v___f_2879_; lean_object* v___x_2880_; lean_object* v_r_2881_; lean_object* v___x_2882_; 
v___f_2879_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2879_, 0, v_cmp_2878_);
v___x_2880_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2881_ = lean_box(1);
v___x_2882_ = l_List_forIn_x27_loop___redArg(v___x_2880_, v___f_2879_, v_l_2877_, v_r_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___redArg___lam__0(lean_object* v_acc_2883_, lean_object* v_k_2884_, lean_object* v_v_2885_){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2886_, 0, v_k_2884_);
lean_ctor_set(v___x_2886_, 1, v_v_2885_);
v___x_2887_ = lean_array_push(v_acc_2883_, v___x_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___redArg(lean_object* v_t_2891_){
_start:
{
lean_object* v___f_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___f_2892_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__0));
v___x_2893_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__1));
v___x_2894_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2892_, v___x_2893_, v_t_2891_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray(lean_object* v_00_u03b1_2895_, lean_object* v_cmp_2896_, lean_object* v_00_u03b2_2897_, lean_object* v_t_2898_){
_start:
{
lean_object* v___f_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___f_2899_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__0));
v___x_2900_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__1));
v___x_2901_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2899_, v___x_2900_, v_t_2898_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___boxed(lean_object* v_00_u03b1_2902_, lean_object* v_cmp_2903_, lean_object* v_00_u03b2_2904_, lean_object* v_t_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Std_DTreeMap_Const_toArray(v_00_u03b1_2902_, v_cmp_2903_, v_00_u03b2_2904_, v_t_2905_);
lean_dec_ref(v_cmp_2903_);
return v_res_2906_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray___redArg(lean_object* v_a_2908_, lean_object* v_cmp_2909_){
_start:
{
lean_object* v___f_2910_; lean_object* v___x_2911_; lean_object* v_r_2912_; size_t v_sz_2913_; size_t v___x_2914_; lean_object* v___x_2915_; 
v___f_2910_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2910_, 0, v_cmp_2909_);
v___x_2911_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2912_ = lean_box(1);
v_sz_2913_ = lean_array_size(v_a_2908_);
v___x_2914_ = ((size_t)0ULL);
v___x_2915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2911_, v_a_2908_, v___f_2910_, v_sz_2913_, v___x_2914_, v_r_2912_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray(lean_object* v_00_u03b1_2916_, lean_object* v_00_u03b2_2917_, lean_object* v_a_2918_, lean_object* v_cmp_2919_){
_start:
{
lean_object* v___f_2920_; lean_object* v___x_2921_; lean_object* v_r_2922_; size_t v_sz_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
v___f_2920_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2920_, 0, v_cmp_2919_);
v___x_2921_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2922_ = lean_box(1);
v_sz_2923_ = lean_array_size(v_a_2918_);
v___x_2924_ = ((size_t)0ULL);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2921_, v_a_2918_, v___f_2920_, v_sz_2923_, v___x_2924_, v_r_2922_);
return v___x_2925_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_2927_, lean_object* v_a_2928_, lean_object* v_x_2929_, lean_object* v___y_2930_){
_start:
{
uint8_t v___x_2931_; 
lean_inc(v___y_2930_);
lean_inc(v_a_2928_);
lean_inc_ref(v_cmp_2927_);
v___x_2931_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2927_, v_a_2928_, v___y_2930_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2932_ = lean_box(0);
v___x_2933_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2927_, v_a_2928_, v___x_2932_, v___y_2930_);
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
return v___x_2934_;
}
else
{
lean_object* v___x_2935_; 
lean_dec(v_a_2928_);
lean_dec_ref(v_cmp_2927_);
v___x_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2935_, 0, v___y_2930_);
return v___x_2935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg(lean_object* v_l_2936_, lean_object* v_cmp_2937_){
_start:
{
lean_object* v___f_2938_; lean_object* v___x_2939_; lean_object* v_r_2940_; lean_object* v___x_2941_; 
v___f_2938_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2938_, 0, v_cmp_2937_);
v___x_2939_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2940_ = lean_box(1);
v___x_2941_ = l_List_forIn_x27_loop___redArg(v___x_2939_, v___f_2938_, v_l_2936_, v_r_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList(lean_object* v_00_u03b1_2942_, lean_object* v_l_2943_, lean_object* v_cmp_2944_){
_start:
{
lean_object* v___f_2945_; lean_object* v___x_2946_; lean_object* v_r_2947_; lean_object* v___x_2948_; 
v___f_2945_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2945_, 0, v_cmp_2944_);
v___x_2946_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2947_ = lean_box(1);
v___x_2948_ = l_List_forIn_x27_loop___redArg(v___x_2946_, v___f_2945_, v_l_2943_, v_r_2947_);
return v___x_2948_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray___redArg(lean_object* v_a_2950_, lean_object* v_cmp_2951_){
_start:
{
lean_object* v___f_2952_; lean_object* v___x_2953_; lean_object* v_r_2954_; size_t v_sz_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v___f_2952_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2952_, 0, v_cmp_2951_);
v___x_2953_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2954_ = lean_box(1);
v_sz_2955_ = lean_array_size(v_a_2950_);
v___x_2956_ = ((size_t)0ULL);
v___x_2957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2953_, v_a_2950_, v___f_2952_, v_sz_2955_, v___x_2956_, v_r_2954_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray(lean_object* v_00_u03b1_2958_, lean_object* v_a_2959_, lean_object* v_cmp_2960_){
_start:
{
lean_object* v___f_2961_; lean_object* v___x_2962_; lean_object* v_r_2963_; size_t v_sz_2964_; size_t v___x_2965_; lean_object* v___x_2966_; 
v___f_2961_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2961_, 0, v_cmp_2960_);
v___x_2962_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2963_ = lean_box(1);
v_sz_2964_ = lean_array_size(v_a_2959_);
v___x_2965_ = ((size_t)0ULL);
v___x_2966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2962_, v_a_2959_, v___f_2961_, v_sz_2964_, v___x_2965_, v_r_2963_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_modify___redArg(lean_object* v_cmp_2967_, lean_object* v_t_2968_, lean_object* v_a_2969_, lean_object* v_f_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2967_, v_a_2969_, v_f_2970_, v_t_2968_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_modify(lean_object* v_00_u03b1_2972_, lean_object* v_cmp_2973_, lean_object* v_00_u03b2_2974_, lean_object* v_t_2975_, lean_object* v_a_2976_, lean_object* v_f_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2973_, v_a_2976_, v_f_2977_, v_t_2975_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_alter___redArg(lean_object* v_cmp_2979_, lean_object* v_t_2980_, lean_object* v_a_2981_, lean_object* v_f_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2979_, v_a_2981_, v_f_2982_, v_t_2980_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_alter(lean_object* v_00_u03b1_2984_, lean_object* v_cmp_2985_, lean_object* v_00_u03b2_2986_, lean_object* v_t_2987_, lean_object* v_a_2988_, lean_object* v_f_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2985_, v_a_2988_, v_f_2989_, v_t_2987_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2991_, lean_object* v_cmp_2992_, lean_object* v_t_2993_, lean_object* v_a_2994_, lean_object* v_b_u2082_2995_){
_start:
{
lean_object* v___f_2996_; lean_object* v___x_2997_; 
lean_inc(v_a_2994_);
v___f_2996_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2996_, 0, v_b_u2082_2995_);
lean_closure_set(v___f_2996_, 1, v_mergeFn_2991_);
lean_closure_set(v___f_2996_, 2, v_a_2994_);
v___x_2997_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2992_, v_a_2994_, v___f_2996_, v_t_2993_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith___redArg(lean_object* v_cmp_2998_, lean_object* v_mergeFn_2999_, lean_object* v_t_u2081_3000_, lean_object* v_t_u2082_3001_){
_start:
{
lean_object* v___f_3002_; lean_object* v___x_3003_; 
v___f_3002_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3002_, 0, v_mergeFn_2999_);
lean_closure_set(v___f_3002_, 1, v_cmp_2998_);
v___x_3003_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3002_, v_t_u2081_3000_, v_t_u2082_3001_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith(lean_object* v_00_u03b1_3004_, lean_object* v_cmp_3005_, lean_object* v_00_u03b2_3006_, lean_object* v_mergeFn_3007_, lean_object* v_t_u2081_3008_, lean_object* v_t_u2082_3009_){
_start:
{
lean_object* v___f_3010_; lean_object* v___x_3011_; 
v___f_3010_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3010_, 0, v_mergeFn_3007_);
lean_closure_set(v___f_3010_, 1, v_cmp_3005_);
v___x_3011_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3010_, v_t_u2081_3008_, v_t_u2082_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_3012_, lean_object* v_x_3013_, lean_object* v_____s_3014_){
_start:
{
lean_object* v_fst_3015_; lean_object* v_snd_3016_; lean_object* v_r_3017_; lean_object* v___x_3018_; 
v_fst_3015_ = lean_ctor_get(v_x_3013_, 0);
lean_inc(v_fst_3015_);
v_snd_3016_ = lean_ctor_get(v_x_3013_, 1);
lean_inc(v_snd_3016_);
lean_dec_ref(v_x_3013_);
v_r_3017_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3012_, v_fst_3015_, v_snd_3016_, v_____s_3014_);
v___x_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3018_, 0, v_r_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany___redArg(lean_object* v_cmp_3019_, lean_object* v_inst_3020_, lean_object* v_t_3021_, lean_object* v_l_3022_){
_start:
{
lean_object* v___f_3023_; lean_object* v___x_3024_; 
v___f_3023_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3023_, 0, v_cmp_3019_);
v___x_3024_ = lean_apply_4(v_inst_3020_, lean_box(0), v_l_3022_, v_t_3021_, v___f_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany(lean_object* v_00_u03b1_3025_, lean_object* v_00_u03b2_3026_, lean_object* v_cmp_3027_, lean_object* v_00_u03c1_3028_, lean_object* v_inst_3029_, lean_object* v_t_3030_, lean_object* v_l_3031_){
_start:
{
lean_object* v___f_3032_; lean_object* v___x_3033_; 
v___f_3032_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3032_, 0, v_cmp_3027_);
v___x_3033_ = lean_apply_4(v_inst_3029_, lean_box(0), v_l_3031_, v_t_3030_, v___f_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew___redArg___lam__0(lean_object* v_cmp_3034_, lean_object* v_x_3035_, lean_object* v_____s_3036_){
_start:
{
lean_object* v_fst_3037_; lean_object* v_snd_3038_; uint8_t v___x_3039_; 
v_fst_3037_ = lean_ctor_get(v_x_3035_, 0);
lean_inc(v_fst_3037_);
v_snd_3038_ = lean_ctor_get(v_x_3035_, 1);
lean_inc(v_snd_3038_);
lean_dec_ref(v_x_3035_);
lean_inc(v_____s_3036_);
lean_inc(v_fst_3037_);
lean_inc_ref(v_cmp_3034_);
v___x_3039_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3034_, v_fst_3037_, v_____s_3036_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3034_, v_fst_3037_, v_snd_3038_, v_____s_3036_);
v___x_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
return v___x_3041_;
}
else
{
lean_object* v___x_3042_; 
lean_dec(v_snd_3038_);
lean_dec(v_fst_3037_);
lean_dec_ref(v_cmp_3034_);
v___x_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3042_, 0, v_____s_3036_);
return v___x_3042_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew___redArg(lean_object* v_cmp_3043_, lean_object* v_inst_3044_, lean_object* v_t_3045_, lean_object* v_l_3046_){
_start:
{
lean_object* v___f_3047_; lean_object* v___x_3048_; 
v___f_3047_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertManyIfNew___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3047_, 0, v_cmp_3043_);
v___x_3048_ = lean_apply_4(v_inst_3044_, lean_box(0), v_l_3046_, v_t_3045_, v___f_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew(lean_object* v_00_u03b1_3049_, lean_object* v_00_u03b2_3050_, lean_object* v_cmp_3051_, lean_object* v_00_u03c1_3052_, lean_object* v_inst_3053_, lean_object* v_t_3054_, lean_object* v_l_3055_){
_start:
{
lean_object* v___f_3056_; lean_object* v___x_3057_; 
v___f_3056_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertManyIfNew___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3056_, 0, v_cmp_3051_);
v___x_3057_ = lean_apply_4(v_inst_3053_, lean_box(0), v_l_3055_, v_t_3054_, v___f_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(lean_object* v_cmp_3058_, lean_object* v_k_3059_, lean_object* v_v_3060_, lean_object* v_t_3061_){
_start:
{
if (lean_obj_tag(v_t_3061_) == 0)
{
lean_object* v_size_3062_; lean_object* v_k_3063_; lean_object* v_v_3064_; lean_object* v_l_3065_; lean_object* v_r_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3347_; 
v_size_3062_ = lean_ctor_get(v_t_3061_, 0);
v_k_3063_ = lean_ctor_get(v_t_3061_, 1);
v_v_3064_ = lean_ctor_get(v_t_3061_, 2);
v_l_3065_ = lean_ctor_get(v_t_3061_, 3);
v_r_3066_ = lean_ctor_get(v_t_3061_, 4);
v_isSharedCheck_3347_ = !lean_is_exclusive(v_t_3061_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3068_ = v_t_3061_;
v_isShared_3069_ = v_isSharedCheck_3347_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_r_3066_);
lean_inc(v_l_3065_);
lean_inc(v_v_3064_);
lean_inc(v_k_3063_);
lean_inc(v_size_3062_);
lean_dec(v_t_3061_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3347_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3070_; uint8_t v___x_3071_; 
lean_inc_ref(v_cmp_3058_);
lean_inc(v_k_3063_);
lean_inc(v_k_3059_);
v___x_3070_ = lean_apply_2(v_cmp_3058_, v_k_3059_, v_k_3063_);
v___x_3071_ = lean_unbox(v___x_3070_);
switch(v___x_3071_)
{
case 0:
{
lean_object* v_impl_3072_; lean_object* v___x_3073_; 
lean_dec(v_size_3062_);
v_impl_3072_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3058_, v_k_3059_, v_v_3060_, v_l_3065_);
v___x_3073_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3066_) == 0)
{
lean_object* v_size_3074_; lean_object* v_size_3075_; lean_object* v_k_3076_; lean_object* v_v_3077_; lean_object* v_l_3078_; lean_object* v_r_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; uint8_t v___x_3082_; 
v_size_3074_ = lean_ctor_get(v_r_3066_, 0);
v_size_3075_ = lean_ctor_get(v_impl_3072_, 0);
lean_inc(v_size_3075_);
v_k_3076_ = lean_ctor_get(v_impl_3072_, 1);
lean_inc(v_k_3076_);
v_v_3077_ = lean_ctor_get(v_impl_3072_, 2);
lean_inc(v_v_3077_);
v_l_3078_ = lean_ctor_get(v_impl_3072_, 3);
lean_inc(v_l_3078_);
v_r_3079_ = lean_ctor_get(v_impl_3072_, 4);
lean_inc(v_r_3079_);
v___x_3080_ = lean_unsigned_to_nat(3u);
v___x_3081_ = lean_nat_mul(v___x_3080_, v_size_3074_);
v___x_3082_ = lean_nat_dec_lt(v___x_3081_, v_size_3075_);
lean_dec(v___x_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
lean_dec(v_r_3079_);
lean_dec(v_l_3078_);
lean_dec(v_v_3077_);
lean_dec(v_k_3076_);
v___x_3083_ = lean_nat_add(v___x_3073_, v_size_3075_);
lean_dec(v_size_3075_);
v___x_3084_ = lean_nat_add(v___x_3083_, v_size_3074_);
lean_dec(v___x_3083_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 3, v_impl_3072_);
lean_ctor_set(v___x_3068_, 0, v___x_3084_);
v___x_3086_ = v___x_3068_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3084_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3087_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3087_, 3, v_impl_3072_);
lean_ctor_set(v_reuseFailAlloc_3087_, 4, v_r_3066_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
else
{
lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3153_; 
v_isSharedCheck_3153_ = !lean_is_exclusive(v_impl_3072_);
if (v_isSharedCheck_3153_ == 0)
{
lean_object* v_unused_3154_; lean_object* v_unused_3155_; lean_object* v_unused_3156_; lean_object* v_unused_3157_; lean_object* v_unused_3158_; 
v_unused_3154_ = lean_ctor_get(v_impl_3072_, 4);
lean_dec(v_unused_3154_);
v_unused_3155_ = lean_ctor_get(v_impl_3072_, 3);
lean_dec(v_unused_3155_);
v_unused_3156_ = lean_ctor_get(v_impl_3072_, 2);
lean_dec(v_unused_3156_);
v_unused_3157_ = lean_ctor_get(v_impl_3072_, 1);
lean_dec(v_unused_3157_);
v_unused_3158_ = lean_ctor_get(v_impl_3072_, 0);
lean_dec(v_unused_3158_);
v___x_3089_ = v_impl_3072_;
v_isShared_3090_ = v_isSharedCheck_3153_;
goto v_resetjp_3088_;
}
else
{
lean_dec(v_impl_3072_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3153_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v_size_3091_; lean_object* v_size_3092_; lean_object* v_k_3093_; lean_object* v_v_3094_; lean_object* v_l_3095_; lean_object* v_r_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v_size_3091_ = lean_ctor_get(v_l_3078_, 0);
v_size_3092_ = lean_ctor_get(v_r_3079_, 0);
v_k_3093_ = lean_ctor_get(v_r_3079_, 1);
v_v_3094_ = lean_ctor_get(v_r_3079_, 2);
v_l_3095_ = lean_ctor_get(v_r_3079_, 3);
v_r_3096_ = lean_ctor_get(v_r_3079_, 4);
v___x_3097_ = lean_unsigned_to_nat(2u);
v___x_3098_ = lean_nat_mul(v___x_3097_, v_size_3091_);
v___x_3099_ = lean_nat_dec_lt(v_size_3092_, v___x_3098_);
lean_dec(v___x_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3128_; 
lean_inc(v_r_3096_);
lean_inc(v_l_3095_);
lean_inc(v_v_3094_);
lean_inc(v_k_3093_);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_r_3079_);
if (v_isSharedCheck_3128_ == 0)
{
lean_object* v_unused_3129_; lean_object* v_unused_3130_; lean_object* v_unused_3131_; lean_object* v_unused_3132_; lean_object* v_unused_3133_; 
v_unused_3129_ = lean_ctor_get(v_r_3079_, 4);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v_r_3079_, 3);
lean_dec(v_unused_3130_);
v_unused_3131_ = lean_ctor_get(v_r_3079_, 2);
lean_dec(v_unused_3131_);
v_unused_3132_ = lean_ctor_get(v_r_3079_, 1);
lean_dec(v_unused_3132_);
v_unused_3133_ = lean_ctor_get(v_r_3079_, 0);
lean_dec(v_unused_3133_);
v___x_3101_ = v_r_3079_;
v_isShared_3102_ = v_isSharedCheck_3128_;
goto v_resetjp_3100_;
}
else
{
lean_dec(v_r_3079_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3128_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___x_3116_; lean_object* v___y_3118_; 
v___x_3103_ = lean_nat_add(v___x_3073_, v_size_3075_);
lean_dec(v_size_3075_);
v___x_3104_ = lean_nat_add(v___x_3103_, v_size_3074_);
lean_dec(v___x_3103_);
v___x_3116_ = lean_nat_add(v___x_3073_, v_size_3091_);
if (lean_obj_tag(v_l_3095_) == 0)
{
lean_object* v_size_3126_; 
v_size_3126_ = lean_ctor_get(v_l_3095_, 0);
lean_inc(v_size_3126_);
v___y_3118_ = v_size_3126_;
goto v___jp_3117_;
}
else
{
lean_object* v___x_3127_; 
v___x_3127_ = lean_unsigned_to_nat(0u);
v___y_3118_ = v___x_3127_;
goto v___jp_3117_;
}
v___jp_3105_:
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3109_ = lean_nat_add(v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec(v___y_3107_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 4, v_r_3066_);
lean_ctor_set(v___x_3101_, 3, v_r_3096_);
lean_ctor_set(v___x_3101_, 2, v_v_3064_);
lean_ctor_set(v___x_3101_, 1, v_k_3063_);
lean_ctor_set(v___x_3101_, 0, v___x_3109_);
v___x_3111_ = v___x_3101_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3109_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3115_, 3, v_r_3096_);
lean_ctor_set(v_reuseFailAlloc_3115_, 4, v_r_3066_);
v___x_3111_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3113_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 4, v___x_3111_);
lean_ctor_set(v___x_3089_, 3, v___y_3106_);
lean_ctor_set(v___x_3089_, 2, v_v_3094_);
lean_ctor_set(v___x_3089_, 1, v_k_3093_);
lean_ctor_set(v___x_3089_, 0, v___x_3104_);
v___x_3113_ = v___x_3089_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_k_3093_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_v_3094_);
lean_ctor_set(v_reuseFailAlloc_3114_, 3, v___y_3106_);
lean_ctor_set(v_reuseFailAlloc_3114_, 4, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
v___jp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3119_ = lean_nat_add(v___x_3116_, v___y_3118_);
lean_dec(v___y_3118_);
lean_dec(v___x_3116_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 4, v_l_3095_);
lean_ctor_set(v___x_3068_, 3, v_l_3078_);
lean_ctor_set(v___x_3068_, 2, v_v_3077_);
lean_ctor_set(v___x_3068_, 1, v_k_3076_);
lean_ctor_set(v___x_3068_, 0, v___x_3119_);
v___x_3121_ = v___x_3068_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_k_3076_);
lean_ctor_set(v_reuseFailAlloc_3125_, 2, v_v_3077_);
lean_ctor_set(v_reuseFailAlloc_3125_, 3, v_l_3078_);
lean_ctor_set(v_reuseFailAlloc_3125_, 4, v_l_3095_);
v___x_3121_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_nat_add(v___x_3073_, v_size_3074_);
if (lean_obj_tag(v_r_3096_) == 0)
{
lean_object* v_size_3123_; 
v_size_3123_ = lean_ctor_get(v_r_3096_, 0);
lean_inc(v_size_3123_);
v___y_3106_ = v___x_3121_;
v___y_3107_ = v___x_3122_;
v___y_3108_ = v_size_3123_;
goto v___jp_3105_;
}
else
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_unsigned_to_nat(0u);
v___y_3106_ = v___x_3121_;
v___y_3107_ = v___x_3122_;
v___y_3108_ = v___x_3124_;
goto v___jp_3105_;
}
}
}
}
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3139_; 
lean_del_object(v___x_3068_);
v___x_3134_ = lean_nat_add(v___x_3073_, v_size_3075_);
lean_dec(v_size_3075_);
v___x_3135_ = lean_nat_add(v___x_3134_, v_size_3074_);
lean_dec(v___x_3134_);
v___x_3136_ = lean_nat_add(v___x_3073_, v_size_3074_);
v___x_3137_ = lean_nat_add(v___x_3136_, v_size_3092_);
lean_dec(v___x_3136_);
lean_inc_ref(v_r_3066_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 4, v_r_3066_);
lean_ctor_set(v___x_3089_, 3, v_r_3079_);
lean_ctor_set(v___x_3089_, 2, v_v_3064_);
lean_ctor_set(v___x_3089_, 1, v_k_3063_);
lean_ctor_set(v___x_3089_, 0, v___x_3137_);
v___x_3139_ = v___x_3089_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3152_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3152_, 3, v_r_3079_);
lean_ctor_set(v_reuseFailAlloc_3152_, 4, v_r_3066_);
v___x_3139_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
v_isSharedCheck_3146_ = !lean_is_exclusive(v_r_3066_);
if (v_isSharedCheck_3146_ == 0)
{
lean_object* v_unused_3147_; lean_object* v_unused_3148_; lean_object* v_unused_3149_; lean_object* v_unused_3150_; lean_object* v_unused_3151_; 
v_unused_3147_ = lean_ctor_get(v_r_3066_, 4);
lean_dec(v_unused_3147_);
v_unused_3148_ = lean_ctor_get(v_r_3066_, 3);
lean_dec(v_unused_3148_);
v_unused_3149_ = lean_ctor_get(v_r_3066_, 2);
lean_dec(v_unused_3149_);
v_unused_3150_ = lean_ctor_get(v_r_3066_, 1);
lean_dec(v_unused_3150_);
v_unused_3151_ = lean_ctor_get(v_r_3066_, 0);
lean_dec(v_unused_3151_);
v___x_3141_ = v_r_3066_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_dec(v_r_3066_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 4, v___x_3139_);
lean_ctor_set(v___x_3141_, 3, v_l_3078_);
lean_ctor_set(v___x_3141_, 2, v_v_3077_);
lean_ctor_set(v___x_3141_, 1, v_k_3076_);
lean_ctor_set(v___x_3141_, 0, v___x_3135_);
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3135_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_k_3076_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_v_3077_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v_l_3078_);
lean_ctor_set(v_reuseFailAlloc_3145_, 4, v___x_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3159_; 
v_l_3159_ = lean_ctor_get(v_impl_3072_, 3);
lean_inc(v_l_3159_);
if (lean_obj_tag(v_l_3159_) == 0)
{
lean_object* v_r_3160_; lean_object* v_k_3161_; lean_object* v_v_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3173_; 
v_r_3160_ = lean_ctor_get(v_impl_3072_, 4);
v_k_3161_ = lean_ctor_get(v_impl_3072_, 1);
v_v_3162_ = lean_ctor_get(v_impl_3072_, 2);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_impl_3072_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; lean_object* v_unused_3175_; 
v_unused_3174_ = lean_ctor_get(v_impl_3072_, 3);
lean_dec(v_unused_3174_);
v_unused_3175_ = lean_ctor_get(v_impl_3072_, 0);
lean_dec(v_unused_3175_);
v___x_3164_ = v_impl_3072_;
v_isShared_3165_ = v_isSharedCheck_3173_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_r_3160_);
lean_inc(v_v_3162_);
lean_inc(v_k_3161_);
lean_dec(v_impl_3072_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3173_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3166_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3160_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 3, v_r_3160_);
lean_ctor_set(v___x_3164_, 2, v_v_3064_);
lean_ctor_set(v___x_3164_, 1, v_k_3063_);
lean_ctor_set(v___x_3164_, 0, v___x_3073_);
v___x_3168_ = v___x_3164_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_r_3160_);
lean_ctor_set(v_reuseFailAlloc_3172_, 4, v_r_3160_);
v___x_3168_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3170_; 
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 4, v___x_3168_);
lean_ctor_set(v___x_3068_, 3, v_l_3159_);
lean_ctor_set(v___x_3068_, 2, v_v_3162_);
lean_ctor_set(v___x_3068_, 1, v_k_3161_);
lean_ctor_set(v___x_3068_, 0, v___x_3166_);
v___x_3170_ = v___x_3068_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3166_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3171_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3171_, 3, v_l_3159_);
lean_ctor_set(v_reuseFailAlloc_3171_, 4, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
else
{
lean_object* v_r_3176_; 
v_r_3176_ = lean_ctor_get(v_impl_3072_, 4);
lean_inc(v_r_3176_);
if (lean_obj_tag(v_r_3176_) == 0)
{
lean_object* v_k_3177_; lean_object* v_v_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3201_; 
v_k_3177_ = lean_ctor_get(v_impl_3072_, 1);
v_v_3178_ = lean_ctor_get(v_impl_3072_, 2);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_impl_3072_);
if (v_isSharedCheck_3201_ == 0)
{
lean_object* v_unused_3202_; lean_object* v_unused_3203_; lean_object* v_unused_3204_; 
v_unused_3202_ = lean_ctor_get(v_impl_3072_, 4);
lean_dec(v_unused_3202_);
v_unused_3203_ = lean_ctor_get(v_impl_3072_, 3);
lean_dec(v_unused_3203_);
v_unused_3204_ = lean_ctor_get(v_impl_3072_, 0);
lean_dec(v_unused_3204_);
v___x_3180_ = v_impl_3072_;
v_isShared_3181_ = v_isSharedCheck_3201_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_v_3178_);
lean_inc(v_k_3177_);
lean_dec(v_impl_3072_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3201_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v_k_3182_; lean_object* v_v_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3197_; 
v_k_3182_ = lean_ctor_get(v_r_3176_, 1);
v_v_3183_ = lean_ctor_get(v_r_3176_, 2);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_r_3176_);
if (v_isSharedCheck_3197_ == 0)
{
lean_object* v_unused_3198_; lean_object* v_unused_3199_; lean_object* v_unused_3200_; 
v_unused_3198_ = lean_ctor_get(v_r_3176_, 4);
lean_dec(v_unused_3198_);
v_unused_3199_ = lean_ctor_get(v_r_3176_, 3);
lean_dec(v_unused_3199_);
v_unused_3200_ = lean_ctor_get(v_r_3176_, 0);
lean_dec(v_unused_3200_);
v___x_3185_ = v_r_3176_;
v_isShared_3186_ = v_isSharedCheck_3197_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_v_3183_);
lean_inc(v_k_3182_);
lean_dec(v_r_3176_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3197_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3187_ = lean_unsigned_to_nat(3u);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 4, v_l_3159_);
lean_ctor_set(v___x_3185_, 3, v_l_3159_);
lean_ctor_set(v___x_3185_, 2, v_v_3178_);
lean_ctor_set(v___x_3185_, 1, v_k_3177_);
lean_ctor_set(v___x_3185_, 0, v___x_3073_);
v___x_3189_ = v___x_3185_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3196_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3196_, 3, v_l_3159_);
lean_ctor_set(v_reuseFailAlloc_3196_, 4, v_l_3159_);
v___x_3189_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3191_; 
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 4, v_l_3159_);
lean_ctor_set(v___x_3180_, 2, v_v_3064_);
lean_ctor_set(v___x_3180_, 1, v_k_3063_);
lean_ctor_set(v___x_3180_, 0, v___x_3073_);
v___x_3191_ = v___x_3180_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3195_, 3, v_l_3159_);
lean_ctor_set(v_reuseFailAlloc_3195_, 4, v_l_3159_);
v___x_3191_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3193_; 
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 4, v___x_3191_);
lean_ctor_set(v___x_3068_, 3, v___x_3189_);
lean_ctor_set(v___x_3068_, 2, v_v_3183_);
lean_ctor_set(v___x_3068_, 1, v_k_3182_);
lean_ctor_set(v___x_3068_, 0, v___x_3187_);
v___x_3193_ = v___x_3068_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_k_3182_);
lean_ctor_set(v_reuseFailAlloc_3194_, 2, v_v_3183_);
lean_ctor_set(v_reuseFailAlloc_3194_, 3, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3194_, 4, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
}
}
else
{
lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3205_ = lean_unsigned_to_nat(2u);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 4, v_r_3176_);
lean_ctor_set(v___x_3068_, 3, v_impl_3072_);
lean_ctor_set(v___x_3068_, 0, v___x_3205_);
v___x_3207_ = v___x_3068_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3205_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3208_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3208_, 3, v_impl_3072_);
lean_ctor_set(v_reuseFailAlloc_3208_, 4, v_r_3176_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3210_; 
lean_dec(v_v_3064_);
lean_dec(v_k_3063_);
lean_dec_ref(v_cmp_3058_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 2, v_v_3060_);
lean_ctor_set(v___x_3068_, 1, v_k_3059_);
v___x_3210_ = v___x_3068_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_size_3062_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_k_3059_);
lean_ctor_set(v_reuseFailAlloc_3211_, 2, v_v_3060_);
lean_ctor_set(v_reuseFailAlloc_3211_, 3, v_l_3065_);
lean_ctor_set(v_reuseFailAlloc_3211_, 4, v_r_3066_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
default: 
{
lean_object* v_impl_3212_; lean_object* v___x_3213_; 
lean_dec(v_size_3062_);
v_impl_3212_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3058_, v_k_3059_, v_v_3060_, v_r_3066_);
v___x_3213_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3065_) == 0)
{
lean_object* v_size_3214_; lean_object* v_size_3215_; lean_object* v_k_3216_; lean_object* v_v_3217_; lean_object* v_l_3218_; lean_object* v_r_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v_size_3214_ = lean_ctor_get(v_l_3065_, 0);
v_size_3215_ = lean_ctor_get(v_impl_3212_, 0);
lean_inc(v_size_3215_);
v_k_3216_ = lean_ctor_get(v_impl_3212_, 1);
lean_inc(v_k_3216_);
v_v_3217_ = lean_ctor_get(v_impl_3212_, 2);
lean_inc(v_v_3217_);
v_l_3218_ = lean_ctor_get(v_impl_3212_, 3);
lean_inc(v_l_3218_);
v_r_3219_ = lean_ctor_get(v_impl_3212_, 4);
lean_inc(v_r_3219_);
v___x_3220_ = lean_unsigned_to_nat(3u);
v___x_3221_ = lean_nat_mul(v___x_3220_, v_size_3214_);
v___x_3222_ = lean_nat_dec_lt(v___x_3221_, v_size_3215_);
lean_dec(v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
lean_dec(v_r_3219_);
lean_dec(v_l_3218_);
lean_dec(v_v_3217_);
lean_dec(v_k_3216_);
v___x_3223_ = lean_nat_add(v___x_3213_, v_size_3214_);
v___x_3224_ = lean_nat_add(v___x_3223_, v_size_3215_);
lean_dec(v_size_3215_);
lean_dec(v___x_3223_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 4, v_impl_3212_);
lean_ctor_set(v___x_3068_, 0, v___x_3224_);
v___x_3226_ = v___x_3068_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3227_, 3, v_l_3065_);
lean_ctor_set(v_reuseFailAlloc_3227_, 4, v_impl_3212_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
else
{
lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3291_; 
v_isSharedCheck_3291_ = !lean_is_exclusive(v_impl_3212_);
if (v_isSharedCheck_3291_ == 0)
{
lean_object* v_unused_3292_; lean_object* v_unused_3293_; lean_object* v_unused_3294_; lean_object* v_unused_3295_; lean_object* v_unused_3296_; 
v_unused_3292_ = lean_ctor_get(v_impl_3212_, 4);
lean_dec(v_unused_3292_);
v_unused_3293_ = lean_ctor_get(v_impl_3212_, 3);
lean_dec(v_unused_3293_);
v_unused_3294_ = lean_ctor_get(v_impl_3212_, 2);
lean_dec(v_unused_3294_);
v_unused_3295_ = lean_ctor_get(v_impl_3212_, 1);
lean_dec(v_unused_3295_);
v_unused_3296_ = lean_ctor_get(v_impl_3212_, 0);
lean_dec(v_unused_3296_);
v___x_3229_ = v_impl_3212_;
v_isShared_3230_ = v_isSharedCheck_3291_;
goto v_resetjp_3228_;
}
else
{
lean_dec(v_impl_3212_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3291_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v_size_3231_; lean_object* v_k_3232_; lean_object* v_v_3233_; lean_object* v_l_3234_; lean_object* v_r_3235_; lean_object* v_size_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v_size_3231_ = lean_ctor_get(v_l_3218_, 0);
v_k_3232_ = lean_ctor_get(v_l_3218_, 1);
v_v_3233_ = lean_ctor_get(v_l_3218_, 2);
v_l_3234_ = lean_ctor_get(v_l_3218_, 3);
v_r_3235_ = lean_ctor_get(v_l_3218_, 4);
v_size_3236_ = lean_ctor_get(v_r_3219_, 0);
v___x_3237_ = lean_unsigned_to_nat(2u);
v___x_3238_ = lean_nat_mul(v___x_3237_, v_size_3236_);
v___x_3239_ = lean_nat_dec_lt(v_size_3231_, v___x_3238_);
lean_dec(v___x_3238_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3267_; 
lean_inc(v_r_3235_);
lean_inc(v_l_3234_);
lean_inc(v_v_3233_);
lean_inc(v_k_3232_);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_l_3218_);
if (v_isSharedCheck_3267_ == 0)
{
lean_object* v_unused_3268_; lean_object* v_unused_3269_; lean_object* v_unused_3270_; lean_object* v_unused_3271_; lean_object* v_unused_3272_; 
v_unused_3268_ = lean_ctor_get(v_l_3218_, 4);
lean_dec(v_unused_3268_);
v_unused_3269_ = lean_ctor_get(v_l_3218_, 3);
lean_dec(v_unused_3269_);
v_unused_3270_ = lean_ctor_get(v_l_3218_, 2);
lean_dec(v_unused_3270_);
v_unused_3271_ = lean_ctor_get(v_l_3218_, 1);
lean_dec(v_unused_3271_);
v_unused_3272_ = lean_ctor_get(v_l_3218_, 0);
lean_dec(v_unused_3272_);
v___x_3241_ = v_l_3218_;
v_isShared_3242_ = v_isSharedCheck_3267_;
goto v_resetjp_3240_;
}
else
{
lean_dec(v_l_3218_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3267_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3257_; 
v___x_3243_ = lean_nat_add(v___x_3213_, v_size_3214_);
v___x_3244_ = lean_nat_add(v___x_3243_, v_size_3215_);
lean_dec(v_size_3215_);
if (lean_obj_tag(v_l_3234_) == 0)
{
lean_object* v_size_3265_; 
v_size_3265_ = lean_ctor_get(v_l_3234_, 0);
lean_inc(v_size_3265_);
v___y_3257_ = v_size_3265_;
goto v___jp_3256_;
}
else
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_unsigned_to_nat(0u);
v___y_3257_ = v___x_3266_;
goto v___jp_3256_;
}
v___jp_3245_:
{
lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3249_ = lean_nat_add(v___y_3246_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec(v___y_3246_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 4, v_r_3219_);
lean_ctor_set(v___x_3241_, 3, v_r_3235_);
lean_ctor_set(v___x_3241_, 2, v_v_3217_);
lean_ctor_set(v___x_3241_, 1, v_k_3216_);
lean_ctor_set(v___x_3241_, 0, v___x_3249_);
v___x_3251_ = v___x_3241_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_k_3216_);
lean_ctor_set(v_reuseFailAlloc_3255_, 2, v_v_3217_);
lean_ctor_set(v_reuseFailAlloc_3255_, 3, v_r_3235_);
lean_ctor_set(v_reuseFailAlloc_3255_, 4, v_r_3219_);
v___x_3251_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
lean_object* v___x_3253_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___x_3251_);
lean_ctor_set(v___x_3229_, 3, v___y_3247_);
lean_ctor_set(v___x_3229_, 2, v_v_3233_);
lean_ctor_set(v___x_3229_, 1, v_k_3232_);
lean_ctor_set(v___x_3229_, 0, v___x_3244_);
v___x_3253_ = v___x_3229_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v_k_3232_);
lean_ctor_set(v_reuseFailAlloc_3254_, 2, v_v_3233_);
lean_ctor_set(v_reuseFailAlloc_3254_, 3, v___y_3247_);
lean_ctor_set(v_reuseFailAlloc_3254_, 4, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
v___jp_3256_:
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3258_ = lean_nat_add(v___x_3243_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec(v___x_3243_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 4, v_l_3234_);
lean_ctor_set(v___x_3068_, 0, v___x_3258_);
v___x_3260_ = v___x_3068_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3258_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3264_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3264_, 3, v_l_3065_);
lean_ctor_set(v_reuseFailAlloc_3264_, 4, v_l_3234_);
v___x_3260_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_nat_add(v___x_3213_, v_size_3236_);
if (lean_obj_tag(v_r_3235_) == 0)
{
lean_object* v_size_3262_; 
v_size_3262_ = lean_ctor_get(v_r_3235_, 0);
lean_inc(v_size_3262_);
v___y_3246_ = v___x_3261_;
v___y_3247_ = v___x_3260_;
v___y_3248_ = v_size_3262_;
goto v___jp_3245_;
}
else
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_unsigned_to_nat(0u);
v___y_3246_ = v___x_3261_;
v___y_3247_ = v___x_3260_;
v___y_3248_ = v___x_3263_;
goto v___jp_3245_;
}
}
}
}
}
else
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3277_; 
lean_del_object(v___x_3068_);
v___x_3273_ = lean_nat_add(v___x_3213_, v_size_3214_);
v___x_3274_ = lean_nat_add(v___x_3273_, v_size_3215_);
lean_dec(v_size_3215_);
v___x_3275_ = lean_nat_add(v___x_3273_, v_size_3231_);
lean_dec(v___x_3273_);
lean_inc_ref(v_l_3065_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v_l_3218_);
lean_ctor_set(v___x_3229_, 3, v_l_3065_);
lean_ctor_set(v___x_3229_, 2, v_v_3064_);
lean_ctor_set(v___x_3229_, 1, v_k_3063_);
lean_ctor_set(v___x_3229_, 0, v___x_3275_);
v___x_3277_ = v___x_3229_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3275_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3290_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3290_, 3, v_l_3065_);
lean_ctor_set(v_reuseFailAlloc_3290_, 4, v_l_3218_);
v___x_3277_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
v_isSharedCheck_3284_ = !lean_is_exclusive(v_l_3065_);
if (v_isSharedCheck_3284_ == 0)
{
lean_object* v_unused_3285_; lean_object* v_unused_3286_; lean_object* v_unused_3287_; lean_object* v_unused_3288_; lean_object* v_unused_3289_; 
v_unused_3285_ = lean_ctor_get(v_l_3065_, 4);
lean_dec(v_unused_3285_);
v_unused_3286_ = lean_ctor_get(v_l_3065_, 3);
lean_dec(v_unused_3286_);
v_unused_3287_ = lean_ctor_get(v_l_3065_, 2);
lean_dec(v_unused_3287_);
v_unused_3288_ = lean_ctor_get(v_l_3065_, 1);
lean_dec(v_unused_3288_);
v_unused_3289_ = lean_ctor_get(v_l_3065_, 0);
lean_dec(v_unused_3289_);
v___x_3279_ = v_l_3065_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_dec(v_l_3065_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 4, v_r_3219_);
lean_ctor_set(v___x_3279_, 3, v___x_3277_);
lean_ctor_set(v___x_3279_, 2, v_v_3217_);
lean_ctor_set(v___x_3279_, 1, v_k_3216_);
lean_ctor_set(v___x_3279_, 0, v___x_3274_);
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3274_);
lean_ctor_set(v_reuseFailAlloc_3283_, 1, v_k_3216_);
lean_ctor_set(v_reuseFailAlloc_3283_, 2, v_v_3217_);
lean_ctor_set(v_reuseFailAlloc_3283_, 3, v___x_3277_);
lean_ctor_set(v_reuseFailAlloc_3283_, 4, v_r_3219_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3297_; 
v_l_3297_ = lean_ctor_get(v_impl_3212_, 3);
lean_inc(v_l_3297_);
if (lean_obj_tag(v_l_3297_) == 0)
{
lean_object* v_r_3298_; lean_object* v_k_3299_; lean_object* v_v_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3323_; 
v_r_3298_ = lean_ctor_get(v_impl_3212_, 4);
v_k_3299_ = lean_ctor_get(v_impl_3212_, 1);
v_v_3300_ = lean_ctor_get(v_impl_3212_, 2);
v_isSharedCheck_3323_ = !lean_is_exclusive(v_impl_3212_);
if (v_isSharedCheck_3323_ == 0)
{
lean_object* v_unused_3324_; lean_object* v_unused_3325_; 
v_unused_3324_ = lean_ctor_get(v_impl_3212_, 3);
lean_dec(v_unused_3324_);
v_unused_3325_ = lean_ctor_get(v_impl_3212_, 0);
lean_dec(v_unused_3325_);
v___x_3302_ = v_impl_3212_;
v_isShared_3303_ = v_isSharedCheck_3323_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_r_3298_);
lean_inc(v_v_3300_);
lean_inc(v_k_3299_);
lean_dec(v_impl_3212_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3323_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v_k_3304_; lean_object* v_v_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3319_; 
v_k_3304_ = lean_ctor_get(v_l_3297_, 1);
v_v_3305_ = lean_ctor_get(v_l_3297_, 2);
v_isSharedCheck_3319_ = !lean_is_exclusive(v_l_3297_);
if (v_isSharedCheck_3319_ == 0)
{
lean_object* v_unused_3320_; lean_object* v_unused_3321_; lean_object* v_unused_3322_; 
v_unused_3320_ = lean_ctor_get(v_l_3297_, 4);
lean_dec(v_unused_3320_);
v_unused_3321_ = lean_ctor_get(v_l_3297_, 3);
lean_dec(v_unused_3321_);
v_unused_3322_ = lean_ctor_get(v_l_3297_, 0);
lean_dec(v_unused_3322_);
v___x_3307_ = v_l_3297_;
v_isShared_3308_ = v_isSharedCheck_3319_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_v_3305_);
lean_inc(v_k_3304_);
lean_dec(v_l_3297_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3319_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3309_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3298_, 2);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 4, v_r_3298_);
lean_ctor_set(v___x_3307_, 3, v_r_3298_);
lean_ctor_set(v___x_3307_, 2, v_v_3064_);
lean_ctor_set(v___x_3307_, 1, v_k_3063_);
lean_ctor_set(v___x_3307_, 0, v___x_3213_);
v___x_3311_ = v___x_3307_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3318_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3318_, 3, v_r_3298_);
lean_ctor_set(v_reuseFailAlloc_3318_, 4, v_r_3298_);
v___x_3311_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
lean_object* v___x_3313_; 
lean_inc(v_r_3298_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 3, v_r_3298_);
lean_ctor_set(v___x_3302_, 0, v___x_3213_);
v___x_3313_ = v___x_3302_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_k_3299_);
lean_ctor_set(v_reuseFailAlloc_3317_, 2, v_v_3300_);
lean_ctor_set(v_reuseFailAlloc_3317_, 3, v_r_3298_);
lean_ctor_set(v_reuseFailAlloc_3317_, 4, v_r_3298_);
v___x_3313_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3315_; 
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 4, v___x_3313_);
lean_ctor_set(v___x_3068_, 3, v___x_3311_);
lean_ctor_set(v___x_3068_, 2, v_v_3305_);
lean_ctor_set(v___x_3068_, 1, v_k_3304_);
lean_ctor_set(v___x_3068_, 0, v___x_3309_);
v___x_3315_ = v___x_3068_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3309_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v_k_3304_);
lean_ctor_set(v_reuseFailAlloc_3316_, 2, v_v_3305_);
lean_ctor_set(v_reuseFailAlloc_3316_, 3, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3316_, 4, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
}
else
{
lean_object* v_r_3326_; 
v_r_3326_ = lean_ctor_get(v_impl_3212_, 4);
lean_inc(v_r_3326_);
if (lean_obj_tag(v_r_3326_) == 0)
{
lean_object* v_k_3327_; lean_object* v_v_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3339_; 
v_k_3327_ = lean_ctor_get(v_impl_3212_, 1);
v_v_3328_ = lean_ctor_get(v_impl_3212_, 2);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_impl_3212_);
if (v_isSharedCheck_3339_ == 0)
{
lean_object* v_unused_3340_; lean_object* v_unused_3341_; lean_object* v_unused_3342_; 
v_unused_3340_ = lean_ctor_get(v_impl_3212_, 4);
lean_dec(v_unused_3340_);
v_unused_3341_ = lean_ctor_get(v_impl_3212_, 3);
lean_dec(v_unused_3341_);
v_unused_3342_ = lean_ctor_get(v_impl_3212_, 0);
lean_dec(v_unused_3342_);
v___x_3330_ = v_impl_3212_;
v_isShared_3331_ = v_isSharedCheck_3339_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_v_3328_);
lean_inc(v_k_3327_);
lean_dec(v_impl_3212_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3339_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3332_ = lean_unsigned_to_nat(3u);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 4, v_l_3297_);
lean_ctor_set(v___x_3330_, 2, v_v_3064_);
lean_ctor_set(v___x_3330_, 1, v_k_3063_);
lean_ctor_set(v___x_3330_, 0, v___x_3213_);
v___x_3334_ = v___x_3330_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3338_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3338_, 3, v_l_3297_);
lean_ctor_set(v_reuseFailAlloc_3338_, 4, v_l_3297_);
v___x_3334_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
lean_object* v___x_3336_; 
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 4, v_r_3326_);
lean_ctor_set(v___x_3068_, 3, v___x_3334_);
lean_ctor_set(v___x_3068_, 2, v_v_3328_);
lean_ctor_set(v___x_3068_, 1, v_k_3327_);
lean_ctor_set(v___x_3068_, 0, v___x_3332_);
v___x_3336_ = v___x_3068_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3337_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3337_, 3, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3337_, 4, v_r_3326_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3343_ = lean_unsigned_to_nat(2u);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 4, v_impl_3212_);
lean_ctor_set(v___x_3068_, 3, v_r_3326_);
lean_ctor_set(v___x_3068_, 0, v___x_3343_);
v___x_3345_ = v___x_3068_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3346_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3346_, 3, v_r_3326_);
lean_ctor_set(v_reuseFailAlloc_3346_, 4, v_impl_3212_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
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
lean_object* v___x_3348_; lean_object* v___x_3349_; 
lean_dec_ref(v_cmp_3058_);
v___x_3348_ = lean_unsigned_to_nat(1u);
v___x_3349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
lean_ctor_set(v___x_3349_, 1, v_k_3059_);
lean_ctor_set(v___x_3349_, 2, v_v_3060_);
lean_ctor_set(v___x_3349_, 3, v_t_3061_);
lean_ctor_set(v___x_3349_, 4, v_t_3061_);
return v___x_3349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(lean_object* v_cmp_3350_, lean_object* v_init_3351_, lean_object* v_x_3352_){
_start:
{
if (lean_obj_tag(v_x_3352_) == 0)
{
lean_object* v_k_3353_; lean_object* v_v_3354_; lean_object* v_l_3355_; lean_object* v_r_3356_; lean_object* v___x_3357_; lean_object* v_a_3358_; lean_object* v_r_3359_; 
v_k_3353_ = lean_ctor_get(v_x_3352_, 1);
lean_inc(v_k_3353_);
v_v_3354_ = lean_ctor_get(v_x_3352_, 2);
lean_inc(v_v_3354_);
v_l_3355_ = lean_ctor_get(v_x_3352_, 3);
lean_inc(v_l_3355_);
v_r_3356_ = lean_ctor_get(v_x_3352_, 4);
lean_inc(v_r_3356_);
lean_dec_ref(v_x_3352_);
lean_inc_ref(v_cmp_3350_);
v___x_3357_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3350_, v_init_3351_, v_l_3355_);
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref(v___x_3357_);
lean_inc_ref(v_cmp_3350_);
v_r_3359_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3350_, v_k_3353_, v_v_3354_, v_a_3358_);
v_init_3351_ = v_r_3359_;
v_x_3352_ = v_r_3356_;
goto _start;
}
else
{
lean_object* v___x_3361_; 
lean_dec_ref(v_cmp_3350_);
v___x_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3361_, 0, v_init_3351_);
return v___x_3361_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(lean_object* v_cmp_3362_, lean_object* v_k_3363_, lean_object* v_t_3364_){
_start:
{
if (lean_obj_tag(v_t_3364_) == 0)
{
lean_object* v_k_3365_; lean_object* v_l_3366_; lean_object* v_r_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v_k_3365_ = lean_ctor_get(v_t_3364_, 1);
lean_inc(v_k_3365_);
v_l_3366_ = lean_ctor_get(v_t_3364_, 3);
lean_inc(v_l_3366_);
v_r_3367_ = lean_ctor_get(v_t_3364_, 4);
lean_inc(v_r_3367_);
lean_dec_ref(v_t_3364_);
lean_inc_ref(v_cmp_3362_);
lean_inc(v_k_3363_);
v___x_3368_ = lean_apply_2(v_cmp_3362_, v_k_3363_, v_k_3365_);
v___x_3369_ = lean_unbox(v___x_3368_);
switch(v___x_3369_)
{
case 0:
{
lean_dec(v_r_3367_);
v_t_3364_ = v_l_3366_;
goto _start;
}
case 1:
{
uint8_t v___x_3371_; 
lean_dec(v_r_3367_);
lean_dec(v_l_3366_);
lean_dec(v_k_3363_);
lean_dec_ref(v_cmp_3362_);
v___x_3371_ = 1;
return v___x_3371_;
}
default: 
{
lean_dec(v_l_3366_);
v_t_3364_ = v_r_3367_;
goto _start;
}
}
}
else
{
uint8_t v___x_3373_; 
lean_dec(v_k_3363_);
lean_dec_ref(v_cmp_3362_);
v___x_3373_ = 0;
return v___x_3373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_3374_, lean_object* v_k_3375_, lean_object* v_t_3376_){
_start:
{
uint8_t v_res_3377_; lean_object* v_r_3378_; 
v_res_3377_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3374_, v_k_3375_, v_t_3376_);
v_r_3378_ = lean_box(v_res_3377_);
return v_r_3378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(lean_object* v_cmp_3379_, lean_object* v_init_3380_, lean_object* v_x_3381_){
_start:
{
if (lean_obj_tag(v_x_3381_) == 0)
{
lean_object* v_k_3382_; lean_object* v_v_3383_; lean_object* v_l_3384_; lean_object* v_r_3385_; lean_object* v___x_3386_; lean_object* v_a_3387_; uint8_t v___x_3388_; 
v_k_3382_ = lean_ctor_get(v_x_3381_, 1);
lean_inc(v_k_3382_);
v_v_3383_ = lean_ctor_get(v_x_3381_, 2);
lean_inc(v_v_3383_);
v_l_3384_ = lean_ctor_get(v_x_3381_, 3);
lean_inc(v_l_3384_);
v_r_3385_ = lean_ctor_get(v_x_3381_, 4);
lean_inc(v_r_3385_);
lean_dec_ref(v_x_3381_);
lean_inc_ref(v_cmp_3379_);
v___x_3386_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3379_, v_init_3380_, v_l_3384_);
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref(v___x_3386_);
lean_inc(v_a_3387_);
lean_inc(v_k_3382_);
lean_inc_ref(v_cmp_3379_);
v___x_3388_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3379_, v_k_3382_, v_a_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; 
lean_inc_ref(v_cmp_3379_);
v___x_3389_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3379_, v_k_3382_, v_v_3383_, v_a_3387_);
v_init_3380_ = v___x_3389_;
v_x_3381_ = v_r_3385_;
goto _start;
}
else
{
lean_dec(v_v_3383_);
lean_dec(v_k_3382_);
v_init_3380_ = v_a_3387_;
v_x_3381_ = v_r_3385_;
goto _start;
}
}
else
{
lean_object* v___x_3392_; 
lean_dec_ref(v_cmp_3379_);
v___x_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3392_, 0, v_init_3380_);
return v___x_3392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object* v_cmp_3393_, lean_object* v_t_u2081_3394_, lean_object* v_t_u2082_3395_){
_start:
{
lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3405_; 
if (lean_obj_tag(v_t_u2081_3394_) == 0)
{
lean_object* v_size_3408_; 
v_size_3408_ = lean_ctor_get(v_t_u2081_3394_, 0);
lean_inc(v_size_3408_);
v___y_3405_ = v_size_3408_;
goto v___jp_3404_;
}
else
{
lean_object* v___x_3409_; 
v___x_3409_ = lean_unsigned_to_nat(0u);
v___y_3405_ = v___x_3409_;
goto v___jp_3404_;
}
v___jp_3396_:
{
uint8_t v___x_3399_; 
v___x_3399_ = lean_nat_dec_le(v___y_3397_, v___y_3398_);
lean_dec(v___y_3398_);
lean_dec(v___y_3397_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; lean_object* v_a_3401_; 
v___x_3400_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3393_, v_t_u2081_3394_, v_t_u2082_3395_);
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref(v___x_3400_);
return v_a_3401_;
}
else
{
lean_object* v___x_3402_; lean_object* v_a_3403_; 
v___x_3402_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3393_, v_t_u2082_3395_, v_t_u2081_3394_);
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref(v___x_3402_);
return v_a_3403_;
}
}
v___jp_3404_:
{
if (lean_obj_tag(v_t_u2082_3395_) == 0)
{
lean_object* v_size_3406_; 
v_size_3406_ = lean_ctor_get(v_t_u2082_3395_, 0);
lean_inc(v_size_3406_);
v___y_3397_ = v___y_3405_;
v___y_3398_ = v_size_3406_;
goto v___jp_3396_;
}
else
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_unsigned_to_nat(0u);
v___y_3397_ = v___y_3405_;
v___y_3398_ = v___x_3407_;
goto v___jp_3396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_union___redArg(lean_object* v_cmp_3410_, lean_object* v_t_u2081_3411_, lean_object* v_t_u2082_3412_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3410_, v_t_u2081_3411_, v_t_u2082_3412_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_union(lean_object* v_00_u03b1_3414_, lean_object* v_00_u03b2_3415_, lean_object* v_cmp_3416_, lean_object* v_t_u2081_3417_, lean_object* v_t_u2082_3418_){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3416_, v_t_u2081_3417_, v_t_u2082_3418_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0(lean_object* v_00_u03b1_3420_, lean_object* v_cmp_3421_, lean_object* v_00_u03b2_3422_, lean_object* v_t_u2081_3423_, lean_object* v_t_u2082_3424_, lean_object* v_h_u2081_3425_, lean_object* v_h_u2082_3426_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3421_, v_t_u2081_3423_, v_t_u2082_3424_);
return v___x_3427_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0(lean_object* v_00_u03b1_3428_, lean_object* v_cmp_3429_, lean_object* v_00_u03b2_3430_, lean_object* v_k_3431_, lean_object* v_t_3432_){
_start:
{
uint8_t v___x_3433_; 
v___x_3433_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3429_, v_k_3431_, v_t_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3434_, lean_object* v_cmp_3435_, lean_object* v_00_u03b2_3436_, lean_object* v_k_3437_, lean_object* v_t_3438_){
_start:
{
uint8_t v_res_3439_; lean_object* v_r_3440_; 
v_res_3439_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0(v_00_u03b1_3434_, v_cmp_3435_, v_00_u03b2_3436_, v_k_3437_, v_t_3438_);
v_r_3440_ = lean_box(v_res_3439_);
return v_r_3440_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1(lean_object* v_00_u03b1_3441_, lean_object* v_cmp_3442_, lean_object* v_00_u03b2_3443_, lean_object* v_k_3444_, lean_object* v_v_3445_, lean_object* v_t_3446_, lean_object* v_hl_3447_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3442_, v_k_3444_, v_v_3445_, v_t_3446_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2(lean_object* v_00_u03b1_3449_, lean_object* v_00_u03b2_3450_, lean_object* v_cmp_3451_, lean_object* v_init_3452_, lean_object* v_x_3453_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3451_, v_init_3452_, v_x_3453_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3(lean_object* v_00_u03b1_3455_, lean_object* v_00_u03b2_3456_, lean_object* v_cmp_3457_, lean_object* v_init_3458_, lean_object* v_x_3459_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3457_, v_init_3458_, v_x_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instUnion___redArg(lean_object* v_cmp_3461_){
_start:
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_alloc_closure((void*)(l_Std_DTreeMap_union), 5, 3);
lean_closure_set(v___x_3462_, 0, lean_box(0));
lean_closure_set(v___x_3462_, 1, lean_box(0));
lean_closure_set(v___x_3462_, 2, v_cmp_3461_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instUnion(lean_object* v_00_u03b1_3463_, lean_object* v_00_u03b2_3464_, lean_object* v_cmp_3465_){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = lean_alloc_closure((void*)(l_Std_DTreeMap_union), 5, 3);
lean_closure_set(v___x_3466_, 0, lean_box(0));
lean_closure_set(v___x_3466_, 1, lean_box(0));
lean_closure_set(v___x_3466_, 2, v_cmp_3465_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(lean_object* v_cmp_3467_, lean_object* v_m_u2082_3468_, lean_object* v_t_3469_){
_start:
{
if (lean_obj_tag(v_t_3469_) == 0)
{
lean_object* v_k_3470_; lean_object* v_v_3471_; lean_object* v_l_3472_; lean_object* v_r_3473_; uint8_t v___x_3474_; 
v_k_3470_ = lean_ctor_get(v_t_3469_, 1);
lean_inc(v_k_3470_);
v_v_3471_ = lean_ctor_get(v_t_3469_, 2);
lean_inc(v_v_3471_);
v_l_3472_ = lean_ctor_get(v_t_3469_, 3);
lean_inc(v_l_3472_);
v_r_3473_ = lean_ctor_get(v_t_3469_, 4);
lean_inc(v_r_3473_);
lean_dec_ref(v_t_3469_);
lean_inc(v_m_u2082_3468_);
lean_inc(v_k_3470_);
lean_inc_ref(v_cmp_3467_);
v___x_3474_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3467_, v_k_3470_, v_m_u2082_3468_);
if (v___x_3474_ == 0)
{
lean_object* v_impl_3475_; lean_object* v_impl_3476_; lean_object* v___x_3477_; 
lean_dec(v_v_3471_);
lean_dec(v_k_3470_);
lean_inc(v_m_u2082_3468_);
lean_inc_ref(v_cmp_3467_);
v_impl_3475_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3467_, v_m_u2082_3468_, v_l_3472_);
v_impl_3476_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3467_, v_m_u2082_3468_, v_r_3473_);
v___x_3477_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_3475_, v_impl_3476_);
return v___x_3477_;
}
else
{
lean_object* v_impl_3478_; lean_object* v_impl_3479_; lean_object* v___x_3480_; 
lean_inc(v_m_u2082_3468_);
lean_inc_ref(v_cmp_3467_);
v_impl_3478_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3467_, v_m_u2082_3468_, v_l_3472_);
v_impl_3479_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3467_, v_m_u2082_3468_, v_r_3473_);
v___x_3480_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_3470_, v_v_3471_, v_impl_3478_, v_impl_3479_);
return v___x_3480_;
}
}
else
{
lean_dec(v_m_u2082_3468_);
lean_dec_ref(v_cmp_3467_);
return v_t_3469_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_3481_, lean_object* v_t_3482_, lean_object* v_k_3483_){
_start:
{
if (lean_obj_tag(v_t_3482_) == 0)
{
lean_object* v_k_3484_; lean_object* v_v_3485_; lean_object* v_l_3486_; lean_object* v_r_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v_k_3484_ = lean_ctor_get(v_t_3482_, 1);
lean_inc(v_k_3484_);
v_v_3485_ = lean_ctor_get(v_t_3482_, 2);
lean_inc(v_v_3485_);
v_l_3486_ = lean_ctor_get(v_t_3482_, 3);
lean_inc(v_l_3486_);
v_r_3487_ = lean_ctor_get(v_t_3482_, 4);
lean_inc(v_r_3487_);
lean_dec_ref(v_t_3482_);
lean_inc_ref(v_cmp_3481_);
lean_inc(v_k_3484_);
lean_inc(v_k_3483_);
v___x_3488_ = lean_apply_2(v_cmp_3481_, v_k_3483_, v_k_3484_);
v___x_3489_ = lean_unbox(v___x_3488_);
switch(v___x_3489_)
{
case 0:
{
lean_dec(v_r_3487_);
lean_dec(v_v_3485_);
lean_dec(v_k_3484_);
v_t_3482_ = v_l_3486_;
goto _start;
}
case 1:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
lean_dec(v_r_3487_);
lean_dec(v_l_3486_);
lean_dec(v_k_3483_);
lean_dec_ref(v_cmp_3481_);
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v_k_3484_);
lean_ctor_set(v___x_3491_, 1, v_v_3485_);
v___x_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
return v___x_3492_;
}
default: 
{
lean_dec(v_l_3486_);
lean_dec(v_v_3485_);
lean_dec(v_k_3484_);
v_t_3482_ = v_r_3487_;
goto _start;
}
}
}
else
{
lean_object* v___x_3494_; 
lean_dec(v_k_3483_);
lean_dec_ref(v_cmp_3481_);
v___x_3494_ = lean_box(0);
return v___x_3494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_cmp_3495_, lean_object* v_m_u2081_3496_, lean_object* v_init_3497_, lean_object* v_x_3498_){
_start:
{
if (lean_obj_tag(v_x_3498_) == 0)
{
lean_object* v_k_3499_; lean_object* v_l_3500_; lean_object* v_r_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_k_3499_ = lean_ctor_get(v_x_3498_, 1);
lean_inc(v_k_3499_);
v_l_3500_ = lean_ctor_get(v_x_3498_, 3);
lean_inc(v_l_3500_);
v_r_3501_ = lean_ctor_get(v_x_3498_, 4);
lean_inc(v_r_3501_);
lean_dec_ref(v_x_3498_);
lean_inc(v_m_u2081_3496_);
lean_inc_ref(v_cmp_3495_);
v___x_3502_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3495_, v_m_u2081_3496_, v_init_3497_, v_l_3500_);
lean_inc(v_m_u2081_3496_);
lean_inc_ref(v_cmp_3495_);
v___x_3503_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3495_, v_m_u2081_3496_, v_k_3499_);
if (lean_obj_tag(v___x_3503_) == 0)
{
v_init_3497_ = v___x_3502_;
v_x_3498_ = v_r_3501_;
goto _start;
}
else
{
lean_object* v_val_3505_; lean_object* v_fst_3506_; lean_object* v_snd_3507_; lean_object* v_impl_3508_; 
v_val_3505_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_val_3505_);
lean_dec_ref(v___x_3503_);
v_fst_3506_ = lean_ctor_get(v_val_3505_, 0);
lean_inc(v_fst_3506_);
v_snd_3507_ = lean_ctor_get(v_val_3505_, 1);
lean_inc(v_snd_3507_);
lean_dec(v_val_3505_);
lean_inc_ref(v_cmp_3495_);
v_impl_3508_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3495_, v_fst_3506_, v_snd_3507_, v___x_3502_);
v_init_3497_ = v_impl_3508_;
v_x_3498_ = v_r_3501_;
goto _start;
}
}
else
{
lean_dec(v_m_u2081_3496_);
lean_dec_ref(v_cmp_3495_);
return v_init_3497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(lean_object* v_cmp_3510_, lean_object* v_m_u2081_3511_, lean_object* v_m_u2082_3512_){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_box(1);
v___x_3514_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3510_, v_m_u2081_3511_, v___x_3513_, v_m_u2082_3512_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(lean_object* v_cmp_3515_, lean_object* v_m_u2081_3516_, lean_object* v_m_u2082_3517_){
_start:
{
lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3525_; 
if (lean_obj_tag(v_m_u2081_3516_) == 0)
{
lean_object* v_size_3528_; 
v_size_3528_ = lean_ctor_get(v_m_u2081_3516_, 0);
lean_inc(v_size_3528_);
v___y_3525_ = v_size_3528_;
goto v___jp_3524_;
}
else
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_unsigned_to_nat(0u);
v___y_3525_ = v___x_3529_;
goto v___jp_3524_;
}
v___jp_3518_:
{
uint8_t v___x_3521_; 
v___x_3521_ = lean_nat_dec_le(v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; 
v___x_3522_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(v_cmp_3515_, v_m_u2081_3516_, v_m_u2082_3517_);
return v___x_3522_;
}
else
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3515_, v_m_u2082_3517_, v_m_u2081_3516_);
return v___x_3523_;
}
}
v___jp_3524_:
{
if (lean_obj_tag(v_m_u2082_3517_) == 0)
{
lean_object* v_size_3526_; 
v_size_3526_ = lean_ctor_get(v_m_u2082_3517_, 0);
lean_inc(v_size_3526_);
v___y_3519_ = v___y_3525_;
v___y_3520_ = v_size_3526_;
goto v___jp_3518_;
}
else
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_unsigned_to_nat(0u);
v___y_3519_ = v___y_3525_;
v___y_3520_ = v___x_3527_;
goto v___jp_3518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_inter___redArg(lean_object* v_cmp_3530_, lean_object* v_t_u2081_3531_, lean_object* v_t_u2082_3532_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3530_, v_t_u2081_3531_, v_t_u2082_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_inter(lean_object* v_00_u03b1_3534_, lean_object* v_00_u03b2_3535_, lean_object* v_cmp_3536_, lean_object* v_t_u2081_3537_, lean_object* v_t_u2082_3538_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3536_, v_t_u2081_3537_, v_t_u2082_3538_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0(lean_object* v_00_u03b1_3540_, lean_object* v_cmp_3541_, lean_object* v_00_u03b2_3542_, lean_object* v_m_u2081_3543_, lean_object* v_m_u2082_3544_, lean_object* v_h_u2081_3545_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3541_, v_m_u2081_3543_, v_m_u2082_3544_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0(lean_object* v_00_u03b1_3547_, lean_object* v_cmp_3548_, lean_object* v_00_u03b2_3549_, lean_object* v_m_u2081_3550_, lean_object* v_m_u2082_3551_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(v_cmp_3548_, v_m_u2081_3550_, v_m_u2082_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1(lean_object* v_00_u03b1_3553_, lean_object* v_00_u03b2_3554_, lean_object* v_cmp_3555_, lean_object* v_m_u2082_3556_, lean_object* v_t_3557_, lean_object* v_hl_3558_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3555_, v_m_u2082_3556_, v_t_3557_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3560_, lean_object* v_cmp_3561_, lean_object* v_00_u03b2_3562_, lean_object* v_t_3563_, lean_object* v_k_3564_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3561_, v_t_3563_, v_k_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2___redArg(lean_object* v_cmp_3566_, lean_object* v_m_u2081_3567_, lean_object* v_init_3568_, lean_object* v_t_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3566_, v_m_u2081_3567_, v_init_3568_, v_t_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3571_, lean_object* v_00_u03b2_3572_, lean_object* v_cmp_3573_, lean_object* v_m_u2081_3574_, lean_object* v_init_3575_, lean_object* v_t_3576_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3573_, v_m_u2081_3574_, v_init_3575_, v_t_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_3578_, lean_object* v_00_u03b2_3579_, lean_object* v_cmp_3580_, lean_object* v_m_u2081_3581_, lean_object* v_init_3582_, lean_object* v_x_3583_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3580_, v_m_u2081_3581_, v_init_3582_, v_x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInter___redArg(lean_object* v_cmp_3585_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_alloc_closure((void*)(l_Std_DTreeMap_inter), 5, 3);
lean_closure_set(v___x_3586_, 0, lean_box(0));
lean_closure_set(v___x_3586_, 1, lean_box(0));
lean_closure_set(v___x_3586_, 2, v_cmp_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInter(lean_object* v_00_u03b1_3587_, lean_object* v_00_u03b2_3588_, lean_object* v_cmp_3589_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_alloc_closure((void*)(l_Std_DTreeMap_inter), 5, 3);
lean_closure_set(v___x_3590_, 0, lean_box(0));
lean_closure_set(v___x_3590_, 1, lean_box(0));
lean_closure_set(v___x_3590_, 2, v_cmp_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_beq___redArg(lean_object* v_cmp_3591_, lean_object* v_inst_3592_, lean_object* v_t_u2081_3593_, lean_object* v_t_u2082_3594_){
_start:
{
uint8_t v___x_3595_; 
v___x_3595_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3591_, v_inst_3592_, v_t_u2081_3593_, v_t_u2082_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_beq___redArg___boxed(lean_object* v_cmp_3596_, lean_object* v_inst_3597_, lean_object* v_t_u2081_3598_, lean_object* v_t_u2082_3599_){
_start:
{
uint8_t v_res_3600_; lean_object* v_r_3601_; 
v_res_3600_ = l_Std_DTreeMap_beq___redArg(v_cmp_3596_, v_inst_3597_, v_t_u2081_3598_, v_t_u2082_3599_);
v_r_3601_ = lean_box(v_res_3600_);
return v_r_3601_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_beq(lean_object* v_00_u03b1_3602_, lean_object* v_00_u03b2_3603_, lean_object* v_cmp_3604_, lean_object* v_inst_3605_, lean_object* v_inst_3606_, lean_object* v_t_u2081_3607_, lean_object* v_t_u2082_3608_){
_start:
{
uint8_t v___x_3609_; 
v___x_3609_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3604_, v_inst_3606_, v_t_u2081_3607_, v_t_u2082_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_beq___boxed(lean_object* v_00_u03b1_3610_, lean_object* v_00_u03b2_3611_, lean_object* v_cmp_3612_, lean_object* v_inst_3613_, lean_object* v_inst_3614_, lean_object* v_t_u2081_3615_, lean_object* v_t_u2082_3616_){
_start:
{
uint8_t v_res_3617_; lean_object* v_r_3618_; 
v_res_3617_ = l_Std_DTreeMap_beq(v_00_u03b1_3610_, v_00_u03b2_3611_, v_cmp_3612_, v_inst_3613_, v_inst_3614_, v_t_u2081_3615_, v_t_u2082_3616_);
v_r_3618_ = lean_box(v_res_3617_);
return v_r_3618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instBEqOfLawfulEqCmp___redArg(lean_object* v_cmp_3619_, lean_object* v_inst_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = lean_alloc_closure((void*)(l_Std_DTreeMap_beq___boxed), 7, 5);
lean_closure_set(v___x_3621_, 0, lean_box(0));
lean_closure_set(v___x_3621_, 1, lean_box(0));
lean_closure_set(v___x_3621_, 2, v_cmp_3619_);
lean_closure_set(v___x_3621_, 3, lean_box(0));
lean_closure_set(v___x_3621_, 4, v_inst_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instBEqOfLawfulEqCmp(lean_object* v_00_u03b1_3622_, lean_object* v_00_u03b2_3623_, lean_object* v_cmp_3624_, lean_object* v_inst_3625_, lean_object* v_inst_3626_){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = lean_alloc_closure((void*)(l_Std_DTreeMap_beq___boxed), 7, 5);
lean_closure_set(v___x_3627_, 0, lean_box(0));
lean_closure_set(v___x_3627_, 1, lean_box(0));
lean_closure_set(v___x_3627_, 2, v_cmp_3624_);
lean_closure_set(v___x_3627_, 3, lean_box(0));
lean_closure_set(v___x_3627_, 4, v_inst_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___redArg(lean_object* v_cmp_3628_, lean_object* v_inst_3629_, lean_object* v_t_u2081_3630_, lean_object* v_t_u2082_3631_){
_start:
{
uint8_t v___x_3632_; 
v___x_3632_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3628_, v_inst_3629_, v_t_u2081_3630_, v_t_u2082_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___redArg___boxed(lean_object* v_cmp_3633_, lean_object* v_inst_3634_, lean_object* v_t_u2081_3635_, lean_object* v_t_u2082_3636_){
_start:
{
uint8_t v_res_3637_; lean_object* v_r_3638_; 
v_res_3637_ = l_Std_DTreeMap_Const_beq___redArg(v_cmp_3633_, v_inst_3634_, v_t_u2081_3635_, v_t_u2082_3636_);
v_r_3638_ = lean_box(v_res_3637_);
return v_r_3638_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq(lean_object* v_00_u03b1_3639_, lean_object* v_cmp_3640_, lean_object* v_00_u03b2_3641_, lean_object* v_inst_3642_, lean_object* v_t_u2081_3643_, lean_object* v_t_u2082_3644_){
_start:
{
uint8_t v___x_3645_; 
v___x_3645_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3640_, v_inst_3642_, v_t_u2081_3643_, v_t_u2082_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___boxed(lean_object* v_00_u03b1_3646_, lean_object* v_cmp_3647_, lean_object* v_00_u03b2_3648_, lean_object* v_inst_3649_, lean_object* v_t_u2081_3650_, lean_object* v_t_u2082_3651_){
_start:
{
uint8_t v_res_3652_; lean_object* v_r_3653_; 
v_res_3652_ = l_Std_DTreeMap_Const_beq(v_00_u03b1_3646_, v_cmp_3647_, v_00_u03b2_3648_, v_inst_3649_, v_t_u2081_3650_, v_t_u2082_3651_);
v_r_3653_ = lean_box(v_res_3652_);
return v_r_3653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(lean_object* v_cmp_3654_, lean_object* v_k_3655_, lean_object* v_t_3656_){
_start:
{
if (lean_obj_tag(v_t_3656_) == 0)
{
lean_object* v_k_3657_; lean_object* v_v_3658_; lean_object* v_l_3659_; lean_object* v_r_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_4315_; 
v_k_3657_ = lean_ctor_get(v_t_3656_, 1);
v_v_3658_ = lean_ctor_get(v_t_3656_, 2);
v_l_3659_ = lean_ctor_get(v_t_3656_, 3);
v_r_3660_ = lean_ctor_get(v_t_3656_, 4);
v_isSharedCheck_4315_ = !lean_is_exclusive(v_t_3656_);
if (v_isSharedCheck_4315_ == 0)
{
lean_object* v_unused_4316_; 
v_unused_4316_ = lean_ctor_get(v_t_3656_, 0);
lean_dec(v_unused_4316_);
v___x_3662_ = v_t_3656_;
v_isShared_3663_ = v_isSharedCheck_4315_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_r_3660_);
lean_inc(v_l_3659_);
lean_inc(v_v_3658_);
lean_inc(v_k_3657_);
lean_dec(v_t_3656_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_4315_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; uint8_t v___x_3665_; 
lean_inc_ref(v_cmp_3654_);
lean_inc(v_k_3657_);
lean_inc(v_k_3655_);
v___x_3664_ = lean_apply_2(v_cmp_3654_, v_k_3655_, v_k_3657_);
v___x_3665_ = lean_unbox(v___x_3664_);
switch(v___x_3665_)
{
case 0:
{
lean_object* v_impl_3666_; lean_object* v___x_3667_; 
v_impl_3666_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_3654_, v_k_3655_, v_l_3659_);
v___x_3667_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3666_) == 0)
{
if (lean_obj_tag(v_r_3660_) == 0)
{
lean_object* v_size_3668_; lean_object* v_size_3669_; lean_object* v_k_3670_; lean_object* v_v_3671_; lean_object* v_l_3672_; lean_object* v_r_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v_size_3668_ = lean_ctor_get(v_impl_3666_, 0);
lean_inc(v_size_3668_);
v_size_3669_ = lean_ctor_get(v_r_3660_, 0);
v_k_3670_ = lean_ctor_get(v_r_3660_, 1);
v_v_3671_ = lean_ctor_get(v_r_3660_, 2);
v_l_3672_ = lean_ctor_get(v_r_3660_, 3);
lean_inc(v_l_3672_);
v_r_3673_ = lean_ctor_get(v_r_3660_, 4);
v___x_3674_ = lean_unsigned_to_nat(3u);
v___x_3675_ = lean_nat_mul(v___x_3674_, v_size_3668_);
v___x_3676_ = lean_nat_dec_lt(v___x_3675_, v_size_3669_);
lean_dec(v___x_3675_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
lean_dec(v_l_3672_);
v___x_3677_ = lean_nat_add(v___x_3667_, v_size_3668_);
lean_dec(v_size_3668_);
v___x_3678_ = lean_nat_add(v___x_3677_, v_size_3669_);
lean_dec(v___x_3677_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 3, v_impl_3666_);
lean_ctor_set(v___x_3662_, 0, v___x_3678_);
v___x_3680_ = v___x_3662_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
lean_ctor_set(v_reuseFailAlloc_3681_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_3681_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_3681_, 3, v_impl_3666_);
lean_ctor_set(v_reuseFailAlloc_3681_, 4, v_r_3660_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
else
{
lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3745_; 
lean_inc(v_r_3673_);
lean_inc(v_v_3671_);
lean_inc(v_k_3670_);
lean_inc(v_size_3669_);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_r_3660_);
if (v_isSharedCheck_3745_ == 0)
{
lean_object* v_unused_3746_; lean_object* v_unused_3747_; lean_object* v_unused_3748_; lean_object* v_unused_3749_; lean_object* v_unused_3750_; 
v_unused_3746_ = lean_ctor_get(v_r_3660_, 4);
lean_dec(v_unused_3746_);
v_unused_3747_ = lean_ctor_get(v_r_3660_, 3);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_r_3660_, 2);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_r_3660_, 1);
lean_dec(v_unused_3749_);
v_unused_3750_ = lean_ctor_get(v_r_3660_, 0);
lean_dec(v_unused_3750_);
v___x_3683_ = v_r_3660_;
v_isShared_3684_ = v_isSharedCheck_3745_;
goto v_resetjp_3682_;
}
else
{
lean_dec(v_r_3660_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3745_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v_size_3685_; lean_object* v_k_3686_; lean_object* v_v_3687_; lean_object* v_l_3688_; lean_object* v_r_3689_; lean_object* v_size_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; 
v_size_3685_ = lean_ctor_get(v_l_3672_, 0);
v_k_3686_ = lean_ctor_get(v_l_3672_, 1);
v_v_3687_ = lean_ctor_get(v_l_3672_, 2);
v_l_3688_ = lean_ctor_get(v_l_3672_, 3);
v_r_3689_ = lean_ctor_get(v_l_3672_, 4);
v_size_3690_ = lean_ctor_get(v_r_3673_, 0);
v___x_3691_ = lean_unsigned_to_nat(2u);
v___x_3692_ = lean_nat_mul(v___x_3691_, v_size_3690_);
v___x_3693_ = lean_nat_dec_lt(v_size_3685_, v___x_3692_);
lean_dec(v___x_3692_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3721_; 
lean_inc(v_r_3689_);
lean_inc(v_l_3688_);
lean_inc(v_v_3687_);
lean_inc(v_k_3686_);
v_isSharedCheck_3721_ = !lean_is_exclusive(v_l_3672_);
if (v_isSharedCheck_3721_ == 0)
{
lean_object* v_unused_3722_; lean_object* v_unused_3723_; lean_object* v_unused_3724_; lean_object* v_unused_3725_; lean_object* v_unused_3726_; 
v_unused_3722_ = lean_ctor_get(v_l_3672_, 4);
lean_dec(v_unused_3722_);
v_unused_3723_ = lean_ctor_get(v_l_3672_, 3);
lean_dec(v_unused_3723_);
v_unused_3724_ = lean_ctor_get(v_l_3672_, 2);
lean_dec(v_unused_3724_);
v_unused_3725_ = lean_ctor_get(v_l_3672_, 1);
lean_dec(v_unused_3725_);
v_unused_3726_ = lean_ctor_get(v_l_3672_, 0);
lean_dec(v_unused_3726_);
v___x_3695_ = v_l_3672_;
v_isShared_3696_ = v_isSharedCheck_3721_;
goto v_resetjp_3694_;
}
else
{
lean_dec(v_l_3672_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3721_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3711_; 
v___x_3697_ = lean_nat_add(v___x_3667_, v_size_3668_);
lean_dec(v_size_3668_);
v___x_3698_ = lean_nat_add(v___x_3697_, v_size_3669_);
lean_dec(v_size_3669_);
if (lean_obj_tag(v_l_3688_) == 0)
{
lean_object* v_size_3719_; 
v_size_3719_ = lean_ctor_get(v_l_3688_, 0);
lean_inc(v_size_3719_);
v___y_3711_ = v_size_3719_;
goto v___jp_3710_;
}
else
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_unsigned_to_nat(0u);
v___y_3711_ = v___x_3720_;
goto v___jp_3710_;
}
v___jp_3699_:
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3703_ = lean_nat_add(v___y_3700_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec(v___y_3700_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 4, v_r_3673_);
lean_ctor_set(v___x_3695_, 3, v_r_3689_);
lean_ctor_set(v___x_3695_, 2, v_v_3671_);
lean_ctor_set(v___x_3695_, 1, v_k_3670_);
lean_ctor_set(v___x_3695_, 0, v___x_3703_);
v___x_3705_ = v___x_3695_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_k_3670_);
lean_ctor_set(v_reuseFailAlloc_3709_, 2, v_v_3671_);
lean_ctor_set(v_reuseFailAlloc_3709_, 3, v_r_3689_);
lean_ctor_set(v_reuseFailAlloc_3709_, 4, v_r_3673_);
v___x_3705_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3707_; 
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 4, v___x_3705_);
lean_ctor_set(v___x_3683_, 3, v___y_3701_);
lean_ctor_set(v___x_3683_, 2, v_v_3687_);
lean_ctor_set(v___x_3683_, 1, v_k_3686_);
lean_ctor_set(v___x_3683_, 0, v___x_3698_);
v___x_3707_ = v___x_3683_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_k_3686_);
lean_ctor_set(v_reuseFailAlloc_3708_, 2, v_v_3687_);
lean_ctor_set(v_reuseFailAlloc_3708_, 3, v___y_3701_);
lean_ctor_set(v_reuseFailAlloc_3708_, 4, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
v___jp_3710_:
{
lean_object* v___x_3712_; lean_object* v___x_3714_; 
v___x_3712_ = lean_nat_add(v___x_3697_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec(v___x_3697_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_l_3688_);
lean_ctor_set(v___x_3662_, 3, v_impl_3666_);
lean_ctor_set(v___x_3662_, 0, v___x_3712_);
v___x_3714_ = v___x_3662_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_3718_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_3718_, 3, v_impl_3666_);
lean_ctor_set(v_reuseFailAlloc_3718_, 4, v_l_3688_);
v___x_3714_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3715_; 
v___x_3715_ = lean_nat_add(v___x_3667_, v_size_3690_);
if (lean_obj_tag(v_r_3689_) == 0)
{
lean_object* v_size_3716_; 
v_size_3716_ = lean_ctor_get(v_r_3689_, 0);
lean_inc(v_size_3716_);
v___y_3700_ = v___x_3715_;
v___y_3701_ = v___x_3714_;
v___y_3702_ = v_size_3716_;
goto v___jp_3699_;
}
else
{
lean_object* v___x_3717_; 
v___x_3717_ = lean_unsigned_to_nat(0u);
v___y_3700_ = v___x_3715_;
v___y_3701_ = v___x_3714_;
v___y_3702_ = v___x_3717_;
goto v___jp_3699_;
}
}
}
}
}
else
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3731_; 
lean_del_object(v___x_3662_);
v___x_3727_ = lean_nat_add(v___x_3667_, v_size_3668_);
lean_dec(v_size_3668_);
v___x_3728_ = lean_nat_add(v___x_3727_, v_size_3669_);
lean_dec(v_size_3669_);
v___x_3729_ = lean_nat_add(v___x_3727_, v_size_3685_);
lean_dec(v___x_3727_);
lean_inc_ref(v_impl_3666_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 4, v_l_3672_);
lean_ctor_set(v___x_3683_, 3, v_impl_3666_);
lean_ctor_set(v___x_3683_, 2, v_v_3658_);
lean_ctor_set(v___x_3683_, 1, v_k_3657_);
lean_ctor_set(v___x_3683_, 0, v___x_3729_);
v___x_3731_ = v___x_3683_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3744_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_3744_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_3744_, 3, v_impl_3666_);
lean_ctor_set(v_reuseFailAlloc_3744_, 4, v_l_3672_);
v___x_3731_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
v_isSharedCheck_3738_ = !lean_is_exclusive(v_impl_3666_);
if (v_isSharedCheck_3738_ == 0)
{
lean_object* v_unused_3739_; lean_object* v_unused_3740_; lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; 
v_unused_3739_ = lean_ctor_get(v_impl_3666_, 4);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_impl_3666_, 3);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_impl_3666_, 2);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_impl_3666_, 1);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_impl_3666_, 0);
lean_dec(v_unused_3743_);
v___x_3733_ = v_impl_3666_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_dec(v_impl_3666_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 4, v_r_3673_);
lean_ctor_set(v___x_3733_, 3, v___x_3731_);
lean_ctor_set(v___x_3733_, 2, v_v_3671_);
lean_ctor_set(v___x_3733_, 1, v_k_3670_);
lean_ctor_set(v___x_3733_, 0, v___x_3728_);
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3728_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_k_3670_);
lean_ctor_set(v_reuseFailAlloc_3737_, 2, v_v_3671_);
lean_ctor_set(v_reuseFailAlloc_3737_, 3, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3737_, 4, v_r_3673_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3751_; lean_object* v___x_3752_; lean_object* v___x_3754_; 
v_size_3751_ = lean_ctor_get(v_impl_3666_, 0);
lean_inc(v_size_3751_);
v___x_3752_ = lean_nat_add(v___x_3667_, v_size_3751_);
lean_dec(v_size_3751_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 3, v_impl_3666_);
lean_ctor_set(v___x_3662_, 0, v___x_3752_);
v___x_3754_ = v___x_3662_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3752_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v_impl_3666_);
lean_ctor_set(v_reuseFailAlloc_3755_, 4, v_r_3660_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
else
{
if (lean_obj_tag(v_r_3660_) == 0)
{
lean_object* v_l_3756_; 
v_l_3756_ = lean_ctor_get(v_r_3660_, 3);
lean_inc(v_l_3756_);
if (lean_obj_tag(v_l_3756_) == 0)
{
lean_object* v_r_3757_; 
v_r_3757_ = lean_ctor_get(v_r_3660_, 4);
lean_inc(v_r_3757_);
if (lean_obj_tag(v_r_3757_) == 0)
{
lean_object* v_size_3758_; lean_object* v_k_3759_; lean_object* v_v_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3773_; 
v_size_3758_ = lean_ctor_get(v_r_3660_, 0);
v_k_3759_ = lean_ctor_get(v_r_3660_, 1);
v_v_3760_ = lean_ctor_get(v_r_3660_, 2);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_r_3660_);
if (v_isSharedCheck_3773_ == 0)
{
lean_object* v_unused_3774_; lean_object* v_unused_3775_; 
v_unused_3774_ = lean_ctor_get(v_r_3660_, 4);
lean_dec(v_unused_3774_);
v_unused_3775_ = lean_ctor_get(v_r_3660_, 3);
lean_dec(v_unused_3775_);
v___x_3762_ = v_r_3660_;
v_isShared_3763_ = v_isSharedCheck_3773_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_v_3760_);
lean_inc(v_k_3759_);
lean_inc(v_size_3758_);
lean_dec(v_r_3660_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3773_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v_size_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
v_size_3764_ = lean_ctor_get(v_l_3756_, 0);
v___x_3765_ = lean_nat_add(v___x_3667_, v_size_3758_);
lean_dec(v_size_3758_);
v___x_3766_ = lean_nat_add(v___x_3667_, v_size_3764_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 4, v_l_3756_);
lean_ctor_set(v___x_3762_, 3, v_impl_3666_);
lean_ctor_set(v___x_3762_, 2, v_v_3658_);
lean_ctor_set(v___x_3762_, 1, v_k_3657_);
lean_ctor_set(v___x_3762_, 0, v___x_3766_);
v___x_3768_ = v___x_3762_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_3772_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_3772_, 3, v_impl_3666_);
lean_ctor_set(v_reuseFailAlloc_3772_, 4, v_l_3756_);
v___x_3768_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3770_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_r_3757_);
lean_ctor_set(v___x_3662_, 3, v___x_3768_);
lean_ctor_set(v___x_3662_, 2, v_v_3760_);
lean_ctor_set(v___x_3662_, 1, v_k_3759_);
lean_ctor_set(v___x_3662_, 0, v___x_3765_);
v___x_3770_ = v___x_3662_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v_k_3759_);
lean_ctor_set(v_reuseFailAlloc_3771_, 2, v_v_3760_);
lean_ctor_set(v_reuseFailAlloc_3771_, 3, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3771_, 4, v_r_3757_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
else
{
lean_object* v_k_3776_; lean_object* v_v_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3800_; 
v_k_3776_ = lean_ctor_get(v_r_3660_, 1);
v_v_3777_ = lean_ctor_get(v_r_3660_, 2);
v_isSharedCheck_3800_ = !lean_is_exclusive(v_r_3660_);
if (v_isSharedCheck_3800_ == 0)
{
lean_object* v_unused_3801_; lean_object* v_unused_3802_; lean_object* v_unused_3803_; 
v_unused_3801_ = lean_ctor_get(v_r_3660_, 4);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v_r_3660_, 3);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_r_3660_, 0);
lean_dec(v_unused_3803_);
v___x_3779_ = v_r_3660_;
v_isShared_3780_ = v_isSharedCheck_3800_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_v_3777_);
lean_inc(v_k_3776_);
lean_dec(v_r_3660_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3800_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v_k_3781_; lean_object* v_v_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3796_; 
v_k_3781_ = lean_ctor_get(v_l_3756_, 1);
v_v_3782_ = lean_ctor_get(v_l_3756_, 2);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_l_3756_);
if (v_isSharedCheck_3796_ == 0)
{
lean_object* v_unused_3797_; lean_object* v_unused_3798_; lean_object* v_unused_3799_; 
v_unused_3797_ = lean_ctor_get(v_l_3756_, 4);
lean_dec(v_unused_3797_);
v_unused_3798_ = lean_ctor_get(v_l_3756_, 3);
lean_dec(v_unused_3798_);
v_unused_3799_ = lean_ctor_get(v_l_3756_, 0);
lean_dec(v_unused_3799_);
v___x_3784_ = v_l_3756_;
v_isShared_3785_ = v_isSharedCheck_3796_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_v_3782_);
lean_inc(v_k_3781_);
lean_dec(v_l_3756_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3796_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3786_; lean_object* v___x_3788_; 
v___x_3786_ = lean_unsigned_to_nat(3u);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 4, v_r_3757_);
lean_ctor_set(v___x_3784_, 3, v_r_3757_);
lean_ctor_set(v___x_3784_, 2, v_v_3658_);
lean_ctor_set(v___x_3784_, 1, v_k_3657_);
lean_ctor_set(v___x_3784_, 0, v___x_3667_);
v___x_3788_ = v___x_3784_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_3795_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_3795_, 3, v_r_3757_);
lean_ctor_set(v_reuseFailAlloc_3795_, 4, v_r_3757_);
v___x_3788_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
lean_object* v___x_3790_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 3, v_r_3757_);
lean_ctor_set(v___x_3779_, 0, v___x_3667_);
v___x_3790_ = v___x_3779_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_k_3776_);
lean_ctor_set(v_reuseFailAlloc_3794_, 2, v_v_3777_);
lean_ctor_set(v_reuseFailAlloc_3794_, 3, v_r_3757_);
lean_ctor_set(v_reuseFailAlloc_3794_, 4, v_r_3757_);
v___x_3790_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
lean_object* v___x_3792_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v___x_3790_);
lean_ctor_set(v___x_3662_, 3, v___x_3788_);
lean_ctor_set(v___x_3662_, 2, v_v_3782_);
lean_ctor_set(v___x_3662_, 1, v_k_3781_);
lean_ctor_set(v___x_3662_, 0, v___x_3786_);
v___x_3792_ = v___x_3662_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3786_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_k_3781_);
lean_ctor_set(v_reuseFailAlloc_3793_, 2, v_v_3782_);
lean_ctor_set(v_reuseFailAlloc_3793_, 3, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3793_, 4, v___x_3790_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3804_; 
v_r_3804_ = lean_ctor_get(v_r_3660_, 4);
lean_inc(v_r_3804_);
if (lean_obj_tag(v_r_3804_) == 0)
{
lean_object* v_k_3805_; lean_object* v_v_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3817_; 
v_k_3805_ = lean_ctor_get(v_r_3660_, 1);
v_v_3806_ = lean_ctor_get(v_r_3660_, 2);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_r_3660_);
if (v_isSharedCheck_3817_ == 0)
{
lean_object* v_unused_3818_; lean_object* v_unused_3819_; lean_object* v_unused_3820_; 
v_unused_3818_ = lean_ctor_get(v_r_3660_, 4);
lean_dec(v_unused_3818_);
v_unused_3819_ = lean_ctor_get(v_r_3660_, 3);
lean_dec(v_unused_3819_);
v_unused_3820_ = lean_ctor_get(v_r_3660_, 0);
lean_dec(v_unused_3820_);
v___x_3808_ = v_r_3660_;
v_isShared_3809_ = v_isSharedCheck_3817_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_v_3806_);
lean_inc(v_k_3805_);
lean_dec(v_r_3660_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3817_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3810_; lean_object* v___x_3812_; 
v___x_3810_ = lean_unsigned_to_nat(3u);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 4, v_l_3756_);
lean_ctor_set(v___x_3808_, 2, v_v_3658_);
lean_ctor_set(v___x_3808_, 1, v_k_3657_);
lean_ctor_set(v___x_3808_, 0, v___x_3667_);
v___x_3812_ = v___x_3808_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_3816_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_3816_, 3, v_l_3756_);
lean_ctor_set(v_reuseFailAlloc_3816_, 4, v_l_3756_);
v___x_3812_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3814_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_r_3804_);
lean_ctor_set(v___x_3662_, 3, v___x_3812_);
lean_ctor_set(v___x_3662_, 2, v_v_3806_);
lean_ctor_set(v___x_3662_, 1, v_k_3805_);
lean_ctor_set(v___x_3662_, 0, v___x_3810_);
v___x_3814_ = v___x_3662_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3810_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_3815_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_3815_, 3, v___x_3812_);
lean_ctor_set(v_reuseFailAlloc_3815_, 4, v_r_3804_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
else
{
lean_object* v_size_3821_; lean_object* v_k_3822_; lean_object* v_v_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3834_; 
v_size_3821_ = lean_ctor_get(v_r_3660_, 0);
v_k_3822_ = lean_ctor_get(v_r_3660_, 1);
v_v_3823_ = lean_ctor_get(v_r_3660_, 2);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_r_3660_);
if (v_isSharedCheck_3834_ == 0)
{
lean_object* v_unused_3835_; lean_object* v_unused_3836_; 
v_unused_3835_ = lean_ctor_get(v_r_3660_, 4);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_r_3660_, 3);
lean_dec(v_unused_3836_);
v___x_3825_ = v_r_3660_;
v_isShared_3826_ = v_isSharedCheck_3834_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_v_3823_);
lean_inc(v_k_3822_);
lean_inc(v_size_3821_);
lean_dec(v_r_3660_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3834_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 3, v_r_3804_);
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_size_3821_);
lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_k_3822_);
lean_ctor_set(v_reuseFailAlloc_3833_, 2, v_v_3823_);
lean_ctor_set(v_reuseFailAlloc_3833_, 3, v_r_3804_);
lean_ctor_set(v_reuseFailAlloc_3833_, 4, v_r_3804_);
v___x_3828_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3829_; lean_object* v___x_3831_; 
v___x_3829_ = lean_unsigned_to_nat(2u);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v___x_3828_);
lean_ctor_set(v___x_3662_, 3, v_r_3804_);
lean_ctor_set(v___x_3662_, 0, v___x_3829_);
v___x_3831_ = v___x_3662_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3829_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_3832_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_3832_, 3, v_r_3804_);
lean_ctor_set(v_reuseFailAlloc_3832_, 4, v___x_3828_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
}
else
{
lean_object* v___x_3838_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 3, v_r_3660_);
lean_ctor_set(v___x_3662_, 0, v___x_3667_);
v___x_3838_ = v___x_3662_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_3839_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_3839_, 3, v_r_3660_);
lean_ctor_set(v_reuseFailAlloc_3839_, 4, v_r_3660_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3662_);
lean_dec(v_v_3658_);
lean_dec(v_k_3657_);
lean_dec(v_k_3655_);
lean_dec_ref(v_cmp_3654_);
if (lean_obj_tag(v_l_3659_) == 0)
{
if (lean_obj_tag(v_r_3660_) == 0)
{
lean_object* v_size_3840_; lean_object* v_k_3841_; lean_object* v_v_3842_; lean_object* v_l_3843_; lean_object* v_r_3844_; lean_object* v_size_3845_; lean_object* v_k_3846_; lean_object* v_v_3847_; lean_object* v_l_3848_; lean_object* v_r_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v_size_3840_ = lean_ctor_get(v_l_3659_, 0);
v_k_3841_ = lean_ctor_get(v_l_3659_, 1);
v_v_3842_ = lean_ctor_get(v_l_3659_, 2);
v_l_3843_ = lean_ctor_get(v_l_3659_, 3);
v_r_3844_ = lean_ctor_get(v_l_3659_, 4);
lean_inc(v_r_3844_);
v_size_3845_ = lean_ctor_get(v_r_3660_, 0);
v_k_3846_ = lean_ctor_get(v_r_3660_, 1);
v_v_3847_ = lean_ctor_get(v_r_3660_, 2);
v_l_3848_ = lean_ctor_get(v_r_3660_, 3);
lean_inc(v_l_3848_);
v_r_3849_ = lean_ctor_get(v_r_3660_, 4);
v___x_3850_ = lean_unsigned_to_nat(1u);
v___x_3851_ = lean_nat_dec_lt(v_size_3840_, v_size_3845_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3987_; 
lean_inc(v_l_3843_);
lean_inc(v_v_3842_);
lean_inc(v_k_3841_);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_l_3659_);
if (v_isSharedCheck_3987_ == 0)
{
lean_object* v_unused_3988_; lean_object* v_unused_3989_; lean_object* v_unused_3990_; lean_object* v_unused_3991_; lean_object* v_unused_3992_; 
v_unused_3988_ = lean_ctor_get(v_l_3659_, 4);
lean_dec(v_unused_3988_);
v_unused_3989_ = lean_ctor_get(v_l_3659_, 3);
lean_dec(v_unused_3989_);
v_unused_3990_ = lean_ctor_get(v_l_3659_, 2);
lean_dec(v_unused_3990_);
v_unused_3991_ = lean_ctor_get(v_l_3659_, 1);
lean_dec(v_unused_3991_);
v_unused_3992_ = lean_ctor_get(v_l_3659_, 0);
lean_dec(v_unused_3992_);
v___x_3853_ = v_l_3659_;
v_isShared_3854_ = v_isSharedCheck_3987_;
goto v_resetjp_3852_;
}
else
{
lean_dec(v_l_3659_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3987_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3855_; lean_object* v_tree_3856_; 
v___x_3855_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3841_, v_v_3842_, v_l_3843_, v_r_3844_);
v_tree_3856_ = lean_ctor_get(v___x_3855_, 2);
lean_inc(v_tree_3856_);
if (lean_obj_tag(v_tree_3856_) == 0)
{
lean_object* v_k_3857_; lean_object* v_v_3858_; lean_object* v_size_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; uint8_t v___x_3862_; 
v_k_3857_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_k_3857_);
v_v_3858_ = lean_ctor_get(v___x_3855_, 1);
lean_inc(v_v_3858_);
lean_dec_ref(v___x_3855_);
v_size_3859_ = lean_ctor_get(v_tree_3856_, 0);
v___x_3860_ = lean_unsigned_to_nat(3u);
v___x_3861_ = lean_nat_mul(v___x_3860_, v_size_3859_);
v___x_3862_ = lean_nat_dec_lt(v___x_3861_, v_size_3845_);
lean_dec(v___x_3861_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3866_; 
lean_dec(v_l_3848_);
v___x_3863_ = lean_nat_add(v___x_3850_, v_size_3859_);
v___x_3864_ = lean_nat_add(v___x_3863_, v_size_3845_);
lean_dec(v___x_3863_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 4, v_r_3660_);
lean_ctor_set(v___x_3853_, 3, v_tree_3856_);
lean_ctor_set(v___x_3853_, 2, v_v_3858_);
lean_ctor_set(v___x_3853_, 1, v_k_3857_);
lean_ctor_set(v___x_3853_, 0, v___x_3864_);
v___x_3866_ = v___x_3853_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_k_3857_);
lean_ctor_set(v_reuseFailAlloc_3867_, 2, v_v_3858_);
lean_ctor_set(v_reuseFailAlloc_3867_, 3, v_tree_3856_);
lean_ctor_set(v_reuseFailAlloc_3867_, 4, v_r_3660_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
else
{
lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3922_; 
lean_inc(v_r_3849_);
lean_inc(v_v_3847_);
lean_inc(v_k_3846_);
lean_inc(v_size_3845_);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_r_3660_);
if (v_isSharedCheck_3922_ == 0)
{
lean_object* v_unused_3923_; lean_object* v_unused_3924_; lean_object* v_unused_3925_; lean_object* v_unused_3926_; lean_object* v_unused_3927_; 
v_unused_3923_ = lean_ctor_get(v_r_3660_, 4);
lean_dec(v_unused_3923_);
v_unused_3924_ = lean_ctor_get(v_r_3660_, 3);
lean_dec(v_unused_3924_);
v_unused_3925_ = lean_ctor_get(v_r_3660_, 2);
lean_dec(v_unused_3925_);
v_unused_3926_ = lean_ctor_get(v_r_3660_, 1);
lean_dec(v_unused_3926_);
v_unused_3927_ = lean_ctor_get(v_r_3660_, 0);
lean_dec(v_unused_3927_);
v___x_3869_ = v_r_3660_;
v_isShared_3870_ = v_isSharedCheck_3922_;
goto v_resetjp_3868_;
}
else
{
lean_dec(v_r_3660_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3922_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v_size_3871_; lean_object* v_k_3872_; lean_object* v_v_3873_; lean_object* v_l_3874_; lean_object* v_r_3875_; lean_object* v_size_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; uint8_t v___x_3879_; 
v_size_3871_ = lean_ctor_get(v_l_3848_, 0);
v_k_3872_ = lean_ctor_get(v_l_3848_, 1);
v_v_3873_ = lean_ctor_get(v_l_3848_, 2);
v_l_3874_ = lean_ctor_get(v_l_3848_, 3);
v_r_3875_ = lean_ctor_get(v_l_3848_, 4);
v_size_3876_ = lean_ctor_get(v_r_3849_, 0);
v___x_3877_ = lean_unsigned_to_nat(2u);
v___x_3878_ = lean_nat_mul(v___x_3877_, v_size_3876_);
v___x_3879_ = lean_nat_dec_lt(v_size_3871_, v___x_3878_);
lean_dec(v___x_3878_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3907_; 
lean_inc(v_r_3875_);
lean_inc(v_l_3874_);
lean_inc(v_v_3873_);
lean_inc(v_k_3872_);
v_isSharedCheck_3907_ = !lean_is_exclusive(v_l_3848_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; lean_object* v_unused_3909_; lean_object* v_unused_3910_; lean_object* v_unused_3911_; lean_object* v_unused_3912_; 
v_unused_3908_ = lean_ctor_get(v_l_3848_, 4);
lean_dec(v_unused_3908_);
v_unused_3909_ = lean_ctor_get(v_l_3848_, 3);
lean_dec(v_unused_3909_);
v_unused_3910_ = lean_ctor_get(v_l_3848_, 2);
lean_dec(v_unused_3910_);
v_unused_3911_ = lean_ctor_get(v_l_3848_, 1);
lean_dec(v_unused_3911_);
v_unused_3912_ = lean_ctor_get(v_l_3848_, 0);
lean_dec(v_unused_3912_);
v___x_3881_ = v_l_3848_;
v_isShared_3882_ = v_isSharedCheck_3907_;
goto v_resetjp_3880_;
}
else
{
lean_dec(v_l_3848_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3907_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3897_; 
v___x_3883_ = lean_nat_add(v___x_3850_, v_size_3859_);
v___x_3884_ = lean_nat_add(v___x_3883_, v_size_3845_);
lean_dec(v_size_3845_);
if (lean_obj_tag(v_l_3874_) == 0)
{
lean_object* v_size_3905_; 
v_size_3905_ = lean_ctor_get(v_l_3874_, 0);
lean_inc(v_size_3905_);
v___y_3897_ = v_size_3905_;
goto v___jp_3896_;
}
else
{
lean_object* v___x_3906_; 
v___x_3906_ = lean_unsigned_to_nat(0u);
v___y_3897_ = v___x_3906_;
goto v___jp_3896_;
}
v___jp_3885_:
{
lean_object* v___x_3889_; lean_object* v___x_3891_; 
v___x_3889_ = lean_nat_add(v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec(v___y_3887_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 4, v_r_3849_);
lean_ctor_set(v___x_3881_, 3, v_r_3875_);
lean_ctor_set(v___x_3881_, 2, v_v_3847_);
lean_ctor_set(v___x_3881_, 1, v_k_3846_);
lean_ctor_set(v___x_3881_, 0, v___x_3889_);
v___x_3891_ = v___x_3881_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v_k_3846_);
lean_ctor_set(v_reuseFailAlloc_3895_, 2, v_v_3847_);
lean_ctor_set(v_reuseFailAlloc_3895_, 3, v_r_3875_);
lean_ctor_set(v_reuseFailAlloc_3895_, 4, v_r_3849_);
v___x_3891_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
lean_object* v___x_3893_; 
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 4, v___x_3891_);
lean_ctor_set(v___x_3869_, 3, v___y_3886_);
lean_ctor_set(v___x_3869_, 2, v_v_3873_);
lean_ctor_set(v___x_3869_, 1, v_k_3872_);
lean_ctor_set(v___x_3869_, 0, v___x_3884_);
v___x_3893_ = v___x_3869_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_k_3872_);
lean_ctor_set(v_reuseFailAlloc_3894_, 2, v_v_3873_);
lean_ctor_set(v_reuseFailAlloc_3894_, 3, v___y_3886_);
lean_ctor_set(v_reuseFailAlloc_3894_, 4, v___x_3891_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
v___jp_3896_:
{
lean_object* v___x_3898_; lean_object* v___x_3900_; 
v___x_3898_ = lean_nat_add(v___x_3883_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec(v___x_3883_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 4, v_l_3874_);
lean_ctor_set(v___x_3853_, 3, v_tree_3856_);
lean_ctor_set(v___x_3853_, 2, v_v_3858_);
lean_ctor_set(v___x_3853_, 1, v_k_3857_);
lean_ctor_set(v___x_3853_, 0, v___x_3898_);
v___x_3900_ = v___x_3853_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3898_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_k_3857_);
lean_ctor_set(v_reuseFailAlloc_3904_, 2, v_v_3858_);
lean_ctor_set(v_reuseFailAlloc_3904_, 3, v_tree_3856_);
lean_ctor_set(v_reuseFailAlloc_3904_, 4, v_l_3874_);
v___x_3900_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
lean_object* v___x_3901_; 
v___x_3901_ = lean_nat_add(v___x_3850_, v_size_3876_);
if (lean_obj_tag(v_r_3875_) == 0)
{
lean_object* v_size_3902_; 
v_size_3902_ = lean_ctor_get(v_r_3875_, 0);
lean_inc(v_size_3902_);
v___y_3886_ = v___x_3900_;
v___y_3887_ = v___x_3901_;
v___y_3888_ = v_size_3902_;
goto v___jp_3885_;
}
else
{
lean_object* v___x_3903_; 
v___x_3903_ = lean_unsigned_to_nat(0u);
v___y_3886_ = v___x_3900_;
v___y_3887_ = v___x_3901_;
v___y_3888_ = v___x_3903_;
goto v___jp_3885_;
}
}
}
}
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3917_; 
v___x_3913_ = lean_nat_add(v___x_3850_, v_size_3859_);
v___x_3914_ = lean_nat_add(v___x_3913_, v_size_3845_);
lean_dec(v_size_3845_);
v___x_3915_ = lean_nat_add(v___x_3913_, v_size_3871_);
lean_dec(v___x_3913_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 4, v_l_3848_);
lean_ctor_set(v___x_3869_, 3, v_tree_3856_);
lean_ctor_set(v___x_3869_, 2, v_v_3858_);
lean_ctor_set(v___x_3869_, 1, v_k_3857_);
lean_ctor_set(v___x_3869_, 0, v___x_3915_);
v___x_3917_ = v___x_3869_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v_k_3857_);
lean_ctor_set(v_reuseFailAlloc_3921_, 2, v_v_3858_);
lean_ctor_set(v_reuseFailAlloc_3921_, 3, v_tree_3856_);
lean_ctor_set(v_reuseFailAlloc_3921_, 4, v_l_3848_);
v___x_3917_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3919_; 
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 4, v_r_3849_);
lean_ctor_set(v___x_3853_, 3, v___x_3917_);
lean_ctor_set(v___x_3853_, 2, v_v_3847_);
lean_ctor_set(v___x_3853_, 1, v_k_3846_);
lean_ctor_set(v___x_3853_, 0, v___x_3914_);
v___x_3919_ = v___x_3853_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3914_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v_k_3846_);
lean_ctor_set(v_reuseFailAlloc_3920_, 2, v_v_3847_);
lean_ctor_set(v_reuseFailAlloc_3920_, 3, v___x_3917_);
lean_ctor_set(v_reuseFailAlloc_3920_, 4, v_r_3849_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
}
else
{
lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3981_; 
lean_inc(v_r_3849_);
lean_inc(v_v_3847_);
lean_inc(v_k_3846_);
lean_inc(v_size_3845_);
v_isSharedCheck_3981_ = !lean_is_exclusive(v_r_3660_);
if (v_isSharedCheck_3981_ == 0)
{
lean_object* v_unused_3982_; lean_object* v_unused_3983_; lean_object* v_unused_3984_; lean_object* v_unused_3985_; lean_object* v_unused_3986_; 
v_unused_3982_ = lean_ctor_get(v_r_3660_, 4);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_r_3660_, 3);
lean_dec(v_unused_3983_);
v_unused_3984_ = lean_ctor_get(v_r_3660_, 2);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_r_3660_, 1);
lean_dec(v_unused_3985_);
v_unused_3986_ = lean_ctor_get(v_r_3660_, 0);
lean_dec(v_unused_3986_);
v___x_3929_ = v_r_3660_;
v_isShared_3930_ = v_isSharedCheck_3981_;
goto v_resetjp_3928_;
}
else
{
lean_dec(v_r_3660_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3981_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
if (lean_obj_tag(v_l_3848_) == 0)
{
if (lean_obj_tag(v_r_3849_) == 0)
{
lean_object* v_k_3931_; lean_object* v_v_3932_; lean_object* v_size_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3937_; 
v_k_3931_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_k_3931_);
v_v_3932_ = lean_ctor_get(v___x_3855_, 1);
lean_inc(v_v_3932_);
lean_dec_ref(v___x_3855_);
v_size_3933_ = lean_ctor_get(v_l_3848_, 0);
v___x_3934_ = lean_nat_add(v___x_3850_, v_size_3845_);
lean_dec(v_size_3845_);
v___x_3935_ = lean_nat_add(v___x_3850_, v_size_3933_);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 4, v_l_3848_);
lean_ctor_set(v___x_3929_, 3, v_tree_3856_);
lean_ctor_set(v___x_3929_, 2, v_v_3932_);
lean_ctor_set(v___x_3929_, 1, v_k_3931_);
lean_ctor_set(v___x_3929_, 0, v___x_3935_);
v___x_3937_ = v___x_3929_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3941_, 1, v_k_3931_);
lean_ctor_set(v_reuseFailAlloc_3941_, 2, v_v_3932_);
lean_ctor_set(v_reuseFailAlloc_3941_, 3, v_tree_3856_);
lean_ctor_set(v_reuseFailAlloc_3941_, 4, v_l_3848_);
v___x_3937_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
lean_object* v___x_3939_; 
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 4, v_r_3849_);
lean_ctor_set(v___x_3853_, 3, v___x_3937_);
lean_ctor_set(v___x_3853_, 2, v_v_3847_);
lean_ctor_set(v___x_3853_, 1, v_k_3846_);
lean_ctor_set(v___x_3853_, 0, v___x_3934_);
v___x_3939_ = v___x_3853_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3934_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_k_3846_);
lean_ctor_set(v_reuseFailAlloc_3940_, 2, v_v_3847_);
lean_ctor_set(v_reuseFailAlloc_3940_, 3, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3940_, 4, v_r_3849_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
else
{
lean_object* v_k_3942_; lean_object* v_v_3943_; lean_object* v_k_3944_; lean_object* v_v_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3959_; 
lean_dec(v_size_3845_);
v_k_3942_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_k_3942_);
v_v_3943_ = lean_ctor_get(v___x_3855_, 1);
lean_inc(v_v_3943_);
lean_dec_ref(v___x_3855_);
v_k_3944_ = lean_ctor_get(v_l_3848_, 1);
v_v_3945_ = lean_ctor_get(v_l_3848_, 2);
v_isSharedCheck_3959_ = !lean_is_exclusive(v_l_3848_);
if (v_isSharedCheck_3959_ == 0)
{
lean_object* v_unused_3960_; lean_object* v_unused_3961_; lean_object* v_unused_3962_; 
v_unused_3960_ = lean_ctor_get(v_l_3848_, 4);
lean_dec(v_unused_3960_);
v_unused_3961_ = lean_ctor_get(v_l_3848_, 3);
lean_dec(v_unused_3961_);
v_unused_3962_ = lean_ctor_get(v_l_3848_, 0);
lean_dec(v_unused_3962_);
v___x_3947_ = v_l_3848_;
v_isShared_3948_ = v_isSharedCheck_3959_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_v_3945_);
lean_inc(v_k_3944_);
lean_dec(v_l_3848_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3959_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3949_; lean_object* v___x_3951_; 
v___x_3949_ = lean_unsigned_to_nat(3u);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 4, v_r_3849_);
lean_ctor_set(v___x_3947_, 3, v_r_3849_);
lean_ctor_set(v___x_3947_, 2, v_v_3943_);
lean_ctor_set(v___x_3947_, 1, v_k_3942_);
lean_ctor_set(v___x_3947_, 0, v___x_3850_);
v___x_3951_ = v___x_3947_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v_k_3942_);
lean_ctor_set(v_reuseFailAlloc_3958_, 2, v_v_3943_);
lean_ctor_set(v_reuseFailAlloc_3958_, 3, v_r_3849_);
lean_ctor_set(v_reuseFailAlloc_3958_, 4, v_r_3849_);
v___x_3951_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
lean_object* v___x_3953_; 
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 3, v_r_3849_);
lean_ctor_set(v___x_3929_, 0, v___x_3850_);
v___x_3953_ = v___x_3929_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v_k_3846_);
lean_ctor_set(v_reuseFailAlloc_3957_, 2, v_v_3847_);
lean_ctor_set(v_reuseFailAlloc_3957_, 3, v_r_3849_);
lean_ctor_set(v_reuseFailAlloc_3957_, 4, v_r_3849_);
v___x_3953_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
lean_object* v___x_3955_; 
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 4, v___x_3953_);
lean_ctor_set(v___x_3853_, 3, v___x_3951_);
lean_ctor_set(v___x_3853_, 2, v_v_3945_);
lean_ctor_set(v___x_3853_, 1, v_k_3944_);
lean_ctor_set(v___x_3853_, 0, v___x_3949_);
v___x_3955_ = v___x_3853_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3949_);
lean_ctor_set(v_reuseFailAlloc_3956_, 1, v_k_3944_);
lean_ctor_set(v_reuseFailAlloc_3956_, 2, v_v_3945_);
lean_ctor_set(v_reuseFailAlloc_3956_, 3, v___x_3951_);
lean_ctor_set(v_reuseFailAlloc_3956_, 4, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3849_) == 0)
{
lean_object* v_k_3963_; lean_object* v_v_3964_; lean_object* v___x_3965_; lean_object* v___x_3967_; 
lean_dec(v_size_3845_);
v_k_3963_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_k_3963_);
v_v_3964_ = lean_ctor_get(v___x_3855_, 1);
lean_inc(v_v_3964_);
lean_dec_ref(v___x_3855_);
v___x_3965_ = lean_unsigned_to_nat(3u);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 4, v_l_3848_);
lean_ctor_set(v___x_3929_, 2, v_v_3964_);
lean_ctor_set(v___x_3929_, 1, v_k_3963_);
lean_ctor_set(v___x_3929_, 0, v___x_3850_);
v___x_3967_ = v___x_3929_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v_k_3963_);
lean_ctor_set(v_reuseFailAlloc_3971_, 2, v_v_3964_);
lean_ctor_set(v_reuseFailAlloc_3971_, 3, v_l_3848_);
lean_ctor_set(v_reuseFailAlloc_3971_, 4, v_l_3848_);
v___x_3967_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
lean_object* v___x_3969_; 
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 4, v_r_3849_);
lean_ctor_set(v___x_3853_, 3, v___x_3967_);
lean_ctor_set(v___x_3853_, 2, v_v_3847_);
lean_ctor_set(v___x_3853_, 1, v_k_3846_);
lean_ctor_set(v___x_3853_, 0, v___x_3965_);
v___x_3969_ = v___x_3853_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3965_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v_k_3846_);
lean_ctor_set(v_reuseFailAlloc_3970_, 2, v_v_3847_);
lean_ctor_set(v_reuseFailAlloc_3970_, 3, v___x_3967_);
lean_ctor_set(v_reuseFailAlloc_3970_, 4, v_r_3849_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
else
{
lean_object* v_k_3972_; lean_object* v_v_3973_; lean_object* v___x_3975_; 
v_k_3972_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_k_3972_);
v_v_3973_ = lean_ctor_get(v___x_3855_, 1);
lean_inc(v_v_3973_);
lean_dec_ref(v___x_3855_);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 3, v_r_3849_);
v___x_3975_ = v___x_3929_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_size_3845_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_k_3846_);
lean_ctor_set(v_reuseFailAlloc_3980_, 2, v_v_3847_);
lean_ctor_set(v_reuseFailAlloc_3980_, 3, v_r_3849_);
lean_ctor_set(v_reuseFailAlloc_3980_, 4, v_r_3849_);
v___x_3975_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3976_ = lean_unsigned_to_nat(2u);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 4, v___x_3975_);
lean_ctor_set(v___x_3853_, 3, v_r_3849_);
lean_ctor_set(v___x_3853_, 2, v_v_3973_);
lean_ctor_set(v___x_3853_, 1, v_k_3972_);
lean_ctor_set(v___x_3853_, 0, v___x_3976_);
v___x_3978_ = v___x_3853_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v_k_3972_);
lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_v_3973_);
lean_ctor_set(v_reuseFailAlloc_3979_, 3, v_r_3849_);
lean_ctor_set(v_reuseFailAlloc_3979_, 4, v___x_3975_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
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
lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4145_; 
lean_inc(v_r_3849_);
lean_inc(v_v_3847_);
lean_inc(v_k_3846_);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_r_3660_);
if (v_isSharedCheck_4145_ == 0)
{
lean_object* v_unused_4146_; lean_object* v_unused_4147_; lean_object* v_unused_4148_; lean_object* v_unused_4149_; lean_object* v_unused_4150_; 
v_unused_4146_ = lean_ctor_get(v_r_3660_, 4);
lean_dec(v_unused_4146_);
v_unused_4147_ = lean_ctor_get(v_r_3660_, 3);
lean_dec(v_unused_4147_);
v_unused_4148_ = lean_ctor_get(v_r_3660_, 2);
lean_dec(v_unused_4148_);
v_unused_4149_ = lean_ctor_get(v_r_3660_, 1);
lean_dec(v_unused_4149_);
v_unused_4150_ = lean_ctor_get(v_r_3660_, 0);
lean_dec(v_unused_4150_);
v___x_3994_ = v_r_3660_;
v_isShared_3995_ = v_isSharedCheck_4145_;
goto v_resetjp_3993_;
}
else
{
lean_dec(v_r_3660_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4145_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3996_; lean_object* v_tree_3997_; 
v___x_3996_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3846_, v_v_3847_, v_l_3848_, v_r_3849_);
v_tree_3997_ = lean_ctor_get(v___x_3996_, 2);
lean_inc(v_tree_3997_);
if (lean_obj_tag(v_tree_3997_) == 0)
{
lean_object* v_k_3998_; lean_object* v_v_3999_; lean_object* v_size_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; uint8_t v___x_4003_; 
v_k_3998_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_k_3998_);
v_v_3999_ = lean_ctor_get(v___x_3996_, 1);
lean_inc(v_v_3999_);
lean_dec_ref(v___x_3996_);
v_size_4000_ = lean_ctor_get(v_tree_3997_, 0);
v___x_4001_ = lean_unsigned_to_nat(3u);
v___x_4002_ = lean_nat_mul(v___x_4001_, v_size_4000_);
v___x_4003_ = lean_nat_dec_lt(v___x_4002_, v_size_3840_);
lean_dec(v___x_4002_);
if (v___x_4003_ == 0)
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4007_; 
lean_dec(v_r_3844_);
v___x_4004_ = lean_nat_add(v___x_3850_, v_size_3840_);
v___x_4005_ = lean_nat_add(v___x_4004_, v_size_4000_);
lean_dec(v___x_4004_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 4, v_tree_3997_);
lean_ctor_set(v___x_3994_, 3, v_l_3659_);
lean_ctor_set(v___x_3994_, 2, v_v_3999_);
lean_ctor_set(v___x_3994_, 1, v_k_3998_);
lean_ctor_set(v___x_3994_, 0, v___x_4005_);
v___x_4007_ = v___x_3994_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4005_);
lean_ctor_set(v_reuseFailAlloc_4008_, 1, v_k_3998_);
lean_ctor_set(v_reuseFailAlloc_4008_, 2, v_v_3999_);
lean_ctor_set(v_reuseFailAlloc_4008_, 3, v_l_3659_);
lean_ctor_set(v_reuseFailAlloc_4008_, 4, v_tree_3997_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
else
{
lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4074_; 
lean_inc(v_l_3843_);
lean_inc(v_v_3842_);
lean_inc(v_k_3841_);
lean_inc(v_size_3840_);
v_isSharedCheck_4074_ = !lean_is_exclusive(v_l_3659_);
if (v_isSharedCheck_4074_ == 0)
{
lean_object* v_unused_4075_; lean_object* v_unused_4076_; lean_object* v_unused_4077_; lean_object* v_unused_4078_; lean_object* v_unused_4079_; 
v_unused_4075_ = lean_ctor_get(v_l_3659_, 4);
lean_dec(v_unused_4075_);
v_unused_4076_ = lean_ctor_get(v_l_3659_, 3);
lean_dec(v_unused_4076_);
v_unused_4077_ = lean_ctor_get(v_l_3659_, 2);
lean_dec(v_unused_4077_);
v_unused_4078_ = lean_ctor_get(v_l_3659_, 1);
lean_dec(v_unused_4078_);
v_unused_4079_ = lean_ctor_get(v_l_3659_, 0);
lean_dec(v_unused_4079_);
v___x_4010_ = v_l_3659_;
v_isShared_4011_ = v_isSharedCheck_4074_;
goto v_resetjp_4009_;
}
else
{
lean_dec(v_l_3659_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4074_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v_size_4012_; lean_object* v_size_4013_; lean_object* v_k_4014_; lean_object* v_v_4015_; lean_object* v_l_4016_; lean_object* v_r_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; uint8_t v___x_4020_; 
v_size_4012_ = lean_ctor_get(v_l_3843_, 0);
v_size_4013_ = lean_ctor_get(v_r_3844_, 0);
v_k_4014_ = lean_ctor_get(v_r_3844_, 1);
v_v_4015_ = lean_ctor_get(v_r_3844_, 2);
v_l_4016_ = lean_ctor_get(v_r_3844_, 3);
v_r_4017_ = lean_ctor_get(v_r_3844_, 4);
v___x_4018_ = lean_unsigned_to_nat(2u);
v___x_4019_ = lean_nat_mul(v___x_4018_, v_size_4012_);
v___x_4020_ = lean_nat_dec_lt(v_size_4013_, v___x_4019_);
lean_dec(v___x_4019_);
if (v___x_4020_ == 0)
{
lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4058_; 
lean_inc(v_r_4017_);
lean_inc(v_l_4016_);
lean_inc(v_v_4015_);
lean_inc(v_k_4014_);
lean_del_object(v___x_4010_);
v_isSharedCheck_4058_ = !lean_is_exclusive(v_r_3844_);
if (v_isSharedCheck_4058_ == 0)
{
lean_object* v_unused_4059_; lean_object* v_unused_4060_; lean_object* v_unused_4061_; lean_object* v_unused_4062_; lean_object* v_unused_4063_; 
v_unused_4059_ = lean_ctor_get(v_r_3844_, 4);
lean_dec(v_unused_4059_);
v_unused_4060_ = lean_ctor_get(v_r_3844_, 3);
lean_dec(v_unused_4060_);
v_unused_4061_ = lean_ctor_get(v_r_3844_, 2);
lean_dec(v_unused_4061_);
v_unused_4062_ = lean_ctor_get(v_r_3844_, 1);
lean_dec(v_unused_4062_);
v_unused_4063_ = lean_ctor_get(v_r_3844_, 0);
lean_dec(v_unused_4063_);
v___x_4022_ = v_r_3844_;
v_isShared_4023_ = v_isSharedCheck_4058_;
goto v_resetjp_4021_;
}
else
{
lean_dec(v_r_3844_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4058_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___x_4046_; lean_object* v___y_4048_; 
v___x_4024_ = lean_nat_add(v___x_3850_, v_size_3840_);
lean_dec(v_size_3840_);
v___x_4025_ = lean_nat_add(v___x_4024_, v_size_4000_);
lean_dec(v___x_4024_);
v___x_4046_ = lean_nat_add(v___x_3850_, v_size_4012_);
if (lean_obj_tag(v_l_4016_) == 0)
{
lean_object* v_size_4056_; 
v_size_4056_ = lean_ctor_get(v_l_4016_, 0);
lean_inc(v_size_4056_);
v___y_4048_ = v_size_4056_;
goto v___jp_4047_;
}
else
{
lean_object* v___x_4057_; 
v___x_4057_ = lean_unsigned_to_nat(0u);
v___y_4048_ = v___x_4057_;
goto v___jp_4047_;
}
v___jp_4026_:
{
lean_object* v___x_4030_; lean_object* v___x_4032_; 
v___x_4030_ = lean_nat_add(v___y_4028_, v___y_4029_);
lean_dec(v___y_4029_);
lean_dec(v___y_4028_);
lean_inc_ref(v_tree_3997_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 4, v_tree_3997_);
lean_ctor_set(v___x_4022_, 3, v_r_4017_);
lean_ctor_set(v___x_4022_, 2, v_v_3999_);
lean_ctor_set(v___x_4022_, 1, v_k_3998_);
lean_ctor_set(v___x_4022_, 0, v___x_4030_);
v___x_4032_ = v___x_4022_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4030_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v_k_3998_);
lean_ctor_set(v_reuseFailAlloc_4045_, 2, v_v_3999_);
lean_ctor_set(v_reuseFailAlloc_4045_, 3, v_r_4017_);
lean_ctor_set(v_reuseFailAlloc_4045_, 4, v_tree_3997_);
v___x_4032_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
v_isSharedCheck_4039_ = !lean_is_exclusive(v_tree_3997_);
if (v_isSharedCheck_4039_ == 0)
{
lean_object* v_unused_4040_; lean_object* v_unused_4041_; lean_object* v_unused_4042_; lean_object* v_unused_4043_; lean_object* v_unused_4044_; 
v_unused_4040_ = lean_ctor_get(v_tree_3997_, 4);
lean_dec(v_unused_4040_);
v_unused_4041_ = lean_ctor_get(v_tree_3997_, 3);
lean_dec(v_unused_4041_);
v_unused_4042_ = lean_ctor_get(v_tree_3997_, 2);
lean_dec(v_unused_4042_);
v_unused_4043_ = lean_ctor_get(v_tree_3997_, 1);
lean_dec(v_unused_4043_);
v_unused_4044_ = lean_ctor_get(v_tree_3997_, 0);
lean_dec(v_unused_4044_);
v___x_4034_ = v_tree_3997_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_dec(v_tree_3997_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 4, v___x_4032_);
lean_ctor_set(v___x_4034_, 3, v___y_4027_);
lean_ctor_set(v___x_4034_, 2, v_v_4015_);
lean_ctor_set(v___x_4034_, 1, v_k_4014_);
lean_ctor_set(v___x_4034_, 0, v___x_4025_);
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4038_, 1, v_k_4014_);
lean_ctor_set(v_reuseFailAlloc_4038_, 2, v_v_4015_);
lean_ctor_set(v_reuseFailAlloc_4038_, 3, v___y_4027_);
lean_ctor_set(v_reuseFailAlloc_4038_, 4, v___x_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
v___jp_4047_:
{
lean_object* v___x_4049_; lean_object* v___x_4051_; 
v___x_4049_ = lean_nat_add(v___x_4046_, v___y_4048_);
lean_dec(v___y_4048_);
lean_dec(v___x_4046_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 4, v_l_4016_);
lean_ctor_set(v___x_3994_, 3, v_l_3843_);
lean_ctor_set(v___x_3994_, 2, v_v_3842_);
lean_ctor_set(v___x_3994_, 1, v_k_3841_);
lean_ctor_set(v___x_3994_, 0, v___x_4049_);
v___x_4051_ = v___x_3994_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4049_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v_k_3841_);
lean_ctor_set(v_reuseFailAlloc_4055_, 2, v_v_3842_);
lean_ctor_set(v_reuseFailAlloc_4055_, 3, v_l_3843_);
lean_ctor_set(v_reuseFailAlloc_4055_, 4, v_l_4016_);
v___x_4051_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
lean_object* v___x_4052_; 
v___x_4052_ = lean_nat_add(v___x_3850_, v_size_4000_);
if (lean_obj_tag(v_r_4017_) == 0)
{
lean_object* v_size_4053_; 
v_size_4053_ = lean_ctor_get(v_r_4017_, 0);
lean_inc(v_size_4053_);
v___y_4027_ = v___x_4051_;
v___y_4028_ = v___x_4052_;
v___y_4029_ = v_size_4053_;
goto v___jp_4026_;
}
else
{
lean_object* v___x_4054_; 
v___x_4054_ = lean_unsigned_to_nat(0u);
v___y_4027_ = v___x_4051_;
v___y_4028_ = v___x_4052_;
v___y_4029_ = v___x_4054_;
goto v___jp_4026_;
}
}
}
}
}
else
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4069_; 
v___x_4064_ = lean_nat_add(v___x_3850_, v_size_3840_);
lean_dec(v_size_3840_);
v___x_4065_ = lean_nat_add(v___x_4064_, v_size_4000_);
lean_dec(v___x_4064_);
v___x_4066_ = lean_nat_add(v___x_3850_, v_size_4000_);
v___x_4067_ = lean_nat_add(v___x_4066_, v_size_4013_);
lean_dec(v___x_4066_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 4, v_tree_3997_);
lean_ctor_set(v___x_3994_, 3, v_r_3844_);
lean_ctor_set(v___x_3994_, 2, v_v_3999_);
lean_ctor_set(v___x_3994_, 1, v_k_3998_);
lean_ctor_set(v___x_3994_, 0, v___x_4067_);
v___x_4069_ = v___x_3994_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4073_, 1, v_k_3998_);
lean_ctor_set(v_reuseFailAlloc_4073_, 2, v_v_3999_);
lean_ctor_set(v_reuseFailAlloc_4073_, 3, v_r_3844_);
lean_ctor_set(v_reuseFailAlloc_4073_, 4, v_tree_3997_);
v___x_4069_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4071_; 
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 4, v___x_4069_);
lean_ctor_set(v___x_4010_, 0, v___x_4065_);
v___x_4071_ = v___x_4010_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v___x_4065_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v_k_3841_);
lean_ctor_set(v_reuseFailAlloc_4072_, 2, v_v_3842_);
lean_ctor_set(v_reuseFailAlloc_4072_, 3, v_l_3843_);
lean_ctor_set(v_reuseFailAlloc_4072_, 4, v___x_4069_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3843_) == 0)
{
lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4103_; 
lean_inc_ref(v_l_3843_);
lean_inc(v_v_3842_);
lean_inc(v_k_3841_);
lean_inc(v_size_3840_);
v_isSharedCheck_4103_ = !lean_is_exclusive(v_l_3659_);
if (v_isSharedCheck_4103_ == 0)
{
lean_object* v_unused_4104_; lean_object* v_unused_4105_; lean_object* v_unused_4106_; lean_object* v_unused_4107_; lean_object* v_unused_4108_; 
v_unused_4104_ = lean_ctor_get(v_l_3659_, 4);
lean_dec(v_unused_4104_);
v_unused_4105_ = lean_ctor_get(v_l_3659_, 3);
lean_dec(v_unused_4105_);
v_unused_4106_ = lean_ctor_get(v_l_3659_, 2);
lean_dec(v_unused_4106_);
v_unused_4107_ = lean_ctor_get(v_l_3659_, 1);
lean_dec(v_unused_4107_);
v_unused_4108_ = lean_ctor_get(v_l_3659_, 0);
lean_dec(v_unused_4108_);
v___x_4081_ = v_l_3659_;
v_isShared_4082_ = v_isSharedCheck_4103_;
goto v_resetjp_4080_;
}
else
{
lean_dec(v_l_3659_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4103_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
if (lean_obj_tag(v_r_3844_) == 0)
{
lean_object* v_k_4083_; lean_object* v_v_4084_; lean_object* v_size_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4089_; 
v_k_4083_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_k_4083_);
v_v_4084_ = lean_ctor_get(v___x_3996_, 1);
lean_inc(v_v_4084_);
lean_dec_ref(v___x_3996_);
v_size_4085_ = lean_ctor_get(v_r_3844_, 0);
v___x_4086_ = lean_nat_add(v___x_3850_, v_size_3840_);
lean_dec(v_size_3840_);
v___x_4087_ = lean_nat_add(v___x_3850_, v_size_4085_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 4, v_tree_3997_);
lean_ctor_set(v___x_3994_, 3, v_r_3844_);
lean_ctor_set(v___x_3994_, 2, v_v_4084_);
lean_ctor_set(v___x_3994_, 1, v_k_4083_);
lean_ctor_set(v___x_3994_, 0, v___x_4087_);
v___x_4089_ = v___x_3994_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4087_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v_k_4083_);
lean_ctor_set(v_reuseFailAlloc_4093_, 2, v_v_4084_);
lean_ctor_set(v_reuseFailAlloc_4093_, 3, v_r_3844_);
lean_ctor_set(v_reuseFailAlloc_4093_, 4, v_tree_3997_);
v___x_4089_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
lean_object* v___x_4091_; 
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 4, v___x_4089_);
lean_ctor_set(v___x_4081_, 0, v___x_4086_);
v___x_4091_ = v___x_4081_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4086_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v_k_3841_);
lean_ctor_set(v_reuseFailAlloc_4092_, 2, v_v_3842_);
lean_ctor_set(v_reuseFailAlloc_4092_, 3, v_l_3843_);
lean_ctor_set(v_reuseFailAlloc_4092_, 4, v___x_4089_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
else
{
lean_object* v_k_4094_; lean_object* v_v_4095_; lean_object* v___x_4096_; lean_object* v___x_4098_; 
lean_dec(v_size_3840_);
v_k_4094_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_k_4094_);
v_v_4095_ = lean_ctor_get(v___x_3996_, 1);
lean_inc(v_v_4095_);
lean_dec_ref(v___x_3996_);
v___x_4096_ = lean_unsigned_to_nat(3u);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 4, v_r_3844_);
lean_ctor_set(v___x_3994_, 3, v_r_3844_);
lean_ctor_set(v___x_3994_, 2, v_v_4095_);
lean_ctor_set(v___x_3994_, 1, v_k_4094_);
lean_ctor_set(v___x_3994_, 0, v___x_3850_);
v___x_4098_ = v___x_3994_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_4102_, 1, v_k_4094_);
lean_ctor_set(v_reuseFailAlloc_4102_, 2, v_v_4095_);
lean_ctor_set(v_reuseFailAlloc_4102_, 3, v_r_3844_);
lean_ctor_set(v_reuseFailAlloc_4102_, 4, v_r_3844_);
v___x_4098_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
lean_object* v___x_4100_; 
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 4, v___x_4098_);
lean_ctor_set(v___x_4081_, 0, v___x_4096_);
v___x_4100_ = v___x_4081_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v___x_4096_);
lean_ctor_set(v_reuseFailAlloc_4101_, 1, v_k_3841_);
lean_ctor_set(v_reuseFailAlloc_4101_, 2, v_v_3842_);
lean_ctor_set(v_reuseFailAlloc_4101_, 3, v_l_3843_);
lean_ctor_set(v_reuseFailAlloc_4101_, 4, v___x_4098_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3844_) == 0)
{
lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4133_; 
lean_inc(v_l_3843_);
lean_inc(v_v_3842_);
lean_inc(v_k_3841_);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_l_3659_);
if (v_isSharedCheck_4133_ == 0)
{
lean_object* v_unused_4134_; lean_object* v_unused_4135_; lean_object* v_unused_4136_; lean_object* v_unused_4137_; lean_object* v_unused_4138_; 
v_unused_4134_ = lean_ctor_get(v_l_3659_, 4);
lean_dec(v_unused_4134_);
v_unused_4135_ = lean_ctor_get(v_l_3659_, 3);
lean_dec(v_unused_4135_);
v_unused_4136_ = lean_ctor_get(v_l_3659_, 2);
lean_dec(v_unused_4136_);
v_unused_4137_ = lean_ctor_get(v_l_3659_, 1);
lean_dec(v_unused_4137_);
v_unused_4138_ = lean_ctor_get(v_l_3659_, 0);
lean_dec(v_unused_4138_);
v___x_4110_ = v_l_3659_;
v_isShared_4111_ = v_isSharedCheck_4133_;
goto v_resetjp_4109_;
}
else
{
lean_dec(v_l_3659_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4133_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v_k_4112_; lean_object* v_v_4113_; lean_object* v_k_4114_; lean_object* v_v_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4129_; 
v_k_4112_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_k_4112_);
v_v_4113_ = lean_ctor_get(v___x_3996_, 1);
lean_inc(v_v_4113_);
lean_dec_ref(v___x_3996_);
v_k_4114_ = lean_ctor_get(v_r_3844_, 1);
v_v_4115_ = lean_ctor_get(v_r_3844_, 2);
v_isSharedCheck_4129_ = !lean_is_exclusive(v_r_3844_);
if (v_isSharedCheck_4129_ == 0)
{
lean_object* v_unused_4130_; lean_object* v_unused_4131_; lean_object* v_unused_4132_; 
v_unused_4130_ = lean_ctor_get(v_r_3844_, 4);
lean_dec(v_unused_4130_);
v_unused_4131_ = lean_ctor_get(v_r_3844_, 3);
lean_dec(v_unused_4131_);
v_unused_4132_ = lean_ctor_get(v_r_3844_, 0);
lean_dec(v_unused_4132_);
v___x_4117_ = v_r_3844_;
v_isShared_4118_ = v_isSharedCheck_4129_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_v_4115_);
lean_inc(v_k_4114_);
lean_dec(v_r_3844_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4129_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4119_; lean_object* v___x_4121_; 
v___x_4119_ = lean_unsigned_to_nat(3u);
if (v_isShared_4118_ == 0)
{
lean_ctor_set(v___x_4117_, 4, v_l_3843_);
lean_ctor_set(v___x_4117_, 3, v_l_3843_);
lean_ctor_set(v___x_4117_, 2, v_v_3842_);
lean_ctor_set(v___x_4117_, 1, v_k_3841_);
lean_ctor_set(v___x_4117_, 0, v___x_3850_);
v___x_4121_ = v___x_4117_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_4128_, 1, v_k_3841_);
lean_ctor_set(v_reuseFailAlloc_4128_, 2, v_v_3842_);
lean_ctor_set(v_reuseFailAlloc_4128_, 3, v_l_3843_);
lean_ctor_set(v_reuseFailAlloc_4128_, 4, v_l_3843_);
v___x_4121_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
lean_object* v___x_4123_; 
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 4, v_l_3843_);
lean_ctor_set(v___x_3994_, 3, v_l_3843_);
lean_ctor_set(v___x_3994_, 2, v_v_4113_);
lean_ctor_set(v___x_3994_, 1, v_k_4112_);
lean_ctor_set(v___x_3994_, 0, v___x_3850_);
v___x_4123_ = v___x_3994_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v_k_4112_);
lean_ctor_set(v_reuseFailAlloc_4127_, 2, v_v_4113_);
lean_ctor_set(v_reuseFailAlloc_4127_, 3, v_l_3843_);
lean_ctor_set(v_reuseFailAlloc_4127_, 4, v_l_3843_);
v___x_4123_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4125_; 
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 4, v___x_4123_);
lean_ctor_set(v___x_4110_, 3, v___x_4121_);
lean_ctor_set(v___x_4110_, 2, v_v_4115_);
lean_ctor_set(v___x_4110_, 1, v_k_4114_);
lean_ctor_set(v___x_4110_, 0, v___x_4119_);
v___x_4125_ = v___x_4110_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4119_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v_k_4114_);
lean_ctor_set(v_reuseFailAlloc_4126_, 2, v_v_4115_);
lean_ctor_set(v_reuseFailAlloc_4126_, 3, v___x_4121_);
lean_ctor_set(v_reuseFailAlloc_4126_, 4, v___x_4123_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
}
}
else
{
lean_object* v_k_4139_; lean_object* v_v_4140_; lean_object* v___x_4141_; lean_object* v___x_4143_; 
v_k_4139_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_k_4139_);
v_v_4140_ = lean_ctor_get(v___x_3996_, 1);
lean_inc(v_v_4140_);
lean_dec_ref(v___x_3996_);
v___x_4141_ = lean_unsigned_to_nat(2u);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 4, v_r_3844_);
lean_ctor_set(v___x_3994_, 3, v_l_3659_);
lean_ctor_set(v___x_3994_, 2, v_v_4140_);
lean_ctor_set(v___x_3994_, 1, v_k_4139_);
lean_ctor_set(v___x_3994_, 0, v___x_4141_);
v___x_4143_ = v___x_3994_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4141_);
lean_ctor_set(v_reuseFailAlloc_4144_, 1, v_k_4139_);
lean_ctor_set(v_reuseFailAlloc_4144_, 2, v_v_4140_);
lean_ctor_set(v_reuseFailAlloc_4144_, 3, v_l_3659_);
lean_ctor_set(v_reuseFailAlloc_4144_, 4, v_r_3844_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
}
}
}
else
{
return v_l_3659_;
}
}
else
{
return v_r_3660_;
}
}
default: 
{
lean_object* v_impl_4151_; lean_object* v___x_4152_; 
v_impl_4151_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_3654_, v_k_3655_, v_r_3660_);
v___x_4152_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_4151_) == 0)
{
if (lean_obj_tag(v_l_3659_) == 0)
{
lean_object* v_size_4153_; lean_object* v_size_4154_; lean_object* v_k_4155_; lean_object* v_v_4156_; lean_object* v_l_4157_; lean_object* v_r_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; 
v_size_4153_ = lean_ctor_get(v_impl_4151_, 0);
lean_inc(v_size_4153_);
v_size_4154_ = lean_ctor_get(v_l_3659_, 0);
v_k_4155_ = lean_ctor_get(v_l_3659_, 1);
v_v_4156_ = lean_ctor_get(v_l_3659_, 2);
v_l_4157_ = lean_ctor_get(v_l_3659_, 3);
v_r_4158_ = lean_ctor_get(v_l_3659_, 4);
lean_inc(v_r_4158_);
v___x_4159_ = lean_unsigned_to_nat(3u);
v___x_4160_ = lean_nat_mul(v___x_4159_, v_size_4153_);
v___x_4161_ = lean_nat_dec_lt(v___x_4160_, v_size_4154_);
lean_dec(v___x_4160_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4165_; 
lean_dec(v_r_4158_);
v___x_4162_ = lean_nat_add(v___x_4152_, v_size_4154_);
v___x_4163_ = lean_nat_add(v___x_4162_, v_size_4153_);
lean_dec(v_size_4153_);
lean_dec(v___x_4162_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_impl_4151_);
lean_ctor_set(v___x_3662_, 0, v___x_4163_);
v___x_4165_ = v___x_3662_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4163_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_4166_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_4166_, 3, v_l_3659_);
lean_ctor_set(v_reuseFailAlloc_4166_, 4, v_impl_4151_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
else
{
lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4232_; 
lean_inc(v_l_4157_);
lean_inc(v_v_4156_);
lean_inc(v_k_4155_);
lean_inc(v_size_4154_);
v_isSharedCheck_4232_ = !lean_is_exclusive(v_l_3659_);
if (v_isSharedCheck_4232_ == 0)
{
lean_object* v_unused_4233_; lean_object* v_unused_4234_; lean_object* v_unused_4235_; lean_object* v_unused_4236_; lean_object* v_unused_4237_; 
v_unused_4233_ = lean_ctor_get(v_l_3659_, 4);
lean_dec(v_unused_4233_);
v_unused_4234_ = lean_ctor_get(v_l_3659_, 3);
lean_dec(v_unused_4234_);
v_unused_4235_ = lean_ctor_get(v_l_3659_, 2);
lean_dec(v_unused_4235_);
v_unused_4236_ = lean_ctor_get(v_l_3659_, 1);
lean_dec(v_unused_4236_);
v_unused_4237_ = lean_ctor_get(v_l_3659_, 0);
lean_dec(v_unused_4237_);
v___x_4168_ = v_l_3659_;
v_isShared_4169_ = v_isSharedCheck_4232_;
goto v_resetjp_4167_;
}
else
{
lean_dec(v_l_3659_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4232_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v_size_4170_; lean_object* v_size_4171_; lean_object* v_k_4172_; lean_object* v_v_4173_; lean_object* v_l_4174_; lean_object* v_r_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; uint8_t v___x_4178_; 
v_size_4170_ = lean_ctor_get(v_l_4157_, 0);
v_size_4171_ = lean_ctor_get(v_r_4158_, 0);
v_k_4172_ = lean_ctor_get(v_r_4158_, 1);
v_v_4173_ = lean_ctor_get(v_r_4158_, 2);
v_l_4174_ = lean_ctor_get(v_r_4158_, 3);
v_r_4175_ = lean_ctor_get(v_r_4158_, 4);
v___x_4176_ = lean_unsigned_to_nat(2u);
v___x_4177_ = lean_nat_mul(v___x_4176_, v_size_4170_);
v___x_4178_ = lean_nat_dec_lt(v_size_4171_, v___x_4177_);
lean_dec(v___x_4177_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4207_; 
lean_inc(v_r_4175_);
lean_inc(v_l_4174_);
lean_inc(v_v_4173_);
lean_inc(v_k_4172_);
v_isSharedCheck_4207_ = !lean_is_exclusive(v_r_4158_);
if (v_isSharedCheck_4207_ == 0)
{
lean_object* v_unused_4208_; lean_object* v_unused_4209_; lean_object* v_unused_4210_; lean_object* v_unused_4211_; lean_object* v_unused_4212_; 
v_unused_4208_ = lean_ctor_get(v_r_4158_, 4);
lean_dec(v_unused_4208_);
v_unused_4209_ = lean_ctor_get(v_r_4158_, 3);
lean_dec(v_unused_4209_);
v_unused_4210_ = lean_ctor_get(v_r_4158_, 2);
lean_dec(v_unused_4210_);
v_unused_4211_ = lean_ctor_get(v_r_4158_, 1);
lean_dec(v_unused_4211_);
v_unused_4212_ = lean_ctor_get(v_r_4158_, 0);
lean_dec(v_unused_4212_);
v___x_4180_ = v_r_4158_;
v_isShared_4181_ = v_isSharedCheck_4207_;
goto v_resetjp_4179_;
}
else
{
lean_dec(v_r_4158_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4207_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___x_4195_; lean_object* v___y_4197_; 
v___x_4182_ = lean_nat_add(v___x_4152_, v_size_4154_);
lean_dec(v_size_4154_);
v___x_4183_ = lean_nat_add(v___x_4182_, v_size_4153_);
lean_dec(v___x_4182_);
v___x_4195_ = lean_nat_add(v___x_4152_, v_size_4170_);
if (lean_obj_tag(v_l_4174_) == 0)
{
lean_object* v_size_4205_; 
v_size_4205_ = lean_ctor_get(v_l_4174_, 0);
lean_inc(v_size_4205_);
v___y_4197_ = v_size_4205_;
goto v___jp_4196_;
}
else
{
lean_object* v___x_4206_; 
v___x_4206_ = lean_unsigned_to_nat(0u);
v___y_4197_ = v___x_4206_;
goto v___jp_4196_;
}
v___jp_4184_:
{
lean_object* v___x_4188_; lean_object* v___x_4190_; 
v___x_4188_ = lean_nat_add(v___y_4186_, v___y_4187_);
lean_dec(v___y_4187_);
lean_dec(v___y_4186_);
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 4, v_impl_4151_);
lean_ctor_set(v___x_4180_, 3, v_r_4175_);
lean_ctor_set(v___x_4180_, 2, v_v_3658_);
lean_ctor_set(v___x_4180_, 1, v_k_3657_);
lean_ctor_set(v___x_4180_, 0, v___x_4188_);
v___x_4190_ = v___x_4180_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_4194_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_4194_, 3, v_r_4175_);
lean_ctor_set(v_reuseFailAlloc_4194_, 4, v_impl_4151_);
v___x_4190_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
lean_object* v___x_4192_; 
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 4, v___x_4190_);
lean_ctor_set(v___x_4168_, 3, v___y_4185_);
lean_ctor_set(v___x_4168_, 2, v_v_4173_);
lean_ctor_set(v___x_4168_, 1, v_k_4172_);
lean_ctor_set(v___x_4168_, 0, v___x_4183_);
v___x_4192_ = v___x_4168_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4183_);
lean_ctor_set(v_reuseFailAlloc_4193_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4193_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4193_, 3, v___y_4185_);
lean_ctor_set(v_reuseFailAlloc_4193_, 4, v___x_4190_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
v___jp_4196_:
{
lean_object* v___x_4198_; lean_object* v___x_4200_; 
v___x_4198_ = lean_nat_add(v___x_4195_, v___y_4197_);
lean_dec(v___y_4197_);
lean_dec(v___x_4195_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_l_4174_);
lean_ctor_set(v___x_3662_, 3, v_l_4157_);
lean_ctor_set(v___x_3662_, 2, v_v_4156_);
lean_ctor_set(v___x_3662_, 1, v_k_4155_);
lean_ctor_set(v___x_3662_, 0, v___x_4198_);
v___x_4200_ = v___x_3662_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v___x_4198_);
lean_ctor_set(v_reuseFailAlloc_4204_, 1, v_k_4155_);
lean_ctor_set(v_reuseFailAlloc_4204_, 2, v_v_4156_);
lean_ctor_set(v_reuseFailAlloc_4204_, 3, v_l_4157_);
lean_ctor_set(v_reuseFailAlloc_4204_, 4, v_l_4174_);
v___x_4200_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
lean_object* v___x_4201_; 
v___x_4201_ = lean_nat_add(v___x_4152_, v_size_4153_);
lean_dec(v_size_4153_);
if (lean_obj_tag(v_r_4175_) == 0)
{
lean_object* v_size_4202_; 
v_size_4202_ = lean_ctor_get(v_r_4175_, 0);
lean_inc(v_size_4202_);
v___y_4185_ = v___x_4200_;
v___y_4186_ = v___x_4201_;
v___y_4187_ = v_size_4202_;
goto v___jp_4184_;
}
else
{
lean_object* v___x_4203_; 
v___x_4203_ = lean_unsigned_to_nat(0u);
v___y_4185_ = v___x_4200_;
v___y_4186_ = v___x_4201_;
v___y_4187_ = v___x_4203_;
goto v___jp_4184_;
}
}
}
}
}
else
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4218_; 
lean_del_object(v___x_3662_);
v___x_4213_ = lean_nat_add(v___x_4152_, v_size_4154_);
lean_dec(v_size_4154_);
v___x_4214_ = lean_nat_add(v___x_4213_, v_size_4153_);
lean_dec(v___x_4213_);
v___x_4215_ = lean_nat_add(v___x_4152_, v_size_4153_);
lean_dec(v_size_4153_);
v___x_4216_ = lean_nat_add(v___x_4215_, v_size_4171_);
lean_dec(v___x_4215_);
lean_inc_ref(v_impl_4151_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 4, v_impl_4151_);
lean_ctor_set(v___x_4168_, 3, v_r_4158_);
lean_ctor_set(v___x_4168_, 2, v_v_3658_);
lean_ctor_set(v___x_4168_, 1, v_k_3657_);
lean_ctor_set(v___x_4168_, 0, v___x_4216_);
v___x_4218_ = v___x_4168_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4216_);
lean_ctor_set(v_reuseFailAlloc_4231_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_4231_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_4231_, 3, v_r_4158_);
lean_ctor_set(v_reuseFailAlloc_4231_, 4, v_impl_4151_);
v___x_4218_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
v_isSharedCheck_4225_ = !lean_is_exclusive(v_impl_4151_);
if (v_isSharedCheck_4225_ == 0)
{
lean_object* v_unused_4226_; lean_object* v_unused_4227_; lean_object* v_unused_4228_; lean_object* v_unused_4229_; lean_object* v_unused_4230_; 
v_unused_4226_ = lean_ctor_get(v_impl_4151_, 4);
lean_dec(v_unused_4226_);
v_unused_4227_ = lean_ctor_get(v_impl_4151_, 3);
lean_dec(v_unused_4227_);
v_unused_4228_ = lean_ctor_get(v_impl_4151_, 2);
lean_dec(v_unused_4228_);
v_unused_4229_ = lean_ctor_get(v_impl_4151_, 1);
lean_dec(v_unused_4229_);
v_unused_4230_ = lean_ctor_get(v_impl_4151_, 0);
lean_dec(v_unused_4230_);
v___x_4220_ = v_impl_4151_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_dec(v_impl_4151_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 4, v___x_4218_);
lean_ctor_set(v___x_4220_, 3, v_l_4157_);
lean_ctor_set(v___x_4220_, 2, v_v_4156_);
lean_ctor_set(v___x_4220_, 1, v_k_4155_);
lean_ctor_set(v___x_4220_, 0, v___x_4214_);
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4214_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v_k_4155_);
lean_ctor_set(v_reuseFailAlloc_4224_, 2, v_v_4156_);
lean_ctor_set(v_reuseFailAlloc_4224_, 3, v_l_4157_);
lean_ctor_set(v_reuseFailAlloc_4224_, 4, v___x_4218_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_4238_; lean_object* v___x_4239_; lean_object* v___x_4241_; 
v_size_4238_ = lean_ctor_get(v_impl_4151_, 0);
lean_inc(v_size_4238_);
v___x_4239_ = lean_nat_add(v___x_4152_, v_size_4238_);
lean_dec(v_size_4238_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_impl_4151_);
lean_ctor_set(v___x_3662_, 0, v___x_4239_);
v___x_4241_ = v___x_3662_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4239_);
lean_ctor_set(v_reuseFailAlloc_4242_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_4242_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_4242_, 3, v_l_3659_);
lean_ctor_set(v_reuseFailAlloc_4242_, 4, v_impl_4151_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
else
{
if (lean_obj_tag(v_l_3659_) == 0)
{
lean_object* v_l_4243_; 
v_l_4243_ = lean_ctor_get(v_l_3659_, 3);
if (lean_obj_tag(v_l_4243_) == 0)
{
lean_object* v_r_4244_; 
lean_inc_ref(v_l_4243_);
v_r_4244_ = lean_ctor_get(v_l_3659_, 4);
lean_inc(v_r_4244_);
if (lean_obj_tag(v_r_4244_) == 0)
{
lean_object* v_size_4245_; lean_object* v_k_4246_; lean_object* v_v_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4260_; 
v_size_4245_ = lean_ctor_get(v_l_3659_, 0);
v_k_4246_ = lean_ctor_get(v_l_3659_, 1);
v_v_4247_ = lean_ctor_get(v_l_3659_, 2);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_l_3659_);
if (v_isSharedCheck_4260_ == 0)
{
lean_object* v_unused_4261_; lean_object* v_unused_4262_; 
v_unused_4261_ = lean_ctor_get(v_l_3659_, 4);
lean_dec(v_unused_4261_);
v_unused_4262_ = lean_ctor_get(v_l_3659_, 3);
lean_dec(v_unused_4262_);
v___x_4249_ = v_l_3659_;
v_isShared_4250_ = v_isSharedCheck_4260_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_v_4247_);
lean_inc(v_k_4246_);
lean_inc(v_size_4245_);
lean_dec(v_l_3659_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4260_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v_size_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4255_; 
v_size_4251_ = lean_ctor_get(v_r_4244_, 0);
v___x_4252_ = lean_nat_add(v___x_4152_, v_size_4245_);
lean_dec(v_size_4245_);
v___x_4253_ = lean_nat_add(v___x_4152_, v_size_4251_);
if (v_isShared_4250_ == 0)
{
lean_ctor_set(v___x_4249_, 4, v_impl_4151_);
lean_ctor_set(v___x_4249_, 3, v_r_4244_);
lean_ctor_set(v___x_4249_, 2, v_v_3658_);
lean_ctor_set(v___x_4249_, 1, v_k_3657_);
lean_ctor_set(v___x_4249_, 0, v___x_4253_);
v___x_4255_ = v___x_4249_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4253_);
lean_ctor_set(v_reuseFailAlloc_4259_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_4259_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_4259_, 3, v_r_4244_);
lean_ctor_set(v_reuseFailAlloc_4259_, 4, v_impl_4151_);
v___x_4255_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
lean_object* v___x_4257_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v___x_4255_);
lean_ctor_set(v___x_3662_, 3, v_l_4243_);
lean_ctor_set(v___x_3662_, 2, v_v_4247_);
lean_ctor_set(v___x_3662_, 1, v_k_4246_);
lean_ctor_set(v___x_3662_, 0, v___x_4252_);
v___x_4257_ = v___x_3662_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4252_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_k_4246_);
lean_ctor_set(v_reuseFailAlloc_4258_, 2, v_v_4247_);
lean_ctor_set(v_reuseFailAlloc_4258_, 3, v_l_4243_);
lean_ctor_set(v_reuseFailAlloc_4258_, 4, v___x_4255_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
else
{
lean_object* v_k_4263_; lean_object* v_v_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4275_; 
v_k_4263_ = lean_ctor_get(v_l_3659_, 1);
v_v_4264_ = lean_ctor_get(v_l_3659_, 2);
v_isSharedCheck_4275_ = !lean_is_exclusive(v_l_3659_);
if (v_isSharedCheck_4275_ == 0)
{
lean_object* v_unused_4276_; lean_object* v_unused_4277_; lean_object* v_unused_4278_; 
v_unused_4276_ = lean_ctor_get(v_l_3659_, 4);
lean_dec(v_unused_4276_);
v_unused_4277_ = lean_ctor_get(v_l_3659_, 3);
lean_dec(v_unused_4277_);
v_unused_4278_ = lean_ctor_get(v_l_3659_, 0);
lean_dec(v_unused_4278_);
v___x_4266_ = v_l_3659_;
v_isShared_4267_ = v_isSharedCheck_4275_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_v_4264_);
lean_inc(v_k_4263_);
lean_dec(v_l_3659_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4275_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4268_; lean_object* v___x_4270_; 
v___x_4268_ = lean_unsigned_to_nat(3u);
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 3, v_r_4244_);
lean_ctor_set(v___x_4266_, 2, v_v_3658_);
lean_ctor_set(v___x_4266_, 1, v_k_3657_);
lean_ctor_set(v___x_4266_, 0, v___x_4152_);
v___x_4270_ = v___x_4266_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4152_);
lean_ctor_set(v_reuseFailAlloc_4274_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_4274_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_4274_, 3, v_r_4244_);
lean_ctor_set(v_reuseFailAlloc_4274_, 4, v_r_4244_);
v___x_4270_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
lean_object* v___x_4272_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v___x_4270_);
lean_ctor_set(v___x_3662_, 3, v_l_4243_);
lean_ctor_set(v___x_3662_, 2, v_v_4264_);
lean_ctor_set(v___x_3662_, 1, v_k_4263_);
lean_ctor_set(v___x_3662_, 0, v___x_4268_);
v___x_4272_ = v___x_3662_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4268_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v_k_4263_);
lean_ctor_set(v_reuseFailAlloc_4273_, 2, v_v_4264_);
lean_ctor_set(v_reuseFailAlloc_4273_, 3, v_l_4243_);
lean_ctor_set(v_reuseFailAlloc_4273_, 4, v___x_4270_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
}
else
{
lean_object* v_r_4279_; 
v_r_4279_ = lean_ctor_get(v_l_3659_, 4);
lean_inc(v_r_4279_);
if (lean_obj_tag(v_r_4279_) == 0)
{
lean_object* v_k_4280_; lean_object* v_v_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4304_; 
lean_inc(v_l_4243_);
v_k_4280_ = lean_ctor_get(v_l_3659_, 1);
v_v_4281_ = lean_ctor_get(v_l_3659_, 2);
v_isSharedCheck_4304_ = !lean_is_exclusive(v_l_3659_);
if (v_isSharedCheck_4304_ == 0)
{
lean_object* v_unused_4305_; lean_object* v_unused_4306_; lean_object* v_unused_4307_; 
v_unused_4305_ = lean_ctor_get(v_l_3659_, 4);
lean_dec(v_unused_4305_);
v_unused_4306_ = lean_ctor_get(v_l_3659_, 3);
lean_dec(v_unused_4306_);
v_unused_4307_ = lean_ctor_get(v_l_3659_, 0);
lean_dec(v_unused_4307_);
v___x_4283_ = v_l_3659_;
v_isShared_4284_ = v_isSharedCheck_4304_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_v_4281_);
lean_inc(v_k_4280_);
lean_dec(v_l_3659_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4304_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v_k_4285_; lean_object* v_v_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4300_; 
v_k_4285_ = lean_ctor_get(v_r_4279_, 1);
v_v_4286_ = lean_ctor_get(v_r_4279_, 2);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_r_4279_);
if (v_isSharedCheck_4300_ == 0)
{
lean_object* v_unused_4301_; lean_object* v_unused_4302_; lean_object* v_unused_4303_; 
v_unused_4301_ = lean_ctor_get(v_r_4279_, 4);
lean_dec(v_unused_4301_);
v_unused_4302_ = lean_ctor_get(v_r_4279_, 3);
lean_dec(v_unused_4302_);
v_unused_4303_ = lean_ctor_get(v_r_4279_, 0);
lean_dec(v_unused_4303_);
v___x_4288_ = v_r_4279_;
v_isShared_4289_ = v_isSharedCheck_4300_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_v_4286_);
lean_inc(v_k_4285_);
lean_dec(v_r_4279_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4300_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4290_; lean_object* v___x_4292_; 
v___x_4290_ = lean_unsigned_to_nat(3u);
if (v_isShared_4289_ == 0)
{
lean_ctor_set(v___x_4288_, 4, v_l_4243_);
lean_ctor_set(v___x_4288_, 3, v_l_4243_);
lean_ctor_set(v___x_4288_, 2, v_v_4281_);
lean_ctor_set(v___x_4288_, 1, v_k_4280_);
lean_ctor_set(v___x_4288_, 0, v___x_4152_);
v___x_4292_ = v___x_4288_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v___x_4152_);
lean_ctor_set(v_reuseFailAlloc_4299_, 1, v_k_4280_);
lean_ctor_set(v_reuseFailAlloc_4299_, 2, v_v_4281_);
lean_ctor_set(v_reuseFailAlloc_4299_, 3, v_l_4243_);
lean_ctor_set(v_reuseFailAlloc_4299_, 4, v_l_4243_);
v___x_4292_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
lean_object* v___x_4294_; 
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 4, v_l_4243_);
lean_ctor_set(v___x_4283_, 2, v_v_3658_);
lean_ctor_set(v___x_4283_, 1, v_k_3657_);
lean_ctor_set(v___x_4283_, 0, v___x_4152_);
v___x_4294_ = v___x_4283_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4152_);
lean_ctor_set(v_reuseFailAlloc_4298_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_4298_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_4298_, 3, v_l_4243_);
lean_ctor_set(v_reuseFailAlloc_4298_, 4, v_l_4243_);
v___x_4294_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
lean_object* v___x_4296_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v___x_4294_);
lean_ctor_set(v___x_3662_, 3, v___x_4292_);
lean_ctor_set(v___x_3662_, 2, v_v_4286_);
lean_ctor_set(v___x_3662_, 1, v_k_4285_);
lean_ctor_set(v___x_3662_, 0, v___x_4290_);
v___x_4296_ = v___x_3662_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v___x_4290_);
lean_ctor_set(v_reuseFailAlloc_4297_, 1, v_k_4285_);
lean_ctor_set(v_reuseFailAlloc_4297_, 2, v_v_4286_);
lean_ctor_set(v_reuseFailAlloc_4297_, 3, v___x_4292_);
lean_ctor_set(v_reuseFailAlloc_4297_, 4, v___x_4294_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
}
}
else
{
lean_object* v___x_4308_; lean_object* v___x_4310_; 
v___x_4308_ = lean_unsigned_to_nat(2u);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_r_4279_);
lean_ctor_set(v___x_3662_, 0, v___x_4308_);
v___x_4310_ = v___x_3662_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4308_);
lean_ctor_set(v_reuseFailAlloc_4311_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_4311_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_4311_, 3, v_l_3659_);
lean_ctor_set(v_reuseFailAlloc_4311_, 4, v_r_4279_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
}
else
{
lean_object* v___x_4313_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_l_3659_);
lean_ctor_set(v___x_3662_, 0, v___x_4152_);
v___x_4313_ = v___x_3662_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v___x_4152_);
lean_ctor_set(v_reuseFailAlloc_4314_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_4314_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_4314_, 3, v_l_3659_);
lean_ctor_set(v_reuseFailAlloc_4314_, 4, v_l_3659_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_3655_);
lean_dec_ref(v_cmp_3654_);
return v_t_3656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(lean_object* v_cmp_4317_, lean_object* v_init_4318_, lean_object* v_x_4319_){
_start:
{
if (lean_obj_tag(v_x_4319_) == 0)
{
lean_object* v_k_4320_; lean_object* v_l_4321_; lean_object* v_r_4322_; lean_object* v___x_4323_; lean_object* v_a_4324_; lean_object* v_r_4325_; 
v_k_4320_ = lean_ctor_get(v_x_4319_, 1);
lean_inc(v_k_4320_);
v_l_4321_ = lean_ctor_get(v_x_4319_, 3);
lean_inc(v_l_4321_);
v_r_4322_ = lean_ctor_get(v_x_4319_, 4);
lean_inc(v_r_4322_);
lean_dec_ref(v_x_4319_);
lean_inc_ref(v_cmp_4317_);
v___x_4323_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4317_, v_init_4318_, v_l_4321_);
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref(v___x_4323_);
lean_inc_ref(v_cmp_4317_);
v_r_4325_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_4317_, v_k_4320_, v_a_4324_);
v_init_4318_ = v_r_4325_;
v_x_4319_ = v_r_4322_;
goto _start;
}
else
{
lean_object* v___x_4327_; 
lean_dec_ref(v_cmp_4317_);
v___x_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4327_, 0, v_init_4318_);
return v___x_4327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(lean_object* v_cmp_4328_, lean_object* v_t_u2082_4329_, lean_object* v_t_4330_){
_start:
{
if (lean_obj_tag(v_t_4330_) == 0)
{
lean_object* v_k_4331_; lean_object* v_v_4332_; lean_object* v_l_4333_; lean_object* v_r_4334_; uint8_t v___x_4335_; 
v_k_4331_ = lean_ctor_get(v_t_4330_, 1);
lean_inc(v_k_4331_);
v_v_4332_ = lean_ctor_get(v_t_4330_, 2);
lean_inc(v_v_4332_);
v_l_4333_ = lean_ctor_get(v_t_4330_, 3);
lean_inc(v_l_4333_);
v_r_4334_ = lean_ctor_get(v_t_4330_, 4);
lean_inc(v_r_4334_);
lean_dec_ref(v_t_4330_);
lean_inc(v_t_u2082_4329_);
lean_inc(v_k_4331_);
lean_inc_ref(v_cmp_4328_);
v___x_4335_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_4328_, v_k_4331_, v_t_u2082_4329_);
if (v___x_4335_ == 0)
{
lean_object* v_impl_4336_; lean_object* v_impl_4337_; lean_object* v___x_4338_; 
lean_inc(v_t_u2082_4329_);
lean_inc_ref(v_cmp_4328_);
v_impl_4336_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4328_, v_t_u2082_4329_, v_l_4333_);
v_impl_4337_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4328_, v_t_u2082_4329_, v_r_4334_);
v___x_4338_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_4331_, v_v_4332_, v_impl_4336_, v_impl_4337_);
return v___x_4338_;
}
else
{
lean_object* v_impl_4339_; lean_object* v_impl_4340_; lean_object* v___x_4341_; 
lean_dec(v_v_4332_);
lean_dec(v_k_4331_);
lean_inc(v_t_u2082_4329_);
lean_inc_ref(v_cmp_4328_);
v_impl_4339_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4328_, v_t_u2082_4329_, v_l_4333_);
v_impl_4340_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4328_, v_t_u2082_4329_, v_r_4334_);
v___x_4341_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_4339_, v_impl_4340_);
return v___x_4341_;
}
}
else
{
lean_dec(v_t_u2082_4329_);
lean_dec_ref(v_cmp_4328_);
return v_t_4330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object* v_cmp_4342_, lean_object* v_t_u2081_4343_, lean_object* v_t_u2082_4344_){
_start:
{
lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4353_; 
if (lean_obj_tag(v_t_u2081_4343_) == 0)
{
lean_object* v_size_4356_; 
v_size_4356_ = lean_ctor_get(v_t_u2081_4343_, 0);
lean_inc(v_size_4356_);
v___y_4353_ = v_size_4356_;
goto v___jp_4352_;
}
else
{
lean_object* v___x_4357_; 
v___x_4357_ = lean_unsigned_to_nat(0u);
v___y_4353_ = v___x_4357_;
goto v___jp_4352_;
}
v___jp_4345_:
{
uint8_t v___x_4348_; 
v___x_4348_ = lean_nat_dec_le(v___y_4346_, v___y_4347_);
lean_dec(v___y_4347_);
lean_dec(v___y_4346_);
if (v___x_4348_ == 0)
{
lean_object* v___x_4349_; lean_object* v_a_4350_; 
v___x_4349_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4342_, v_t_u2081_4343_, v_t_u2082_4344_);
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref(v___x_4349_);
return v_a_4350_;
}
else
{
lean_object* v___x_4351_; 
v___x_4351_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4342_, v_t_u2082_4344_, v_t_u2081_4343_);
return v___x_4351_;
}
}
v___jp_4352_:
{
if (lean_obj_tag(v_t_u2082_4344_) == 0)
{
lean_object* v_size_4354_; 
v_size_4354_ = lean_ctor_get(v_t_u2082_4344_, 0);
lean_inc(v_size_4354_);
v___y_4346_ = v___y_4353_;
v___y_4347_ = v_size_4354_;
goto v___jp_4345_;
}
else
{
lean_object* v___x_4355_; 
v___x_4355_ = lean_unsigned_to_nat(0u);
v___y_4346_ = v___y_4353_;
v___y_4347_ = v___x_4355_;
goto v___jp_4345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff___redArg(lean_object* v_cmp_4358_, lean_object* v_t_u2081_4359_, lean_object* v_t_u2082_4360_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4358_, v_t_u2081_4359_, v_t_u2082_4360_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff(lean_object* v_00_u03b1_4362_, lean_object* v_00_u03b2_4363_, lean_object* v_cmp_4364_, lean_object* v_t_u2081_4365_, lean_object* v_t_u2082_4366_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4364_, v_t_u2081_4365_, v_t_u2082_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0(lean_object* v_00_u03b1_4368_, lean_object* v_cmp_4369_, lean_object* v_00_u03b2_4370_, lean_object* v_t_u2081_4371_, lean_object* v_t_u2082_4372_, lean_object* v_h_u2081_4373_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4369_, v_t_u2081_4371_, v_t_u2082_4372_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0(lean_object* v_00_u03b1_4375_, lean_object* v_cmp_4376_, lean_object* v_00_u03b2_4377_, lean_object* v_k_4378_, lean_object* v_t_4379_, lean_object* v_h_4380_){
_start:
{
lean_object* v___x_4381_; 
v___x_4381_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_4376_, v_k_4378_, v_t_4379_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1(lean_object* v_00_u03b1_4382_, lean_object* v_00_u03b2_4383_, lean_object* v_cmp_4384_, lean_object* v_init_4385_, lean_object* v_x_4386_){
_start:
{
lean_object* v___x_4387_; 
v___x_4387_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4384_, v_init_4385_, v_x_4386_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2(lean_object* v_00_u03b1_4388_, lean_object* v_00_u03b2_4389_, lean_object* v_cmp_4390_, lean_object* v_t_u2082_4391_, lean_object* v_t_4392_, lean_object* v_hl_4393_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4390_, v_t_u2082_4391_, v_t_4392_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSDiff___redArg(lean_object* v_cmp_4395_){
_start:
{
lean_object* v___x_4396_; 
v___x_4396_ = lean_alloc_closure((void*)(l_Std_DTreeMap_diff), 5, 3);
lean_closure_set(v___x_4396_, 0, lean_box(0));
lean_closure_set(v___x_4396_, 1, lean_box(0));
lean_closure_set(v___x_4396_, 2, v_cmp_4395_);
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSDiff(lean_object* v_00_u03b1_4397_, lean_object* v_00_u03b2_4398_, lean_object* v_cmp_4399_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = lean_alloc_closure((void*)(l_Std_DTreeMap_diff), 5, 3);
lean_closure_set(v___x_4400_, 0, lean_box(0));
lean_closure_set(v___x_4400_, 1, lean_box(0));
lean_closure_set(v___x_4400_, 2, v_cmp_4399_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_4401_, lean_object* v_a_4402_, lean_object* v_____s_4403_){
_start:
{
lean_object* v_r_4404_; lean_object* v___x_4405_; 
v_r_4404_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_4401_, v_a_4402_, v_____s_4403_);
v___x_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4405_, 0, v_r_4404_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany___redArg(lean_object* v_cmp_4406_, lean_object* v_inst_4407_, lean_object* v_t_4408_, lean_object* v_l_4409_){
_start:
{
lean_object* v___f_4410_; lean_object* v___x_4411_; 
v___f_4410_ = lean_alloc_closure((void*)(l_Std_DTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4410_, 0, v_cmp_4406_);
v___x_4411_ = lean_apply_4(v_inst_4407_, lean_box(0), v_l_4409_, v_t_4408_, v___f_4410_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany(lean_object* v_00_u03b1_4412_, lean_object* v_00_u03b2_4413_, lean_object* v_cmp_4414_, lean_object* v_00_u03c1_4415_, lean_object* v_inst_4416_, lean_object* v_t_4417_, lean_object* v_l_4418_){
_start:
{
lean_object* v___f_4419_; lean_object* v___x_4420_; 
v___f_4419_ = lean_alloc_closure((void*)(l_Std_DTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4419_, 0, v_cmp_4414_);
v___x_4420_ = lean_apply_4(v_inst_4416_, lean_box(0), v_l_4418_, v_t_4417_, v___f_4419_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany___redArg___lam__0(lean_object* v_cmp_4421_, lean_object* v_x_4422_, lean_object* v_____s_4423_){
_start:
{
lean_object* v_fst_4424_; lean_object* v_snd_4425_; lean_object* v_r_4426_; lean_object* v___x_4427_; 
v_fst_4424_ = lean_ctor_get(v_x_4422_, 0);
lean_inc(v_fst_4424_);
v_snd_4425_ = lean_ctor_get(v_x_4422_, 1);
lean_inc(v_snd_4425_);
lean_dec_ref(v_x_4422_);
v_r_4426_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4421_, v_fst_4424_, v_snd_4425_, v_____s_4423_);
v___x_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4427_, 0, v_r_4426_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany___redArg(lean_object* v_cmp_4428_, lean_object* v_inst_4429_, lean_object* v_t_4430_, lean_object* v_l_4431_){
_start:
{
lean_object* v___f_4432_; lean_object* v___x_4433_; 
v___f_4432_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4432_, 0, v_cmp_4428_);
v___x_4433_ = lean_apply_4(v_inst_4429_, lean_box(0), v_l_4431_, v_t_4430_, v___f_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany(lean_object* v_00_u03b1_4434_, lean_object* v_cmp_4435_, lean_object* v_00_u03b2_4436_, lean_object* v_00_u03c1_4437_, lean_object* v_inst_4438_, lean_object* v_t_4439_, lean_object* v_l_4440_){
_start:
{
lean_object* v___f_4441_; lean_object* v___x_4442_; 
v___f_4441_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4441_, 0, v_cmp_4435_);
v___x_4442_ = lean_apply_4(v_inst_4438_, lean_box(0), v_l_4440_, v_t_4439_, v___f_4441_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_4443_, lean_object* v_a_4444_, lean_object* v_____s_4445_){
_start:
{
uint8_t v___x_4446_; 
lean_inc(v_____s_4445_);
lean_inc(v_a_4444_);
lean_inc_ref(v_cmp_4443_);
v___x_4446_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4443_, v_a_4444_, v_____s_4445_);
if (v___x_4446_ == 0)
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4447_ = lean_box(0);
v___x_4448_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4443_, v_a_4444_, v___x_4447_, v_____s_4445_);
v___x_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
return v___x_4449_;
}
else
{
lean_object* v___x_4450_; 
lean_dec(v_a_4444_);
lean_dec_ref(v_cmp_4443_);
v___x_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4450_, 0, v_____s_4445_);
return v___x_4450_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_4451_, lean_object* v_inst_4452_, lean_object* v_t_4453_, lean_object* v_l_4454_){
_start:
{
lean_object* v___f_4455_; lean_object* v___x_4456_; 
v___f_4455_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4455_, 0, v_cmp_4451_);
v___x_4456_ = lean_apply_4(v_inst_4452_, lean_box(0), v_l_4454_, v_t_4453_, v___f_4455_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_4457_, lean_object* v_cmp_4458_, lean_object* v_00_u03c1_4459_, lean_object* v_inst_4460_, lean_object* v_t_4461_, lean_object* v_l_4462_){
_start:
{
lean_object* v___f_4463_; lean_object* v___x_4464_; 
v___f_4463_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4463_, 0, v_cmp_4458_);
v___x_4464_ = lean_apply_4(v_inst_4460_, lean_box(0), v_l_4462_, v_t_4461_, v___f_4463_);
return v___x_4464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1(lean_object* v___f_4468_, lean_object* v___x_4469_, lean_object* v_m_4470_, lean_object* v_prec_4471_){
_start:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4472_ = ((lean_object*)(l_Std_DTreeMap_instRepr___redArg___lam__1___closed__1));
v___x_4473_ = lean_box(0);
v___x_4474_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_4475_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_4474_, v___f_4468_, v___x_4473_, v_m_4470_);
v___x_4476_ = l_List_repr___redArg(v___x_4469_, v___x_4475_);
v___x_4477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4472_);
lean_ctor_set(v___x_4477_, 1, v___x_4476_);
v___x_4478_ = l_Repr_addAppParen(v___x_4477_, v_prec_4471_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1___boxed(lean_object* v___f_4479_, lean_object* v___x_4480_, lean_object* v_m_4481_, lean_object* v_prec_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Std_DTreeMap_instRepr___redArg___lam__1(v___f_4479_, v___x_4480_, v_m_4481_, v_prec_4482_);
lean_dec(v_prec_4482_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg(lean_object* v_inst_4484_, lean_object* v_inst_4485_){
_start:
{
lean_object* v___f_4486_; lean_object* v___x_4487_; lean_object* v___f_4488_; 
v___f_4486_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_4487_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_4487_, 0, lean_box(0));
lean_closure_set(v___x_4487_, 1, lean_box(0));
lean_closure_set(v___x_4487_, 2, v_inst_4484_);
lean_closure_set(v___x_4487_, 3, v_inst_4485_);
v___f_4488_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4488_, 0, v___f_4486_);
lean_closure_set(v___f_4488_, 1, v___x_4487_);
return v___f_4488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr(lean_object* v_00_u03b1_4489_, lean_object* v_00_u03b2_4490_, lean_object* v_cmp_4491_, lean_object* v_inst_4492_, lean_object* v_inst_4493_){
_start:
{
lean_object* v___x_4494_; 
v___x_4494_ = l_Std_DTreeMap_instRepr___redArg(v_inst_4492_, v_inst_4493_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___boxed(lean_object* v_00_u03b1_4495_, lean_object* v_00_u03b2_4496_, lean_object* v_cmp_4497_, lean_object* v_inst_4498_, lean_object* v_inst_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_Std_DTreeMap_instRepr(v_00_u03b1_4495_, v_00_u03b2_4496_, v_cmp_4497_, v_inst_4498_, v_inst_4499_);
lean_dec_ref(v_cmp_4497_);
return v_res_4500_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
