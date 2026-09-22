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
lean_object* lean_string_utf8_byte_size(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall___redArg(){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(0);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall___redArg___boxed(lean_object* v___dummy_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_DTreeMap_instCoeTypeForall___redArg();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall(lean_object* v_00_u03b1_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(0);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty___redArg(){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(1);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty___redArg___boxed(lean_object* v___dummy_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_DTreeMap_empty___redArg();
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_cmp_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(1);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_empty___boxed(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b2_90_, lean_object* v_cmp_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_DTreeMap_empty(v_00_u03b1_89_, v_00_u03b2_90_, v_cmp_91_);
lean_dec_ref(v_cmp_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(1);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_DTreeMap_instEmptyCollection___redArg();
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_cmp_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_box(1);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_cmp_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_DTreeMap_instEmptyCollection(v_00_u03b1_101_, v_00_u03b2_102_, v_cmp_103_);
lean_dec_ref(v_cmp_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(1);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited___redArg___boxed(lean_object* v___dummy_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_DTreeMap_instInhabited___redArg();
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited(lean_object* v_00_u03b1_109_, lean_object* v_00_u03b2_110_, lean_object* v_cmp_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(1);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited___boxed(lean_object* v_00_u03b1_113_, lean_object* v_00_u03b2_114_, lean_object* v_cmp_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_DTreeMap_instInhabited(v_00_u03b1_113_, v_00_u03b2_114_, v_cmp_115_);
lean_dec_ref(v_cmp_115_);
return v_res_116_;
}
}
static lean_object* _init_l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3));
v___x_155_ = l_String_toRawSubstring_x27(v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1(lean_object* v_x_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__3));
lean_inc(v_x_173_);
v___x_177_ = l_Lean_Syntax_isOfKind(v_x_173_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_x_173_);
v___x_178_ = lean_box(1);
v___x_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v_a_175_);
return v___x_179_;
}
else
{
lean_object* v_quotContext_180_; lean_object* v_currMacroScope_181_; lean_object* v_ref_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_quotContext_180_ = lean_ctor_get(v_a_174_, 1);
v_currMacroScope_181_ = lean_ctor_get(v_a_174_, 2);
v_ref_182_ = lean_ctor_get(v_a_174_, 5);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = l_Lean_Syntax_getArg(v_x_173_, v___x_183_);
v___x_185_ = lean_unsigned_to_nat(2u);
v___x_186_ = l_Lean_Syntax_getArg(v_x_173_, v___x_185_);
lean_dec(v_x_173_);
v___x_187_ = 0;
v___x_188_ = l_Lean_SourceInfo_fromRef(v_ref_182_, v___x_187_);
v___x_189_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2));
v___x_190_ = lean_obj_once(&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4, &l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4_once, _init_l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4);
v___x_191_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_181_);
lean_inc(v_quotContext_180_);
v___x_192_ = l_Lean_addMacroScope(v_quotContext_180_, v___x_191_, v_currMacroScope_181_);
v___x_193_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__10));
lean_inc_n(v___x_188_, 2);
v___x_194_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_194_, 0, v___x_188_);
lean_ctor_set(v___x_194_, 1, v___x_190_);
lean_ctor_set(v___x_194_, 2, v___x_192_);
lean_ctor_set(v___x_194_, 3, v___x_193_);
v___x_195_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__9));
v___x_196_ = l_Lean_Syntax_node2(v___x_188_, v___x_195_, v___x_184_, v___x_186_);
v___x_197_ = l_Lean_Syntax_node2(v___x_188_, v___x_189_, v___x_194_, v___x_196_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v_a_175_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___boxed(lean_object* v_x_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1(v_x_199_, v_a_200_, v_a_201_);
lean_dec_ref(v_a_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(lean_object* v_x_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2));
lean_inc(v_x_206_);
v___x_210_ = l_Lean_Syntax_isOfKind(v_x_206_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_x_206_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v_a_208_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = l_Lean_Syntax_getArg(v_x_206_, v___x_213_);
v___x_215_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__1));
lean_inc(v___x_214_);
v___x_216_ = l_Lean_Syntax_isOfKind(v___x_214_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec(v___x_214_);
lean_dec(v_x_206_);
v___x_217_ = lean_box(0);
v___x_218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_a_208_);
return v___x_218_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = l_Lean_Syntax_getArg(v_x_206_, v___x_219_);
lean_dec(v_x_206_);
v___x_221_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_220_);
v___x_222_ = l_Lean_Syntax_matchesNull(v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v___x_220_);
lean_dec(v___x_214_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v_a_208_);
return v___x_224_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_ref_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_225_ = l_Lean_Syntax_getArg(v___x_220_, v___x_213_);
v___x_226_ = l_Lean_Syntax_getArg(v___x_220_, v___x_219_);
lean_dec(v___x_220_);
v_ref_227_ = l_Lean_replaceRef(v___x_214_, v_a_207_);
lean_dec(v___x_214_);
v___x_228_ = 0;
v___x_229_ = l_Lean_SourceInfo_fromRef(v_ref_227_, v___x_228_);
lean_dec(v_ref_227_);
v___x_230_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__3));
v___x_231_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__6));
lean_inc(v___x_229_);
v___x_232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_229_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = l_Lean_Syntax_node3(v___x_229_, v___x_230_, v___x_225_, v___x_232_, v___x_226_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v_a_208_);
return v___x_234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___boxed(lean_object* v_x_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(v_x_235_, v_a_236_, v_a_237_);
lean_dec(v_a_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insert___redArg(lean_object* v_cmp_239_, lean_object* v_t_240_, lean_object* v_a_241_, lean_object* v_b_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_239_, v_a_241_, v_b_242_, v_t_240_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insert(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_cmp_246_, lean_object* v_t_247_, lean_object* v_a_248_, lean_object* v_b_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_246_, v_a_248_, v_b_249_, v_t_247_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma___redArg___lam__0(lean_object* v_cmp_251_, lean_object* v_e_252_){
_start:
{
lean_object* v_fst_253_; lean_object* v_snd_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_fst_253_ = lean_ctor_get(v_e_252_, 0);
lean_inc(v_fst_253_);
v_snd_254_ = lean_ctor_get(v_e_252_, 1);
lean_inc(v_snd_254_);
lean_dec_ref(v_e_252_);
v___x_255_ = lean_box(1);
v___x_256_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_251_, v_fst_253_, v_snd_254_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma___redArg(lean_object* v_cmp_257_){
_start:
{
lean_object* v___f_258_; 
v___f_258_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_258_, 0, v_cmp_257_);
return v___f_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma(lean_object* v_00_u03b1_259_, lean_object* v_00_u03b2_260_, lean_object* v_cmp_261_){
_start:
{
lean_object* v___f_262_; 
v___f_262_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_262_, 0, v_cmp_261_);
return v___f_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma___redArg___lam__0(lean_object* v_cmp_263_, lean_object* v_e_264_, lean_object* v_s_265_){
_start:
{
lean_object* v_fst_266_; lean_object* v_snd_267_; lean_object* v___x_268_; 
v_fst_266_ = lean_ctor_get(v_e_264_, 0);
lean_inc(v_fst_266_);
v_snd_267_ = lean_ctor_get(v_e_264_, 1);
lean_inc(v_snd_267_);
lean_dec_ref(v_e_264_);
v___x_268_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_263_, v_fst_266_, v_snd_267_, v_s_265_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma___redArg(lean_object* v_cmp_269_){
_start:
{
lean_object* v___f_270_; 
v___f_270_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_270_, 0, v_cmp_269_);
return v___f_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma(lean_object* v_00_u03b1_271_, lean_object* v_00_u03b2_272_, lean_object* v_cmp_273_){
_start:
{
lean_object* v___f_274_; 
v___f_274_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_274_, 0, v_cmp_273_);
return v___f_274_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertIfNew___redArg(lean_object* v_cmp_275_, lean_object* v_t_276_, lean_object* v_a_277_, lean_object* v_b_278_){
_start:
{
uint8_t v___x_279_; 
lean_inc(v_t_276_);
lean_inc(v_a_277_);
lean_inc_ref(v_cmp_275_);
v___x_279_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_275_, v_a_277_, v_t_276_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
v___x_280_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_275_, v_a_277_, v_b_278_, v_t_276_);
return v___x_280_;
}
else
{
lean_dec(v_b_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_cmp_275_);
return v_t_276_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertIfNew(lean_object* v_00_u03b1_281_, lean_object* v_00_u03b2_282_, lean_object* v_cmp_283_, lean_object* v_t_284_, lean_object* v_a_285_, lean_object* v_b_286_){
_start:
{
uint8_t v___x_287_; 
lean_inc(v_t_284_);
lean_inc(v_a_285_);
lean_inc_ref(v_cmp_283_);
v___x_287_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_283_, v_a_285_, v_t_284_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; 
v___x_288_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_283_, v_a_285_, v_b_286_, v_t_284_);
return v___x_288_;
}
else
{
lean_dec(v_b_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_cmp_283_);
return v_t_284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsert___redArg(lean_object* v_cmp_289_, lean_object* v_t_290_, lean_object* v_a_291_, lean_object* v_b_292_){
_start:
{
lean_object* v_sz_293_; lean_object* v_m_294_; lean_object* v___y_296_; 
v_sz_293_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_290_);
v_m_294_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_289_, v_a_291_, v_b_292_, v_t_290_);
if (lean_obj_tag(v_m_294_) == 0)
{
lean_object* v_size_300_; 
v_size_300_ = lean_ctor_get(v_m_294_, 0);
lean_inc(v_size_300_);
v___y_296_ = v_size_300_;
goto v___jp_295_;
}
else
{
lean_object* v___x_301_; 
v___x_301_ = lean_unsigned_to_nat(0u);
v___y_296_ = v___x_301_;
goto v___jp_295_;
}
v___jp_295_:
{
uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_nat_dec_eq(v_sz_293_, v___y_296_);
lean_dec(v___y_296_);
lean_dec(v_sz_293_);
v___x_298_ = lean_box(v___x_297_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_m_294_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsert(lean_object* v_00_u03b1_302_, lean_object* v_00_u03b2_303_, lean_object* v_cmp_304_, lean_object* v_t_305_, lean_object* v_a_306_, lean_object* v_b_307_){
_start:
{
lean_object* v_sz_308_; lean_object* v_m_309_; lean_object* v___y_311_; 
v_sz_308_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_305_);
v_m_309_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_304_, v_a_306_, v_b_307_, v_t_305_);
if (lean_obj_tag(v_m_309_) == 0)
{
lean_object* v_size_315_; 
v_size_315_ = lean_ctor_get(v_m_309_, 0);
lean_inc(v_size_315_);
v___y_311_ = v_size_315_;
goto v___jp_310_;
}
else
{
lean_object* v___x_316_; 
v___x_316_ = lean_unsigned_to_nat(0u);
v___y_311_ = v___x_316_;
goto v___jp_310_;
}
v___jp_310_:
{
uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_nat_dec_eq(v_sz_308_, v___y_311_);
lean_dec(v___y_311_);
lean_dec(v_sz_308_);
v___x_313_ = lean_box(v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v_m_309_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_317_, lean_object* v_t_318_, lean_object* v_a_319_, lean_object* v_b_320_){
_start:
{
uint8_t v___x_321_; 
lean_inc(v_t_318_);
lean_inc(v_a_319_);
lean_inc_ref(v_cmp_317_);
v___x_321_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_317_, v_a_319_, v_t_318_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_317_, v_a_319_, v_b_320_, v_t_318_);
v___x_323_ = lean_box(v___x_321_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec(v_b_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_cmp_317_);
v___x_325_ = lean_box(v___x_321_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v_t_318_);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_327_, lean_object* v_00_u03b2_328_, lean_object* v_cmp_329_, lean_object* v_t_330_, lean_object* v_a_331_, lean_object* v_b_332_){
_start:
{
uint8_t v___x_333_; 
lean_inc(v_t_330_);
lean_inc(v_a_331_);
lean_inc_ref(v_cmp_329_);
v___x_333_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_329_, v_a_331_, v_t_330_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_329_, v_a_331_, v_b_332_, v_t_330_);
v___x_335_ = lean_box(v___x_333_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_b_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_cmp_329_);
v___x_337_ = lean_box(v___x_333_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v_t_330_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_339_, lean_object* v_t_340_, lean_object* v_a_341_, lean_object* v_b_342_){
_start:
{
lean_object* v___x_343_; 
lean_inc(v_a_341_);
lean_inc(v_t_340_);
lean_inc_ref(v_cmp_339_);
v___x_343_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_339_, v_t_340_, v_a_341_);
if (lean_obj_tag(v___x_343_) == 0)
{
uint8_t v___x_344_; 
lean_inc(v_t_340_);
lean_inc(v_a_341_);
lean_inc_ref(v_cmp_339_);
v___x_344_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_339_, v_a_341_, v_t_340_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_339_, v_a_341_, v_b_342_, v_t_340_);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_343_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
return v___x_346_;
}
else
{
lean_object* v___x_347_; 
lean_dec(v_b_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_cmp_339_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_343_);
lean_ctor_set(v___x_347_, 1, v_t_340_);
return v___x_347_;
}
}
else
{
lean_object* v___x_348_; 
lean_dec(v_b_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_cmp_339_);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_343_);
lean_ctor_set(v___x_348_, 1, v_t_340_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_349_, lean_object* v_00_u03b2_350_, lean_object* v_cmp_351_, lean_object* v_inst_352_, lean_object* v_t_353_, lean_object* v_a_354_, lean_object* v_b_355_){
_start:
{
lean_object* v___x_356_; 
lean_inc(v_a_354_);
lean_inc(v_t_353_);
lean_inc_ref(v_cmp_351_);
v___x_356_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_351_, v_t_353_, v_a_354_);
if (lean_obj_tag(v___x_356_) == 0)
{
uint8_t v___x_357_; 
lean_inc(v_t_353_);
lean_inc(v_a_354_);
lean_inc_ref(v_cmp_351_);
v___x_357_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_351_, v_a_354_, v_t_353_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_351_, v_a_354_, v_b_355_, v_t_353_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_356_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; 
lean_dec(v_b_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_cmp_351_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_356_);
lean_ctor_set(v___x_360_, 1, v_t_353_);
return v___x_360_;
}
}
else
{
lean_object* v___x_361_; 
lean_dec(v_b_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_cmp_351_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_356_);
lean_ctor_set(v___x_361_, 1, v_t_353_);
return v___x_361_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_contains___redArg(lean_object* v_cmp_362_, lean_object* v_t_363_, lean_object* v_a_364_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_362_, v_a_364_, v_t_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_contains___redArg___boxed(lean_object* v_cmp_366_, lean_object* v_t_367_, lean_object* v_a_368_){
_start:
{
uint8_t v_res_369_; lean_object* v_r_370_; 
v_res_369_ = l_Std_DTreeMap_contains___redArg(v_cmp_366_, v_t_367_, v_a_368_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_contains(lean_object* v_00_u03b1_371_, lean_object* v_00_u03b2_372_, lean_object* v_cmp_373_, lean_object* v_t_374_, lean_object* v_a_375_){
_start:
{
uint8_t v___x_376_; 
v___x_376_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_373_, v_a_375_, v_t_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_contains___boxed(lean_object* v_00_u03b1_377_, lean_object* v_00_u03b2_378_, lean_object* v_cmp_379_, lean_object* v_t_380_, lean_object* v_a_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Std_DTreeMap_contains(v_00_u03b1_377_, v_00_u03b2_378_, v_cmp_379_, v_t_380_, v_a_381_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___redArg(){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(0);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___redArg___boxed(lean_object* v___dummy_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_DTreeMap_instMembership___redArg();
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_cmp_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_box(0);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___boxed(lean_object* v_00_u03b1_392_, lean_object* v_00_u03b2_393_, lean_object* v_cmp_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_DTreeMap_instMembership(v_00_u03b1_392_, v_00_u03b2_393_, v_cmp_394_);
lean_dec_ref(v_cmp_394_);
return v_res_395_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableMem___redArg(lean_object* v_cmp_396_, lean_object* v_m_397_, lean_object* v_a_398_){
_start:
{
uint8_t v___x_399_; 
v___x_399_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_396_, v_a_398_, v_m_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_400_, lean_object* v_m_401_, lean_object* v_a_402_){
_start:
{
uint8_t v_res_403_; lean_object* v_r_404_; 
v_res_403_ = l_Std_DTreeMap_instDecidableMem___redArg(v_cmp_400_, v_m_401_, v_a_402_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableMem(lean_object* v_00_u03b1_405_, lean_object* v_00_u03b2_406_, lean_object* v_cmp_407_, lean_object* v_m_408_, lean_object* v_a_409_){
_start:
{
uint8_t v___x_410_; 
v___x_410_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_407_, v_a_409_, v_m_408_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_411_, lean_object* v_00_u03b2_412_, lean_object* v_cmp_413_, lean_object* v_m_414_, lean_object* v_a_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_Std_DTreeMap_instDecidableMem(v_00_u03b1_411_, v_00_u03b2_412_, v_cmp_413_, v_m_414_, v_a_415_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___redArg(lean_object* v_t_418_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___redArg___boxed(lean_object* v_t_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Std_DTreeMap_size___redArg(v_t_421_);
lean_dec(v_t_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size(lean_object* v_00_u03b1_423_, lean_object* v_00_u03b2_424_, lean_object* v_cmp_425_, lean_object* v_t_426_){
_start:
{
if (lean_obj_tag(v_t_426_) == 0)
{
lean_object* v_size_427_; 
v_size_427_ = lean_ctor_get(v_t_426_, 0);
lean_inc(v_size_427_);
return v_size_427_;
}
else
{
lean_object* v___x_428_; 
v___x_428_ = lean_unsigned_to_nat(0u);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___boxed(lean_object* v_00_u03b1_429_, lean_object* v_00_u03b2_430_, lean_object* v_cmp_431_, lean_object* v_t_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_DTreeMap_size(v_00_u03b1_429_, v_00_u03b2_430_, v_cmp_431_, v_t_432_);
lean_dec(v_t_432_);
lean_dec_ref(v_cmp_431_);
return v_res_433_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_isEmpty___redArg(lean_object* v_t_434_){
_start:
{
if (lean_obj_tag(v_t_434_) == 0)
{
uint8_t v___x_435_; 
v___x_435_ = 0;
return v___x_435_;
}
else
{
uint8_t v___x_436_; 
v___x_436_ = 1;
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isEmpty___redArg___boxed(lean_object* v_t_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Std_DTreeMap_isEmpty___redArg(v_t_437_);
lean_dec(v_t_437_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_isEmpty(lean_object* v_00_u03b1_440_, lean_object* v_00_u03b2_441_, lean_object* v_cmp_442_, lean_object* v_t_443_){
_start:
{
if (lean_obj_tag(v_t_443_) == 0)
{
uint8_t v___x_444_; 
v___x_444_ = 0;
return v___x_444_;
}
else
{
uint8_t v___x_445_; 
v___x_445_ = 1;
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_cmp_448_, lean_object* v_t_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_Std_DTreeMap_isEmpty(v_00_u03b1_446_, v_00_u03b2_447_, v_cmp_448_, v_t_449_);
lean_dec(v_t_449_);
lean_dec_ref(v_cmp_448_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_erase___redArg(lean_object* v_cmp_452_, lean_object* v_t_453_, lean_object* v_a_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_452_, v_a_454_, v_t_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_erase(lean_object* v_00_u03b1_456_, lean_object* v_00_u03b2_457_, lean_object* v_cmp_458_, lean_object* v_t_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_458_, v_a_460_, v_t_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x3f___redArg(lean_object* v_cmp_462_, lean_object* v_t_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_462_, v_t_463_, v_a_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x3f(lean_object* v_00_u03b1_466_, lean_object* v_00_u03b2_467_, lean_object* v_cmp_468_, lean_object* v_inst_469_, lean_object* v_t_470_, lean_object* v_a_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_468_, v_t_470_, v_a_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get___redArg(lean_object* v_cmp_473_, lean_object* v_t_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_473_, v_t_474_, v_a_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get(lean_object* v_00_u03b1_477_, lean_object* v_00_u03b2_478_, lean_object* v_cmp_479_, lean_object* v_inst_480_, lean_object* v_t_481_, lean_object* v_a_482_, lean_object* v_h_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_479_, v_t_481_, v_a_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___redArg(lean_object* v_cmp_485_, lean_object* v_t_486_, lean_object* v_a_487_, lean_object* v_inst_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_485_, v_t_486_, v_a_487_, v_inst_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___redArg___boxed(lean_object* v_cmp_490_, lean_object* v_t_491_, lean_object* v_a_492_, lean_object* v_inst_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_DTreeMap_get_x21___redArg(v_cmp_490_, v_t_491_, v_a_492_, v_inst_493_);
lean_dec(v_inst_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21(lean_object* v_00_u03b1_495_, lean_object* v_00_u03b2_496_, lean_object* v_cmp_497_, lean_object* v_inst_498_, lean_object* v_t_499_, lean_object* v_a_500_, lean_object* v_inst_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_497_, v_t_499_, v_a_500_, v_inst_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___boxed(lean_object* v_00_u03b1_503_, lean_object* v_00_u03b2_504_, lean_object* v_cmp_505_, lean_object* v_inst_506_, lean_object* v_t_507_, lean_object* v_a_508_, lean_object* v_inst_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_DTreeMap_get_x21(v_00_u03b1_503_, v_00_u03b2_504_, v_cmp_505_, v_inst_506_, v_t_507_, v_a_508_, v_inst_509_);
lean_dec(v_inst_509_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg(lean_object* v_cmp_511_, lean_object* v_t_512_, lean_object* v_a_513_, lean_object* v_fallback_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_511_, v_t_512_, v_a_513_, v_fallback_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg___boxed(lean_object* v_cmp_516_, lean_object* v_t_517_, lean_object* v_a_518_, lean_object* v_fallback_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_DTreeMap_getD___redArg(v_cmp_516_, v_t_517_, v_a_518_, v_fallback_519_);
lean_dec(v_fallback_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD(lean_object* v_00_u03b1_521_, lean_object* v_00_u03b2_522_, lean_object* v_cmp_523_, lean_object* v_inst_524_, lean_object* v_t_525_, lean_object* v_a_526_, lean_object* v_fallback_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_523_, v_t_525_, v_a_526_, v_fallback_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___boxed(lean_object* v_00_u03b1_529_, lean_object* v_00_u03b2_530_, lean_object* v_cmp_531_, lean_object* v_inst_532_, lean_object* v_t_533_, lean_object* v_a_534_, lean_object* v_fallback_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_DTreeMap_getD(v_00_u03b1_529_, v_00_u03b2_530_, v_cmp_531_, v_inst_532_, v_t_533_, v_a_534_, v_fallback_535_);
lean_dec(v_fallback_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f___redArg(lean_object* v_cmp_537_, lean_object* v_t_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_537_, v_t_538_, v_a_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f(lean_object* v_00_u03b1_541_, lean_object* v_00_u03b2_542_, lean_object* v_cmp_543_, lean_object* v_t_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_543_, v_t_544_, v_a_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey___redArg(lean_object* v_cmp_547_, lean_object* v_t_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_547_, v_t_548_, v_a_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey(lean_object* v_00_u03b1_551_, lean_object* v_00_u03b2_552_, lean_object* v_cmp_553_, lean_object* v_t_554_, lean_object* v_a_555_, lean_object* v_h_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_553_, v_t_554_, v_a_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___redArg(lean_object* v_cmp_558_, lean_object* v_inst_559_, lean_object* v_t_560_, lean_object* v_a_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_558_, v_t_560_, v_a_561_, v_inst_559_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___redArg___boxed(lean_object* v_cmp_563_, lean_object* v_inst_564_, lean_object* v_t_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_DTreeMap_getKey_x21___redArg(v_cmp_563_, v_inst_564_, v_t_565_, v_a_566_);
lean_dec(v_inst_564_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21(lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_cmp_570_, lean_object* v_inst_571_, lean_object* v_t_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_570_, v_t_572_, v_a_573_, v_inst_571_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___boxed(lean_object* v_00_u03b1_575_, lean_object* v_00_u03b2_576_, lean_object* v_cmp_577_, lean_object* v_inst_578_, lean_object* v_t_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_DTreeMap_getKey_x21(v_00_u03b1_575_, v_00_u03b2_576_, v_cmp_577_, v_inst_578_, v_t_579_, v_a_580_);
lean_dec(v_inst_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___redArg(lean_object* v_cmp_582_, lean_object* v_t_583_, lean_object* v_a_584_, lean_object* v_fallback_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_582_, v_t_583_, v_a_584_, v_fallback_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_587_, lean_object* v_t_588_, lean_object* v_a_589_, lean_object* v_fallback_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_DTreeMap_getKeyD___redArg(v_cmp_587_, v_t_588_, v_a_589_, v_fallback_590_);
lean_dec(v_fallback_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD(lean_object* v_00_u03b1_592_, lean_object* v_00_u03b2_593_, lean_object* v_cmp_594_, lean_object* v_t_595_, lean_object* v_a_596_, lean_object* v_fallback_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_594_, v_t_595_, v_a_596_, v_fallback_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_599_, lean_object* v_00_u03b2_600_, lean_object* v_cmp_601_, lean_object* v_t_602_, lean_object* v_a_603_, lean_object* v_fallback_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Std_DTreeMap_getKeyD(v_00_u03b1_599_, v_00_u03b2_600_, v_cmp_601_, v_t_602_, v_a_603_, v_fallback_604_);
lean_dec(v_fallback_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x3f___redArg(lean_object* v_cmp_606_, lean_object* v_t_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_606_, v_t_607_, v_a_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x3f(lean_object* v_00_u03b1_610_, lean_object* v_00_u03b2_611_, lean_object* v_cmp_612_, lean_object* v_t_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_612_, v_t_613_, v_a_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry___redArg(lean_object* v_cmp_616_, lean_object* v_t_617_, lean_object* v_a_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_616_, v_t_617_, v_a_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry(lean_object* v_00_u03b1_620_, lean_object* v_00_u03b2_621_, lean_object* v_cmp_622_, lean_object* v_t_623_, lean_object* v_a_624_, lean_object* v_h_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_622_, v_t_623_, v_a_624_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___redArg(lean_object* v_cmp_627_, lean_object* v_t_628_, lean_object* v_a_629_, lean_object* v_fallback_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_627_, v_t_628_, v_a_629_, v_fallback_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___redArg___boxed(lean_object* v_cmp_632_, lean_object* v_t_633_, lean_object* v_a_634_, lean_object* v_fallback_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_DTreeMap_getEntryD___redArg(v_cmp_632_, v_t_633_, v_a_634_, v_fallback_635_);
lean_dec_ref(v_fallback_635_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD(lean_object* v_00_u03b1_637_, lean_object* v_00_u03b2_638_, lean_object* v_cmp_639_, lean_object* v_t_640_, lean_object* v_a_641_, lean_object* v_fallback_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_639_, v_t_640_, v_a_641_, v_fallback_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___boxed(lean_object* v_00_u03b1_644_, lean_object* v_00_u03b2_645_, lean_object* v_cmp_646_, lean_object* v_t_647_, lean_object* v_a_648_, lean_object* v_fallback_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_DTreeMap_getEntryD(v_00_u03b1_644_, v_00_u03b2_645_, v_cmp_646_, v_t_647_, v_a_648_, v_fallback_649_);
lean_dec_ref(v_fallback_649_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___redArg(lean_object* v_cmp_651_, lean_object* v_inst_652_, lean_object* v_t_653_, lean_object* v_a_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_651_, v_inst_652_, v_t_653_, v_a_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___redArg___boxed(lean_object* v_cmp_656_, lean_object* v_inst_657_, lean_object* v_t_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_DTreeMap_getEntry_x21___redArg(v_cmp_656_, v_inst_657_, v_t_658_, v_a_659_);
lean_dec_ref(v_inst_657_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_cmp_663_, lean_object* v_inst_664_, lean_object* v_t_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_663_, v_inst_664_, v_t_665_, v_a_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___boxed(lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_cmp_670_, lean_object* v_inst_671_, lean_object* v_t_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_DTreeMap_getEntry_x21(v_00_u03b1_668_, v_00_u03b2_669_, v_cmp_670_, v_inst_671_, v_t_672_, v_a_673_);
lean_dec_ref(v_inst_671_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___redArg(lean_object* v_t_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_DTreeMap_minEntry_x3f___redArg(v_t_677_);
lean_dec(v_t_677_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f(lean_object* v_00_u03b1_679_, lean_object* v_00_u03b2_680_, lean_object* v_cmp_681_, lean_object* v_t_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_684_, lean_object* v_00_u03b2_685_, lean_object* v_cmp_686_, lean_object* v_t_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Std_DTreeMap_minEntry_x3f(v_00_u03b1_684_, v_00_u03b2_685_, v_cmp_686_, v_t_687_);
lean_dec(v_t_687_);
lean_dec_ref(v_cmp_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___redArg(lean_object* v_t_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___redArg___boxed(lean_object* v_t_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Std_DTreeMap_minEntry___redArg(v_t_691_);
lean_dec(v_t_691_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry(lean_object* v_00_u03b1_693_, lean_object* v_00_u03b2_694_, lean_object* v_cmp_695_, lean_object* v_t_696_, lean_object* v_h_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_696_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___boxed(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_cmp_701_, lean_object* v_t_702_, lean_object* v_h_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_DTreeMap_minEntry(v_00_u03b1_699_, v_00_u03b2_700_, v_cmp_701_, v_t_702_, v_h_703_);
lean_dec(v_t_702_);
lean_dec_ref(v_cmp_701_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___redArg(lean_object* v_inst_705_, lean_object* v_t_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_705_, v_t_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_708_, lean_object* v_t_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_DTreeMap_minEntry_x21___redArg(v_inst_708_, v_t_709_);
lean_dec(v_t_709_);
lean_dec_ref(v_inst_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21(lean_object* v_00_u03b1_711_, lean_object* v_00_u03b2_712_, lean_object* v_cmp_713_, lean_object* v_inst_714_, lean_object* v_t_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_714_, v_t_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_717_, lean_object* v_00_u03b2_718_, lean_object* v_cmp_719_, lean_object* v_inst_720_, lean_object* v_t_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_DTreeMap_minEntry_x21(v_00_u03b1_717_, v_00_u03b2_718_, v_cmp_719_, v_inst_720_, v_t_721_);
lean_dec(v_t_721_);
lean_dec_ref(v_inst_720_);
lean_dec_ref(v_cmp_719_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___redArg(lean_object* v_t_723_, lean_object* v_fallback_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_723_, v_fallback_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___redArg___boxed(lean_object* v_t_726_, lean_object* v_fallback_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_DTreeMap_minEntryD___redArg(v_t_726_, v_fallback_727_);
lean_dec_ref(v_fallback_727_);
lean_dec(v_t_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD(lean_object* v_00_u03b1_729_, lean_object* v_00_u03b2_730_, lean_object* v_cmp_731_, lean_object* v_t_732_, lean_object* v_fallback_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_732_, v_fallback_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_735_, lean_object* v_00_u03b2_736_, lean_object* v_cmp_737_, lean_object* v_t_738_, lean_object* v_fallback_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_DTreeMap_minEntryD(v_00_u03b1_735_, v_00_u03b2_736_, v_cmp_737_, v_t_738_, v_fallback_739_);
lean_dec_ref(v_fallback_739_);
lean_dec(v_t_738_);
lean_dec_ref(v_cmp_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___redArg(lean_object* v_t_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_DTreeMap_maxEntry_x3f___redArg(v_t_743_);
lean_dec(v_t_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_745_, lean_object* v_00_u03b2_746_, lean_object* v_cmp_747_, lean_object* v_t_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_750_, lean_object* v_00_u03b2_751_, lean_object* v_cmp_752_, lean_object* v_t_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_DTreeMap_maxEntry_x3f(v_00_u03b1_750_, v_00_u03b2_751_, v_cmp_752_, v_t_753_);
lean_dec(v_t_753_);
lean_dec_ref(v_cmp_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___redArg(lean_object* v_t_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___redArg___boxed(lean_object* v_t_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DTreeMap_maxEntry___redArg(v_t_757_);
lean_dec(v_t_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry(lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_cmp_761_, lean_object* v_t_762_, lean_object* v_h_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_762_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_765_, lean_object* v_00_u03b2_766_, lean_object* v_cmp_767_, lean_object* v_t_768_, lean_object* v_h_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_DTreeMap_maxEntry(v_00_u03b1_765_, v_00_u03b2_766_, v_cmp_767_, v_t_768_, v_h_769_);
lean_dec(v_t_768_);
lean_dec_ref(v_cmp_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___redArg(lean_object* v_inst_771_, lean_object* v_t_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_771_, v_t_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_774_, lean_object* v_t_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Std_DTreeMap_maxEntry_x21___redArg(v_inst_774_, v_t_775_);
lean_dec(v_t_775_);
lean_dec_ref(v_inst_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21(lean_object* v_00_u03b1_777_, lean_object* v_00_u03b2_778_, lean_object* v_cmp_779_, lean_object* v_inst_780_, lean_object* v_t_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_780_, v_t_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_783_, lean_object* v_00_u03b2_784_, lean_object* v_cmp_785_, lean_object* v_inst_786_, lean_object* v_t_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_DTreeMap_maxEntry_x21(v_00_u03b1_783_, v_00_u03b2_784_, v_cmp_785_, v_inst_786_, v_t_787_);
lean_dec(v_t_787_);
lean_dec_ref(v_inst_786_);
lean_dec_ref(v_cmp_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___redArg(lean_object* v_t_789_, lean_object* v_fallback_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_789_, v_fallback_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_792_, lean_object* v_fallback_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_DTreeMap_maxEntryD___redArg(v_t_792_, v_fallback_793_);
lean_dec_ref(v_fallback_793_);
lean_dec(v_t_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD(lean_object* v_00_u03b1_795_, lean_object* v_00_u03b2_796_, lean_object* v_cmp_797_, lean_object* v_t_798_, lean_object* v_fallback_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_798_, v_fallback_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_cmp_803_, lean_object* v_t_804_, lean_object* v_fallback_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_DTreeMap_maxEntryD(v_00_u03b1_801_, v_00_u03b2_802_, v_cmp_803_, v_t_804_, v_fallback_805_);
lean_dec_ref(v_fallback_805_);
lean_dec(v_t_804_);
lean_dec_ref(v_cmp_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___redArg(lean_object* v_t_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_DTreeMap_minKey_x3f___redArg(v_t_809_);
lean_dec(v_t_809_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f(lean_object* v_00_u03b1_811_, lean_object* v_00_u03b2_812_, lean_object* v_cmp_813_, lean_object* v_t_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_cmp_818_, lean_object* v_t_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_DTreeMap_minKey_x3f(v_00_u03b1_816_, v_00_u03b2_817_, v_cmp_818_, v_t_819_);
lean_dec(v_t_819_);
lean_dec_ref(v_cmp_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___redArg(lean_object* v_t_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___redArg___boxed(lean_object* v_t_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_DTreeMap_minKey___redArg(v_t_823_);
lean_dec(v_t_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey(lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_cmp_827_, lean_object* v_t_828_, lean_object* v_h_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___boxed(lean_object* v_00_u03b1_831_, lean_object* v_00_u03b2_832_, lean_object* v_cmp_833_, lean_object* v_t_834_, lean_object* v_h_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_DTreeMap_minKey(v_00_u03b1_831_, v_00_u03b2_832_, v_cmp_833_, v_t_834_, v_h_835_);
lean_dec(v_t_834_);
lean_dec_ref(v_cmp_833_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___redArg(lean_object* v_inst_837_, lean_object* v_t_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_837_, v_t_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_840_, lean_object* v_t_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_DTreeMap_minKey_x21___redArg(v_inst_840_, v_t_841_);
lean_dec(v_t_841_);
lean_dec(v_inst_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21(lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_cmp_845_, lean_object* v_inst_846_, lean_object* v_t_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_846_, v_t_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_849_, lean_object* v_00_u03b2_850_, lean_object* v_cmp_851_, lean_object* v_inst_852_, lean_object* v_t_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Std_DTreeMap_minKey_x21(v_00_u03b1_849_, v_00_u03b2_850_, v_cmp_851_, v_inst_852_, v_t_853_);
lean_dec(v_t_853_);
lean_dec(v_inst_852_);
lean_dec_ref(v_cmp_851_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___redArg(lean_object* v_t_855_, lean_object* v_fallback_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_855_, v_fallback_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___redArg___boxed(lean_object* v_t_858_, lean_object* v_fallback_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Std_DTreeMap_minKeyD___redArg(v_t_858_, v_fallback_859_);
lean_dec(v_fallback_859_);
lean_dec(v_t_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD(lean_object* v_00_u03b1_861_, lean_object* v_00_u03b2_862_, lean_object* v_cmp_863_, lean_object* v_t_864_, lean_object* v_fallback_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_864_, v_fallback_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_867_, lean_object* v_00_u03b2_868_, lean_object* v_cmp_869_, lean_object* v_t_870_, lean_object* v_fallback_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_DTreeMap_minKeyD(v_00_u03b1_867_, v_00_u03b2_868_, v_cmp_869_, v_t_870_, v_fallback_871_);
lean_dec(v_fallback_871_);
lean_dec(v_t_870_);
lean_dec_ref(v_cmp_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___redArg(lean_object* v_t_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_DTreeMap_maxKey_x3f___redArg(v_t_875_);
lean_dec(v_t_875_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f(lean_object* v_00_u03b1_877_, lean_object* v_00_u03b2_878_, lean_object* v_cmp_879_, lean_object* v_t_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_882_, lean_object* v_00_u03b2_883_, lean_object* v_cmp_884_, lean_object* v_t_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Std_DTreeMap_maxKey_x3f(v_00_u03b1_882_, v_00_u03b2_883_, v_cmp_884_, v_t_885_);
lean_dec(v_t_885_);
lean_dec_ref(v_cmp_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___redArg(lean_object* v_t_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___redArg___boxed(lean_object* v_t_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_DTreeMap_maxKey___redArg(v_t_889_);
lean_dec(v_t_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_cmp_893_, lean_object* v_t_894_, lean_object* v_h_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___boxed(lean_object* v_00_u03b1_897_, lean_object* v_00_u03b2_898_, lean_object* v_cmp_899_, lean_object* v_t_900_, lean_object* v_h_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_DTreeMap_maxKey(v_00_u03b1_897_, v_00_u03b2_898_, v_cmp_899_, v_t_900_, v_h_901_);
lean_dec(v_t_900_);
lean_dec_ref(v_cmp_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___redArg(lean_object* v_inst_903_, lean_object* v_t_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_903_, v_t_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_906_, lean_object* v_t_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_DTreeMap_maxKey_x21___redArg(v_inst_906_, v_t_907_);
lean_dec(v_t_907_);
lean_dec(v_inst_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21(lean_object* v_00_u03b1_909_, lean_object* v_00_u03b2_910_, lean_object* v_cmp_911_, lean_object* v_inst_912_, lean_object* v_t_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_912_, v_t_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_915_, lean_object* v_00_u03b2_916_, lean_object* v_cmp_917_, lean_object* v_inst_918_, lean_object* v_t_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Std_DTreeMap_maxKey_x21(v_00_u03b1_915_, v_00_u03b2_916_, v_cmp_917_, v_inst_918_, v_t_919_);
lean_dec(v_t_919_);
lean_dec(v_inst_918_);
lean_dec_ref(v_cmp_917_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___redArg(lean_object* v_t_921_, lean_object* v_fallback_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_921_, v_fallback_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_924_, lean_object* v_fallback_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Std_DTreeMap_maxKeyD___redArg(v_t_924_, v_fallback_925_);
lean_dec(v_fallback_925_);
lean_dec(v_t_924_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD(lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v_cmp_929_, lean_object* v_t_930_, lean_object* v_fallback_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_930_, v_fallback_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_933_, lean_object* v_00_u03b2_934_, lean_object* v_cmp_935_, lean_object* v_t_936_, lean_object* v_fallback_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_DTreeMap_maxKeyD(v_00_u03b1_933_, v_00_u03b2_934_, v_cmp_935_, v_t_936_, v_fallback_937_);
lean_dec(v_fallback_937_);
lean_dec(v_t_936_);
lean_dec_ref(v_cmp_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_939_, lean_object* v_n_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_939_, v_n_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_942_, lean_object* v_n_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Std_DTreeMap_entryAtIdx_x3f___redArg(v_t_942_, v_n_943_);
lean_dec(v_t_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_945_, lean_object* v_00_u03b2_946_, lean_object* v_cmp_947_, lean_object* v_t_948_, lean_object* v_n_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_948_, v_n_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_951_, lean_object* v_00_u03b2_952_, lean_object* v_cmp_953_, lean_object* v_t_954_, lean_object* v_n_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_DTreeMap_entryAtIdx_x3f(v_00_u03b1_951_, v_00_u03b2_952_, v_cmp_953_, v_t_954_, v_n_955_);
lean_dec(v_t_954_);
lean_dec_ref(v_cmp_953_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___redArg(lean_object* v_t_957_, lean_object* v_n_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_957_, v_n_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_960_, lean_object* v_n_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Std_DTreeMap_entryAtIdx___redArg(v_t_960_, v_n_961_);
lean_dec(v_t_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx(lean_object* v_00_u03b1_963_, lean_object* v_00_u03b2_964_, lean_object* v_cmp_965_, lean_object* v_t_966_, lean_object* v_n_967_, lean_object* v_h_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_966_, v_n_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_970_, lean_object* v_00_u03b2_971_, lean_object* v_cmp_972_, lean_object* v_t_973_, lean_object* v_n_974_, lean_object* v_h_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Std_DTreeMap_entryAtIdx(v_00_u03b1_970_, v_00_u03b2_971_, v_cmp_972_, v_t_973_, v_n_974_, v_h_975_);
lean_dec(v_t_973_);
lean_dec_ref(v_cmp_972_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_977_, lean_object* v_t_978_, lean_object* v_n_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_977_, v_t_978_, v_n_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_981_, lean_object* v_t_982_, lean_object* v_n_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Std_DTreeMap_entryAtIdx_x21___redArg(v_inst_981_, v_t_982_, v_n_983_);
lean_dec(v_t_982_);
lean_dec_ref(v_inst_981_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_985_, lean_object* v_00_u03b2_986_, lean_object* v_cmp_987_, lean_object* v_inst_988_, lean_object* v_t_989_, lean_object* v_n_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_988_, v_t_989_, v_n_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_992_, lean_object* v_00_u03b2_993_, lean_object* v_cmp_994_, lean_object* v_inst_995_, lean_object* v_t_996_, lean_object* v_n_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DTreeMap_entryAtIdx_x21(v_00_u03b1_992_, v_00_u03b2_993_, v_cmp_994_, v_inst_995_, v_t_996_, v_n_997_);
lean_dec(v_t_996_);
lean_dec_ref(v_inst_995_);
lean_dec_ref(v_cmp_994_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___redArg(lean_object* v_t_999_, lean_object* v_n_1000_, lean_object* v_fallback_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_999_, v_n_1000_, v_fallback_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_1003_, lean_object* v_n_1004_, lean_object* v_fallback_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Std_DTreeMap_entryAtIdxD___redArg(v_t_1003_, v_n_1004_, v_fallback_1005_);
lean_dec_ref(v_fallback_1005_);
lean_dec(v_t_1003_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD(lean_object* v_00_u03b1_1007_, lean_object* v_00_u03b2_1008_, lean_object* v_cmp_1009_, lean_object* v_t_1010_, lean_object* v_n_1011_, lean_object* v_fallback_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_1010_, v_n_1011_, v_fallback_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_cmp_1016_, lean_object* v_t_1017_, lean_object* v_n_1018_, lean_object* v_fallback_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Std_DTreeMap_entryAtIdxD(v_00_u03b1_1014_, v_00_u03b2_1015_, v_cmp_1016_, v_t_1017_, v_n_1018_, v_fallback_1019_);
lean_dec_ref(v_fallback_1019_);
lean_dec(v_t_1017_);
lean_dec_ref(v_cmp_1016_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_1021_, lean_object* v_n_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_1021_, v_n_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_1024_, lean_object* v_n_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Std_DTreeMap_keyAtIdx_x3f___redArg(v_t_1024_, v_n_1025_);
lean_dec(v_t_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_1027_, lean_object* v_00_u03b2_1028_, lean_object* v_cmp_1029_, lean_object* v_t_1030_, lean_object* v_n_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_1030_, v_n_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_1033_, lean_object* v_00_u03b2_1034_, lean_object* v_cmp_1035_, lean_object* v_t_1036_, lean_object* v_n_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Std_DTreeMap_keyAtIdx_x3f(v_00_u03b1_1033_, v_00_u03b2_1034_, v_cmp_1035_, v_t_1036_, v_n_1037_);
lean_dec(v_t_1036_);
lean_dec_ref(v_cmp_1035_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___redArg(lean_object* v_t_1039_, lean_object* v_n_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1039_, v_n_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_1042_, lean_object* v_n_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Std_DTreeMap_keyAtIdx___redArg(v_t_1042_, v_n_1043_);
lean_dec(v_t_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx(lean_object* v_00_u03b1_1045_, lean_object* v_00_u03b2_1046_, lean_object* v_cmp_1047_, lean_object* v_t_1048_, lean_object* v_n_1049_, lean_object* v_h_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1048_, v_n_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_1052_, lean_object* v_00_u03b2_1053_, lean_object* v_cmp_1054_, lean_object* v_t_1055_, lean_object* v_n_1056_, lean_object* v_h_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Std_DTreeMap_keyAtIdx(v_00_u03b1_1052_, v_00_u03b2_1053_, v_cmp_1054_, v_t_1055_, v_n_1056_, v_h_1057_);
lean_dec(v_t_1055_);
lean_dec_ref(v_cmp_1054_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_1059_, lean_object* v_t_1060_, lean_object* v_n_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1059_, v_t_1060_, v_n_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_1063_, lean_object* v_t_1064_, lean_object* v_n_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Std_DTreeMap_keyAtIdx_x21___redArg(v_inst_1063_, v_t_1064_, v_n_1065_);
lean_dec(v_t_1064_);
lean_dec(v_inst_1063_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_1067_, lean_object* v_00_u03b2_1068_, lean_object* v_cmp_1069_, lean_object* v_inst_1070_, lean_object* v_t_1071_, lean_object* v_n_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1070_, v_t_1071_, v_n_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_1074_, lean_object* v_00_u03b2_1075_, lean_object* v_cmp_1076_, lean_object* v_inst_1077_, lean_object* v_t_1078_, lean_object* v_n_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Std_DTreeMap_keyAtIdx_x21(v_00_u03b1_1074_, v_00_u03b2_1075_, v_cmp_1076_, v_inst_1077_, v_t_1078_, v_n_1079_);
lean_dec(v_t_1078_);
lean_dec(v_inst_1077_);
lean_dec_ref(v_cmp_1076_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___redArg(lean_object* v_t_1081_, lean_object* v_n_1082_, lean_object* v_fallback_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1081_, v_n_1082_, v_fallback_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_1085_, lean_object* v_n_1086_, lean_object* v_fallback_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Std_DTreeMap_keyAtIdxD___redArg(v_t_1085_, v_n_1086_, v_fallback_1087_);
lean_dec(v_fallback_1087_);
lean_dec(v_t_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD(lean_object* v_00_u03b1_1089_, lean_object* v_00_u03b2_1090_, lean_object* v_cmp_1091_, lean_object* v_t_1092_, lean_object* v_n_1093_, lean_object* v_fallback_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1092_, v_n_1093_, v_fallback_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_cmp_1098_, lean_object* v_t_1099_, lean_object* v_n_1100_, lean_object* v_fallback_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_DTreeMap_keyAtIdxD(v_00_u03b1_1096_, v_00_u03b2_1097_, v_cmp_1098_, v_t_1099_, v_n_1100_, v_fallback_1101_);
lean_dec(v_fallback_1101_);
lean_dec(v_t_1099_);
lean_dec_ref(v_cmp_1098_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1103_, lean_object* v_t_1104_, lean_object* v_k_1105_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_box(0);
v___x_1107_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1103_, v_k_1105_, v___x_1106_, v_t_1104_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1108_, lean_object* v_00_u03b2_1109_, lean_object* v_cmp_1110_, lean_object* v_t_1111_, lean_object* v_k_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1110_, v_k_1112_, v___x_1113_, v_t_1111_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1115_, lean_object* v_t_1116_, lean_object* v_k_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_box(0);
v___x_1119_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1115_, v_k_1117_, v___x_1118_, v_t_1116_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1120_, lean_object* v_00_u03b2_1121_, lean_object* v_cmp_1122_, lean_object* v_t_1123_, lean_object* v_k_1124_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_box(0);
v___x_1126_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1122_, v_k_1124_, v___x_1125_, v_t_1123_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1127_, lean_object* v_t_1128_, lean_object* v_k_1129_){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_box(0);
v___x_1131_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1127_, v_k_1129_, v___x_1130_, v_t_1128_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1132_, lean_object* v_00_u03b2_1133_, lean_object* v_cmp_1134_, lean_object* v_t_1135_, lean_object* v_k_1136_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_box(0);
v___x_1138_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1134_, v_k_1136_, v___x_1137_, v_t_1135_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1139_, lean_object* v_t_1140_, lean_object* v_k_1141_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_box(0);
v___x_1143_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1139_, v_k_1141_, v___x_1142_, v_t_1140_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1144_, lean_object* v_00_u03b2_1145_, lean_object* v_cmp_1146_, lean_object* v_t_1147_, lean_object* v_k_1148_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_box(0);
v___x_1150_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1146_, v_k_1148_, v___x_1149_, v_t_1147_);
return v___x_1150_;
}
}
static lean_object* _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1154_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1155_ = lean_unsigned_to_nat(14u);
v___x_1156_ = lean_unsigned_to_nat(22u);
v___x_1157_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1158_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1159_ = l_mkPanicMessageWithDecl(v___x_1158_, v___x_1157_, v___x_1156_, v___x_1155_, v___x_1154_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1160_, lean_object* v_inst_1161_, lean_object* v_t_1162_, lean_object* v_k_1163_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_box(0);
v___x_1165_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1160_, v_k_1163_, v___x_1164_, v_t_1162_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1169_, lean_object* v_inst_1170_, lean_object* v_t_1171_, lean_object* v_k_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Std_DTreeMap_getEntryGE_x21___redArg(v_cmp_1169_, v_inst_1170_, v_t_1171_, v_k_1172_);
lean_dec_ref(v_inst_1170_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1174_, lean_object* v_00_u03b2_1175_, lean_object* v_cmp_1176_, lean_object* v_inst_1177_, lean_object* v_t_1178_, lean_object* v_k_1179_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_box(0);
v___x_1181_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1176_, v_k_1179_, v___x_1180_, v_t_1178_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1183_ = l_panic___redArg(v_inst_1177_, v___x_1182_);
return v___x_1183_;
}
else
{
lean_object* v_val_1184_; 
v_val_1184_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_val_1184_);
lean_dec_ref_known(v___x_1181_, 1);
return v_val_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1185_, lean_object* v_00_u03b2_1186_, lean_object* v_cmp_1187_, lean_object* v_inst_1188_, lean_object* v_t_1189_, lean_object* v_k_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Std_DTreeMap_getEntryGE_x21(v_00_u03b1_1185_, v_00_u03b2_1186_, v_cmp_1187_, v_inst_1188_, v_t_1189_, v_k_1190_);
lean_dec_ref(v_inst_1188_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1192_, lean_object* v_inst_1193_, lean_object* v_t_1194_, lean_object* v_k_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_box(0);
v___x_1197_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1192_, v_k_1195_, v___x_1196_, v_t_1194_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1199_ = l_panic___redArg(v_inst_1193_, v___x_1198_);
return v___x_1199_;
}
else
{
lean_object* v_val_1200_; 
v_val_1200_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_val_1200_);
lean_dec_ref_known(v___x_1197_, 1);
return v_val_1200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1201_, lean_object* v_inst_1202_, lean_object* v_t_1203_, lean_object* v_k_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Std_DTreeMap_getEntryGT_x21___redArg(v_cmp_1201_, v_inst_1202_, v_t_1203_, v_k_1204_);
lean_dec_ref(v_inst_1202_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1206_, lean_object* v_00_u03b2_1207_, lean_object* v_cmp_1208_, lean_object* v_inst_1209_, lean_object* v_t_1210_, lean_object* v_k_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1208_, v_k_1211_, v___x_1212_, v_t_1210_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1215_ = l_panic___redArg(v_inst_1209_, v___x_1214_);
return v___x_1215_;
}
else
{
lean_object* v_val_1216_; 
v_val_1216_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_val_1216_);
lean_dec_ref_known(v___x_1213_, 1);
return v_val_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1217_, lean_object* v_00_u03b2_1218_, lean_object* v_cmp_1219_, lean_object* v_inst_1220_, lean_object* v_t_1221_, lean_object* v_k_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Std_DTreeMap_getEntryGT_x21(v_00_u03b1_1217_, v_00_u03b2_1218_, v_cmp_1219_, v_inst_1220_, v_t_1221_, v_k_1222_);
lean_dec_ref(v_inst_1220_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1224_, lean_object* v_inst_1225_, lean_object* v_t_1226_, lean_object* v_k_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_box(0);
v___x_1229_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1224_, v_k_1227_, v___x_1228_, v_t_1226_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1231_ = l_panic___redArg(v_inst_1225_, v___x_1230_);
return v___x_1231_;
}
else
{
lean_object* v_val_1232_; 
v_val_1232_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_val_1232_);
lean_dec_ref_known(v___x_1229_, 1);
return v_val_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1233_, lean_object* v_inst_1234_, lean_object* v_t_1235_, lean_object* v_k_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Std_DTreeMap_getEntryLE_x21___redArg(v_cmp_1233_, v_inst_1234_, v_t_1235_, v_k_1236_);
lean_dec_ref(v_inst_1234_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1238_, lean_object* v_00_u03b2_1239_, lean_object* v_cmp_1240_, lean_object* v_inst_1241_, lean_object* v_t_1242_, lean_object* v_k_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_box(0);
v___x_1245_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1240_, v_k_1243_, v___x_1244_, v_t_1242_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_00_u03b2_1250_, lean_object* v_cmp_1251_, lean_object* v_inst_1252_, lean_object* v_t_1253_, lean_object* v_k_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Std_DTreeMap_getEntryLE_x21(v_00_u03b1_1249_, v_00_u03b2_1250_, v_cmp_1251_, v_inst_1252_, v_t_1253_, v_k_1254_);
lean_dec_ref(v_inst_1252_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1256_, lean_object* v_inst_1257_, lean_object* v_t_1258_, lean_object* v_k_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_box(0);
v___x_1261_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1256_, v_k_1259_, v___x_1260_, v_t_1258_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1263_ = l_panic___redArg(v_inst_1257_, v___x_1262_);
return v___x_1263_;
}
else
{
lean_object* v_val_1264_; 
v_val_1264_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_val_1264_);
lean_dec_ref_known(v___x_1261_, 1);
return v_val_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1265_, lean_object* v_inst_1266_, lean_object* v_t_1267_, lean_object* v_k_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Std_DTreeMap_getEntryLT_x21___redArg(v_cmp_1265_, v_inst_1266_, v_t_1267_, v_k_1268_);
lean_dec_ref(v_inst_1266_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1270_, lean_object* v_00_u03b2_1271_, lean_object* v_cmp_1272_, lean_object* v_inst_1273_, lean_object* v_t_1274_, lean_object* v_k_1275_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_box(0);
v___x_1277_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1272_, v_k_1275_, v___x_1276_, v_t_1274_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1281_, lean_object* v_00_u03b2_1282_, lean_object* v_cmp_1283_, lean_object* v_inst_1284_, lean_object* v_t_1285_, lean_object* v_k_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Std_DTreeMap_getEntryLT_x21(v_00_u03b1_1281_, v_00_u03b2_1282_, v_cmp_1283_, v_inst_1284_, v_t_1285_, v_k_1286_);
lean_dec_ref(v_inst_1284_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___redArg(lean_object* v_cmp_1288_, lean_object* v_t_1289_, lean_object* v_k_1290_, lean_object* v_fallback_1291_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_box(0);
v___x_1293_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1288_, v_k_1290_, v___x_1292_, v_t_1289_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_inc_ref(v_fallback_1291_);
return v_fallback_1291_;
}
else
{
lean_object* v_val_1294_; 
v_val_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_val_1294_);
lean_dec_ref_known(v___x_1293_, 1);
return v_val_1294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1295_, lean_object* v_t_1296_, lean_object* v_k_1297_, lean_object* v_fallback_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_DTreeMap_getEntryGED___redArg(v_cmp_1295_, v_t_1296_, v_k_1297_, v_fallback_1298_);
lean_dec_ref(v_fallback_1298_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED(lean_object* v_00_u03b1_1300_, lean_object* v_00_u03b2_1301_, lean_object* v_cmp_1302_, lean_object* v_t_1303_, lean_object* v_k_1304_, lean_object* v_fallback_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1302_, v_k_1304_, v___x_1306_, v_t_1303_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_inc_ref(v_fallback_1305_);
return v_fallback_1305_;
}
else
{
lean_object* v_val_1308_; 
v_val_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v___x_1307_, 1);
return v_val_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_cmp_1311_, lean_object* v_t_1312_, lean_object* v_k_1313_, lean_object* v_fallback_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Std_DTreeMap_getEntryGED(v_00_u03b1_1309_, v_00_u03b2_1310_, v_cmp_1311_, v_t_1312_, v_k_1313_, v_fallback_1314_);
lean_dec_ref(v_fallback_1314_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1316_, lean_object* v_t_1317_, lean_object* v_k_1318_, lean_object* v_fallback_1319_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_box(0);
v___x_1321_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1316_, v_k_1318_, v___x_1320_, v_t_1317_);
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
lean_dec_ref_known(v___x_1321_, 1);
return v_val_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1323_, lean_object* v_t_1324_, lean_object* v_k_1325_, lean_object* v_fallback_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Std_DTreeMap_getEntryGTD___redArg(v_cmp_1323_, v_t_1324_, v_k_1325_, v_fallback_1326_);
lean_dec_ref(v_fallback_1326_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD(lean_object* v_00_u03b1_1328_, lean_object* v_00_u03b2_1329_, lean_object* v_cmp_1330_, lean_object* v_t_1331_, lean_object* v_k_1332_, lean_object* v_fallback_1333_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_box(0);
v___x_1335_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1330_, v_k_1332_, v___x_1334_, v_t_1331_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_cmp_1339_, lean_object* v_t_1340_, lean_object* v_k_1341_, lean_object* v_fallback_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_DTreeMap_getEntryGTD(v_00_u03b1_1337_, v_00_u03b2_1338_, v_cmp_1339_, v_t_1340_, v_k_1341_, v_fallback_1342_);
lean_dec_ref(v_fallback_1342_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___redArg(lean_object* v_cmp_1344_, lean_object* v_t_1345_, lean_object* v_k_1346_, lean_object* v_fallback_1347_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_box(0);
v___x_1349_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1344_, v_k_1346_, v___x_1348_, v_t_1345_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_inc_ref(v_fallback_1347_);
return v_fallback_1347_;
}
else
{
lean_object* v_val_1350_; 
v_val_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_val_1350_);
lean_dec_ref_known(v___x_1349_, 1);
return v_val_1350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1351_, lean_object* v_t_1352_, lean_object* v_k_1353_, lean_object* v_fallback_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Std_DTreeMap_getEntryLED___redArg(v_cmp_1351_, v_t_1352_, v_k_1353_, v_fallback_1354_);
lean_dec_ref(v_fallback_1354_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED(lean_object* v_00_u03b1_1356_, lean_object* v_00_u03b2_1357_, lean_object* v_cmp_1358_, lean_object* v_t_1359_, lean_object* v_k_1360_, lean_object* v_fallback_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1358_, v_k_1360_, v___x_1362_, v_t_1359_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_inc_ref(v_fallback_1361_);
return v_fallback_1361_;
}
else
{
lean_object* v_val_1364_; 
v_val_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_val_1364_);
lean_dec_ref_known(v___x_1363_, 1);
return v_val_1364_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_cmp_1367_, lean_object* v_t_1368_, lean_object* v_k_1369_, lean_object* v_fallback_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Std_DTreeMap_getEntryLED(v_00_u03b1_1365_, v_00_u03b2_1366_, v_cmp_1367_, v_t_1368_, v_k_1369_, v_fallback_1370_);
lean_dec_ref(v_fallback_1370_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1372_, lean_object* v_t_1373_, lean_object* v_k_1374_, lean_object* v_fallback_1375_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_box(0);
v___x_1377_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1372_, v_k_1374_, v___x_1376_, v_t_1373_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_inc_ref(v_fallback_1375_);
return v_fallback_1375_;
}
else
{
lean_object* v_val_1378_; 
v_val_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_val_1378_);
lean_dec_ref_known(v___x_1377_, 1);
return v_val_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1379_, lean_object* v_t_1380_, lean_object* v_k_1381_, lean_object* v_fallback_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Std_DTreeMap_getEntryLTD___redArg(v_cmp_1379_, v_t_1380_, v_k_1381_, v_fallback_1382_);
lean_dec_ref(v_fallback_1382_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD(lean_object* v_00_u03b1_1384_, lean_object* v_00_u03b2_1385_, lean_object* v_cmp_1386_, lean_object* v_t_1387_, lean_object* v_k_1388_, lean_object* v_fallback_1389_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_box(0);
v___x_1391_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1386_, v_k_1388_, v___x_1390_, v_t_1387_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_inc_ref(v_fallback_1389_);
return v_fallback_1389_;
}
else
{
lean_object* v_val_1392_; 
v_val_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_val_1392_);
lean_dec_ref_known(v___x_1391_, 1);
return v_val_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1393_, lean_object* v_00_u03b2_1394_, lean_object* v_cmp_1395_, lean_object* v_t_1396_, lean_object* v_k_1397_, lean_object* v_fallback_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Std_DTreeMap_getEntryLTD(v_00_u03b1_1393_, v_00_u03b2_1394_, v_cmp_1395_, v_t_1396_, v_k_1397_, v_fallback_1398_);
lean_dec_ref(v_fallback_1398_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1400_, lean_object* v_t_1401_, lean_object* v_k_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_box(0);
v___x_1404_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1400_, v_k_1402_, v___x_1403_, v_t_1401_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1405_, lean_object* v_00_u03b2_1406_, lean_object* v_cmp_1407_, lean_object* v_t_1408_, lean_object* v_k_1409_){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_box(0);
v___x_1411_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1407_, v_k_1409_, v___x_1410_, v_t_1408_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1412_, lean_object* v_t_1413_, lean_object* v_k_1414_){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_box(0);
v___x_1416_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1412_, v_k_1414_, v___x_1415_, v_t_1413_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1417_, lean_object* v_00_u03b2_1418_, lean_object* v_cmp_1419_, lean_object* v_t_1420_, lean_object* v_k_1421_){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_box(0);
v___x_1423_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1419_, v_k_1421_, v___x_1422_, v_t_1420_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1424_, lean_object* v_t_1425_, lean_object* v_k_1426_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_box(0);
v___x_1428_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1424_, v_k_1426_, v___x_1427_, v_t_1425_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1429_, lean_object* v_00_u03b2_1430_, lean_object* v_cmp_1431_, lean_object* v_t_1432_, lean_object* v_k_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1431_, v_k_1433_, v___x_1434_, v_t_1432_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1436_, lean_object* v_t_1437_, lean_object* v_k_1438_){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_box(0);
v___x_1440_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1436_, v_k_1438_, v___x_1439_, v_t_1437_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1441_, lean_object* v_00_u03b2_1442_, lean_object* v_cmp_1443_, lean_object* v_t_1444_, lean_object* v_k_1445_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_box(0);
v___x_1447_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1443_, v_k_1445_, v___x_1446_, v_t_1444_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1448_, lean_object* v_inst_1449_, lean_object* v_t_1450_, lean_object* v_k_1451_){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_box(0);
v___x_1453_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1448_, v_k_1451_, v___x_1452_, v_t_1450_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1455_ = l_panic___redArg(v_inst_1449_, v___x_1454_);
return v___x_1455_;
}
else
{
lean_object* v_val_1456_; 
v_val_1456_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_val_1456_);
lean_dec_ref_known(v___x_1453_, 1);
return v_val_1456_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1457_, lean_object* v_inst_1458_, lean_object* v_t_1459_, lean_object* v_k_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Std_DTreeMap_getKeyGE_x21___redArg(v_cmp_1457_, v_inst_1458_, v_t_1459_, v_k_1460_);
lean_dec(v_inst_1458_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1462_, lean_object* v_00_u03b2_1463_, lean_object* v_cmp_1464_, lean_object* v_inst_1465_, lean_object* v_t_1466_, lean_object* v_k_1467_){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_box(0);
v___x_1469_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1464_, v_k_1467_, v___x_1468_, v_t_1466_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1471_ = l_panic___redArg(v_inst_1465_, v___x_1470_);
return v___x_1471_;
}
else
{
lean_object* v_val_1472_; 
v_val_1472_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_val_1472_);
lean_dec_ref_known(v___x_1469_, 1);
return v_val_1472_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1473_, lean_object* v_00_u03b2_1474_, lean_object* v_cmp_1475_, lean_object* v_inst_1476_, lean_object* v_t_1477_, lean_object* v_k_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Std_DTreeMap_getKeyGE_x21(v_00_u03b1_1473_, v_00_u03b2_1474_, v_cmp_1475_, v_inst_1476_, v_t_1477_, v_k_1478_);
lean_dec(v_inst_1476_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1480_, lean_object* v_inst_1481_, lean_object* v_t_1482_, lean_object* v_k_1483_){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_box(0);
v___x_1485_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1480_, v_k_1483_, v___x_1484_, v_t_1482_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1487_ = l_panic___redArg(v_inst_1481_, v___x_1486_);
return v___x_1487_;
}
else
{
lean_object* v_val_1488_; 
v_val_1488_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v___x_1485_, 1);
return v_val_1488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1489_, lean_object* v_inst_1490_, lean_object* v_t_1491_, lean_object* v_k_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Std_DTreeMap_getKeyGT_x21___redArg(v_cmp_1489_, v_inst_1490_, v_t_1491_, v_k_1492_);
lean_dec(v_inst_1490_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1494_, lean_object* v_00_u03b2_1495_, lean_object* v_cmp_1496_, lean_object* v_inst_1497_, lean_object* v_t_1498_, lean_object* v_k_1499_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_box(0);
v___x_1501_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1496_, v_k_1499_, v___x_1500_, v_t_1498_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1503_ = l_panic___redArg(v_inst_1497_, v___x_1502_);
return v___x_1503_;
}
else
{
lean_object* v_val_1504_; 
v_val_1504_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_val_1504_);
lean_dec_ref_known(v___x_1501_, 1);
return v_val_1504_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1505_, lean_object* v_00_u03b2_1506_, lean_object* v_cmp_1507_, lean_object* v_inst_1508_, lean_object* v_t_1509_, lean_object* v_k_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Std_DTreeMap_getKeyGT_x21(v_00_u03b1_1505_, v_00_u03b2_1506_, v_cmp_1507_, v_inst_1508_, v_t_1509_, v_k_1510_);
lean_dec(v_inst_1508_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1512_, lean_object* v_inst_1513_, lean_object* v_t_1514_, lean_object* v_k_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_box(0);
v___x_1517_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1512_, v_k_1515_, v___x_1516_, v_t_1514_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1519_ = l_panic___redArg(v_inst_1513_, v___x_1518_);
return v___x_1519_;
}
else
{
lean_object* v_val_1520_; 
v_val_1520_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v___x_1517_, 1);
return v_val_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1521_, lean_object* v_inst_1522_, lean_object* v_t_1523_, lean_object* v_k_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Std_DTreeMap_getKeyLE_x21___redArg(v_cmp_1521_, v_inst_1522_, v_t_1523_, v_k_1524_);
lean_dec(v_inst_1522_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1526_, lean_object* v_00_u03b2_1527_, lean_object* v_cmp_1528_, lean_object* v_inst_1529_, lean_object* v_t_1530_, lean_object* v_k_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_box(0);
v___x_1533_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1528_, v_k_1531_, v___x_1532_, v_t_1530_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1535_ = l_panic___redArg(v_inst_1529_, v___x_1534_);
return v___x_1535_;
}
else
{
lean_object* v_val_1536_; 
v_val_1536_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___x_1533_, 1);
return v_val_1536_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_00_u03b2_1538_, lean_object* v_cmp_1539_, lean_object* v_inst_1540_, lean_object* v_t_1541_, lean_object* v_k_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Std_DTreeMap_getKeyLE_x21(v_00_u03b1_1537_, v_00_u03b2_1538_, v_cmp_1539_, v_inst_1540_, v_t_1541_, v_k_1542_);
lean_dec(v_inst_1540_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1544_, lean_object* v_inst_1545_, lean_object* v_t_1546_, lean_object* v_k_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1544_, v_k_1547_, v___x_1548_, v_t_1546_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1551_ = l_panic___redArg(v_inst_1545_, v___x_1550_);
return v___x_1551_;
}
else
{
lean_object* v_val_1552_; 
v_val_1552_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1549_, 1);
return v_val_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1553_, lean_object* v_inst_1554_, lean_object* v_t_1555_, lean_object* v_k_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Std_DTreeMap_getKeyLT_x21___redArg(v_cmp_1553_, v_inst_1554_, v_t_1555_, v_k_1556_);
lean_dec(v_inst_1554_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1558_, lean_object* v_00_u03b2_1559_, lean_object* v_cmp_1560_, lean_object* v_inst_1561_, lean_object* v_t_1562_, lean_object* v_k_1563_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_box(0);
v___x_1565_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1560_, v_k_1563_, v___x_1564_, v_t_1562_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1569_, lean_object* v_00_u03b2_1570_, lean_object* v_cmp_1571_, lean_object* v_inst_1572_, lean_object* v_t_1573_, lean_object* v_k_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Std_DTreeMap_getKeyLT_x21(v_00_u03b1_1569_, v_00_u03b2_1570_, v_cmp_1571_, v_inst_1572_, v_t_1573_, v_k_1574_);
lean_dec(v_inst_1572_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___redArg(lean_object* v_cmp_1576_, lean_object* v_t_1577_, lean_object* v_k_1578_, lean_object* v_fallback_1579_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_box(0);
v___x_1581_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1576_, v_k_1578_, v___x_1580_, v_t_1577_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_inc(v_fallback_1579_);
return v_fallback_1579_;
}
else
{
lean_object* v_val_1582_; 
v_val_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_val_1582_);
lean_dec_ref_known(v___x_1581_, 1);
return v_val_1582_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1583_, lean_object* v_t_1584_, lean_object* v_k_1585_, lean_object* v_fallback_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Std_DTreeMap_getKeyGED___redArg(v_cmp_1583_, v_t_1584_, v_k_1585_, v_fallback_1586_);
lean_dec(v_fallback_1586_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED(lean_object* v_00_u03b1_1588_, lean_object* v_00_u03b2_1589_, lean_object* v_cmp_1590_, lean_object* v_t_1591_, lean_object* v_k_1592_, lean_object* v_fallback_1593_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_box(0);
v___x_1595_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1590_, v_k_1592_, v___x_1594_, v_t_1591_);
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
lean_dec_ref_known(v___x_1595_, 1);
return v_val_1596_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1597_, lean_object* v_00_u03b2_1598_, lean_object* v_cmp_1599_, lean_object* v_t_1600_, lean_object* v_k_1601_, lean_object* v_fallback_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Std_DTreeMap_getKeyGED(v_00_u03b1_1597_, v_00_u03b2_1598_, v_cmp_1599_, v_t_1600_, v_k_1601_, v_fallback_1602_);
lean_dec(v_fallback_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1604_, lean_object* v_t_1605_, lean_object* v_k_1606_, lean_object* v_fallback_1607_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_box(0);
v___x_1609_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1604_, v_k_1606_, v___x_1608_, v_t_1605_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_inc(v_fallback_1607_);
return v_fallback_1607_;
}
else
{
lean_object* v_val_1610_; 
v_val_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_val_1610_);
lean_dec_ref_known(v___x_1609_, 1);
return v_val_1610_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1611_, lean_object* v_t_1612_, lean_object* v_k_1613_, lean_object* v_fallback_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Std_DTreeMap_getKeyGTD___redArg(v_cmp_1611_, v_t_1612_, v_k_1613_, v_fallback_1614_);
lean_dec(v_fallback_1614_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD(lean_object* v_00_u03b1_1616_, lean_object* v_00_u03b2_1617_, lean_object* v_cmp_1618_, lean_object* v_t_1619_, lean_object* v_k_1620_, lean_object* v_fallback_1621_){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_box(0);
v___x_1623_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1618_, v_k_1620_, v___x_1622_, v_t_1619_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1625_, lean_object* v_00_u03b2_1626_, lean_object* v_cmp_1627_, lean_object* v_t_1628_, lean_object* v_k_1629_, lean_object* v_fallback_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Std_DTreeMap_getKeyGTD(v_00_u03b1_1625_, v_00_u03b2_1626_, v_cmp_1627_, v_t_1628_, v_k_1629_, v_fallback_1630_);
lean_dec(v_fallback_1630_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___redArg(lean_object* v_cmp_1632_, lean_object* v_t_1633_, lean_object* v_k_1634_, lean_object* v_fallback_1635_){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_box(0);
v___x_1637_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1632_, v_k_1634_, v___x_1636_, v_t_1633_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_inc(v_fallback_1635_);
return v_fallback_1635_;
}
else
{
lean_object* v_val_1638_; 
v_val_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_val_1638_);
lean_dec_ref_known(v___x_1637_, 1);
return v_val_1638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1639_, lean_object* v_t_1640_, lean_object* v_k_1641_, lean_object* v_fallback_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Std_DTreeMap_getKeyLED___redArg(v_cmp_1639_, v_t_1640_, v_k_1641_, v_fallback_1642_);
lean_dec(v_fallback_1642_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED(lean_object* v_00_u03b1_1644_, lean_object* v_00_u03b2_1645_, lean_object* v_cmp_1646_, lean_object* v_t_1647_, lean_object* v_k_1648_, lean_object* v_fallback_1649_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_box(0);
v___x_1651_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1646_, v_k_1648_, v___x_1650_, v_t_1647_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1653_, lean_object* v_00_u03b2_1654_, lean_object* v_cmp_1655_, lean_object* v_t_1656_, lean_object* v_k_1657_, lean_object* v_fallback_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Std_DTreeMap_getKeyLED(v_00_u03b1_1653_, v_00_u03b2_1654_, v_cmp_1655_, v_t_1656_, v_k_1657_, v_fallback_1658_);
lean_dec(v_fallback_1658_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1660_, lean_object* v_t_1661_, lean_object* v_k_1662_, lean_object* v_fallback_1663_){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_box(0);
v___x_1665_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1660_, v_k_1662_, v___x_1664_, v_t_1661_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_inc(v_fallback_1663_);
return v_fallback_1663_;
}
else
{
lean_object* v_val_1666_; 
v_val_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_val_1666_);
lean_dec_ref_known(v___x_1665_, 1);
return v_val_1666_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1667_, lean_object* v_t_1668_, lean_object* v_k_1669_, lean_object* v_fallback_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Std_DTreeMap_getKeyLTD___redArg(v_cmp_1667_, v_t_1668_, v_k_1669_, v_fallback_1670_);
lean_dec(v_fallback_1670_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD(lean_object* v_00_u03b1_1672_, lean_object* v_00_u03b2_1673_, lean_object* v_cmp_1674_, lean_object* v_t_1675_, lean_object* v_k_1676_, lean_object* v_fallback_1677_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_box(0);
v___x_1679_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1674_, v_k_1676_, v___x_1678_, v_t_1675_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_inc(v_fallback_1677_);
return v_fallback_1677_;
}
else
{
lean_object* v_val_1680_; 
v_val_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_val_1680_);
lean_dec_ref_known(v___x_1679_, 1);
return v_val_1680_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_cmp_1683_, lean_object* v_t_1684_, lean_object* v_k_1685_, lean_object* v_fallback_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Std_DTreeMap_getKeyLTD(v_00_u03b1_1681_, v_00_u03b2_1682_, v_cmp_1683_, v_t_1684_, v_k_1685_, v_fallback_1686_);
lean_dec(v_fallback_1686_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1688_, lean_object* v_t_1689_, lean_object* v_a_1690_, lean_object* v_b_1691_){
_start:
{
lean_object* v___x_1692_; 
lean_inc(v_a_1690_);
lean_inc(v_t_1689_);
lean_inc_ref(v_cmp_1688_);
v___x_1692_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1688_, v_t_1689_, v_a_1690_);
if (lean_obj_tag(v___x_1692_) == 0)
{
uint8_t v___x_1693_; 
lean_inc(v_t_1689_);
lean_inc(v_a_1690_);
lean_inc_ref(v_cmp_1688_);
v___x_1693_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1688_, v_a_1690_, v_t_1689_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1688_, v_a_1690_, v_b_1691_, v_t_1689_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1692_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
return v___x_1695_;
}
else
{
lean_object* v___x_1696_; 
lean_dec(v_b_1691_);
lean_dec(v_a_1690_);
lean_dec_ref(v_cmp_1688_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1692_);
lean_ctor_set(v___x_1696_, 1, v_t_1689_);
return v___x_1696_;
}
}
else
{
lean_object* v___x_1697_; 
lean_dec(v_b_1691_);
lean_dec(v_a_1690_);
lean_dec_ref(v_cmp_1688_);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1692_);
lean_ctor_set(v___x_1697_, 1, v_t_1689_);
return v___x_1697_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1698_, lean_object* v_cmp_1699_, lean_object* v_00_u03b2_1700_, lean_object* v_t_1701_, lean_object* v_a_1702_, lean_object* v_b_1703_){
_start:
{
lean_object* v___x_1704_; 
lean_inc(v_a_1702_);
lean_inc(v_t_1701_);
lean_inc_ref(v_cmp_1699_);
v___x_1704_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1699_, v_t_1701_, v_a_1702_);
if (lean_obj_tag(v___x_1704_) == 0)
{
uint8_t v___x_1705_; 
lean_inc(v_t_1701_);
lean_inc(v_a_1702_);
lean_inc_ref(v_cmp_1699_);
v___x_1705_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1699_, v_a_1702_, v_t_1701_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1699_, v_a_1702_, v_b_1703_, v_t_1701_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1704_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; 
lean_dec(v_b_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_cmp_1699_);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1704_);
lean_ctor_set(v___x_1708_, 1, v_t_1701_);
return v___x_1708_;
}
}
else
{
lean_object* v___x_1709_; 
lean_dec(v_b_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_cmp_1699_);
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1704_);
lean_ctor_set(v___x_1709_, 1, v_t_1701_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x3f___redArg(lean_object* v_cmp_1710_, lean_object* v_t_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1710_, v_t_1711_, v_a_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x3f(lean_object* v_00_u03b1_1714_, lean_object* v_cmp_1715_, lean_object* v_00_u03b2_1716_, lean_object* v_t_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1715_, v_t_1717_, v_a_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get___redArg(lean_object* v_cmp_1720_, lean_object* v_t_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1720_, v_t_1721_, v_a_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get(lean_object* v_00_u03b1_1724_, lean_object* v_cmp_1725_, lean_object* v_00_u03b2_1726_, lean_object* v_t_1727_, lean_object* v_a_1728_, lean_object* v_h_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1725_, v_t_1727_, v_a_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___redArg(lean_object* v_cmp_1731_, lean_object* v_inst_1732_, lean_object* v_t_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1731_, v_inst_1732_, v_t_1733_, v_a_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___redArg___boxed(lean_object* v_cmp_1736_, lean_object* v_inst_1737_, lean_object* v_t_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Std_DTreeMap_Const_get_x21___redArg(v_cmp_1736_, v_inst_1737_, v_t_1738_, v_a_1739_);
lean_dec(v_inst_1737_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21(lean_object* v_00_u03b1_1741_, lean_object* v_cmp_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_inst_1744_, lean_object* v_t_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1742_, v_inst_1744_, v_t_1745_, v_a_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___boxed(lean_object* v_00_u03b1_1748_, lean_object* v_cmp_1749_, lean_object* v_00_u03b2_1750_, lean_object* v_inst_1751_, lean_object* v_t_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Std_DTreeMap_Const_get_x21(v_00_u03b1_1748_, v_cmp_1749_, v_00_u03b2_1750_, v_inst_1751_, v_t_1752_, v_a_1753_);
lean_dec(v_inst_1751_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___redArg(lean_object* v_cmp_1755_, lean_object* v_t_1756_, lean_object* v_a_1757_, lean_object* v_fallback_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1755_, v_t_1756_, v_a_1757_, v_fallback_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___redArg___boxed(lean_object* v_cmp_1760_, lean_object* v_t_1761_, lean_object* v_a_1762_, lean_object* v_fallback_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Std_DTreeMap_Const_getD___redArg(v_cmp_1760_, v_t_1761_, v_a_1762_, v_fallback_1763_);
lean_dec(v_fallback_1763_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD(lean_object* v_00_u03b1_1765_, lean_object* v_cmp_1766_, lean_object* v_00_u03b2_1767_, lean_object* v_t_1768_, lean_object* v_a_1769_, lean_object* v_fallback_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1766_, v_t_1768_, v_a_1769_, v_fallback_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___boxed(lean_object* v_00_u03b1_1772_, lean_object* v_cmp_1773_, lean_object* v_00_u03b2_1774_, lean_object* v_t_1775_, lean_object* v_a_1776_, lean_object* v_fallback_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Std_DTreeMap_Const_getD(v_00_u03b1_1772_, v_cmp_1773_, v_00_u03b2_1774_, v_t_1775_, v_a_1776_, v_fallback_1777_);
lean_dec(v_fallback_1777_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___redArg(lean_object* v_t_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Std_DTreeMap_Const_minEntry_x3f___redArg(v_t_1781_);
lean_dec(v_t_1781_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f(lean_object* v_00_u03b1_1783_, lean_object* v_cmp_1784_, lean_object* v_00_u03b2_1785_, lean_object* v_t_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1788_, lean_object* v_cmp_1789_, lean_object* v_00_u03b2_1790_, lean_object* v_t_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Std_DTreeMap_Const_minEntry_x3f(v_00_u03b1_1788_, v_cmp_1789_, v_00_u03b2_1790_, v_t_1791_);
lean_dec(v_t_1791_);
lean_dec_ref(v_cmp_1789_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___redArg(lean_object* v_t_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___redArg___boxed(lean_object* v_t_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Std_DTreeMap_Const_minEntry___redArg(v_t_1795_);
lean_dec(v_t_1795_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry(lean_object* v_00_u03b1_1797_, lean_object* v_cmp_1798_, lean_object* v_00_u03b2_1799_, lean_object* v_t_1800_, lean_object* v_h_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___boxed(lean_object* v_00_u03b1_1803_, lean_object* v_cmp_1804_, lean_object* v_00_u03b2_1805_, lean_object* v_t_1806_, lean_object* v_h_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_DTreeMap_Const_minEntry(v_00_u03b1_1803_, v_cmp_1804_, v_00_u03b2_1805_, v_t_1806_, v_h_1807_);
lean_dec(v_t_1806_);
lean_dec_ref(v_cmp_1804_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___redArg(lean_object* v_inst_1809_, lean_object* v_t_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1809_, v_t_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1812_, lean_object* v_t_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Std_DTreeMap_Const_minEntry_x21___redArg(v_inst_1812_, v_t_1813_);
lean_dec(v_t_1813_);
lean_dec_ref(v_inst_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21(lean_object* v_00_u03b1_1815_, lean_object* v_cmp_1816_, lean_object* v_00_u03b2_1817_, lean_object* v_inst_1818_, lean_object* v_t_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1818_, v_t_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1821_, lean_object* v_cmp_1822_, lean_object* v_00_u03b2_1823_, lean_object* v_inst_1824_, lean_object* v_t_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Std_DTreeMap_Const_minEntry_x21(v_00_u03b1_1821_, v_cmp_1822_, v_00_u03b2_1823_, v_inst_1824_, v_t_1825_);
lean_dec(v_t_1825_);
lean_dec_ref(v_inst_1824_);
lean_dec_ref(v_cmp_1822_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___redArg(lean_object* v_t_1827_, lean_object* v_fallback_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1827_, v_fallback_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___redArg___boxed(lean_object* v_t_1830_, lean_object* v_fallback_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Std_DTreeMap_Const_minEntryD___redArg(v_t_1830_, v_fallback_1831_);
lean_dec_ref(v_fallback_1831_);
lean_dec(v_t_1830_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD(lean_object* v_00_u03b1_1833_, lean_object* v_cmp_1834_, lean_object* v_00_u03b2_1835_, lean_object* v_t_1836_, lean_object* v_fallback_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1836_, v_fallback_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___boxed(lean_object* v_00_u03b1_1839_, lean_object* v_cmp_1840_, lean_object* v_00_u03b2_1841_, lean_object* v_t_1842_, lean_object* v_fallback_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Std_DTreeMap_Const_minEntryD(v_00_u03b1_1839_, v_cmp_1840_, v_00_u03b2_1841_, v_t_1842_, v_fallback_1843_);
lean_dec_ref(v_fallback_1843_);
lean_dec(v_t_1842_);
lean_dec_ref(v_cmp_1840_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___redArg(lean_object* v_t_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Std_DTreeMap_Const_maxEntry_x3f___redArg(v_t_1847_);
lean_dec(v_t_1847_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f(lean_object* v_00_u03b1_1849_, lean_object* v_cmp_1850_, lean_object* v_00_u03b2_1851_, lean_object* v_t_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1854_, lean_object* v_cmp_1855_, lean_object* v_00_u03b2_1856_, lean_object* v_t_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Std_DTreeMap_Const_maxEntry_x3f(v_00_u03b1_1854_, v_cmp_1855_, v_00_u03b2_1856_, v_t_1857_);
lean_dec(v_t_1857_);
lean_dec_ref(v_cmp_1855_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___redArg(lean_object* v_t_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___redArg___boxed(lean_object* v_t_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Std_DTreeMap_Const_maxEntry___redArg(v_t_1861_);
lean_dec(v_t_1861_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry(lean_object* v_00_u03b1_1863_, lean_object* v_cmp_1864_, lean_object* v_00_u03b2_1865_, lean_object* v_t_1866_, lean_object* v_h_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___boxed(lean_object* v_00_u03b1_1869_, lean_object* v_cmp_1870_, lean_object* v_00_u03b2_1871_, lean_object* v_t_1872_, lean_object* v_h_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Std_DTreeMap_Const_maxEntry(v_00_u03b1_1869_, v_cmp_1870_, v_00_u03b2_1871_, v_t_1872_, v_h_1873_);
lean_dec(v_t_1872_);
lean_dec_ref(v_cmp_1870_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___redArg(lean_object* v_inst_1875_, lean_object* v_t_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1875_, v_t_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_1878_, lean_object* v_t_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Std_DTreeMap_Const_maxEntry_x21___redArg(v_inst_1878_, v_t_1879_);
lean_dec(v_t_1879_);
lean_dec_ref(v_inst_1878_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21(lean_object* v_00_u03b1_1881_, lean_object* v_cmp_1882_, lean_object* v_00_u03b2_1883_, lean_object* v_inst_1884_, lean_object* v_t_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1884_, v_t_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_1887_, lean_object* v_cmp_1888_, lean_object* v_00_u03b2_1889_, lean_object* v_inst_1890_, lean_object* v_t_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Std_DTreeMap_Const_maxEntry_x21(v_00_u03b1_1887_, v_cmp_1888_, v_00_u03b2_1889_, v_inst_1890_, v_t_1891_);
lean_dec(v_t_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v_cmp_1888_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___redArg(lean_object* v_t_1893_, lean_object* v_fallback_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1893_, v_fallback_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___redArg___boxed(lean_object* v_t_1896_, lean_object* v_fallback_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Std_DTreeMap_Const_maxEntryD___redArg(v_t_1896_, v_fallback_1897_);
lean_dec_ref(v_fallback_1897_);
lean_dec(v_t_1896_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD(lean_object* v_00_u03b1_1899_, lean_object* v_cmp_1900_, lean_object* v_00_u03b2_1901_, lean_object* v_t_1902_, lean_object* v_fallback_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1902_, v_fallback_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___boxed(lean_object* v_00_u03b1_1905_, lean_object* v_cmp_1906_, lean_object* v_00_u03b2_1907_, lean_object* v_t_1908_, lean_object* v_fallback_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Std_DTreeMap_Const_maxEntryD(v_00_u03b1_1905_, v_cmp_1906_, v_00_u03b2_1907_, v_t_1908_, v_fallback_1909_);
lean_dec_ref(v_fallback_1909_);
lean_dec(v_t_1908_);
lean_dec_ref(v_cmp_1906_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(lean_object* v_t_1911_, lean_object* v_n_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1911_, v_n_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_1914_, lean_object* v_n_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(v_t_1914_, v_n_1915_);
lean_dec(v_t_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_1917_, lean_object* v_cmp_1918_, lean_object* v_00_u03b2_1919_, lean_object* v_t_1920_, lean_object* v_n_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1920_, v_n_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1923_, lean_object* v_cmp_1924_, lean_object* v_00_u03b2_1925_, lean_object* v_t_1926_, lean_object* v_n_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Std_DTreeMap_Const_entryAtIdx_x3f(v_00_u03b1_1923_, v_cmp_1924_, v_00_u03b2_1925_, v_t_1926_, v_n_1927_);
lean_dec(v_t_1926_);
lean_dec_ref(v_cmp_1924_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___redArg(lean_object* v_t_1929_, lean_object* v_n_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_1929_, v_n_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___redArg___boxed(lean_object* v_t_1932_, lean_object* v_n_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Std_DTreeMap_Const_entryAtIdx___redArg(v_t_1932_, v_n_1933_);
lean_dec(v_t_1932_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx(lean_object* v_00_u03b1_1935_, lean_object* v_cmp_1936_, lean_object* v_00_u03b2_1937_, lean_object* v_t_1938_, lean_object* v_n_1939_, lean_object* v_h_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_1938_, v_n_1939_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_1942_, lean_object* v_cmp_1943_, lean_object* v_00_u03b2_1944_, lean_object* v_t_1945_, lean_object* v_n_1946_, lean_object* v_h_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Std_DTreeMap_Const_entryAtIdx(v_00_u03b1_1942_, v_cmp_1943_, v_00_u03b2_1944_, v_t_1945_, v_n_1946_, v_h_1947_);
lean_dec(v_t_1945_);
lean_dec_ref(v_cmp_1943_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(lean_object* v_inst_1949_, lean_object* v_t_1950_, lean_object* v_n_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1949_, v_t_1950_, v_n_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_1953_, lean_object* v_t_1954_, lean_object* v_n_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(v_inst_1953_, v_t_1954_, v_n_1955_);
lean_dec(v_t_1954_);
lean_dec_ref(v_inst_1953_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21(lean_object* v_00_u03b1_1957_, lean_object* v_cmp_1958_, lean_object* v_00_u03b2_1959_, lean_object* v_inst_1960_, lean_object* v_t_1961_, lean_object* v_n_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1960_, v_t_1961_, v_n_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_1964_, lean_object* v_cmp_1965_, lean_object* v_00_u03b2_1966_, lean_object* v_inst_1967_, lean_object* v_t_1968_, lean_object* v_n_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Std_DTreeMap_Const_entryAtIdx_x21(v_00_u03b1_1964_, v_cmp_1965_, v_00_u03b2_1966_, v_inst_1967_, v_t_1968_, v_n_1969_);
lean_dec(v_t_1968_);
lean_dec_ref(v_inst_1967_);
lean_dec_ref(v_cmp_1965_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___redArg(lean_object* v_t_1971_, lean_object* v_n_1972_, lean_object* v_fallback_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1971_, v_n_1972_, v_fallback_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_1975_, lean_object* v_n_1976_, lean_object* v_fallback_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Std_DTreeMap_Const_entryAtIdxD___redArg(v_t_1975_, v_n_1976_, v_fallback_1977_);
lean_dec_ref(v_fallback_1977_);
lean_dec(v_t_1975_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD(lean_object* v_00_u03b1_1979_, lean_object* v_cmp_1980_, lean_object* v_00_u03b2_1981_, lean_object* v_t_1982_, lean_object* v_n_1983_, lean_object* v_fallback_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1982_, v_n_1983_, v_fallback_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_1986_, lean_object* v_cmp_1987_, lean_object* v_00_u03b2_1988_, lean_object* v_t_1989_, lean_object* v_n_1990_, lean_object* v_fallback_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Std_DTreeMap_Const_entryAtIdxD(v_00_u03b1_1986_, v_cmp_1987_, v_00_u03b2_1988_, v_t_1989_, v_n_1990_, v_fallback_1991_);
lean_dec_ref(v_fallback_1991_);
lean_dec(v_t_1989_);
lean_dec_ref(v_cmp_1987_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_1993_, lean_object* v_t_1994_, lean_object* v_k_1995_){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_box(0);
v___x_1997_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1993_, v_k_1995_, v___x_1996_, v_t_1994_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x3f(lean_object* v_00_u03b1_1998_, lean_object* v_cmp_1999_, lean_object* v_00_u03b2_2000_, lean_object* v_t_2001_, lean_object* v_k_2002_){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_box(0);
v___x_2004_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1999_, v_k_2002_, v___x_2003_, v_t_2001_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_2005_, lean_object* v_t_2006_, lean_object* v_k_2007_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_box(0);
v___x_2009_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2005_, v_k_2007_, v___x_2008_, v_t_2006_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x3f(lean_object* v_00_u03b1_2010_, lean_object* v_cmp_2011_, lean_object* v_00_u03b2_2012_, lean_object* v_t_2013_, lean_object* v_k_2014_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_box(0);
v___x_2016_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2011_, v_k_2014_, v___x_2015_, v_t_2013_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_2017_, lean_object* v_t_2018_, lean_object* v_k_2019_){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_box(0);
v___x_2021_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2017_, v_k_2019_, v___x_2020_, v_t_2018_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x3f(lean_object* v_00_u03b1_2022_, lean_object* v_cmp_2023_, lean_object* v_00_u03b2_2024_, lean_object* v_t_2025_, lean_object* v_k_2026_){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_box(0);
v___x_2028_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2023_, v_k_2026_, v___x_2027_, v_t_2025_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_2029_, lean_object* v_t_2030_, lean_object* v_k_2031_){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_box(0);
v___x_2033_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2029_, v_k_2031_, v___x_2032_, v_t_2030_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x3f(lean_object* v_00_u03b1_2034_, lean_object* v_cmp_2035_, lean_object* v_00_u03b2_2036_, lean_object* v_t_2037_, lean_object* v_k_2038_){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_box(0);
v___x_2040_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2035_, v_k_2038_, v___x_2039_, v_t_2037_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___redArg(lean_object* v_cmp_2041_, lean_object* v_inst_2042_, lean_object* v_t_2043_, lean_object* v_k_2044_){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_box(0);
v___x_2046_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2041_, v_k_2044_, v___x_2045_, v_t_2043_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2048_ = l_panic___redArg(v_inst_2042_, v___x_2047_);
return v___x_2048_;
}
else
{
lean_object* v_val_2049_; 
v_val_2049_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_val_2049_);
lean_dec_ref_known(v___x_2046_, 1);
return v_val_2049_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_2050_, lean_object* v_inst_2051_, lean_object* v_t_2052_, lean_object* v_k_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Std_DTreeMap_Const_getEntryGE_x21___redArg(v_cmp_2050_, v_inst_2051_, v_t_2052_, v_k_2053_);
lean_dec_ref(v_inst_2051_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21(lean_object* v_00_u03b1_2055_, lean_object* v_cmp_2056_, lean_object* v_00_u03b2_2057_, lean_object* v_inst_2058_, lean_object* v_t_2059_, lean_object* v_k_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_box(0);
v___x_2062_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2056_, v_k_2060_, v___x_2061_, v_t_2059_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2064_ = l_panic___redArg(v_inst_2058_, v___x_2063_);
return v___x_2064_;
}
else
{
lean_object* v_val_2065_; 
v_val_2065_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_val_2065_);
lean_dec_ref_known(v___x_2062_, 1);
return v_val_2065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_2066_, lean_object* v_cmp_2067_, lean_object* v_00_u03b2_2068_, lean_object* v_inst_2069_, lean_object* v_t_2070_, lean_object* v_k_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Std_DTreeMap_Const_getEntryGE_x21(v_00_u03b1_2066_, v_cmp_2067_, v_00_u03b2_2068_, v_inst_2069_, v_t_2070_, v_k_2071_);
lean_dec_ref(v_inst_2069_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___redArg(lean_object* v_cmp_2073_, lean_object* v_inst_2074_, lean_object* v_t_2075_, lean_object* v_k_2076_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_box(0);
v___x_2078_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2073_, v_k_2076_, v___x_2077_, v_t_2075_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2080_ = l_panic___redArg(v_inst_2074_, v___x_2079_);
return v___x_2080_;
}
else
{
lean_object* v_val_2081_; 
v_val_2081_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_val_2081_);
lean_dec_ref_known(v___x_2078_, 1);
return v_val_2081_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_2082_, lean_object* v_inst_2083_, lean_object* v_t_2084_, lean_object* v_k_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Std_DTreeMap_Const_getEntryGT_x21___redArg(v_cmp_2082_, v_inst_2083_, v_t_2084_, v_k_2085_);
lean_dec_ref(v_inst_2083_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21(lean_object* v_00_u03b1_2087_, lean_object* v_cmp_2088_, lean_object* v_00_u03b2_2089_, lean_object* v_inst_2090_, lean_object* v_t_2091_, lean_object* v_k_2092_){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_box(0);
v___x_2094_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2088_, v_k_2092_, v___x_2093_, v_t_2091_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2096_ = l_panic___redArg(v_inst_2090_, v___x_2095_);
return v___x_2096_;
}
else
{
lean_object* v_val_2097_; 
v_val_2097_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_val_2097_);
lean_dec_ref_known(v___x_2094_, 1);
return v_val_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_2098_, lean_object* v_cmp_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_inst_2101_, lean_object* v_t_2102_, lean_object* v_k_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Std_DTreeMap_Const_getEntryGT_x21(v_00_u03b1_2098_, v_cmp_2099_, v_00_u03b2_2100_, v_inst_2101_, v_t_2102_, v_k_2103_);
lean_dec_ref(v_inst_2101_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___redArg(lean_object* v_cmp_2105_, lean_object* v_inst_2106_, lean_object* v_t_2107_, lean_object* v_k_2108_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_box(0);
v___x_2110_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2105_, v_k_2108_, v___x_2109_, v_t_2107_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2112_ = l_panic___redArg(v_inst_2106_, v___x_2111_);
return v___x_2112_;
}
else
{
lean_object* v_val_2113_; 
v_val_2113_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_val_2113_);
lean_dec_ref_known(v___x_2110_, 1);
return v_val_2113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_2114_, lean_object* v_inst_2115_, lean_object* v_t_2116_, lean_object* v_k_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Std_DTreeMap_Const_getEntryLE_x21___redArg(v_cmp_2114_, v_inst_2115_, v_t_2116_, v_k_2117_);
lean_dec_ref(v_inst_2115_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21(lean_object* v_00_u03b1_2119_, lean_object* v_cmp_2120_, lean_object* v_00_u03b2_2121_, lean_object* v_inst_2122_, lean_object* v_t_2123_, lean_object* v_k_2124_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_box(0);
v___x_2126_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2120_, v_k_2124_, v___x_2125_, v_t_2123_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2128_ = l_panic___redArg(v_inst_2122_, v___x_2127_);
return v___x_2128_;
}
else
{
lean_object* v_val_2129_; 
v_val_2129_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_val_2129_);
lean_dec_ref_known(v___x_2126_, 1);
return v_val_2129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2130_, lean_object* v_cmp_2131_, lean_object* v_00_u03b2_2132_, lean_object* v_inst_2133_, lean_object* v_t_2134_, lean_object* v_k_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Std_DTreeMap_Const_getEntryLE_x21(v_00_u03b1_2130_, v_cmp_2131_, v_00_u03b2_2132_, v_inst_2133_, v_t_2134_, v_k_2135_);
lean_dec_ref(v_inst_2133_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___redArg(lean_object* v_cmp_2137_, lean_object* v_inst_2138_, lean_object* v_t_2139_, lean_object* v_k_2140_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_box(0);
v___x_2142_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2137_, v_k_2140_, v___x_2141_, v_t_2139_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2144_ = l_panic___redArg(v_inst_2138_, v___x_2143_);
return v___x_2144_;
}
else
{
lean_object* v_val_2145_; 
v_val_2145_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v___x_2142_, 1);
return v_val_2145_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_2146_, lean_object* v_inst_2147_, lean_object* v_t_2148_, lean_object* v_k_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Std_DTreeMap_Const_getEntryLT_x21___redArg(v_cmp_2146_, v_inst_2147_, v_t_2148_, v_k_2149_);
lean_dec_ref(v_inst_2147_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21(lean_object* v_00_u03b1_2151_, lean_object* v_cmp_2152_, lean_object* v_00_u03b2_2153_, lean_object* v_inst_2154_, lean_object* v_t_2155_, lean_object* v_k_2156_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_box(0);
v___x_2158_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2152_, v_k_2156_, v___x_2157_, v_t_2155_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2160_ = l_panic___redArg(v_inst_2154_, v___x_2159_);
return v___x_2160_;
}
else
{
lean_object* v_val_2161_; 
v_val_2161_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_val_2161_);
lean_dec_ref_known(v___x_2158_, 1);
return v_val_2161_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2162_, lean_object* v_cmp_2163_, lean_object* v_00_u03b2_2164_, lean_object* v_inst_2165_, lean_object* v_t_2166_, lean_object* v_k_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Std_DTreeMap_Const_getEntryLT_x21(v_00_u03b1_2162_, v_cmp_2163_, v_00_u03b2_2164_, v_inst_2165_, v_t_2166_, v_k_2167_);
lean_dec_ref(v_inst_2165_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___redArg(lean_object* v_cmp_2169_, lean_object* v_t_2170_, lean_object* v_k_2171_, lean_object* v_fallback_2172_){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_box(0);
v___x_2174_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2169_, v_k_2171_, v___x_2173_, v_t_2170_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_inc_ref(v_fallback_2172_);
return v_fallback_2172_;
}
else
{
lean_object* v_val_2175_; 
v_val_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_val_2175_);
lean_dec_ref_known(v___x_2174_, 1);
return v_val_2175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2176_, lean_object* v_t_2177_, lean_object* v_k_2178_, lean_object* v_fallback_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Std_DTreeMap_Const_getEntryGED___redArg(v_cmp_2176_, v_t_2177_, v_k_2178_, v_fallback_2179_);
lean_dec_ref(v_fallback_2179_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED(lean_object* v_00_u03b1_2181_, lean_object* v_cmp_2182_, lean_object* v_00_u03b2_2183_, lean_object* v_t_2184_, lean_object* v_k_2185_, lean_object* v_fallback_2186_){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = lean_box(0);
v___x_2188_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2182_, v_k_2185_, v___x_2187_, v_t_2184_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_inc_ref(v_fallback_2186_);
return v_fallback_2186_;
}
else
{
lean_object* v_val_2189_; 
v_val_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_val_2189_);
lean_dec_ref_known(v___x_2188_, 1);
return v_val_2189_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2190_, lean_object* v_cmp_2191_, lean_object* v_00_u03b2_2192_, lean_object* v_t_2193_, lean_object* v_k_2194_, lean_object* v_fallback_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Std_DTreeMap_Const_getEntryGED(v_00_u03b1_2190_, v_cmp_2191_, v_00_u03b2_2192_, v_t_2193_, v_k_2194_, v_fallback_2195_);
lean_dec_ref(v_fallback_2195_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___redArg(lean_object* v_cmp_2197_, lean_object* v_t_2198_, lean_object* v_k_2199_, lean_object* v_fallback_2200_){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = lean_box(0);
v___x_2202_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2197_, v_k_2199_, v___x_2201_, v_t_2198_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_inc_ref(v_fallback_2200_);
return v_fallback_2200_;
}
else
{
lean_object* v_val_2203_; 
v_val_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_val_2203_);
lean_dec_ref_known(v___x_2202_, 1);
return v_val_2203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2204_, lean_object* v_t_2205_, lean_object* v_k_2206_, lean_object* v_fallback_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Std_DTreeMap_Const_getEntryGTD___redArg(v_cmp_2204_, v_t_2205_, v_k_2206_, v_fallback_2207_);
lean_dec_ref(v_fallback_2207_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD(lean_object* v_00_u03b1_2209_, lean_object* v_cmp_2210_, lean_object* v_00_u03b2_2211_, lean_object* v_t_2212_, lean_object* v_k_2213_, lean_object* v_fallback_2214_){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_box(0);
v___x_2216_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2210_, v_k_2213_, v___x_2215_, v_t_2212_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_inc_ref(v_fallback_2214_);
return v_fallback_2214_;
}
else
{
lean_object* v_val_2217_; 
v_val_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v___x_2216_, 1);
return v_val_2217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2218_, lean_object* v_cmp_2219_, lean_object* v_00_u03b2_2220_, lean_object* v_t_2221_, lean_object* v_k_2222_, lean_object* v_fallback_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Std_DTreeMap_Const_getEntryGTD(v_00_u03b1_2218_, v_cmp_2219_, v_00_u03b2_2220_, v_t_2221_, v_k_2222_, v_fallback_2223_);
lean_dec_ref(v_fallback_2223_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___redArg(lean_object* v_cmp_2225_, lean_object* v_t_2226_, lean_object* v_k_2227_, lean_object* v_fallback_2228_){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_box(0);
v___x_2230_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2225_, v_k_2227_, v___x_2229_, v_t_2226_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_inc_ref(v_fallback_2228_);
return v_fallback_2228_;
}
else
{
lean_object* v_val_2231_; 
v_val_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_val_2231_);
lean_dec_ref_known(v___x_2230_, 1);
return v_val_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2232_, lean_object* v_t_2233_, lean_object* v_k_2234_, lean_object* v_fallback_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Std_DTreeMap_Const_getEntryLED___redArg(v_cmp_2232_, v_t_2233_, v_k_2234_, v_fallback_2235_);
lean_dec_ref(v_fallback_2235_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED(lean_object* v_00_u03b1_2237_, lean_object* v_cmp_2238_, lean_object* v_00_u03b2_2239_, lean_object* v_t_2240_, lean_object* v_k_2241_, lean_object* v_fallback_2242_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_box(0);
v___x_2244_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2238_, v_k_2241_, v___x_2243_, v_t_2240_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_inc_ref(v_fallback_2242_);
return v_fallback_2242_;
}
else
{
lean_object* v_val_2245_; 
v_val_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_val_2245_);
lean_dec_ref_known(v___x_2244_, 1);
return v_val_2245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2246_, lean_object* v_cmp_2247_, lean_object* v_00_u03b2_2248_, lean_object* v_t_2249_, lean_object* v_k_2250_, lean_object* v_fallback_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Std_DTreeMap_Const_getEntryLED(v_00_u03b1_2246_, v_cmp_2247_, v_00_u03b2_2248_, v_t_2249_, v_k_2250_, v_fallback_2251_);
lean_dec_ref(v_fallback_2251_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___redArg(lean_object* v_cmp_2253_, lean_object* v_t_2254_, lean_object* v_k_2255_, lean_object* v_fallback_2256_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_box(0);
v___x_2258_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2253_, v_k_2255_, v___x_2257_, v_t_2254_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_inc_ref(v_fallback_2256_);
return v_fallback_2256_;
}
else
{
lean_object* v_val_2259_; 
v_val_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_val_2259_);
lean_dec_ref_known(v___x_2258_, 1);
return v_val_2259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2260_, lean_object* v_t_2261_, lean_object* v_k_2262_, lean_object* v_fallback_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Std_DTreeMap_Const_getEntryLTD___redArg(v_cmp_2260_, v_t_2261_, v_k_2262_, v_fallback_2263_);
lean_dec_ref(v_fallback_2263_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD(lean_object* v_00_u03b1_2265_, lean_object* v_cmp_2266_, lean_object* v_00_u03b2_2267_, lean_object* v_t_2268_, lean_object* v_k_2269_, lean_object* v_fallback_2270_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_box(0);
v___x_2272_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2266_, v_k_2269_, v___x_2271_, v_t_2268_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_inc_ref(v_fallback_2270_);
return v_fallback_2270_;
}
else
{
lean_object* v_val_2273_; 
v_val_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_val_2273_);
lean_dec_ref_known(v___x_2272_, 1);
return v_val_2273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2274_, lean_object* v_cmp_2275_, lean_object* v_00_u03b2_2276_, lean_object* v_t_2277_, lean_object* v_k_2278_, lean_object* v_fallback_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Std_DTreeMap_Const_getEntryLTD(v_00_u03b1_2274_, v_cmp_2275_, v_00_u03b2_2276_, v_t_2277_, v_k_2278_, v_fallback_2279_);
lean_dec_ref(v_fallback_2279_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter___redArg(lean_object* v_f_2281_, lean_object* v_t_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2281_, v_t_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter(lean_object* v_00_u03b1_2284_, lean_object* v_00_u03b2_2285_, lean_object* v_cmp_2286_, lean_object* v_f_2287_, lean_object* v_t_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2287_, v_t_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter___boxed(lean_object* v_00_u03b1_2290_, lean_object* v_00_u03b2_2291_, lean_object* v_cmp_2292_, lean_object* v_f_2293_, lean_object* v_t_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Std_DTreeMap_filter(v_00_u03b1_2290_, v_00_u03b2_2291_, v_cmp_2292_, v_f_2293_, v_t_2294_);
lean_dec_ref(v_cmp_2292_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM___redArg(lean_object* v_inst_2296_, lean_object* v_f_2297_, lean_object* v_init_2298_, lean_object* v_t_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2296_, v_f_2297_, v_init_2298_, v_t_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM(lean_object* v_00_u03b1_2301_, lean_object* v_00_u03b2_2302_, lean_object* v_cmp_2303_, lean_object* v_00_u03b4_2304_, lean_object* v_m_2305_, lean_object* v_inst_2306_, lean_object* v_f_2307_, lean_object* v_init_2308_, lean_object* v_t_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2306_, v_f_2307_, v_init_2308_, v_t_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM___boxed(lean_object* v_00_u03b1_2311_, lean_object* v_00_u03b2_2312_, lean_object* v_cmp_2313_, lean_object* v_00_u03b4_2314_, lean_object* v_m_2315_, lean_object* v_inst_2316_, lean_object* v_f_2317_, lean_object* v_init_2318_, lean_object* v_t_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Std_DTreeMap_foldlM(v_00_u03b1_2311_, v_00_u03b2_2312_, v_cmp_2313_, v_00_u03b4_2314_, v_m_2315_, v_inst_2316_, v_f_2317_, v_init_2318_, v_t_2319_);
lean_dec_ref(v_cmp_2313_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl___redArg(lean_object* v_f_2321_, lean_object* v_init_2322_, lean_object* v_t_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2321_, v_init_2322_, v_t_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl(lean_object* v_00_u03b1_2325_, lean_object* v_00_u03b2_2326_, lean_object* v_cmp_2327_, lean_object* v_00_u03b4_2328_, lean_object* v_f_2329_, lean_object* v_init_2330_, lean_object* v_t_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2329_, v_init_2330_, v_t_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl___boxed(lean_object* v_00_u03b1_2333_, lean_object* v_00_u03b2_2334_, lean_object* v_cmp_2335_, lean_object* v_00_u03b4_2336_, lean_object* v_f_2337_, lean_object* v_init_2338_, lean_object* v_t_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Std_DTreeMap_foldl(v_00_u03b1_2333_, v_00_u03b2_2334_, v_cmp_2335_, v_00_u03b4_2336_, v_f_2337_, v_init_2338_, v_t_2339_);
lean_dec_ref(v_cmp_2335_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM___redArg(lean_object* v_inst_2341_, lean_object* v_f_2342_, lean_object* v_init_2343_, lean_object* v_t_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2341_, v_f_2342_, v_init_2343_, v_t_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM(lean_object* v_00_u03b1_2346_, lean_object* v_00_u03b2_2347_, lean_object* v_cmp_2348_, lean_object* v_00_u03b4_2349_, lean_object* v_m_2350_, lean_object* v_inst_2351_, lean_object* v_f_2352_, lean_object* v_init_2353_, lean_object* v_t_2354_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2351_, v_f_2352_, v_init_2353_, v_t_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM___boxed(lean_object* v_00_u03b1_2356_, lean_object* v_00_u03b2_2357_, lean_object* v_cmp_2358_, lean_object* v_00_u03b4_2359_, lean_object* v_m_2360_, lean_object* v_inst_2361_, lean_object* v_f_2362_, lean_object* v_init_2363_, lean_object* v_t_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Std_DTreeMap_foldrM(v_00_u03b1_2356_, v_00_u03b2_2357_, v_cmp_2358_, v_00_u03b4_2359_, v_m_2360_, v_inst_2361_, v_f_2362_, v_init_2363_, v_t_2364_);
lean_dec_ref(v_cmp_2358_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___redArg___lam__0(lean_object* v_f_2366_, lean_object* v_x1_2367_, lean_object* v_x2_2368_, lean_object* v_x3_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_apply_3(v_f_2366_, v_x1_2367_, v_x2_2368_, v_x3_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___redArg(lean_object* v_f_2390_, lean_object* v_init_2391_, lean_object* v_t_2392_){
_start:
{
lean_object* v___f_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___f_2393_ = lean_alloc_closure((void*)(l_Std_DTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2393_, 0, v_f_2390_);
v___x_2394_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2395_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2394_, v___f_2393_, v_init_2391_, v_t_2392_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr(lean_object* v_00_u03b1_2396_, lean_object* v_00_u03b2_2397_, lean_object* v_cmp_2398_, lean_object* v_00_u03b4_2399_, lean_object* v_f_2400_, lean_object* v_init_2401_, lean_object* v_t_2402_){
_start:
{
lean_object* v___f_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___f_2403_ = lean_alloc_closure((void*)(l_Std_DTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2403_, 0, v_f_2400_);
v___x_2404_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2405_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2404_, v___f_2403_, v_init_2401_, v_t_2402_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___boxed(lean_object* v_00_u03b1_2406_, lean_object* v_00_u03b2_2407_, lean_object* v_cmp_2408_, lean_object* v_00_u03b4_2409_, lean_object* v_f_2410_, lean_object* v_init_2411_, lean_object* v_t_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Std_DTreeMap_foldr(v_00_u03b1_2406_, v_00_u03b2_2407_, v_cmp_2408_, v_00_u03b4_2409_, v_f_2410_, v_init_2411_, v_t_2412_);
lean_dec_ref(v_cmp_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition___redArg___lam__0(lean_object* v_f_2414_, lean_object* v_cmp_2415_, lean_object* v_x_2416_, lean_object* v_a_2417_, lean_object* v_b_2418_){
_start:
{
lean_object* v_fst_2419_; lean_object* v_snd_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2434_; 
v_fst_2419_ = lean_ctor_get(v_x_2416_, 0);
v_snd_2420_ = lean_ctor_get(v_x_2416_, 1);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_x_2416_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2422_ = v_x_2416_;
v_isShared_2423_ = v_isSharedCheck_2434_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_snd_2420_);
lean_inc(v_fst_2419_);
lean_dec(v_x_2416_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2434_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2424_; uint8_t v___x_2425_; 
lean_inc(v_b_2418_);
lean_inc(v_a_2417_);
v___x_2424_ = lean_apply_2(v_f_2414_, v_a_2417_, v_b_2418_);
v___x_2425_ = lean_unbox(v___x_2424_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2426_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2415_, v_a_2417_, v_b_2418_, v_snd_2420_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v___x_2426_);
v___x_2428_ = v___x_2422_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_fst_2419_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
else
{
lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2430_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2415_, v_a_2417_, v_b_2418_, v_fst_2419_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2430_);
v___x_2432_ = v___x_2422_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v_snd_2420_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition___redArg(lean_object* v_cmp_2437_, lean_object* v_f_2438_, lean_object* v_t_2439_){
_start:
{
lean_object* v___f_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___f_2440_ = lean_alloc_closure((void*)(l_Std_DTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2440_, 0, v_f_2438_);
lean_closure_set(v___f_2440_, 1, v_cmp_2437_);
v___x_2441_ = ((lean_object*)(l_Std_DTreeMap_partition___redArg___closed__0));
v___x_2442_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2440_, v___x_2441_, v_t_2439_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition(lean_object* v_00_u03b1_2443_, lean_object* v_00_u03b2_2444_, lean_object* v_cmp_2445_, lean_object* v_f_2446_, lean_object* v_t_2447_){
_start:
{
lean_object* v___f_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___f_2448_ = lean_alloc_closure((void*)(l_Std_DTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2448_, 0, v_f_2446_);
lean_closure_set(v___f_2448_, 1, v_cmp_2445_);
v___x_2449_ = ((lean_object*)(l_Std_DTreeMap_partition___redArg___closed__0));
v___x_2450_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2448_, v___x_2449_, v_t_2447_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___redArg___lam__0(lean_object* v_f_2451_, lean_object* v_x_2452_, lean_object* v_k_2453_, lean_object* v_v_2454_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_apply_2(v_f_2451_, v_k_2453_, v_v_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___redArg(lean_object* v_inst_2456_, lean_object* v_f_2457_, lean_object* v_t_2458_){
_start:
{
lean_object* v___f_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___f_2459_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2459_, 0, v_f_2457_);
v___x_2460_ = lean_box(0);
v___x_2461_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2456_, v___f_2459_, v___x_2460_, v_t_2458_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM(lean_object* v_00_u03b1_2462_, lean_object* v_00_u03b2_2463_, lean_object* v_cmp_2464_, lean_object* v_m_2465_, lean_object* v_inst_2466_, lean_object* v_f_2467_, lean_object* v_t_2468_){
_start:
{
lean_object* v___f_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___f_2469_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2469_, 0, v_f_2467_);
v___x_2470_ = lean_box(0);
v___x_2471_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2466_, v___f_2469_, v___x_2470_, v_t_2468_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___boxed(lean_object* v_00_u03b1_2472_, lean_object* v_00_u03b2_2473_, lean_object* v_cmp_2474_, lean_object* v_m_2475_, lean_object* v_inst_2476_, lean_object* v_f_2477_, lean_object* v_t_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Std_DTreeMap_forM(v_00_u03b1_2472_, v_00_u03b2_2473_, v_cmp_2474_, v_m_2475_, v_inst_2476_, v_f_2477_, v_t_2478_);
lean_dec_ref(v_cmp_2474_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___redArg___lam__0(lean_object* v_toPure_2480_, lean_object* v_____do__lift_2481_){
_start:
{
lean_object* v_a_2482_; lean_object* v___x_2483_; 
v_a_2482_ = lean_ctor_get(v_____do__lift_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref(v_____do__lift_2481_);
v___x_2483_ = lean_apply_2(v_toPure_2480_, lean_box(0), v_a_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___redArg(lean_object* v_inst_2484_, lean_object* v_f_2485_, lean_object* v_init_2486_, lean_object* v_t_2487_){
_start:
{
lean_object* v_toApplicative_2488_; lean_object* v_toBind_2489_; lean_object* v_toPure_2490_; lean_object* v___x_2491_; lean_object* v___f_2492_; lean_object* v___x_2493_; 
v_toApplicative_2488_ = lean_ctor_get(v_inst_2484_, 0);
v_toBind_2489_ = lean_ctor_get(v_inst_2484_, 1);
lean_inc(v_toBind_2489_);
v_toPure_2490_ = lean_ctor_get(v_toApplicative_2488_, 1);
lean_inc(v_toPure_2490_);
v___x_2491_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2484_, v_f_2485_, v_init_2486_, v_t_2487_);
v___f_2492_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2492_, 0, v_toPure_2490_);
v___x_2493_ = lean_apply_4(v_toBind_2489_, lean_box(0), lean_box(0), v___x_2491_, v___f_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn(lean_object* v_00_u03b1_2494_, lean_object* v_00_u03b2_2495_, lean_object* v_cmp_2496_, lean_object* v_00_u03b4_2497_, lean_object* v_m_2498_, lean_object* v_inst_2499_, lean_object* v_f_2500_, lean_object* v_init_2501_, lean_object* v_t_2502_){
_start:
{
lean_object* v_toApplicative_2503_; lean_object* v_toBind_2504_; lean_object* v_toPure_2505_; lean_object* v___x_2506_; lean_object* v___f_2507_; lean_object* v___x_2508_; 
v_toApplicative_2503_ = lean_ctor_get(v_inst_2499_, 0);
v_toBind_2504_ = lean_ctor_get(v_inst_2499_, 1);
lean_inc(v_toBind_2504_);
v_toPure_2505_ = lean_ctor_get(v_toApplicative_2503_, 1);
lean_inc(v_toPure_2505_);
v___x_2506_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2499_, v_f_2500_, v_init_2501_, v_t_2502_);
v___f_2507_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2507_, 0, v_toPure_2505_);
v___x_2508_ = lean_apply_4(v_toBind_2504_, lean_box(0), lean_box(0), v___x_2506_, v___f_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___boxed(lean_object* v_00_u03b1_2509_, lean_object* v_00_u03b2_2510_, lean_object* v_cmp_2511_, lean_object* v_00_u03b4_2512_, lean_object* v_m_2513_, lean_object* v_inst_2514_, lean_object* v_f_2515_, lean_object* v_init_2516_, lean_object* v_t_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Std_DTreeMap_forIn(v_00_u03b1_2509_, v_00_u03b2_2510_, v_cmp_2511_, v_00_u03b4_2512_, v_m_2513_, v_inst_2514_, v_f_2515_, v_init_2516_, v_t_2517_);
lean_dec_ref(v_cmp_2511_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_2519_, lean_object* v_x_2520_, lean_object* v_k_2521_, lean_object* v_v_2522_){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v_k_2521_);
lean_ctor_set(v___x_2523_, 1, v_v_2522_);
v___x_2524_ = lean_apply_1(v_f_2519_, v___x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1(lean_object* v_inst_2525_, lean_object* v_t_2526_, lean_object* v_f_2527_){
_start:
{
lean_object* v___f_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___f_2528_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2528_, 0, v_f_2527_);
v___x_2529_ = lean_box(0);
v___x_2530_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2525_, v___f_2528_, v___x_2529_, v_t_2526_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg(lean_object* v_inst_2531_){
_start:
{
lean_object* v___f_2532_; 
v___f_2532_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2532_, 0, v_inst_2531_);
return v___f_2532_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad(lean_object* v_00_u03b1_2533_, lean_object* v_00_u03b2_2534_, lean_object* v_cmp_2535_, lean_object* v_m_2536_, lean_object* v_inst_2537_){
_start:
{
lean_object* v___f_2538_; 
v___f_2538_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2538_, 0, v_inst_2537_);
return v___f_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___boxed(lean_object* v_00_u03b1_2539_, lean_object* v_00_u03b2_2540_, lean_object* v_cmp_2541_, lean_object* v_m_2542_, lean_object* v_inst_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Std_DTreeMap_instForMSigmaOfMonad(v_00_u03b1_2539_, v_00_u03b2_2540_, v_cmp_2541_, v_m_2542_, v_inst_2543_);
lean_dec_ref(v_cmp_2541_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_2545_, lean_object* v_a_2546_, lean_object* v_b_2547_, lean_object* v_acc_2548_){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v_a_2546_);
lean_ctor_set(v___x_2549_, 1, v_b_2547_);
v___x_2550_ = lean_apply_2(v_f_2545_, v___x_2549_, v_acc_2548_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_2551_, lean_object* v_00_u03b2_2552_, lean_object* v_m_2553_, lean_object* v_init_2554_, lean_object* v_f_2555_){
_start:
{
lean_object* v_toApplicative_2556_; lean_object* v_toBind_2557_; lean_object* v_toPure_2558_; lean_object* v___f_2559_; lean_object* v___x_2560_; lean_object* v___f_2561_; lean_object* v___x_2562_; 
v_toApplicative_2556_ = lean_ctor_get(v_inst_2551_, 0);
v_toBind_2557_ = lean_ctor_get(v_inst_2551_, 1);
lean_inc(v_toBind_2557_);
v_toPure_2558_ = lean_ctor_get(v_toApplicative_2556_, 1);
lean_inc(v_toPure_2558_);
v___f_2559_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2559_, 0, v_f_2555_);
v___x_2560_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2551_, v___f_2559_, v_init_2554_, v_m_2553_);
v___f_2561_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2561_, 0, v_toPure_2558_);
v___x_2562_ = lean_apply_4(v_toBind_2557_, lean_box(0), lean_box(0), v___x_2560_, v___f_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg(lean_object* v_inst_2563_){
_start:
{
lean_object* v___f_2564_; 
v___f_2564_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2564_, 0, v_inst_2563_);
return v___f_2564_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad(lean_object* v_00_u03b1_2565_, lean_object* v_00_u03b2_2566_, lean_object* v_cmp_2567_, lean_object* v_m_2568_, lean_object* v_inst_2569_){
_start:
{
lean_object* v___f_2570_; 
v___f_2570_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2570_, 0, v_inst_2569_);
return v___f_2570_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___boxed(lean_object* v_00_u03b1_2571_, lean_object* v_00_u03b2_2572_, lean_object* v_cmp_2573_, lean_object* v_m_2574_, lean_object* v_inst_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Std_DTreeMap_instForInSigmaOfMonad(v_00_u03b1_2571_, v_00_u03b2_2572_, v_cmp_2573_, v_m_2574_, v_inst_2575_);
lean_dec_ref(v_cmp_2573_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2577_, lean_object* v_x_2578_, lean_object* v_k_2579_, lean_object* v_v_2580_){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v_k_2579_);
lean_ctor_set(v___x_2581_, 1, v_v_2580_);
v___x_2582_ = lean_apply_1(v_f_2577_, v___x_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___redArg(lean_object* v_inst_2583_, lean_object* v_f_2584_, lean_object* v_t_2585_){
_start:
{
lean_object* v___f_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___f_2586_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2586_, 0, v_f_2584_);
v___x_2587_ = lean_box(0);
v___x_2588_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2583_, v___f_2586_, v___x_2587_, v_t_2585_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried(lean_object* v_00_u03b1_2589_, lean_object* v_cmp_2590_, lean_object* v_m_2591_, lean_object* v_inst_2592_, lean_object* v_00_u03b2_2593_, lean_object* v_f_2594_, lean_object* v_t_2595_){
_start:
{
lean_object* v___f_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___f_2596_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2596_, 0, v_f_2594_);
v___x_2597_ = lean_box(0);
v___x_2598_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2592_, v___f_2596_, v___x_2597_, v_t_2595_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2599_, lean_object* v_cmp_2600_, lean_object* v_m_2601_, lean_object* v_inst_2602_, lean_object* v_00_u03b2_2603_, lean_object* v_f_2604_, lean_object* v_t_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Std_DTreeMap_Const_forMUncurried(v_00_u03b1_2599_, v_cmp_2600_, v_m_2601_, v_inst_2602_, v_00_u03b2_2603_, v_f_2604_, v_t_2605_);
lean_dec_ref(v_cmp_2600_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2607_, lean_object* v_a_2608_, lean_object* v_b_2609_, lean_object* v_acc_2610_){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2611_, 0, v_a_2608_);
lean_ctor_set(v___x_2611_, 1, v_b_2609_);
v___x_2612_ = lean_apply_2(v_f_2607_, v___x_2611_, v_acc_2610_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___redArg(lean_object* v_inst_2613_, lean_object* v_f_2614_, lean_object* v_init_2615_, lean_object* v_t_2616_){
_start:
{
lean_object* v_toApplicative_2617_; lean_object* v_toBind_2618_; lean_object* v_toPure_2619_; lean_object* v___f_2620_; lean_object* v___x_2621_; lean_object* v___f_2622_; lean_object* v___x_2623_; 
v_toApplicative_2617_ = lean_ctor_get(v_inst_2613_, 0);
v_toBind_2618_ = lean_ctor_get(v_inst_2613_, 1);
lean_inc(v_toBind_2618_);
v_toPure_2619_ = lean_ctor_get(v_toApplicative_2617_, 1);
lean_inc(v_toPure_2619_);
v___f_2620_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2620_, 0, v_f_2614_);
v___x_2621_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2613_, v___f_2620_, v_init_2615_, v_t_2616_);
v___f_2622_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2622_, 0, v_toPure_2619_);
v___x_2623_ = lean_apply_4(v_toBind_2618_, lean_box(0), lean_box(0), v___x_2621_, v___f_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried(lean_object* v_00_u03b1_2624_, lean_object* v_cmp_2625_, lean_object* v_00_u03b4_2626_, lean_object* v_m_2627_, lean_object* v_inst_2628_, lean_object* v_00_u03b2_2629_, lean_object* v_f_2630_, lean_object* v_init_2631_, lean_object* v_t_2632_){
_start:
{
lean_object* v_toApplicative_2633_; lean_object* v_toBind_2634_; lean_object* v_toPure_2635_; lean_object* v___f_2636_; lean_object* v___x_2637_; lean_object* v___f_2638_; lean_object* v___x_2639_; 
v_toApplicative_2633_ = lean_ctor_get(v_inst_2628_, 0);
v_toBind_2634_ = lean_ctor_get(v_inst_2628_, 1);
lean_inc(v_toBind_2634_);
v_toPure_2635_ = lean_ctor_get(v_toApplicative_2633_, 1);
lean_inc(v_toPure_2635_);
v___f_2636_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2636_, 0, v_f_2630_);
v___x_2637_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2628_, v___f_2636_, v_init_2631_, v_t_2632_);
v___f_2638_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2638_, 0, v_toPure_2635_);
v___x_2639_ = lean_apply_4(v_toBind_2634_, lean_box(0), lean_box(0), v___x_2637_, v___f_2638_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_cmp_2641_, lean_object* v_00_u03b4_2642_, lean_object* v_m_2643_, lean_object* v_inst_2644_, lean_object* v_00_u03b2_2645_, lean_object* v_f_2646_, lean_object* v_init_2647_, lean_object* v_t_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Std_DTreeMap_Const_forInUncurried(v_00_u03b1_2640_, v_cmp_2641_, v_00_u03b4_2642_, v_m_2643_, v_inst_2644_, v_00_u03b2_2645_, v_f_2646_, v_init_2647_, v_t_2648_);
lean_dec_ref(v_cmp_2641_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___lam__0(lean_object* v_p_2650_, lean_object* v___x_2651_, lean_object* v___x_2652_, lean_object* v_a_2653_, lean_object* v_b_2654_, lean_object* v_acc_2655_){
_start:
{
lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2656_ = lean_apply_2(v_p_2650_, v_a_2653_, v_b_2654_);
v___x_2657_ = lean_unbox(v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2651_);
return v___x_2658_;
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_dec_ref(v___x_2651_);
v___x_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2656_);
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
lean_ctor_set(v___x_2660_, 1, v___x_2652_);
v___x_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2660_);
return v___x_2661_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2662_, lean_object* v___x_2663_, lean_object* v___x_2664_, lean_object* v_a_2665_, lean_object* v_b_2666_, lean_object* v_acc_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Std_DTreeMap_any___redArg___lam__0(v_p_2662_, v___x_2663_, v___x_2664_, v_a_2665_, v_b_2666_, v_acc_2667_);
lean_dec_ref(v_acc_2667_);
return v_res_2668_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_any___redArg(lean_object* v_t_2672_, lean_object* v_p_2673_){
_start:
{
lean_object* v___y_2675_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___f_2683_; lean_object* v___x_2684_; lean_object* v_a_2685_; 
v___x_2680_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2681_ = lean_box(0);
v___x_2682_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2683_ = lean_alloc_closure((void*)(l_Std_DTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2683_, 0, v_p_2673_);
lean_closure_set(v___f_2683_, 1, v___x_2682_);
lean_closure_set(v___f_2683_, 2, v___x_2681_);
v___x_2684_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2680_, v___f_2683_, v___x_2682_, v_t_2672_);
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___y_2675_ = v_a_2685_;
goto v___jp_2674_;
v___jp_2674_:
{
lean_object* v_fst_2676_; 
v_fst_2676_ = lean_ctor_get(v___y_2675_, 0);
lean_inc(v_fst_2676_);
lean_dec_ref(v___y_2675_);
if (lean_obj_tag(v_fst_2676_) == 0)
{
uint8_t v___x_2677_; 
v___x_2677_ = 0;
return v___x_2677_;
}
else
{
lean_object* v_val_2678_; uint8_t v___x_2679_; 
v_val_2678_ = lean_ctor_get(v_fst_2676_, 0);
lean_inc(v_val_2678_);
lean_dec_ref_known(v_fst_2676_, 1);
v___x_2679_ = lean_unbox(v_val_2678_);
lean_dec(v_val_2678_);
return v___x_2679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___boxed(lean_object* v_t_2686_, lean_object* v_p_2687_){
_start:
{
uint8_t v_res_2688_; lean_object* v_r_2689_; 
v_res_2688_ = l_Std_DTreeMap_any___redArg(v_t_2686_, v_p_2687_);
v_r_2689_ = lean_box(v_res_2688_);
return v_r_2689_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_any(lean_object* v_00_u03b1_2690_, lean_object* v_00_u03b2_2691_, lean_object* v_cmp_2692_, lean_object* v_t_2693_, lean_object* v_p_2694_){
_start:
{
lean_object* v___y_2696_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___f_2704_; lean_object* v___x_2705_; lean_object* v_a_2706_; 
v___x_2701_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2702_ = lean_box(0);
v___x_2703_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2704_ = lean_alloc_closure((void*)(l_Std_DTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2704_, 0, v_p_2694_);
lean_closure_set(v___f_2704_, 1, v___x_2703_);
lean_closure_set(v___f_2704_, 2, v___x_2702_);
v___x_2705_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2701_, v___f_2704_, v___x_2703_, v_t_2693_);
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec(v___x_2705_);
v___y_2696_ = v_a_2706_;
goto v___jp_2695_;
v___jp_2695_:
{
lean_object* v_fst_2697_; 
v_fst_2697_ = lean_ctor_get(v___y_2696_, 0);
lean_inc(v_fst_2697_);
lean_dec_ref(v___y_2696_);
if (lean_obj_tag(v_fst_2697_) == 0)
{
uint8_t v___x_2698_; 
v___x_2698_ = 0;
return v___x_2698_;
}
else
{
lean_object* v_val_2699_; uint8_t v___x_2700_; 
v_val_2699_ = lean_ctor_get(v_fst_2697_, 0);
lean_inc(v_val_2699_);
lean_dec_ref_known(v_fst_2697_, 1);
v___x_2700_ = lean_unbox(v_val_2699_);
lean_dec(v_val_2699_);
return v___x_2700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___boxed(lean_object* v_00_u03b1_2707_, lean_object* v_00_u03b2_2708_, lean_object* v_cmp_2709_, lean_object* v_t_2710_, lean_object* v_p_2711_){
_start:
{
uint8_t v_res_2712_; lean_object* v_r_2713_; 
v_res_2712_ = l_Std_DTreeMap_any(v_00_u03b1_2707_, v_00_u03b2_2708_, v_cmp_2709_, v_t_2710_, v_p_2711_);
lean_dec_ref(v_cmp_2709_);
v_r_2713_ = lean_box(v_res_2712_);
return v_r_2713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___lam__0(lean_object* v_p_2714_, lean_object* v___x_2715_, lean_object* v___x_2716_, lean_object* v_a_2717_, lean_object* v_b_2718_, lean_object* v_acc_2719_){
_start:
{
lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2720_ = lean_apply_2(v_p_2714_, v_a_2717_, v_b_2718_);
v___x_2721_ = lean_unbox(v___x_2720_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
lean_dec_ref(v___x_2716_);
v___x_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v___x_2715_);
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
}
else
{
lean_object* v___x_2725_; 
v___x_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2716_);
return v___x_2725_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_2726_, lean_object* v___x_2727_, lean_object* v___x_2728_, lean_object* v_a_2729_, lean_object* v_b_2730_, lean_object* v_acc_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Std_DTreeMap_all___redArg___lam__0(v_p_2726_, v___x_2727_, v___x_2728_, v_a_2729_, v_b_2730_, v_acc_2731_);
lean_dec_ref(v_acc_2731_);
return v_res_2732_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_all___redArg(lean_object* v_t_2733_, lean_object* v_p_2734_){
_start:
{
lean_object* v___y_2736_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___f_2744_; lean_object* v___x_2745_; lean_object* v_a_2746_; 
v___x_2741_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2742_ = lean_box(0);
v___x_2743_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2744_ = lean_alloc_closure((void*)(l_Std_DTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2744_, 0, v_p_2734_);
lean_closure_set(v___f_2744_, 1, v___x_2742_);
lean_closure_set(v___f_2744_, 2, v___x_2743_);
v___x_2745_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2741_, v___f_2744_, v___x_2743_, v_t_2733_);
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___y_2736_ = v_a_2746_;
goto v___jp_2735_;
v___jp_2735_:
{
lean_object* v_fst_2737_; 
v_fst_2737_ = lean_ctor_get(v___y_2736_, 0);
lean_inc(v_fst_2737_);
lean_dec_ref(v___y_2736_);
if (lean_obj_tag(v_fst_2737_) == 0)
{
uint8_t v___x_2738_; 
v___x_2738_ = 1;
return v___x_2738_;
}
else
{
lean_object* v_val_2739_; uint8_t v___x_2740_; 
v_val_2739_ = lean_ctor_get(v_fst_2737_, 0);
lean_inc(v_val_2739_);
lean_dec_ref_known(v_fst_2737_, 1);
v___x_2740_ = lean_unbox(v_val_2739_);
lean_dec(v_val_2739_);
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___boxed(lean_object* v_t_2747_, lean_object* v_p_2748_){
_start:
{
uint8_t v_res_2749_; lean_object* v_r_2750_; 
v_res_2749_ = l_Std_DTreeMap_all___redArg(v_t_2747_, v_p_2748_);
v_r_2750_ = lean_box(v_res_2749_);
return v_r_2750_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_all(lean_object* v_00_u03b1_2751_, lean_object* v_00_u03b2_2752_, lean_object* v_cmp_2753_, lean_object* v_t_2754_, lean_object* v_p_2755_){
_start:
{
lean_object* v___y_2757_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___f_2765_; lean_object* v___x_2766_; lean_object* v_a_2767_; 
v___x_2762_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2763_ = lean_box(0);
v___x_2764_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2765_ = lean_alloc_closure((void*)(l_Std_DTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2765_, 0, v_p_2755_);
lean_closure_set(v___f_2765_, 1, v___x_2763_);
lean_closure_set(v___f_2765_, 2, v___x_2764_);
v___x_2766_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2762_, v___f_2765_, v___x_2764_, v_t_2754_);
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec(v___x_2766_);
v___y_2757_ = v_a_2767_;
goto v___jp_2756_;
v___jp_2756_:
{
lean_object* v_fst_2758_; 
v_fst_2758_ = lean_ctor_get(v___y_2757_, 0);
lean_inc(v_fst_2758_);
lean_dec_ref(v___y_2757_);
if (lean_obj_tag(v_fst_2758_) == 0)
{
uint8_t v___x_2759_; 
v___x_2759_ = 1;
return v___x_2759_;
}
else
{
lean_object* v_val_2760_; uint8_t v___x_2761_; 
v_val_2760_ = lean_ctor_get(v_fst_2758_, 0);
lean_inc(v_val_2760_);
lean_dec_ref_known(v_fst_2758_, 1);
v___x_2761_ = lean_unbox(v_val_2760_);
lean_dec(v_val_2760_);
return v___x_2761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___boxed(lean_object* v_00_u03b1_2768_, lean_object* v_00_u03b2_2769_, lean_object* v_cmp_2770_, lean_object* v_t_2771_, lean_object* v_p_2772_){
_start:
{
uint8_t v_res_2773_; lean_object* v_r_2774_; 
v_res_2773_ = l_Std_DTreeMap_all(v_00_u03b1_2768_, v_00_u03b2_2769_, v_cmp_2770_, v_t_2771_, v_p_2772_);
lean_dec_ref(v_cmp_2770_);
v_r_2774_ = lean_box(v_res_2773_);
return v_r_2774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg___lam__0(lean_object* v_x1_2775_, lean_object* v_x2_2776_, lean_object* v_x3_2777_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2778_, 0, v_x1_2775_);
lean_ctor_set(v___x_2778_, 1, v_x3_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_2779_, lean_object* v_x2_2780_, lean_object* v_x3_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Std_DTreeMap_keys___redArg___lam__0(v_x1_2779_, v_x2_2780_, v_x3_2781_);
lean_dec(v_x2_2780_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg(lean_object* v_t_2784_){
_start:
{
lean_object* v___f_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___f_2785_ = ((lean_object*)(l_Std_DTreeMap_keys___redArg___closed__0));
v___x_2786_ = lean_box(0);
v___x_2787_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2788_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2787_, v___f_2785_, v___x_2786_, v_t_2784_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys(lean_object* v_00_u03b1_2789_, lean_object* v_00_u03b2_2790_, lean_object* v_cmp_2791_, lean_object* v_t_2792_){
_start:
{
lean_object* v___f_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___f_2793_ = ((lean_object*)(l_Std_DTreeMap_keys___redArg___closed__0));
v___x_2794_ = lean_box(0);
v___x_2795_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2796_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2795_, v___f_2793_, v___x_2794_, v_t_2792_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___boxed(lean_object* v_00_u03b1_2797_, lean_object* v_00_u03b2_2798_, lean_object* v_cmp_2799_, lean_object* v_t_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Std_DTreeMap_keys(v_00_u03b1_2797_, v_00_u03b2_2798_, v_cmp_2799_, v_t_2800_);
lean_dec_ref(v_cmp_2799_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg___lam__0(lean_object* v_l_2802_, lean_object* v_k_2803_, lean_object* v_x_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_array_push(v_l_2802_, v_k_2803_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_2806_, lean_object* v_k_2807_, lean_object* v_x_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Std_DTreeMap_keysArray___redArg___lam__0(v_l_2806_, v_k_2807_, v_x_2808_);
lean_dec(v_x_2808_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg(lean_object* v_t_2811_){
_start:
{
lean_object* v___f_2812_; lean_object* v___y_2814_; 
v___f_2812_ = ((lean_object*)(l_Std_DTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2811_) == 0)
{
lean_object* v_size_2817_; 
v_size_2817_ = lean_ctor_get(v_t_2811_, 0);
lean_inc(v_size_2817_);
v___y_2814_ = v_size_2817_;
goto v___jp_2813_;
}
else
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_unsigned_to_nat(0u);
v___y_2814_ = v___x_2818_;
goto v___jp_2813_;
}
v___jp_2813_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = lean_mk_empty_array_with_capacity(v___y_2814_);
lean_dec(v___y_2814_);
v___x_2816_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2812_, v___x_2815_, v_t_2811_);
return v___x_2816_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray(lean_object* v_00_u03b1_2819_, lean_object* v_00_u03b2_2820_, lean_object* v_cmp_2821_, lean_object* v_t_2822_){
_start:
{
lean_object* v___f_2823_; lean_object* v___y_2825_; 
v___f_2823_ = ((lean_object*)(l_Std_DTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2822_) == 0)
{
lean_object* v_size_2828_; 
v_size_2828_ = lean_ctor_get(v_t_2822_, 0);
lean_inc(v_size_2828_);
v___y_2825_ = v_size_2828_;
goto v___jp_2824_;
}
else
{
lean_object* v___x_2829_; 
v___x_2829_ = lean_unsigned_to_nat(0u);
v___y_2825_ = v___x_2829_;
goto v___jp_2824_;
}
v___jp_2824_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_mk_empty_array_with_capacity(v___y_2825_);
lean_dec(v___y_2825_);
v___x_2827_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2823_, v___x_2826_, v_t_2822_);
return v___x_2827_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___boxed(lean_object* v_00_u03b1_2830_, lean_object* v_00_u03b2_2831_, lean_object* v_cmp_2832_, lean_object* v_t_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Std_DTreeMap_keysArray(v_00_u03b1_2830_, v_00_u03b2_2831_, v_cmp_2832_, v_t_2833_);
lean_dec_ref(v_cmp_2832_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg___lam__0(lean_object* v_x1_2835_, lean_object* v_x2_2836_, lean_object* v_x3_2837_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2838_, 0, v_x2_2836_);
lean_ctor_set(v___x_2838_, 1, v_x3_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_2839_, lean_object* v_x2_2840_, lean_object* v_x3_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_Std_DTreeMap_values___redArg___lam__0(v_x1_2839_, v_x2_2840_, v_x3_2841_);
lean_dec(v_x1_2839_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg(lean_object* v_t_2844_){
_start:
{
lean_object* v___f_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___f_2845_ = ((lean_object*)(l_Std_DTreeMap_values___redArg___closed__0));
v___x_2846_ = lean_box(0);
v___x_2847_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2848_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2847_, v___f_2845_, v___x_2846_, v_t_2844_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values(lean_object* v_00_u03b1_2849_, lean_object* v_cmp_2850_, lean_object* v_00_u03b2_2851_, lean_object* v_t_2852_){
_start:
{
lean_object* v___f_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___f_2853_ = ((lean_object*)(l_Std_DTreeMap_values___redArg___closed__0));
v___x_2854_ = lean_box(0);
v___x_2855_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2856_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2855_, v___f_2853_, v___x_2854_, v_t_2852_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___boxed(lean_object* v_00_u03b1_2857_, lean_object* v_cmp_2858_, lean_object* v_00_u03b2_2859_, lean_object* v_t_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Std_DTreeMap_values(v_00_u03b1_2857_, v_cmp_2858_, v_00_u03b2_2859_, v_t_2860_);
lean_dec_ref(v_cmp_2858_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_2862_, lean_object* v_x_2863_, lean_object* v_v_2864_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = lean_array_push(v_l_2862_, v_v_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2866_, lean_object* v_x_2867_, lean_object* v_v_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Std_DTreeMap_valuesArray___redArg___lam__0(v_l_2866_, v_x_2867_, v_v_2868_);
lean_dec(v_x_2867_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg(lean_object* v_t_2871_){
_start:
{
lean_object* v___f_2872_; lean_object* v___y_2874_; 
v___f_2872_ = ((lean_object*)(l_Std_DTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2871_) == 0)
{
lean_object* v_size_2877_; 
v_size_2877_ = lean_ctor_get(v_t_2871_, 0);
lean_inc(v_size_2877_);
v___y_2874_ = v_size_2877_;
goto v___jp_2873_;
}
else
{
lean_object* v___x_2878_; 
v___x_2878_ = lean_unsigned_to_nat(0u);
v___y_2874_ = v___x_2878_;
goto v___jp_2873_;
}
v___jp_2873_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = lean_mk_empty_array_with_capacity(v___y_2874_);
lean_dec(v___y_2874_);
v___x_2876_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2872_, v___x_2875_, v_t_2871_);
return v___x_2876_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray(lean_object* v_00_u03b1_2879_, lean_object* v_cmp_2880_, lean_object* v_00_u03b2_2881_, lean_object* v_t_2882_){
_start:
{
lean_object* v___f_2883_; lean_object* v___y_2885_; 
v___f_2883_ = ((lean_object*)(l_Std_DTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2882_) == 0)
{
lean_object* v_size_2888_; 
v_size_2888_ = lean_ctor_get(v_t_2882_, 0);
lean_inc(v_size_2888_);
v___y_2885_ = v_size_2888_;
goto v___jp_2884_;
}
else
{
lean_object* v___x_2889_; 
v___x_2889_ = lean_unsigned_to_nat(0u);
v___y_2885_ = v___x_2889_;
goto v___jp_2884_;
}
v___jp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_mk_empty_array_with_capacity(v___y_2885_);
lean_dec(v___y_2885_);
v___x_2887_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2883_, v___x_2886_, v_t_2882_);
return v___x_2887_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_2890_, lean_object* v_cmp_2891_, lean_object* v_00_u03b2_2892_, lean_object* v_t_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Std_DTreeMap_valuesArray(v_00_u03b1_2890_, v_cmp_2891_, v_00_u03b2_2892_, v_t_2893_);
lean_dec_ref(v_cmp_2891_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___redArg___lam__0(lean_object* v_x1_2895_, lean_object* v_x2_2896_, lean_object* v_x3_2897_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v_x1_2895_);
lean_ctor_set(v___x_2898_, 1, v_x2_2896_);
v___x_2899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
lean_ctor_set(v___x_2899_, 1, v_x3_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___redArg(lean_object* v_t_2901_){
_start:
{
lean_object* v___f_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___f_2902_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_2903_ = lean_box(0);
v___x_2904_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2905_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2904_, v___f_2902_, v___x_2903_, v_t_2901_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList(lean_object* v_00_u03b1_2906_, lean_object* v_00_u03b2_2907_, lean_object* v_cmp_2908_, lean_object* v_t_2909_){
_start:
{
lean_object* v___f_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___f_2910_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_2911_ = lean_box(0);
v___x_2912_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2913_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2912_, v___f_2910_, v___x_2911_, v_t_2909_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___boxed(lean_object* v_00_u03b1_2914_, lean_object* v_00_u03b2_2915_, lean_object* v_cmp_2916_, lean_object* v_t_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Std_DTreeMap_toList(v_00_u03b1_2914_, v_00_u03b2_2915_, v_cmp_2916_, v_t_2917_);
lean_dec_ref(v_cmp_2916_);
return v_res_2918_;
}
}
static lean_object* _init_l_Std_DTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_2920_, lean_object* v_a_2921_, lean_object* v_x_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_fst_2924_; lean_object* v_snd_2925_; lean_object* v_r_2926_; lean_object* v___x_2927_; 
v_fst_2924_ = lean_ctor_get(v_a_2921_, 0);
lean_inc(v_fst_2924_);
v_snd_2925_ = lean_ctor_get(v_a_2921_, 1);
lean_inc(v_snd_2925_);
lean_dec_ref(v_a_2921_);
v_r_2926_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2920_, v_fst_2924_, v_snd_2925_, v___y_2923_);
v___x_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2927_, 0, v_r_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg(lean_object* v_l_2928_, lean_object* v_cmp_2929_){
_start:
{
lean_object* v___f_2930_; lean_object* v___x_2931_; lean_object* v_r_2932_; lean_object* v___x_2933_; 
v___f_2930_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2930_, 0, v_cmp_2929_);
v___x_2931_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2932_ = lean_box(1);
v___x_2933_ = l_List_forIn_x27_loop___redArg(v___x_2931_, v___f_2930_, v_l_2928_, v_r_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg___boxed(lean_object* v_l_2934_, lean_object* v_cmp_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Std_DTreeMap_ofList___redArg(v_l_2934_, v_cmp_2935_);
lean_dec(v_l_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList(lean_object* v_00_u03b1_2937_, lean_object* v_00_u03b2_2938_, lean_object* v_l_2939_, lean_object* v_cmp_2940_){
_start:
{
lean_object* v___f_2941_; lean_object* v___x_2942_; lean_object* v_r_2943_; lean_object* v___x_2944_; 
v___f_2941_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2941_, 0, v_cmp_2940_);
v___x_2942_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2943_ = lean_box(1);
v___x_2944_ = l_List_forIn_x27_loop___redArg(v___x_2942_, v___f_2941_, v_l_2939_, v_r_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___boxed(lean_object* v_00_u03b1_2945_, lean_object* v_00_u03b2_2946_, lean_object* v_l_2947_, lean_object* v_cmp_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Std_DTreeMap_ofList(v_00_u03b1_2945_, v_00_u03b2_2946_, v_l_2947_, v_cmp_2948_);
lean_dec(v_l_2947_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___redArg___lam__0(lean_object* v_l_2950_, lean_object* v_k_2951_, lean_object* v_v_2952_){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v_k_2951_);
lean_ctor_set(v___x_2953_, 1, v_v_2952_);
v___x_2954_ = lean_array_push(v_l_2950_, v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___redArg(lean_object* v_t_2956_){
_start:
{
lean_object* v___f_2957_; lean_object* v___y_2959_; 
v___f_2957_ = ((lean_object*)(l_Std_DTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2956_) == 0)
{
lean_object* v_size_2962_; 
v_size_2962_ = lean_ctor_get(v_t_2956_, 0);
lean_inc(v_size_2962_);
v___y_2959_ = v_size_2962_;
goto v___jp_2958_;
}
else
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_unsigned_to_nat(0u);
v___y_2959_ = v___x_2963_;
goto v___jp_2958_;
}
v___jp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = lean_mk_empty_array_with_capacity(v___y_2959_);
lean_dec(v___y_2959_);
v___x_2961_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2957_, v___x_2960_, v_t_2956_);
return v___x_2961_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray(lean_object* v_00_u03b1_2964_, lean_object* v_00_u03b2_2965_, lean_object* v_cmp_2966_, lean_object* v_t_2967_){
_start:
{
lean_object* v___f_2968_; lean_object* v___y_2970_; 
v___f_2968_ = ((lean_object*)(l_Std_DTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2967_) == 0)
{
lean_object* v_size_2973_; 
v_size_2973_ = lean_ctor_get(v_t_2967_, 0);
lean_inc(v_size_2973_);
v___y_2970_ = v_size_2973_;
goto v___jp_2969_;
}
else
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_unsigned_to_nat(0u);
v___y_2970_ = v___x_2974_;
goto v___jp_2969_;
}
v___jp_2969_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_mk_empty_array_with_capacity(v___y_2970_);
lean_dec(v___y_2970_);
v___x_2972_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2968_, v___x_2971_, v_t_2967_);
return v___x_2972_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___boxed(lean_object* v_00_u03b1_2975_, lean_object* v_00_u03b2_2976_, lean_object* v_cmp_2977_, lean_object* v_t_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Std_DTreeMap_toArray(v_00_u03b1_2975_, v_00_u03b2_2976_, v_cmp_2977_, v_t_2978_);
lean_dec_ref(v_cmp_2977_);
return v_res_2979_;
}
}
static lean_object* _init_l_Std_DTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray___redArg(lean_object* v_a_2981_, lean_object* v_cmp_2982_){
_start:
{
lean_object* v___f_2983_; lean_object* v___x_2984_; lean_object* v_r_2985_; size_t v_sz_2986_; size_t v___x_2987_; lean_object* v___x_2988_; 
v___f_2983_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2983_, 0, v_cmp_2982_);
v___x_2984_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2985_ = lean_box(1);
v_sz_2986_ = lean_array_size(v_a_2981_);
v___x_2987_ = ((size_t)0ULL);
v___x_2988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2984_, v_a_2981_, v___f_2983_, v_sz_2986_, v___x_2987_, v_r_2985_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray(lean_object* v_00_u03b1_2989_, lean_object* v_00_u03b2_2990_, lean_object* v_a_2991_, lean_object* v_cmp_2992_){
_start:
{
lean_object* v___f_2993_; lean_object* v___x_2994_; lean_object* v_r_2995_; size_t v_sz_2996_; size_t v___x_2997_; lean_object* v___x_2998_; 
v___f_2993_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2993_, 0, v_cmp_2992_);
v___x_2994_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2995_ = lean_box(1);
v_sz_2996_ = lean_array_size(v_a_2991_);
v___x_2997_ = ((size_t)0ULL);
v___x_2998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2994_, v_a_2991_, v___f_2993_, v_sz_2996_, v___x_2997_, v_r_2995_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_modify___redArg(lean_object* v_cmp_2999_, lean_object* v_t_3000_, lean_object* v_a_3001_, lean_object* v_f_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2999_, v_a_3001_, v_f_3002_, v_t_3000_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_modify(lean_object* v_00_u03b1_3004_, lean_object* v_00_u03b2_3005_, lean_object* v_cmp_3006_, lean_object* v_inst_3007_, lean_object* v_t_3008_, lean_object* v_a_3009_, lean_object* v_f_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3006_, v_a_3009_, v_f_3010_, v_t_3008_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_alter___redArg(lean_object* v_cmp_3012_, lean_object* v_t_3013_, lean_object* v_a_3014_, lean_object* v_f_3015_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3012_, v_a_3014_, v_f_3015_, v_t_3013_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_alter(lean_object* v_00_u03b1_3017_, lean_object* v_00_u03b2_3018_, lean_object* v_cmp_3019_, lean_object* v_inst_3020_, lean_object* v_t_3021_, lean_object* v_a_3022_, lean_object* v_f_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3019_, v_a_3022_, v_f_3023_, v_t_3021_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_3025_, lean_object* v_mergeFn_3026_, lean_object* v_a_3027_, lean_object* v_x_3028_){
_start:
{
if (lean_obj_tag(v_x_3028_) == 0)
{
lean_object* v___x_3029_; 
lean_dec(v_a_3027_);
lean_dec(v_mergeFn_3026_);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v_b_u2082_3025_);
return v___x_3029_;
}
else
{
lean_object* v_val_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3038_; 
v_val_3030_ = lean_ctor_get(v_x_3028_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_x_3028_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3032_ = v_x_3028_;
v_isShared_3033_ = v_isSharedCheck_3038_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_val_3030_);
lean_dec(v_x_3028_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3038_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3034_; lean_object* v___x_3036_; 
v___x_3034_ = lean_apply_3(v_mergeFn_3026_, v_a_3027_, v_val_3030_, v_b_u2082_3025_);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v___x_3034_);
v___x_3036_ = v___x_3032_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3039_, lean_object* v_cmp_3040_, lean_object* v_t_3041_, lean_object* v_a_3042_, lean_object* v_b_u2082_3043_){
_start:
{
lean_object* v___f_3044_; lean_object* v___x_3045_; 
lean_inc(v_a_3042_);
v___f_3044_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3044_, 0, v_b_u2082_3043_);
lean_closure_set(v___f_3044_, 1, v_mergeFn_3039_);
lean_closure_set(v___f_3044_, 2, v_a_3042_);
v___x_3045_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3040_, v_a_3042_, v___f_3044_, v_t_3041_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg(lean_object* v_cmp_3046_, lean_object* v_mergeFn_3047_, lean_object* v_t_u2081_3048_, lean_object* v_t_u2082_3049_){
_start:
{
lean_object* v___f_3050_; lean_object* v___x_3051_; 
v___f_3050_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3050_, 0, v_mergeFn_3047_);
lean_closure_set(v___f_3050_, 1, v_cmp_3046_);
v___x_3051_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3050_, v_t_u2081_3048_, v_t_u2082_3049_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith(lean_object* v_00_u03b1_3052_, lean_object* v_00_u03b2_3053_, lean_object* v_cmp_3054_, lean_object* v_inst_3055_, lean_object* v_mergeFn_3056_, lean_object* v_t_u2081_3057_, lean_object* v_t_u2082_3058_){
_start:
{
lean_object* v___f_3059_; lean_object* v___x_3060_; 
v___f_3059_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3059_, 0, v_mergeFn_3056_);
lean_closure_set(v___f_3059_, 1, v_cmp_3054_);
v___x_3060_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3059_, v_t_u2081_3057_, v_t_u2082_3058_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___redArg___lam__0(lean_object* v_x1_3061_, lean_object* v_x2_3062_, lean_object* v_x3_3063_){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3064_, 0, v_x1_3061_);
lean_ctor_set(v___x_3064_, 1, v_x2_3062_);
v___x_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v_x3_3063_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___redArg(lean_object* v_t_3067_){
_start:
{
lean_object* v___f_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___f_3068_ = ((lean_object*)(l_Std_DTreeMap_Const_toList___redArg___closed__0));
v___x_3069_ = lean_box(0);
v___x_3070_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_3071_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3070_, v___f_3068_, v___x_3069_, v_t_3067_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList(lean_object* v_00_u03b1_3072_, lean_object* v_cmp_3073_, lean_object* v_00_u03b2_3074_, lean_object* v_t_3075_){
_start:
{
lean_object* v___f_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___f_3076_ = ((lean_object*)(l_Std_DTreeMap_Const_toList___redArg___closed__0));
v___x_3077_ = lean_box(0);
v___x_3078_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_3079_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3078_, v___f_3076_, v___x_3077_, v_t_3075_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___boxed(lean_object* v_00_u03b1_3080_, lean_object* v_cmp_3081_, lean_object* v_00_u03b2_3082_, lean_object* v_t_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Std_DTreeMap_Const_toList(v_00_u03b1_3080_, v_cmp_3081_, v_00_u03b2_3082_, v_t_3083_);
lean_dec_ref(v_cmp_3081_);
return v_res_3084_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg___lam__0(lean_object* v_cmp_3086_, lean_object* v_a_3087_, lean_object* v_x_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_fst_3090_; lean_object* v_snd_3091_; lean_object* v_r_3092_; lean_object* v___x_3093_; 
v_fst_3090_ = lean_ctor_get(v_a_3087_, 0);
lean_inc(v_fst_3090_);
v_snd_3091_ = lean_ctor_get(v_a_3087_, 1);
lean_inc(v_snd_3091_);
lean_dec_ref(v_a_3087_);
v_r_3092_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3086_, v_fst_3090_, v_snd_3091_, v___y_3089_);
v___x_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3093_, 0, v_r_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg(lean_object* v_l_3094_, lean_object* v_cmp_3095_){
_start:
{
lean_object* v___f_3096_; lean_object* v___x_3097_; lean_object* v_r_3098_; lean_object* v___x_3099_; 
v___f_3096_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3096_, 0, v_cmp_3095_);
v___x_3097_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3098_ = lean_box(1);
v___x_3099_ = l_List_forIn_x27_loop___redArg(v___x_3097_, v___f_3096_, v_l_3094_, v_r_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg___boxed(lean_object* v_l_3100_, lean_object* v_cmp_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Std_DTreeMap_Const_ofList___redArg(v_l_3100_, v_cmp_3101_);
lean_dec(v_l_3100_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList(lean_object* v_00_u03b1_3103_, lean_object* v_00_u03b2_3104_, lean_object* v_l_3105_, lean_object* v_cmp_3106_){
_start:
{
lean_object* v___f_3107_; lean_object* v___x_3108_; lean_object* v_r_3109_; lean_object* v___x_3110_; 
v___f_3107_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3107_, 0, v_cmp_3106_);
v___x_3108_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3109_ = lean_box(1);
v___x_3110_ = l_List_forIn_x27_loop___redArg(v___x_3108_, v___f_3107_, v_l_3105_, v_r_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___boxed(lean_object* v_00_u03b1_3111_, lean_object* v_00_u03b2_3112_, lean_object* v_l_3113_, lean_object* v_cmp_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Std_DTreeMap_Const_ofList(v_00_u03b1_3111_, v_00_u03b2_3112_, v_l_3113_, v_cmp_3114_);
lean_dec(v_l_3113_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___redArg___lam__0(lean_object* v_acc_3116_, lean_object* v_k_3117_, lean_object* v_v_3118_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_k_3117_);
lean_ctor_set(v___x_3119_, 1, v_v_3118_);
v___x_3120_ = lean_array_push(v_acc_3116_, v___x_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___redArg(lean_object* v_t_3124_){
_start:
{
lean_object* v___f_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___f_3125_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__0));
v___x_3126_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__1));
v___x_3127_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3125_, v___x_3126_, v_t_3124_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray(lean_object* v_00_u03b1_3128_, lean_object* v_cmp_3129_, lean_object* v_00_u03b2_3130_, lean_object* v_t_3131_){
_start:
{
lean_object* v___f_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___f_3132_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__0));
v___x_3133_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__1));
v___x_3134_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3132_, v___x_3133_, v_t_3131_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___boxed(lean_object* v_00_u03b1_3135_, lean_object* v_cmp_3136_, lean_object* v_00_u03b2_3137_, lean_object* v_t_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Std_DTreeMap_Const_toArray(v_00_u03b1_3135_, v_cmp_3136_, v_00_u03b2_3137_, v_t_3138_);
lean_dec_ref(v_cmp_3136_);
return v_res_3139_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray___redArg(lean_object* v_a_3141_, lean_object* v_cmp_3142_){
_start:
{
lean_object* v___f_3143_; lean_object* v___x_3144_; lean_object* v_r_3145_; size_t v_sz_3146_; size_t v___x_3147_; lean_object* v___x_3148_; 
v___f_3143_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3143_, 0, v_cmp_3142_);
v___x_3144_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3145_ = lean_box(1);
v_sz_3146_ = lean_array_size(v_a_3141_);
v___x_3147_ = ((size_t)0ULL);
v___x_3148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3144_, v_a_3141_, v___f_3143_, v_sz_3146_, v___x_3147_, v_r_3145_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray(lean_object* v_00_u03b1_3149_, lean_object* v_00_u03b2_3150_, lean_object* v_a_3151_, lean_object* v_cmp_3152_){
_start:
{
lean_object* v___f_3153_; lean_object* v___x_3154_; lean_object* v_r_3155_; size_t v_sz_3156_; size_t v___x_3157_; lean_object* v___x_3158_; 
v___f_3153_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3153_, 0, v_cmp_3152_);
v___x_3154_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3155_ = lean_box(1);
v_sz_3156_ = lean_array_size(v_a_3151_);
v___x_3157_ = ((size_t)0ULL);
v___x_3158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3154_, v_a_3151_, v___f_3153_, v_sz_3156_, v___x_3157_, v_r_3155_);
return v___x_3158_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_3160_, lean_object* v_a_3161_, lean_object* v_x_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v___x_3164_; 
lean_inc(v___y_3163_);
lean_inc(v_a_3161_);
lean_inc_ref(v_cmp_3160_);
v___x_3164_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3160_, v_a_3161_, v___y_3163_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = lean_box(0);
v___x_3166_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3160_, v_a_3161_, v___x_3165_, v___y_3163_);
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
else
{
lean_object* v___x_3168_; 
lean_dec(v_a_3161_);
lean_dec_ref(v_cmp_3160_);
v___x_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___y_3163_);
return v___x_3168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg(lean_object* v_l_3169_, lean_object* v_cmp_3170_){
_start:
{
lean_object* v___f_3171_; lean_object* v___x_3172_; lean_object* v_r_3173_; lean_object* v___x_3174_; 
v___f_3171_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3171_, 0, v_cmp_3170_);
v___x_3172_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3173_ = lean_box(1);
v___x_3174_ = l_List_forIn_x27_loop___redArg(v___x_3172_, v___f_3171_, v_l_3169_, v_r_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg___boxed(lean_object* v_l_3175_, lean_object* v_cmp_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_Std_DTreeMap_Const_unitOfList___redArg(v_l_3175_, v_cmp_3176_);
lean_dec(v_l_3175_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList(lean_object* v_00_u03b1_3178_, lean_object* v_l_3179_, lean_object* v_cmp_3180_){
_start:
{
lean_object* v___f_3181_; lean_object* v___x_3182_; lean_object* v_r_3183_; lean_object* v___x_3184_; 
v___f_3181_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3181_, 0, v_cmp_3180_);
v___x_3182_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3183_ = lean_box(1);
v___x_3184_ = l_List_forIn_x27_loop___redArg(v___x_3182_, v___f_3181_, v_l_3179_, v_r_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___boxed(lean_object* v_00_u03b1_3185_, lean_object* v_l_3186_, lean_object* v_cmp_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Std_DTreeMap_Const_unitOfList(v_00_u03b1_3185_, v_l_3186_, v_cmp_3187_);
lean_dec(v_l_3186_);
return v_res_3188_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray___redArg(lean_object* v_a_3190_, lean_object* v_cmp_3191_){
_start:
{
lean_object* v___f_3192_; lean_object* v___x_3193_; lean_object* v_r_3194_; size_t v_sz_3195_; size_t v___x_3196_; lean_object* v___x_3197_; 
v___f_3192_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3192_, 0, v_cmp_3191_);
v___x_3193_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3194_ = lean_box(1);
v_sz_3195_ = lean_array_size(v_a_3190_);
v___x_3196_ = ((size_t)0ULL);
v___x_3197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3193_, v_a_3190_, v___f_3192_, v_sz_3195_, v___x_3196_, v_r_3194_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray(lean_object* v_00_u03b1_3198_, lean_object* v_a_3199_, lean_object* v_cmp_3200_){
_start:
{
lean_object* v___f_3201_; lean_object* v___x_3202_; lean_object* v_r_3203_; size_t v_sz_3204_; size_t v___x_3205_; lean_object* v___x_3206_; 
v___f_3201_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3201_, 0, v_cmp_3200_);
v___x_3202_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3203_ = lean_box(1);
v_sz_3204_ = lean_array_size(v_a_3199_);
v___x_3205_ = ((size_t)0ULL);
v___x_3206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3202_, v_a_3199_, v___f_3201_, v_sz_3204_, v___x_3205_, v_r_3203_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_modify___redArg(lean_object* v_cmp_3207_, lean_object* v_t_3208_, lean_object* v_a_3209_, lean_object* v_f_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3207_, v_a_3209_, v_f_3210_, v_t_3208_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_modify(lean_object* v_00_u03b1_3212_, lean_object* v_cmp_3213_, lean_object* v_00_u03b2_3214_, lean_object* v_t_3215_, lean_object* v_a_3216_, lean_object* v_f_3217_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3213_, v_a_3216_, v_f_3217_, v_t_3215_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_alter___redArg(lean_object* v_cmp_3219_, lean_object* v_t_3220_, lean_object* v_a_3221_, lean_object* v_f_3222_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3219_, v_a_3221_, v_f_3222_, v_t_3220_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_alter(lean_object* v_00_u03b1_3224_, lean_object* v_cmp_3225_, lean_object* v_00_u03b2_3226_, lean_object* v_t_3227_, lean_object* v_a_3228_, lean_object* v_f_3229_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3225_, v_a_3228_, v_f_3229_, v_t_3227_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3231_, lean_object* v_cmp_3232_, lean_object* v_t_3233_, lean_object* v_a_3234_, lean_object* v_b_u2082_3235_){
_start:
{
lean_object* v___f_3236_; lean_object* v___x_3237_; 
lean_inc(v_a_3234_);
v___f_3236_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3236_, 0, v_b_u2082_3235_);
lean_closure_set(v___f_3236_, 1, v_mergeFn_3231_);
lean_closure_set(v___f_3236_, 2, v_a_3234_);
v___x_3237_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3232_, v_a_3234_, v___f_3236_, v_t_3233_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith___redArg(lean_object* v_cmp_3238_, lean_object* v_mergeFn_3239_, lean_object* v_t_u2081_3240_, lean_object* v_t_u2082_3241_){
_start:
{
lean_object* v___f_3242_; lean_object* v___x_3243_; 
v___f_3242_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3242_, 0, v_mergeFn_3239_);
lean_closure_set(v___f_3242_, 1, v_cmp_3238_);
v___x_3243_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3242_, v_t_u2081_3240_, v_t_u2082_3241_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith(lean_object* v_00_u03b1_3244_, lean_object* v_cmp_3245_, lean_object* v_00_u03b2_3246_, lean_object* v_mergeFn_3247_, lean_object* v_t_u2081_3248_, lean_object* v_t_u2082_3249_){
_start:
{
lean_object* v___f_3250_; lean_object* v___x_3251_; 
v___f_3250_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3250_, 0, v_mergeFn_3247_);
lean_closure_set(v___f_3250_, 1, v_cmp_3245_);
v___x_3251_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3250_, v_t_u2081_3248_, v_t_u2082_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_3252_, lean_object* v_x_3253_, lean_object* v_____s_3254_){
_start:
{
lean_object* v_fst_3255_; lean_object* v_snd_3256_; lean_object* v_r_3257_; lean_object* v___x_3258_; 
v_fst_3255_ = lean_ctor_get(v_x_3253_, 0);
lean_inc(v_fst_3255_);
v_snd_3256_ = lean_ctor_get(v_x_3253_, 1);
lean_inc(v_snd_3256_);
lean_dec_ref(v_x_3253_);
v_r_3257_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3252_, v_fst_3255_, v_snd_3256_, v_____s_3254_);
v___x_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3258_, 0, v_r_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany___redArg(lean_object* v_cmp_3259_, lean_object* v_inst_3260_, lean_object* v_t_3261_, lean_object* v_l_3262_){
_start:
{
lean_object* v___f_3263_; lean_object* v___x_3264_; 
v___f_3263_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3263_, 0, v_cmp_3259_);
v___x_3264_ = lean_apply_4(v_inst_3260_, lean_box(0), v_l_3262_, v_t_3261_, v___f_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany(lean_object* v_00_u03b1_3265_, lean_object* v_00_u03b2_3266_, lean_object* v_cmp_3267_, lean_object* v_00_u03c1_3268_, lean_object* v_inst_3269_, lean_object* v_t_3270_, lean_object* v_l_3271_){
_start:
{
lean_object* v___f_3272_; lean_object* v___x_3273_; 
v___f_3272_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3272_, 0, v_cmp_3267_);
v___x_3273_ = lean_apply_4(v_inst_3269_, lean_box(0), v_l_3271_, v_t_3270_, v___f_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew___redArg___lam__0(lean_object* v_cmp_3274_, lean_object* v_x_3275_, lean_object* v_____s_3276_){
_start:
{
lean_object* v_fst_3277_; lean_object* v_snd_3278_; uint8_t v___x_3279_; 
v_fst_3277_ = lean_ctor_get(v_x_3275_, 0);
lean_inc_n(v_fst_3277_, 2);
v_snd_3278_ = lean_ctor_get(v_x_3275_, 1);
lean_inc(v_snd_3278_);
lean_dec_ref(v_x_3275_);
lean_inc(v_____s_3276_);
lean_inc_ref(v_cmp_3274_);
v___x_3279_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3274_, v_fst_3277_, v_____s_3276_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3274_, v_fst_3277_, v_snd_3278_, v_____s_3276_);
v___x_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
return v___x_3281_;
}
else
{
lean_object* v___x_3282_; 
lean_dec(v_snd_3278_);
lean_dec(v_fst_3277_);
lean_dec_ref(v_cmp_3274_);
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v_____s_3276_);
return v___x_3282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew___redArg(lean_object* v_cmp_3283_, lean_object* v_inst_3284_, lean_object* v_t_3285_, lean_object* v_l_3286_){
_start:
{
lean_object* v___f_3287_; lean_object* v___x_3288_; 
v___f_3287_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertManyIfNew___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3287_, 0, v_cmp_3283_);
v___x_3288_ = lean_apply_4(v_inst_3284_, lean_box(0), v_l_3286_, v_t_3285_, v___f_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew(lean_object* v_00_u03b1_3289_, lean_object* v_00_u03b2_3290_, lean_object* v_cmp_3291_, lean_object* v_00_u03c1_3292_, lean_object* v_inst_3293_, lean_object* v_t_3294_, lean_object* v_l_3295_){
_start:
{
lean_object* v___f_3296_; lean_object* v___x_3297_; 
v___f_3296_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertManyIfNew___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3296_, 0, v_cmp_3291_);
v___x_3297_ = lean_apply_4(v_inst_3293_, lean_box(0), v_l_3295_, v_t_3294_, v___f_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(lean_object* v_cmp_3298_, lean_object* v_k_3299_, lean_object* v_v_3300_, lean_object* v_t_3301_){
_start:
{
if (lean_obj_tag(v_t_3301_) == 0)
{
lean_object* v_size_3302_; lean_object* v_k_3303_; lean_object* v_v_3304_; lean_object* v_l_3305_; lean_object* v_r_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3587_; 
v_size_3302_ = lean_ctor_get(v_t_3301_, 0);
v_k_3303_ = lean_ctor_get(v_t_3301_, 1);
v_v_3304_ = lean_ctor_get(v_t_3301_, 2);
v_l_3305_ = lean_ctor_get(v_t_3301_, 3);
v_r_3306_ = lean_ctor_get(v_t_3301_, 4);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_t_3301_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3308_ = v_t_3301_;
v_isShared_3309_ = v_isSharedCheck_3587_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_r_3306_);
lean_inc(v_l_3305_);
lean_inc(v_v_3304_);
lean_inc(v_k_3303_);
lean_inc(v_size_3302_);
lean_dec(v_t_3301_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3587_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; uint8_t v___x_3311_; 
lean_inc_ref(v_cmp_3298_);
lean_inc(v_k_3303_);
lean_inc(v_k_3299_);
v___x_3310_ = lean_apply_2(v_cmp_3298_, v_k_3299_, v_k_3303_);
v___x_3311_ = lean_unbox(v___x_3310_);
switch(v___x_3311_)
{
case 0:
{
lean_object* v_impl_3312_; lean_object* v___x_3313_; 
lean_dec(v_size_3302_);
v_impl_3312_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3298_, v_k_3299_, v_v_3300_, v_l_3305_);
v___x_3313_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3306_) == 0)
{
lean_object* v_size_3314_; lean_object* v_size_3315_; lean_object* v_k_3316_; lean_object* v_v_3317_; lean_object* v_l_3318_; lean_object* v_r_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v_size_3314_ = lean_ctor_get(v_r_3306_, 0);
v_size_3315_ = lean_ctor_get(v_impl_3312_, 0);
lean_inc(v_size_3315_);
v_k_3316_ = lean_ctor_get(v_impl_3312_, 1);
lean_inc(v_k_3316_);
v_v_3317_ = lean_ctor_get(v_impl_3312_, 2);
lean_inc(v_v_3317_);
v_l_3318_ = lean_ctor_get(v_impl_3312_, 3);
lean_inc(v_l_3318_);
v_r_3319_ = lean_ctor_get(v_impl_3312_, 4);
lean_inc(v_r_3319_);
v___x_3320_ = lean_unsigned_to_nat(3u);
v___x_3321_ = lean_nat_mul(v___x_3320_, v_size_3314_);
v___x_3322_ = lean_nat_dec_lt(v___x_3321_, v_size_3315_);
lean_dec(v___x_3321_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3326_; 
lean_dec(v_r_3319_);
lean_dec(v_l_3318_);
lean_dec(v_v_3317_);
lean_dec(v_k_3316_);
v___x_3323_ = lean_nat_add(v___x_3313_, v_size_3315_);
lean_dec(v_size_3315_);
v___x_3324_ = lean_nat_add(v___x_3323_, v_size_3314_);
lean_dec(v___x_3323_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 3, v_impl_3312_);
lean_ctor_set(v___x_3308_, 0, v___x_3324_);
v___x_3326_ = v___x_3308_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_k_3303_);
lean_ctor_set(v_reuseFailAlloc_3327_, 2, v_v_3304_);
lean_ctor_set(v_reuseFailAlloc_3327_, 3, v_impl_3312_);
lean_ctor_set(v_reuseFailAlloc_3327_, 4, v_r_3306_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
else
{
lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3393_; 
v_isSharedCheck_3393_ = !lean_is_exclusive(v_impl_3312_);
if (v_isSharedCheck_3393_ == 0)
{
lean_object* v_unused_3394_; lean_object* v_unused_3395_; lean_object* v_unused_3396_; lean_object* v_unused_3397_; lean_object* v_unused_3398_; 
v_unused_3394_ = lean_ctor_get(v_impl_3312_, 4);
lean_dec(v_unused_3394_);
v_unused_3395_ = lean_ctor_get(v_impl_3312_, 3);
lean_dec(v_unused_3395_);
v_unused_3396_ = lean_ctor_get(v_impl_3312_, 2);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v_impl_3312_, 1);
lean_dec(v_unused_3397_);
v_unused_3398_ = lean_ctor_get(v_impl_3312_, 0);
lean_dec(v_unused_3398_);
v___x_3329_ = v_impl_3312_;
v_isShared_3330_ = v_isSharedCheck_3393_;
goto v_resetjp_3328_;
}
else
{
lean_dec(v_impl_3312_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3393_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v_size_3331_; lean_object* v_size_3332_; lean_object* v_k_3333_; lean_object* v_v_3334_; lean_object* v_l_3335_; lean_object* v_r_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; uint8_t v___x_3339_; 
v_size_3331_ = lean_ctor_get(v_l_3318_, 0);
v_size_3332_ = lean_ctor_get(v_r_3319_, 0);
v_k_3333_ = lean_ctor_get(v_r_3319_, 1);
v_v_3334_ = lean_ctor_get(v_r_3319_, 2);
v_l_3335_ = lean_ctor_get(v_r_3319_, 3);
v_r_3336_ = lean_ctor_get(v_r_3319_, 4);
v___x_3337_ = lean_unsigned_to_nat(2u);
v___x_3338_ = lean_nat_mul(v___x_3337_, v_size_3331_);
v___x_3339_ = lean_nat_dec_lt(v_size_3332_, v___x_3338_);
lean_dec(v___x_3338_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3368_; 
lean_inc(v_r_3336_);
lean_inc(v_l_3335_);
lean_inc(v_v_3334_);
lean_inc(v_k_3333_);
v_isSharedCheck_3368_ = !lean_is_exclusive(v_r_3319_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; lean_object* v_unused_3370_; lean_object* v_unused_3371_; lean_object* v_unused_3372_; lean_object* v_unused_3373_; 
v_unused_3369_ = lean_ctor_get(v_r_3319_, 4);
lean_dec(v_unused_3369_);
v_unused_3370_ = lean_ctor_get(v_r_3319_, 3);
lean_dec(v_unused_3370_);
v_unused_3371_ = lean_ctor_get(v_r_3319_, 2);
lean_dec(v_unused_3371_);
v_unused_3372_ = lean_ctor_get(v_r_3319_, 1);
lean_dec(v_unused_3372_);
v_unused_3373_ = lean_ctor_get(v_r_3319_, 0);
lean_dec(v_unused_3373_);
v___x_3341_ = v_r_3319_;
v_isShared_3342_ = v_isSharedCheck_3368_;
goto v_resetjp_3340_;
}
else
{
lean_dec(v_r_3319_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3368_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___x_3356_; lean_object* v___y_3358_; 
v___x_3343_ = lean_nat_add(v___x_3313_, v_size_3315_);
lean_dec(v_size_3315_);
v___x_3344_ = lean_nat_add(v___x_3343_, v_size_3314_);
lean_dec(v___x_3343_);
v___x_3356_ = lean_nat_add(v___x_3313_, v_size_3331_);
if (lean_obj_tag(v_l_3335_) == 0)
{
lean_object* v_size_3366_; 
v_size_3366_ = lean_ctor_get(v_l_3335_, 0);
lean_inc(v_size_3366_);
v___y_3358_ = v_size_3366_;
goto v___jp_3357_;
}
else
{
lean_object* v___x_3367_; 
v___x_3367_ = lean_unsigned_to_nat(0u);
v___y_3358_ = v___x_3367_;
goto v___jp_3357_;
}
v___jp_3345_:
{
lean_object* v___x_3349_; lean_object* v___x_3351_; 
v___x_3349_ = lean_nat_add(v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec(v___y_3347_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 4, v_r_3306_);
lean_ctor_set(v___x_3341_, 3, v_r_3336_);
lean_ctor_set(v___x_3341_, 2, v_v_3304_);
lean_ctor_set(v___x_3341_, 1, v_k_3303_);
lean_ctor_set(v___x_3341_, 0, v___x_3349_);
v___x_3351_ = v___x_3341_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_k_3303_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_v_3304_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v_r_3336_);
lean_ctor_set(v_reuseFailAlloc_3355_, 4, v_r_3306_);
v___x_3351_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3353_; 
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 4, v___x_3351_);
lean_ctor_set(v___x_3329_, 3, v___y_3346_);
lean_ctor_set(v___x_3329_, 2, v_v_3334_);
lean_ctor_set(v___x_3329_, 1, v_k_3333_);
lean_ctor_set(v___x_3329_, 0, v___x_3344_);
v___x_3353_ = v___x_3329_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3344_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_k_3333_);
lean_ctor_set(v_reuseFailAlloc_3354_, 2, v_v_3334_);
lean_ctor_set(v_reuseFailAlloc_3354_, 3, v___y_3346_);
lean_ctor_set(v_reuseFailAlloc_3354_, 4, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
v___jp_3357_:
{
lean_object* v___x_3359_; lean_object* v___x_3361_; 
v___x_3359_ = lean_nat_add(v___x_3356_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec(v___x_3356_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v_l_3335_);
lean_ctor_set(v___x_3308_, 3, v_l_3318_);
lean_ctor_set(v___x_3308_, 2, v_v_3317_);
lean_ctor_set(v___x_3308_, 1, v_k_3316_);
lean_ctor_set(v___x_3308_, 0, v___x_3359_);
v___x_3361_ = v___x_3308_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3359_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3365_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3365_, 3, v_l_3318_);
lean_ctor_set(v_reuseFailAlloc_3365_, 4, v_l_3335_);
v___x_3361_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3362_; 
v___x_3362_ = lean_nat_add(v___x_3313_, v_size_3314_);
if (lean_obj_tag(v_r_3336_) == 0)
{
lean_object* v_size_3363_; 
v_size_3363_ = lean_ctor_get(v_r_3336_, 0);
lean_inc(v_size_3363_);
v___y_3346_ = v___x_3361_;
v___y_3347_ = v___x_3362_;
v___y_3348_ = v_size_3363_;
goto v___jp_3345_;
}
else
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_unsigned_to_nat(0u);
v___y_3346_ = v___x_3361_;
v___y_3347_ = v___x_3362_;
v___y_3348_ = v___x_3364_;
goto v___jp_3345_;
}
}
}
}
}
else
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
lean_del_object(v___x_3308_);
v___x_3374_ = lean_nat_add(v___x_3313_, v_size_3315_);
lean_dec(v_size_3315_);
v___x_3375_ = lean_nat_add(v___x_3374_, v_size_3314_);
lean_dec(v___x_3374_);
v___x_3376_ = lean_nat_add(v___x_3313_, v_size_3314_);
v___x_3377_ = lean_nat_add(v___x_3376_, v_size_3332_);
lean_dec(v___x_3376_);
lean_inc_ref(v_r_3306_);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 4, v_r_3306_);
lean_ctor_set(v___x_3329_, 3, v_r_3319_);
lean_ctor_set(v___x_3329_, 2, v_v_3304_);
lean_ctor_set(v___x_3329_, 1, v_k_3303_);
lean_ctor_set(v___x_3329_, 0, v___x_3377_);
v___x_3379_ = v___x_3329_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3377_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_k_3303_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_v_3304_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_r_3319_);
lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_r_3306_);
v___x_3379_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
v_isSharedCheck_3386_ = !lean_is_exclusive(v_r_3306_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; lean_object* v_unused_3388_; lean_object* v_unused_3389_; lean_object* v_unused_3390_; lean_object* v_unused_3391_; 
v_unused_3387_ = lean_ctor_get(v_r_3306_, 4);
lean_dec(v_unused_3387_);
v_unused_3388_ = lean_ctor_get(v_r_3306_, 3);
lean_dec(v_unused_3388_);
v_unused_3389_ = lean_ctor_get(v_r_3306_, 2);
lean_dec(v_unused_3389_);
v_unused_3390_ = lean_ctor_get(v_r_3306_, 1);
lean_dec(v_unused_3390_);
v_unused_3391_ = lean_ctor_get(v_r_3306_, 0);
lean_dec(v_unused_3391_);
v___x_3381_ = v_r_3306_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_dec(v_r_3306_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 4, v___x_3379_);
lean_ctor_set(v___x_3381_, 3, v_l_3318_);
lean_ctor_set(v___x_3381_, 2, v_v_3317_);
lean_ctor_set(v___x_3381_, 1, v_k_3316_);
lean_ctor_set(v___x_3381_, 0, v___x_3375_);
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3385_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3385_, 3, v_l_3318_);
lean_ctor_set(v_reuseFailAlloc_3385_, 4, v___x_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3399_; 
v_l_3399_ = lean_ctor_get(v_impl_3312_, 3);
lean_inc(v_l_3399_);
if (lean_obj_tag(v_l_3399_) == 0)
{
lean_object* v_r_3400_; lean_object* v_k_3401_; lean_object* v_v_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3413_; 
v_r_3400_ = lean_ctor_get(v_impl_3312_, 4);
v_k_3401_ = lean_ctor_get(v_impl_3312_, 1);
v_v_3402_ = lean_ctor_get(v_impl_3312_, 2);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_impl_3312_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; lean_object* v_unused_3415_; 
v_unused_3414_ = lean_ctor_get(v_impl_3312_, 3);
lean_dec(v_unused_3414_);
v_unused_3415_ = lean_ctor_get(v_impl_3312_, 0);
lean_dec(v_unused_3415_);
v___x_3404_ = v_impl_3312_;
v_isShared_3405_ = v_isSharedCheck_3413_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_r_3400_);
lean_inc(v_v_3402_);
lean_inc(v_k_3401_);
lean_dec(v_impl_3312_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3413_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3406_; lean_object* v___x_3408_; 
v___x_3406_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3400_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 3, v_r_3400_);
lean_ctor_set(v___x_3404_, 2, v_v_3304_);
lean_ctor_set(v___x_3404_, 1, v_k_3303_);
lean_ctor_set(v___x_3404_, 0, v___x_3313_);
v___x_3408_ = v___x_3404_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_k_3303_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_v_3304_);
lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_r_3400_);
lean_ctor_set(v_reuseFailAlloc_3412_, 4, v_r_3400_);
v___x_3408_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3410_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v___x_3408_);
lean_ctor_set(v___x_3308_, 3, v_l_3399_);
lean_ctor_set(v___x_3308_, 2, v_v_3402_);
lean_ctor_set(v___x_3308_, 1, v_k_3401_);
lean_ctor_set(v___x_3308_, 0, v___x_3406_);
v___x_3410_ = v___x_3308_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3406_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_k_3401_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v_v_3402_);
lean_ctor_set(v_reuseFailAlloc_3411_, 3, v_l_3399_);
lean_ctor_set(v_reuseFailAlloc_3411_, 4, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
else
{
lean_object* v_r_3416_; 
v_r_3416_ = lean_ctor_get(v_impl_3312_, 4);
lean_inc(v_r_3416_);
if (lean_obj_tag(v_r_3416_) == 0)
{
lean_object* v_k_3417_; lean_object* v_v_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3441_; 
v_k_3417_ = lean_ctor_get(v_impl_3312_, 1);
v_v_3418_ = lean_ctor_get(v_impl_3312_, 2);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_impl_3312_);
if (v_isSharedCheck_3441_ == 0)
{
lean_object* v_unused_3442_; lean_object* v_unused_3443_; lean_object* v_unused_3444_; 
v_unused_3442_ = lean_ctor_get(v_impl_3312_, 4);
lean_dec(v_unused_3442_);
v_unused_3443_ = lean_ctor_get(v_impl_3312_, 3);
lean_dec(v_unused_3443_);
v_unused_3444_ = lean_ctor_get(v_impl_3312_, 0);
lean_dec(v_unused_3444_);
v___x_3420_ = v_impl_3312_;
v_isShared_3421_ = v_isSharedCheck_3441_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_v_3418_);
lean_inc(v_k_3417_);
lean_dec(v_impl_3312_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3441_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v_k_3422_; lean_object* v_v_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3437_; 
v_k_3422_ = lean_ctor_get(v_r_3416_, 1);
v_v_3423_ = lean_ctor_get(v_r_3416_, 2);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_r_3416_);
if (v_isSharedCheck_3437_ == 0)
{
lean_object* v_unused_3438_; lean_object* v_unused_3439_; lean_object* v_unused_3440_; 
v_unused_3438_ = lean_ctor_get(v_r_3416_, 4);
lean_dec(v_unused_3438_);
v_unused_3439_ = lean_ctor_get(v_r_3416_, 3);
lean_dec(v_unused_3439_);
v_unused_3440_ = lean_ctor_get(v_r_3416_, 0);
lean_dec(v_unused_3440_);
v___x_3425_ = v_r_3416_;
v_isShared_3426_ = v_isSharedCheck_3437_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_v_3423_);
lean_inc(v_k_3422_);
lean_dec(v_r_3416_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3437_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3427_ = lean_unsigned_to_nat(3u);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 4, v_l_3399_);
lean_ctor_set(v___x_3425_, 3, v_l_3399_);
lean_ctor_set(v___x_3425_, 2, v_v_3418_);
lean_ctor_set(v___x_3425_, 1, v_k_3417_);
lean_ctor_set(v___x_3425_, 0, v___x_3313_);
v___x_3429_ = v___x_3425_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v_k_3417_);
lean_ctor_set(v_reuseFailAlloc_3436_, 2, v_v_3418_);
lean_ctor_set(v_reuseFailAlloc_3436_, 3, v_l_3399_);
lean_ctor_set(v_reuseFailAlloc_3436_, 4, v_l_3399_);
v___x_3429_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3431_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 4, v_l_3399_);
lean_ctor_set(v___x_3420_, 2, v_v_3304_);
lean_ctor_set(v___x_3420_, 1, v_k_3303_);
lean_ctor_set(v___x_3420_, 0, v___x_3313_);
v___x_3431_ = v___x_3420_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3435_, 1, v_k_3303_);
lean_ctor_set(v_reuseFailAlloc_3435_, 2, v_v_3304_);
lean_ctor_set(v_reuseFailAlloc_3435_, 3, v_l_3399_);
lean_ctor_set(v_reuseFailAlloc_3435_, 4, v_l_3399_);
v___x_3431_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3433_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v___x_3431_);
lean_ctor_set(v___x_3308_, 3, v___x_3429_);
lean_ctor_set(v___x_3308_, 2, v_v_3423_);
lean_ctor_set(v___x_3308_, 1, v_k_3422_);
lean_ctor_set(v___x_3308_, 0, v___x_3427_);
v___x_3433_ = v___x_3308_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3427_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_k_3422_);
lean_ctor_set(v_reuseFailAlloc_3434_, 2, v_v_3423_);
lean_ctor_set(v_reuseFailAlloc_3434_, 3, v___x_3429_);
lean_ctor_set(v_reuseFailAlloc_3434_, 4, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
}
else
{
lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3445_ = lean_unsigned_to_nat(2u);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v_r_3416_);
lean_ctor_set(v___x_3308_, 3, v_impl_3312_);
lean_ctor_set(v___x_3308_, 0, v___x_3445_);
v___x_3447_ = v___x_3308_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_k_3303_);
lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_v_3304_);
lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_impl_3312_);
lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_r_3416_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3450_; 
lean_dec(v_v_3304_);
lean_dec(v_k_3303_);
lean_dec_ref(v_cmp_3298_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 2, v_v_3300_);
lean_ctor_set(v___x_3308_, 1, v_k_3299_);
v___x_3450_ = v___x_3308_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_size_3302_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_k_3299_);
lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_v_3300_);
lean_ctor_set(v_reuseFailAlloc_3451_, 3, v_l_3305_);
lean_ctor_set(v_reuseFailAlloc_3451_, 4, v_r_3306_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
default: 
{
lean_object* v_impl_3452_; lean_object* v___x_3453_; 
lean_dec(v_size_3302_);
v_impl_3452_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3298_, v_k_3299_, v_v_3300_, v_r_3306_);
v___x_3453_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3305_) == 0)
{
lean_object* v_size_3454_; lean_object* v_size_3455_; lean_object* v_k_3456_; lean_object* v_v_3457_; lean_object* v_l_3458_; lean_object* v_r_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; uint8_t v___x_3462_; 
v_size_3454_ = lean_ctor_get(v_l_3305_, 0);
v_size_3455_ = lean_ctor_get(v_impl_3452_, 0);
lean_inc(v_size_3455_);
v_k_3456_ = lean_ctor_get(v_impl_3452_, 1);
lean_inc(v_k_3456_);
v_v_3457_ = lean_ctor_get(v_impl_3452_, 2);
lean_inc(v_v_3457_);
v_l_3458_ = lean_ctor_get(v_impl_3452_, 3);
lean_inc(v_l_3458_);
v_r_3459_ = lean_ctor_get(v_impl_3452_, 4);
lean_inc(v_r_3459_);
v___x_3460_ = lean_unsigned_to_nat(3u);
v___x_3461_ = lean_nat_mul(v___x_3460_, v_size_3454_);
v___x_3462_ = lean_nat_dec_lt(v___x_3461_, v_size_3455_);
lean_dec(v___x_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
lean_dec(v_r_3459_);
lean_dec(v_l_3458_);
lean_dec(v_v_3457_);
lean_dec(v_k_3456_);
v___x_3463_ = lean_nat_add(v___x_3453_, v_size_3454_);
v___x_3464_ = lean_nat_add(v___x_3463_, v_size_3455_);
lean_dec(v_size_3455_);
lean_dec(v___x_3463_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v_impl_3452_);
lean_ctor_set(v___x_3308_, 0, v___x_3464_);
v___x_3466_ = v___x_3308_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_k_3303_);
lean_ctor_set(v_reuseFailAlloc_3467_, 2, v_v_3304_);
lean_ctor_set(v_reuseFailAlloc_3467_, 3, v_l_3305_);
lean_ctor_set(v_reuseFailAlloc_3467_, 4, v_impl_3452_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
else
{
lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3531_; 
v_isSharedCheck_3531_ = !lean_is_exclusive(v_impl_3452_);
if (v_isSharedCheck_3531_ == 0)
{
lean_object* v_unused_3532_; lean_object* v_unused_3533_; lean_object* v_unused_3534_; lean_object* v_unused_3535_; lean_object* v_unused_3536_; 
v_unused_3532_ = lean_ctor_get(v_impl_3452_, 4);
lean_dec(v_unused_3532_);
v_unused_3533_ = lean_ctor_get(v_impl_3452_, 3);
lean_dec(v_unused_3533_);
v_unused_3534_ = lean_ctor_get(v_impl_3452_, 2);
lean_dec(v_unused_3534_);
v_unused_3535_ = lean_ctor_get(v_impl_3452_, 1);
lean_dec(v_unused_3535_);
v_unused_3536_ = lean_ctor_get(v_impl_3452_, 0);
lean_dec(v_unused_3536_);
v___x_3469_ = v_impl_3452_;
v_isShared_3470_ = v_isSharedCheck_3531_;
goto v_resetjp_3468_;
}
else
{
lean_dec(v_impl_3452_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3531_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v_size_3471_; lean_object* v_k_3472_; lean_object* v_v_3473_; lean_object* v_l_3474_; lean_object* v_r_3475_; lean_object* v_size_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; uint8_t v___x_3479_; 
v_size_3471_ = lean_ctor_get(v_l_3458_, 0);
v_k_3472_ = lean_ctor_get(v_l_3458_, 1);
v_v_3473_ = lean_ctor_get(v_l_3458_, 2);
v_l_3474_ = lean_ctor_get(v_l_3458_, 3);
v_r_3475_ = lean_ctor_get(v_l_3458_, 4);
v_size_3476_ = lean_ctor_get(v_r_3459_, 0);
v___x_3477_ = lean_unsigned_to_nat(2u);
v___x_3478_ = lean_nat_mul(v___x_3477_, v_size_3476_);
v___x_3479_ = lean_nat_dec_lt(v_size_3471_, v___x_3478_);
lean_dec(v___x_3478_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3507_; 
lean_inc(v_r_3475_);
lean_inc(v_l_3474_);
lean_inc(v_v_3473_);
lean_inc(v_k_3472_);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_l_3458_);
if (v_isSharedCheck_3507_ == 0)
{
lean_object* v_unused_3508_; lean_object* v_unused_3509_; lean_object* v_unused_3510_; lean_object* v_unused_3511_; lean_object* v_unused_3512_; 
v_unused_3508_ = lean_ctor_get(v_l_3458_, 4);
lean_dec(v_unused_3508_);
v_unused_3509_ = lean_ctor_get(v_l_3458_, 3);
lean_dec(v_unused_3509_);
v_unused_3510_ = lean_ctor_get(v_l_3458_, 2);
lean_dec(v_unused_3510_);
v_unused_3511_ = lean_ctor_get(v_l_3458_, 1);
lean_dec(v_unused_3511_);
v_unused_3512_ = lean_ctor_get(v_l_3458_, 0);
lean_dec(v_unused_3512_);
v___x_3481_ = v_l_3458_;
v_isShared_3482_ = v_isSharedCheck_3507_;
goto v_resetjp_3480_;
}
else
{
lean_dec(v_l_3458_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3507_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3497_; 
v___x_3483_ = lean_nat_add(v___x_3453_, v_size_3454_);
v___x_3484_ = lean_nat_add(v___x_3483_, v_size_3455_);
lean_dec(v_size_3455_);
if (lean_obj_tag(v_l_3474_) == 0)
{
lean_object* v_size_3505_; 
v_size_3505_ = lean_ctor_get(v_l_3474_, 0);
lean_inc(v_size_3505_);
v___y_3497_ = v_size_3505_;
goto v___jp_3496_;
}
else
{
lean_object* v___x_3506_; 
v___x_3506_ = lean_unsigned_to_nat(0u);
v___y_3497_ = v___x_3506_;
goto v___jp_3496_;
}
v___jp_3485_:
{
lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3489_ = lean_nat_add(v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec(v___y_3487_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 4, v_r_3459_);
lean_ctor_set(v___x_3481_, 3, v_r_3475_);
lean_ctor_set(v___x_3481_, 2, v_v_3457_);
lean_ctor_set(v___x_3481_, 1, v_k_3456_);
lean_ctor_set(v___x_3481_, 0, v___x_3489_);
v___x_3491_ = v___x_3481_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_k_3456_);
lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_v_3457_);
lean_ctor_set(v_reuseFailAlloc_3495_, 3, v_r_3475_);
lean_ctor_set(v_reuseFailAlloc_3495_, 4, v_r_3459_);
v___x_3491_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3493_; 
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 4, v___x_3491_);
lean_ctor_set(v___x_3469_, 3, v___y_3486_);
lean_ctor_set(v___x_3469_, 2, v_v_3473_);
lean_ctor_set(v___x_3469_, 1, v_k_3472_);
lean_ctor_set(v___x_3469_, 0, v___x_3484_);
v___x_3493_ = v___x_3469_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3484_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_k_3472_);
lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_v_3473_);
lean_ctor_set(v_reuseFailAlloc_3494_, 3, v___y_3486_);
lean_ctor_set(v_reuseFailAlloc_3494_, 4, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
v___jp_3496_:
{
lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3498_ = lean_nat_add(v___x_3483_, v___y_3497_);
lean_dec(v___y_3497_);
lean_dec(v___x_3483_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v_l_3474_);
lean_ctor_set(v___x_3308_, 0, v___x_3498_);
v___x_3500_ = v___x_3308_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v_k_3303_);
lean_ctor_set(v_reuseFailAlloc_3504_, 2, v_v_3304_);
lean_ctor_set(v_reuseFailAlloc_3504_, 3, v_l_3305_);
lean_ctor_set(v_reuseFailAlloc_3504_, 4, v_l_3474_);
v___x_3500_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3501_; 
v___x_3501_ = lean_nat_add(v___x_3453_, v_size_3476_);
if (lean_obj_tag(v_r_3475_) == 0)
{
lean_object* v_size_3502_; 
v_size_3502_ = lean_ctor_get(v_r_3475_, 0);
lean_inc(v_size_3502_);
v___y_3486_ = v___x_3500_;
v___y_3487_ = v___x_3501_;
v___y_3488_ = v_size_3502_;
goto v___jp_3485_;
}
else
{
lean_object* v___x_3503_; 
v___x_3503_ = lean_unsigned_to_nat(0u);
v___y_3486_ = v___x_3500_;
v___y_3487_ = v___x_3501_;
v___y_3488_ = v___x_3503_;
goto v___jp_3485_;
}
}
}
}
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
lean_del_object(v___x_3308_);
v___x_3513_ = lean_nat_add(v___x_3453_, v_size_3454_);
v___x_3514_ = lean_nat_add(v___x_3513_, v_size_3455_);
lean_dec(v_size_3455_);
v___x_3515_ = lean_nat_add(v___x_3513_, v_size_3471_);
lean_dec(v___x_3513_);
lean_inc_ref(v_l_3305_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 4, v_l_3458_);
lean_ctor_set(v___x_3469_, 3, v_l_3305_);
lean_ctor_set(v___x_3469_, 2, v_v_3304_);
lean_ctor_set(v___x_3469_, 1, v_k_3303_);
lean_ctor_set(v___x_3469_, 0, v___x_3515_);
v___x_3517_ = v___x_3469_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_k_3303_);
lean_ctor_set(v_reuseFailAlloc_3530_, 2, v_v_3304_);
lean_ctor_set(v_reuseFailAlloc_3530_, 3, v_l_3305_);
lean_ctor_set(v_reuseFailAlloc_3530_, 4, v_l_3458_);
v___x_3517_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
v_isSharedCheck_3524_ = !lean_is_exclusive(v_l_3305_);
if (v_isSharedCheck_3524_ == 0)
{
lean_object* v_unused_3525_; lean_object* v_unused_3526_; lean_object* v_unused_3527_; lean_object* v_unused_3528_; lean_object* v_unused_3529_; 
v_unused_3525_ = lean_ctor_get(v_l_3305_, 4);
lean_dec(v_unused_3525_);
v_unused_3526_ = lean_ctor_get(v_l_3305_, 3);
lean_dec(v_unused_3526_);
v_unused_3527_ = lean_ctor_get(v_l_3305_, 2);
lean_dec(v_unused_3527_);
v_unused_3528_ = lean_ctor_get(v_l_3305_, 1);
lean_dec(v_unused_3528_);
v_unused_3529_ = lean_ctor_get(v_l_3305_, 0);
lean_dec(v_unused_3529_);
v___x_3519_ = v_l_3305_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_dec(v_l_3305_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 4, v_r_3459_);
lean_ctor_set(v___x_3519_, 3, v___x_3517_);
lean_ctor_set(v___x_3519_, 2, v_v_3457_);
lean_ctor_set(v___x_3519_, 1, v_k_3456_);
lean_ctor_set(v___x_3519_, 0, v___x_3514_);
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3514_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_k_3456_);
lean_ctor_set(v_reuseFailAlloc_3523_, 2, v_v_3457_);
lean_ctor_set(v_reuseFailAlloc_3523_, 3, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3523_, 4, v_r_3459_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3537_; 
v_l_3537_ = lean_ctor_get(v_impl_3452_, 3);
lean_inc(v_l_3537_);
if (lean_obj_tag(v_l_3537_) == 0)
{
lean_object* v_r_3538_; lean_object* v_k_3539_; lean_object* v_v_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3563_; 
v_r_3538_ = lean_ctor_get(v_impl_3452_, 4);
v_k_3539_ = lean_ctor_get(v_impl_3452_, 1);
v_v_3540_ = lean_ctor_get(v_impl_3452_, 2);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_impl_3452_);
if (v_isSharedCheck_3563_ == 0)
{
lean_object* v_unused_3564_; lean_object* v_unused_3565_; 
v_unused_3564_ = lean_ctor_get(v_impl_3452_, 3);
lean_dec(v_unused_3564_);
v_unused_3565_ = lean_ctor_get(v_impl_3452_, 0);
lean_dec(v_unused_3565_);
v___x_3542_ = v_impl_3452_;
v_isShared_3543_ = v_isSharedCheck_3563_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_r_3538_);
lean_inc(v_v_3540_);
lean_inc(v_k_3539_);
lean_dec(v_impl_3452_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3563_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v_k_3544_; lean_object* v_v_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3559_; 
v_k_3544_ = lean_ctor_get(v_l_3537_, 1);
v_v_3545_ = lean_ctor_get(v_l_3537_, 2);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_l_3537_);
if (v_isSharedCheck_3559_ == 0)
{
lean_object* v_unused_3560_; lean_object* v_unused_3561_; lean_object* v_unused_3562_; 
v_unused_3560_ = lean_ctor_get(v_l_3537_, 4);
lean_dec(v_unused_3560_);
v_unused_3561_ = lean_ctor_get(v_l_3537_, 3);
lean_dec(v_unused_3561_);
v_unused_3562_ = lean_ctor_get(v_l_3537_, 0);
lean_dec(v_unused_3562_);
v___x_3547_ = v_l_3537_;
v_isShared_3548_ = v_isSharedCheck_3559_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_v_3545_);
lean_inc(v_k_3544_);
lean_dec(v_l_3537_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3559_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
v___x_3549_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3538_, 2);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 4, v_r_3538_);
lean_ctor_set(v___x_3547_, 3, v_r_3538_);
lean_ctor_set(v___x_3547_, 2, v_v_3304_);
lean_ctor_set(v___x_3547_, 1, v_k_3303_);
lean_ctor_set(v___x_3547_, 0, v___x_3453_);
v___x_3551_ = v___x_3547_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_k_3303_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_v_3304_);
lean_ctor_set(v_reuseFailAlloc_3558_, 3, v_r_3538_);
lean_ctor_set(v_reuseFailAlloc_3558_, 4, v_r_3538_);
v___x_3551_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3553_; 
lean_inc(v_r_3538_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 3, v_r_3538_);
lean_ctor_set(v___x_3542_, 0, v___x_3453_);
v___x_3553_ = v___x_3542_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_k_3539_);
lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_v_3540_);
lean_ctor_set(v_reuseFailAlloc_3557_, 3, v_r_3538_);
lean_ctor_set(v_reuseFailAlloc_3557_, 4, v_r_3538_);
v___x_3553_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
lean_object* v___x_3555_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v___x_3553_);
lean_ctor_set(v___x_3308_, 3, v___x_3551_);
lean_ctor_set(v___x_3308_, 2, v_v_3545_);
lean_ctor_set(v___x_3308_, 1, v_k_3544_);
lean_ctor_set(v___x_3308_, 0, v___x_3549_);
v___x_3555_ = v___x_3308_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v_k_3544_);
lean_ctor_set(v_reuseFailAlloc_3556_, 2, v_v_3545_);
lean_ctor_set(v_reuseFailAlloc_3556_, 3, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3556_, 4, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
}
}
else
{
lean_object* v_r_3566_; 
v_r_3566_ = lean_ctor_get(v_impl_3452_, 4);
lean_inc(v_r_3566_);
if (lean_obj_tag(v_r_3566_) == 0)
{
lean_object* v_k_3567_; lean_object* v_v_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3579_; 
v_k_3567_ = lean_ctor_get(v_impl_3452_, 1);
v_v_3568_ = lean_ctor_get(v_impl_3452_, 2);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_impl_3452_);
if (v_isSharedCheck_3579_ == 0)
{
lean_object* v_unused_3580_; lean_object* v_unused_3581_; lean_object* v_unused_3582_; 
v_unused_3580_ = lean_ctor_get(v_impl_3452_, 4);
lean_dec(v_unused_3580_);
v_unused_3581_ = lean_ctor_get(v_impl_3452_, 3);
lean_dec(v_unused_3581_);
v_unused_3582_ = lean_ctor_get(v_impl_3452_, 0);
lean_dec(v_unused_3582_);
v___x_3570_ = v_impl_3452_;
v_isShared_3571_ = v_isSharedCheck_3579_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_v_3568_);
lean_inc(v_k_3567_);
lean_dec(v_impl_3452_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3579_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3572_ = lean_unsigned_to_nat(3u);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 4, v_l_3537_);
lean_ctor_set(v___x_3570_, 2, v_v_3304_);
lean_ctor_set(v___x_3570_, 1, v_k_3303_);
lean_ctor_set(v___x_3570_, 0, v___x_3453_);
v___x_3574_ = v___x_3570_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v_k_3303_);
lean_ctor_set(v_reuseFailAlloc_3578_, 2, v_v_3304_);
lean_ctor_set(v_reuseFailAlloc_3578_, 3, v_l_3537_);
lean_ctor_set(v_reuseFailAlloc_3578_, 4, v_l_3537_);
v___x_3574_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3576_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v_r_3566_);
lean_ctor_set(v___x_3308_, 3, v___x_3574_);
lean_ctor_set(v___x_3308_, 2, v_v_3568_);
lean_ctor_set(v___x_3308_, 1, v_k_3567_);
lean_ctor_set(v___x_3308_, 0, v___x_3572_);
v___x_3576_ = v___x_3308_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_k_3567_);
lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_v_3568_);
lean_ctor_set(v_reuseFailAlloc_3577_, 3, v___x_3574_);
lean_ctor_set(v_reuseFailAlloc_3577_, 4, v_r_3566_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3583_ = lean_unsigned_to_nat(2u);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v_impl_3452_);
lean_ctor_set(v___x_3308_, 3, v_r_3566_);
lean_ctor_set(v___x_3308_, 0, v___x_3583_);
v___x_3585_ = v___x_3308_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3583_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_k_3303_);
lean_ctor_set(v_reuseFailAlloc_3586_, 2, v_v_3304_);
lean_ctor_set(v_reuseFailAlloc_3586_, 3, v_r_3566_);
lean_ctor_set(v_reuseFailAlloc_3586_, 4, v_impl_3452_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
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
lean_object* v___x_3588_; lean_object* v___x_3589_; 
lean_dec_ref(v_cmp_3298_);
v___x_3588_ = lean_unsigned_to_nat(1u);
v___x_3589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
lean_ctor_set(v___x_3589_, 1, v_k_3299_);
lean_ctor_set(v___x_3589_, 2, v_v_3300_);
lean_ctor_set(v___x_3589_, 3, v_t_3301_);
lean_ctor_set(v___x_3589_, 4, v_t_3301_);
return v___x_3589_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(lean_object* v_cmp_3590_, lean_object* v_init_3591_, lean_object* v_x_3592_){
_start:
{
if (lean_obj_tag(v_x_3592_) == 0)
{
lean_object* v_k_3593_; lean_object* v_v_3594_; lean_object* v_l_3595_; lean_object* v_r_3596_; lean_object* v___x_3597_; lean_object* v_a_3598_; lean_object* v_r_3599_; 
v_k_3593_ = lean_ctor_get(v_x_3592_, 1);
lean_inc(v_k_3593_);
v_v_3594_ = lean_ctor_get(v_x_3592_, 2);
lean_inc(v_v_3594_);
v_l_3595_ = lean_ctor_get(v_x_3592_, 3);
lean_inc(v_l_3595_);
v_r_3596_ = lean_ctor_get(v_x_3592_, 4);
lean_inc(v_r_3596_);
lean_dec_ref_known(v_x_3592_, 5);
lean_inc_ref_n(v_cmp_3590_, 2);
v___x_3597_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3590_, v_init_3591_, v_l_3595_);
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref(v___x_3597_);
v_r_3599_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3590_, v_k_3593_, v_v_3594_, v_a_3598_);
v_init_3591_ = v_r_3599_;
v_x_3592_ = v_r_3596_;
goto _start;
}
else
{
lean_object* v___x_3601_; 
lean_dec_ref(v_cmp_3590_);
v___x_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3601_, 0, v_init_3591_);
return v___x_3601_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(lean_object* v_cmp_3602_, lean_object* v_k_3603_, lean_object* v_t_3604_){
_start:
{
if (lean_obj_tag(v_t_3604_) == 0)
{
lean_object* v_k_3605_; lean_object* v_l_3606_; lean_object* v_r_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; 
v_k_3605_ = lean_ctor_get(v_t_3604_, 1);
lean_inc(v_k_3605_);
v_l_3606_ = lean_ctor_get(v_t_3604_, 3);
lean_inc(v_l_3606_);
v_r_3607_ = lean_ctor_get(v_t_3604_, 4);
lean_inc(v_r_3607_);
lean_dec_ref_known(v_t_3604_, 5);
lean_inc_ref(v_cmp_3602_);
lean_inc(v_k_3603_);
v___x_3608_ = lean_apply_2(v_cmp_3602_, v_k_3603_, v_k_3605_);
v___x_3609_ = lean_unbox(v___x_3608_);
switch(v___x_3609_)
{
case 0:
{
lean_dec(v_r_3607_);
v_t_3604_ = v_l_3606_;
goto _start;
}
case 1:
{
uint8_t v___x_3611_; 
lean_dec(v_r_3607_);
lean_dec(v_l_3606_);
lean_dec(v_k_3603_);
lean_dec_ref(v_cmp_3602_);
v___x_3611_ = 1;
return v___x_3611_;
}
default: 
{
lean_dec(v_l_3606_);
v_t_3604_ = v_r_3607_;
goto _start;
}
}
}
else
{
uint8_t v___x_3613_; 
lean_dec(v_k_3603_);
lean_dec_ref(v_cmp_3602_);
v___x_3613_ = 0;
return v___x_3613_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_3614_, lean_object* v_k_3615_, lean_object* v_t_3616_){
_start:
{
uint8_t v_res_3617_; lean_object* v_r_3618_; 
v_res_3617_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3614_, v_k_3615_, v_t_3616_);
v_r_3618_ = lean_box(v_res_3617_);
return v_r_3618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(lean_object* v_cmp_3619_, lean_object* v_init_3620_, lean_object* v_x_3621_){
_start:
{
if (lean_obj_tag(v_x_3621_) == 0)
{
lean_object* v_k_3622_; lean_object* v_v_3623_; lean_object* v_l_3624_; lean_object* v_r_3625_; lean_object* v___x_3626_; lean_object* v_a_3627_; uint8_t v___x_3628_; 
v_k_3622_ = lean_ctor_get(v_x_3621_, 1);
lean_inc_n(v_k_3622_, 2);
v_v_3623_ = lean_ctor_get(v_x_3621_, 2);
lean_inc(v_v_3623_);
v_l_3624_ = lean_ctor_get(v_x_3621_, 3);
lean_inc(v_l_3624_);
v_r_3625_ = lean_ctor_get(v_x_3621_, 4);
lean_inc(v_r_3625_);
lean_dec_ref_known(v_x_3621_, 5);
lean_inc_ref_n(v_cmp_3619_, 2);
v___x_3626_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3619_, v_init_3620_, v_l_3624_);
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc_n(v_a_3627_, 2);
lean_dec_ref(v___x_3626_);
v___x_3628_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3619_, v_k_3622_, v_a_3627_);
if (v___x_3628_ == 0)
{
lean_object* v___x_3629_; 
lean_inc_ref(v_cmp_3619_);
v___x_3629_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3619_, v_k_3622_, v_v_3623_, v_a_3627_);
v_init_3620_ = v___x_3629_;
v_x_3621_ = v_r_3625_;
goto _start;
}
else
{
lean_dec(v_v_3623_);
lean_dec(v_k_3622_);
v_init_3620_ = v_a_3627_;
v_x_3621_ = v_r_3625_;
goto _start;
}
}
else
{
lean_object* v___x_3632_; 
lean_dec_ref(v_cmp_3619_);
v___x_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3632_, 0, v_init_3620_);
return v___x_3632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object* v_cmp_3633_, lean_object* v_t_u2081_3634_, lean_object* v_t_u2082_3635_){
_start:
{
lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3645_; 
if (lean_obj_tag(v_t_u2081_3634_) == 0)
{
lean_object* v_size_3648_; 
v_size_3648_ = lean_ctor_get(v_t_u2081_3634_, 0);
lean_inc(v_size_3648_);
v___y_3645_ = v_size_3648_;
goto v___jp_3644_;
}
else
{
lean_object* v___x_3649_; 
v___x_3649_ = lean_unsigned_to_nat(0u);
v___y_3645_ = v___x_3649_;
goto v___jp_3644_;
}
v___jp_3636_:
{
uint8_t v___x_3639_; 
v___x_3639_ = lean_nat_dec_le(v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec(v___y_3637_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; lean_object* v_a_3641_; 
v___x_3640_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3633_, v_t_u2081_3634_, v_t_u2082_3635_);
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref(v___x_3640_);
return v_a_3641_;
}
else
{
lean_object* v___x_3642_; lean_object* v_a_3643_; 
v___x_3642_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3633_, v_t_u2082_3635_, v_t_u2081_3634_);
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref(v___x_3642_);
return v_a_3643_;
}
}
v___jp_3644_:
{
if (lean_obj_tag(v_t_u2082_3635_) == 0)
{
lean_object* v_size_3646_; 
v_size_3646_ = lean_ctor_get(v_t_u2082_3635_, 0);
lean_inc(v_size_3646_);
v___y_3637_ = v___y_3645_;
v___y_3638_ = v_size_3646_;
goto v___jp_3636_;
}
else
{
lean_object* v___x_3647_; 
v___x_3647_ = lean_unsigned_to_nat(0u);
v___y_3637_ = v___y_3645_;
v___y_3638_ = v___x_3647_;
goto v___jp_3636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_union___redArg(lean_object* v_cmp_3650_, lean_object* v_t_u2081_3651_, lean_object* v_t_u2082_3652_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3650_, v_t_u2081_3651_, v_t_u2082_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_union(lean_object* v_00_u03b1_3654_, lean_object* v_00_u03b2_3655_, lean_object* v_cmp_3656_, lean_object* v_t_u2081_3657_, lean_object* v_t_u2082_3658_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3656_, v_t_u2081_3657_, v_t_u2082_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0(lean_object* v_00_u03b1_3660_, lean_object* v_cmp_3661_, lean_object* v_00_u03b2_3662_, lean_object* v_t_u2081_3663_, lean_object* v_t_u2082_3664_, lean_object* v_h_u2081_3665_, lean_object* v_h_u2082_3666_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3661_, v_t_u2081_3663_, v_t_u2082_3664_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0(lean_object* v_00_u03b1_3668_, lean_object* v_cmp_3669_, lean_object* v_00_u03b2_3670_, lean_object* v_k_3671_, lean_object* v_v_3672_, lean_object* v_t_3673_, lean_object* v_hl_3674_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3669_, v_k_3671_, v_v_3672_, v_t_3673_);
return v___x_3675_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1(lean_object* v_00_u03b1_3676_, lean_object* v_cmp_3677_, lean_object* v_00_u03b2_3678_, lean_object* v_k_3679_, lean_object* v_t_3680_){
_start:
{
uint8_t v___x_3681_; 
v___x_3681_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3677_, v_k_3679_, v_t_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3682_, lean_object* v_cmp_3683_, lean_object* v_00_u03b2_3684_, lean_object* v_k_3685_, lean_object* v_t_3686_){
_start:
{
uint8_t v_res_3687_; lean_object* v_r_3688_; 
v_res_3687_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1(v_00_u03b1_3682_, v_cmp_3683_, v_00_u03b2_3684_, v_k_3685_, v_t_3686_);
v_r_3688_ = lean_box(v_res_3687_);
return v_r_3688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2(lean_object* v_00_u03b1_3689_, lean_object* v_00_u03b2_3690_, lean_object* v_cmp_3691_, lean_object* v_init_3692_, lean_object* v_x_3693_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3691_, v_init_3692_, v_x_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3(lean_object* v_00_u03b1_3695_, lean_object* v_00_u03b2_3696_, lean_object* v_cmp_3697_, lean_object* v_init_3698_, lean_object* v_x_3699_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3697_, v_init_3698_, v_x_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instUnion___redArg(lean_object* v_cmp_3701_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_alloc_closure((void*)(l_Std_DTreeMap_union), 5, 3);
lean_closure_set(v___x_3702_, 0, lean_box(0));
lean_closure_set(v___x_3702_, 1, lean_box(0));
lean_closure_set(v___x_3702_, 2, v_cmp_3701_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instUnion(lean_object* v_00_u03b1_3703_, lean_object* v_00_u03b2_3704_, lean_object* v_cmp_3705_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_alloc_closure((void*)(l_Std_DTreeMap_union), 5, 3);
lean_closure_set(v___x_3706_, 0, lean_box(0));
lean_closure_set(v___x_3706_, 1, lean_box(0));
lean_closure_set(v___x_3706_, 2, v_cmp_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(lean_object* v_cmp_3707_, lean_object* v_m_u2082_3708_, lean_object* v_t_3709_){
_start:
{
if (lean_obj_tag(v_t_3709_) == 0)
{
lean_object* v_k_3710_; lean_object* v_v_3711_; lean_object* v_l_3712_; lean_object* v_r_3713_; uint8_t v___x_3714_; 
v_k_3710_ = lean_ctor_get(v_t_3709_, 1);
lean_inc_n(v_k_3710_, 2);
v_v_3711_ = lean_ctor_get(v_t_3709_, 2);
lean_inc(v_v_3711_);
v_l_3712_ = lean_ctor_get(v_t_3709_, 3);
lean_inc(v_l_3712_);
v_r_3713_ = lean_ctor_get(v_t_3709_, 4);
lean_inc(v_r_3713_);
lean_dec_ref_known(v_t_3709_, 5);
lean_inc(v_m_u2082_3708_);
lean_inc_ref(v_cmp_3707_);
v___x_3714_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3707_, v_k_3710_, v_m_u2082_3708_);
if (v___x_3714_ == 0)
{
lean_object* v_impl_3715_; lean_object* v_impl_3716_; lean_object* v___x_3717_; 
lean_dec(v_v_3711_);
lean_dec(v_k_3710_);
lean_inc(v_m_u2082_3708_);
lean_inc_ref(v_cmp_3707_);
v_impl_3715_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3707_, v_m_u2082_3708_, v_l_3712_);
v_impl_3716_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3707_, v_m_u2082_3708_, v_r_3713_);
v___x_3717_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_3715_, v_impl_3716_);
return v___x_3717_;
}
else
{
lean_object* v_impl_3718_; lean_object* v_impl_3719_; lean_object* v___x_3720_; 
lean_inc(v_m_u2082_3708_);
lean_inc_ref(v_cmp_3707_);
v_impl_3718_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3707_, v_m_u2082_3708_, v_l_3712_);
v_impl_3719_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3707_, v_m_u2082_3708_, v_r_3713_);
v___x_3720_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_3710_, v_v_3711_, v_impl_3718_, v_impl_3719_);
return v___x_3720_;
}
}
else
{
lean_dec(v_m_u2082_3708_);
lean_dec_ref(v_cmp_3707_);
return v_t_3709_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_3721_, lean_object* v_t_3722_, lean_object* v_k_3723_){
_start:
{
if (lean_obj_tag(v_t_3722_) == 0)
{
lean_object* v_k_3724_; lean_object* v_v_3725_; lean_object* v_l_3726_; lean_object* v_r_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v_k_3724_ = lean_ctor_get(v_t_3722_, 1);
lean_inc_n(v_k_3724_, 2);
v_v_3725_ = lean_ctor_get(v_t_3722_, 2);
lean_inc(v_v_3725_);
v_l_3726_ = lean_ctor_get(v_t_3722_, 3);
lean_inc(v_l_3726_);
v_r_3727_ = lean_ctor_get(v_t_3722_, 4);
lean_inc(v_r_3727_);
lean_dec_ref_known(v_t_3722_, 5);
lean_inc_ref(v_cmp_3721_);
lean_inc(v_k_3723_);
v___x_3728_ = lean_apply_2(v_cmp_3721_, v_k_3723_, v_k_3724_);
v___x_3729_ = lean_unbox(v___x_3728_);
switch(v___x_3729_)
{
case 0:
{
lean_dec(v_r_3727_);
lean_dec(v_v_3725_);
lean_dec(v_k_3724_);
v_t_3722_ = v_l_3726_;
goto _start;
}
case 1:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
lean_dec(v_r_3727_);
lean_dec(v_l_3726_);
lean_dec(v_k_3723_);
lean_dec_ref(v_cmp_3721_);
v___x_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3731_, 0, v_k_3724_);
lean_ctor_set(v___x_3731_, 1, v_v_3725_);
v___x_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
return v___x_3732_;
}
default: 
{
lean_dec(v_l_3726_);
lean_dec(v_v_3725_);
lean_dec(v_k_3724_);
v_t_3722_ = v_r_3727_;
goto _start;
}
}
}
else
{
lean_object* v___x_3734_; 
lean_dec(v_k_3723_);
lean_dec_ref(v_cmp_3721_);
v___x_3734_ = lean_box(0);
return v___x_3734_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_cmp_3735_, lean_object* v_m_u2081_3736_, lean_object* v_init_3737_, lean_object* v_x_3738_){
_start:
{
if (lean_obj_tag(v_x_3738_) == 0)
{
lean_object* v_k_3739_; lean_object* v_l_3740_; lean_object* v_r_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v_k_3739_ = lean_ctor_get(v_x_3738_, 1);
lean_inc(v_k_3739_);
v_l_3740_ = lean_ctor_get(v_x_3738_, 3);
lean_inc(v_l_3740_);
v_r_3741_ = lean_ctor_get(v_x_3738_, 4);
lean_inc(v_r_3741_);
lean_dec_ref_known(v_x_3738_, 5);
lean_inc_n(v_m_u2081_3736_, 2);
lean_inc_ref_n(v_cmp_3735_, 2);
v___x_3742_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3735_, v_m_u2081_3736_, v_init_3737_, v_l_3740_);
v___x_3743_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3735_, v_m_u2081_3736_, v_k_3739_);
if (lean_obj_tag(v___x_3743_) == 0)
{
v_init_3737_ = v___x_3742_;
v_x_3738_ = v_r_3741_;
goto _start;
}
else
{
lean_object* v_val_3745_; lean_object* v_fst_3746_; lean_object* v_snd_3747_; lean_object* v_impl_3748_; 
v_val_3745_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_val_3745_);
lean_dec_ref_known(v___x_3743_, 1);
v_fst_3746_ = lean_ctor_get(v_val_3745_, 0);
lean_inc(v_fst_3746_);
v_snd_3747_ = lean_ctor_get(v_val_3745_, 1);
lean_inc(v_snd_3747_);
lean_dec(v_val_3745_);
lean_inc_ref(v_cmp_3735_);
v_impl_3748_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3735_, v_fst_3746_, v_snd_3747_, v___x_3742_);
v_init_3737_ = v_impl_3748_;
v_x_3738_ = v_r_3741_;
goto _start;
}
}
else
{
lean_dec(v_m_u2081_3736_);
lean_dec_ref(v_cmp_3735_);
return v_init_3737_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(lean_object* v_cmp_3750_, lean_object* v_m_u2081_3751_, lean_object* v_m_u2082_3752_){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = lean_box(1);
v___x_3754_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3750_, v_m_u2081_3751_, v___x_3753_, v_m_u2082_3752_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(lean_object* v_cmp_3755_, lean_object* v_m_u2081_3756_, lean_object* v_m_u2082_3757_){
_start:
{
lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3765_; 
if (lean_obj_tag(v_m_u2081_3756_) == 0)
{
lean_object* v_size_3768_; 
v_size_3768_ = lean_ctor_get(v_m_u2081_3756_, 0);
lean_inc(v_size_3768_);
v___y_3765_ = v_size_3768_;
goto v___jp_3764_;
}
else
{
lean_object* v___x_3769_; 
v___x_3769_ = lean_unsigned_to_nat(0u);
v___y_3765_ = v___x_3769_;
goto v___jp_3764_;
}
v___jp_3758_:
{
uint8_t v___x_3761_; 
v___x_3761_ = lean_nat_dec_le(v___y_3759_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec(v___y_3759_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(v_cmp_3755_, v_m_u2081_3756_, v_m_u2082_3757_);
return v___x_3762_;
}
else
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3755_, v_m_u2082_3757_, v_m_u2081_3756_);
return v___x_3763_;
}
}
v___jp_3764_:
{
if (lean_obj_tag(v_m_u2082_3757_) == 0)
{
lean_object* v_size_3766_; 
v_size_3766_ = lean_ctor_get(v_m_u2082_3757_, 0);
lean_inc(v_size_3766_);
v___y_3759_ = v___y_3765_;
v___y_3760_ = v_size_3766_;
goto v___jp_3758_;
}
else
{
lean_object* v___x_3767_; 
v___x_3767_ = lean_unsigned_to_nat(0u);
v___y_3759_ = v___y_3765_;
v___y_3760_ = v___x_3767_;
goto v___jp_3758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_inter___redArg(lean_object* v_cmp_3770_, lean_object* v_t_u2081_3771_, lean_object* v_t_u2082_3772_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3770_, v_t_u2081_3771_, v_t_u2082_3772_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_inter(lean_object* v_00_u03b1_3774_, lean_object* v_00_u03b2_3775_, lean_object* v_cmp_3776_, lean_object* v_t_u2081_3777_, lean_object* v_t_u2082_3778_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3776_, v_t_u2081_3777_, v_t_u2082_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0(lean_object* v_00_u03b1_3780_, lean_object* v_cmp_3781_, lean_object* v_00_u03b2_3782_, lean_object* v_m_u2081_3783_, lean_object* v_m_u2082_3784_, lean_object* v_h_u2081_3785_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3781_, v_m_u2081_3783_, v_m_u2082_3784_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0(lean_object* v_00_u03b1_3787_, lean_object* v_cmp_3788_, lean_object* v_00_u03b2_3789_, lean_object* v_m_u2081_3790_, lean_object* v_m_u2082_3791_){
_start:
{
lean_object* v___x_3792_; 
v___x_3792_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(v_cmp_3788_, v_m_u2081_3790_, v_m_u2082_3791_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1(lean_object* v_00_u03b1_3793_, lean_object* v_00_u03b2_3794_, lean_object* v_cmp_3795_, lean_object* v_m_u2082_3796_, lean_object* v_t_3797_, lean_object* v_hl_3798_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3795_, v_m_u2082_3796_, v_t_3797_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3800_, lean_object* v_cmp_3801_, lean_object* v_00_u03b2_3802_, lean_object* v_t_3803_, lean_object* v_k_3804_){
_start:
{
lean_object* v___x_3805_; 
v___x_3805_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3801_, v_t_3803_, v_k_3804_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2___redArg(lean_object* v_cmp_3806_, lean_object* v_m_u2081_3807_, lean_object* v_init_3808_, lean_object* v_t_3809_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3806_, v_m_u2081_3807_, v_init_3808_, v_t_3809_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3811_, lean_object* v_00_u03b2_3812_, lean_object* v_cmp_3813_, lean_object* v_m_u2081_3814_, lean_object* v_init_3815_, lean_object* v_t_3816_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3813_, v_m_u2081_3814_, v_init_3815_, v_t_3816_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_3818_, lean_object* v_00_u03b2_3819_, lean_object* v_cmp_3820_, lean_object* v_m_u2081_3821_, lean_object* v_init_3822_, lean_object* v_x_3823_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3820_, v_m_u2081_3821_, v_init_3822_, v_x_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInter___redArg(lean_object* v_cmp_3825_){
_start:
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_alloc_closure((void*)(l_Std_DTreeMap_inter), 5, 3);
lean_closure_set(v___x_3826_, 0, lean_box(0));
lean_closure_set(v___x_3826_, 1, lean_box(0));
lean_closure_set(v___x_3826_, 2, v_cmp_3825_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInter(lean_object* v_00_u03b1_3827_, lean_object* v_00_u03b2_3828_, lean_object* v_cmp_3829_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = lean_alloc_closure((void*)(l_Std_DTreeMap_inter), 5, 3);
lean_closure_set(v___x_3830_, 0, lean_box(0));
lean_closure_set(v___x_3830_, 1, lean_box(0));
lean_closure_set(v___x_3830_, 2, v_cmp_3829_);
return v___x_3830_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_beq___redArg(lean_object* v_cmp_3831_, lean_object* v_inst_3832_, lean_object* v_t_u2081_3833_, lean_object* v_t_u2082_3834_){
_start:
{
uint8_t v___x_3835_; 
v___x_3835_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3831_, v_inst_3832_, v_t_u2081_3833_, v_t_u2082_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_beq___redArg___boxed(lean_object* v_cmp_3836_, lean_object* v_inst_3837_, lean_object* v_t_u2081_3838_, lean_object* v_t_u2082_3839_){
_start:
{
uint8_t v_res_3840_; lean_object* v_r_3841_; 
v_res_3840_ = l_Std_DTreeMap_beq___redArg(v_cmp_3836_, v_inst_3837_, v_t_u2081_3838_, v_t_u2082_3839_);
v_r_3841_ = lean_box(v_res_3840_);
return v_r_3841_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_beq(lean_object* v_00_u03b1_3842_, lean_object* v_00_u03b2_3843_, lean_object* v_cmp_3844_, lean_object* v_inst_3845_, lean_object* v_inst_3846_, lean_object* v_t_u2081_3847_, lean_object* v_t_u2082_3848_){
_start:
{
uint8_t v___x_3849_; 
v___x_3849_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3844_, v_inst_3846_, v_t_u2081_3847_, v_t_u2082_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_beq___boxed(lean_object* v_00_u03b1_3850_, lean_object* v_00_u03b2_3851_, lean_object* v_cmp_3852_, lean_object* v_inst_3853_, lean_object* v_inst_3854_, lean_object* v_t_u2081_3855_, lean_object* v_t_u2082_3856_){
_start:
{
uint8_t v_res_3857_; lean_object* v_r_3858_; 
v_res_3857_ = l_Std_DTreeMap_beq(v_00_u03b1_3850_, v_00_u03b2_3851_, v_cmp_3852_, v_inst_3853_, v_inst_3854_, v_t_u2081_3855_, v_t_u2082_3856_);
v_r_3858_ = lean_box(v_res_3857_);
return v_r_3858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instBEqOfLawfulEqCmp___redArg(lean_object* v_cmp_3859_, lean_object* v_inst_3860_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_alloc_closure((void*)(l_Std_DTreeMap_beq___boxed), 7, 5);
lean_closure_set(v___x_3861_, 0, lean_box(0));
lean_closure_set(v___x_3861_, 1, lean_box(0));
lean_closure_set(v___x_3861_, 2, v_cmp_3859_);
lean_closure_set(v___x_3861_, 3, lean_box(0));
lean_closure_set(v___x_3861_, 4, v_inst_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instBEqOfLawfulEqCmp(lean_object* v_00_u03b1_3862_, lean_object* v_00_u03b2_3863_, lean_object* v_cmp_3864_, lean_object* v_inst_3865_, lean_object* v_inst_3866_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = lean_alloc_closure((void*)(l_Std_DTreeMap_beq___boxed), 7, 5);
lean_closure_set(v___x_3867_, 0, lean_box(0));
lean_closure_set(v___x_3867_, 1, lean_box(0));
lean_closure_set(v___x_3867_, 2, v_cmp_3864_);
lean_closure_set(v___x_3867_, 3, lean_box(0));
lean_closure_set(v___x_3867_, 4, v_inst_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___redArg(lean_object* v_cmp_3868_, lean_object* v_inst_3869_, lean_object* v_t_u2081_3870_, lean_object* v_t_u2082_3871_){
_start:
{
uint8_t v___x_3872_; 
v___x_3872_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3868_, v_inst_3869_, v_t_u2081_3870_, v_t_u2082_3871_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___redArg___boxed(lean_object* v_cmp_3873_, lean_object* v_inst_3874_, lean_object* v_t_u2081_3875_, lean_object* v_t_u2082_3876_){
_start:
{
uint8_t v_res_3877_; lean_object* v_r_3878_; 
v_res_3877_ = l_Std_DTreeMap_Const_beq___redArg(v_cmp_3873_, v_inst_3874_, v_t_u2081_3875_, v_t_u2082_3876_);
v_r_3878_ = lean_box(v_res_3877_);
return v_r_3878_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq(lean_object* v_00_u03b1_3879_, lean_object* v_cmp_3880_, lean_object* v_00_u03b2_3881_, lean_object* v_inst_3882_, lean_object* v_t_u2081_3883_, lean_object* v_t_u2082_3884_){
_start:
{
uint8_t v___x_3885_; 
v___x_3885_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3880_, v_inst_3882_, v_t_u2081_3883_, v_t_u2082_3884_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___boxed(lean_object* v_00_u03b1_3886_, lean_object* v_cmp_3887_, lean_object* v_00_u03b2_3888_, lean_object* v_inst_3889_, lean_object* v_t_u2081_3890_, lean_object* v_t_u2082_3891_){
_start:
{
uint8_t v_res_3892_; lean_object* v_r_3893_; 
v_res_3892_ = l_Std_DTreeMap_Const_beq(v_00_u03b1_3886_, v_cmp_3887_, v_00_u03b2_3888_, v_inst_3889_, v_t_u2081_3890_, v_t_u2082_3891_);
v_r_3893_ = lean_box(v_res_3892_);
return v_r_3893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(lean_object* v_cmp_3894_, lean_object* v_k_3895_, lean_object* v_t_3896_){
_start:
{
if (lean_obj_tag(v_t_3896_) == 0)
{
lean_object* v_k_3897_; lean_object* v_v_3898_; lean_object* v_l_3899_; lean_object* v_r_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_4555_; 
v_k_3897_ = lean_ctor_get(v_t_3896_, 1);
v_v_3898_ = lean_ctor_get(v_t_3896_, 2);
v_l_3899_ = lean_ctor_get(v_t_3896_, 3);
v_r_3900_ = lean_ctor_get(v_t_3896_, 4);
v_isSharedCheck_4555_ = !lean_is_exclusive(v_t_3896_);
if (v_isSharedCheck_4555_ == 0)
{
lean_object* v_unused_4556_; 
v_unused_4556_ = lean_ctor_get(v_t_3896_, 0);
lean_dec(v_unused_4556_);
v___x_3902_ = v_t_3896_;
v_isShared_3903_ = v_isSharedCheck_4555_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_r_3900_);
lean_inc(v_l_3899_);
lean_inc(v_v_3898_);
lean_inc(v_k_3897_);
lean_dec(v_t_3896_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_4555_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3904_; uint8_t v___x_3905_; 
lean_inc_ref(v_cmp_3894_);
lean_inc(v_k_3897_);
lean_inc(v_k_3895_);
v___x_3904_ = lean_apply_2(v_cmp_3894_, v_k_3895_, v_k_3897_);
v___x_3905_ = lean_unbox(v___x_3904_);
switch(v___x_3905_)
{
case 0:
{
lean_object* v_impl_3906_; lean_object* v___x_3907_; 
v_impl_3906_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_3894_, v_k_3895_, v_l_3899_);
v___x_3907_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3906_) == 0)
{
if (lean_obj_tag(v_r_3900_) == 0)
{
lean_object* v_size_3908_; lean_object* v_size_3909_; lean_object* v_k_3910_; lean_object* v_v_3911_; lean_object* v_l_3912_; lean_object* v_r_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; uint8_t v___x_3916_; 
v_size_3908_ = lean_ctor_get(v_impl_3906_, 0);
lean_inc(v_size_3908_);
v_size_3909_ = lean_ctor_get(v_r_3900_, 0);
v_k_3910_ = lean_ctor_get(v_r_3900_, 1);
v_v_3911_ = lean_ctor_get(v_r_3900_, 2);
v_l_3912_ = lean_ctor_get(v_r_3900_, 3);
lean_inc(v_l_3912_);
v_r_3913_ = lean_ctor_get(v_r_3900_, 4);
v___x_3914_ = lean_unsigned_to_nat(3u);
v___x_3915_ = lean_nat_mul(v___x_3914_, v_size_3908_);
v___x_3916_ = lean_nat_dec_lt(v___x_3915_, v_size_3909_);
lean_dec(v___x_3915_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3920_; 
lean_dec(v_l_3912_);
v___x_3917_ = lean_nat_add(v___x_3907_, v_size_3908_);
lean_dec(v_size_3908_);
v___x_3918_ = lean_nat_add(v___x_3917_, v_size_3909_);
lean_dec(v___x_3917_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 3, v_impl_3906_);
lean_ctor_set(v___x_3902_, 0, v___x_3918_);
v___x_3920_ = v___x_3902_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_3921_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_3921_, 3, v_impl_3906_);
lean_ctor_set(v_reuseFailAlloc_3921_, 4, v_r_3900_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
else
{
lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3985_; 
lean_inc(v_r_3913_);
lean_inc(v_v_3911_);
lean_inc(v_k_3910_);
lean_inc(v_size_3909_);
v_isSharedCheck_3985_ = !lean_is_exclusive(v_r_3900_);
if (v_isSharedCheck_3985_ == 0)
{
lean_object* v_unused_3986_; lean_object* v_unused_3987_; lean_object* v_unused_3988_; lean_object* v_unused_3989_; lean_object* v_unused_3990_; 
v_unused_3986_ = lean_ctor_get(v_r_3900_, 4);
lean_dec(v_unused_3986_);
v_unused_3987_ = lean_ctor_get(v_r_3900_, 3);
lean_dec(v_unused_3987_);
v_unused_3988_ = lean_ctor_get(v_r_3900_, 2);
lean_dec(v_unused_3988_);
v_unused_3989_ = lean_ctor_get(v_r_3900_, 1);
lean_dec(v_unused_3989_);
v_unused_3990_ = lean_ctor_get(v_r_3900_, 0);
lean_dec(v_unused_3990_);
v___x_3923_ = v_r_3900_;
v_isShared_3924_ = v_isSharedCheck_3985_;
goto v_resetjp_3922_;
}
else
{
lean_dec(v_r_3900_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3985_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v_size_3925_; lean_object* v_k_3926_; lean_object* v_v_3927_; lean_object* v_l_3928_; lean_object* v_r_3929_; lean_object* v_size_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; uint8_t v___x_3933_; 
v_size_3925_ = lean_ctor_get(v_l_3912_, 0);
v_k_3926_ = lean_ctor_get(v_l_3912_, 1);
v_v_3927_ = lean_ctor_get(v_l_3912_, 2);
v_l_3928_ = lean_ctor_get(v_l_3912_, 3);
v_r_3929_ = lean_ctor_get(v_l_3912_, 4);
v_size_3930_ = lean_ctor_get(v_r_3913_, 0);
v___x_3931_ = lean_unsigned_to_nat(2u);
v___x_3932_ = lean_nat_mul(v___x_3931_, v_size_3930_);
v___x_3933_ = lean_nat_dec_lt(v_size_3925_, v___x_3932_);
lean_dec(v___x_3932_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3961_; 
lean_inc(v_r_3929_);
lean_inc(v_l_3928_);
lean_inc(v_v_3927_);
lean_inc(v_k_3926_);
v_isSharedCheck_3961_ = !lean_is_exclusive(v_l_3912_);
if (v_isSharedCheck_3961_ == 0)
{
lean_object* v_unused_3962_; lean_object* v_unused_3963_; lean_object* v_unused_3964_; lean_object* v_unused_3965_; lean_object* v_unused_3966_; 
v_unused_3962_ = lean_ctor_get(v_l_3912_, 4);
lean_dec(v_unused_3962_);
v_unused_3963_ = lean_ctor_get(v_l_3912_, 3);
lean_dec(v_unused_3963_);
v_unused_3964_ = lean_ctor_get(v_l_3912_, 2);
lean_dec(v_unused_3964_);
v_unused_3965_ = lean_ctor_get(v_l_3912_, 1);
lean_dec(v_unused_3965_);
v_unused_3966_ = lean_ctor_get(v_l_3912_, 0);
lean_dec(v_unused_3966_);
v___x_3935_ = v_l_3912_;
v_isShared_3936_ = v_isSharedCheck_3961_;
goto v_resetjp_3934_;
}
else
{
lean_dec(v_l_3912_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3961_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3951_; 
v___x_3937_ = lean_nat_add(v___x_3907_, v_size_3908_);
lean_dec(v_size_3908_);
v___x_3938_ = lean_nat_add(v___x_3937_, v_size_3909_);
lean_dec(v_size_3909_);
if (lean_obj_tag(v_l_3928_) == 0)
{
lean_object* v_size_3959_; 
v_size_3959_ = lean_ctor_get(v_l_3928_, 0);
lean_inc(v_size_3959_);
v___y_3951_ = v_size_3959_;
goto v___jp_3950_;
}
else
{
lean_object* v___x_3960_; 
v___x_3960_ = lean_unsigned_to_nat(0u);
v___y_3951_ = v___x_3960_;
goto v___jp_3950_;
}
v___jp_3939_:
{
lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3943_ = lean_nat_add(v___y_3940_, v___y_3942_);
lean_dec(v___y_3942_);
lean_dec(v___y_3940_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 4, v_r_3913_);
lean_ctor_set(v___x_3935_, 3, v_r_3929_);
lean_ctor_set(v___x_3935_, 2, v_v_3911_);
lean_ctor_set(v___x_3935_, 1, v_k_3910_);
lean_ctor_set(v___x_3935_, 0, v___x_3943_);
v___x_3945_ = v___x_3935_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3943_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v_k_3910_);
lean_ctor_set(v_reuseFailAlloc_3949_, 2, v_v_3911_);
lean_ctor_set(v_reuseFailAlloc_3949_, 3, v_r_3929_);
lean_ctor_set(v_reuseFailAlloc_3949_, 4, v_r_3913_);
v___x_3945_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
lean_object* v___x_3947_; 
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v___x_3945_);
lean_ctor_set(v___x_3923_, 3, v___y_3941_);
lean_ctor_set(v___x_3923_, 2, v_v_3927_);
lean_ctor_set(v___x_3923_, 1, v_k_3926_);
lean_ctor_set(v___x_3923_, 0, v___x_3938_);
v___x_3947_ = v___x_3923_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3938_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_k_3926_);
lean_ctor_set(v_reuseFailAlloc_3948_, 2, v_v_3927_);
lean_ctor_set(v_reuseFailAlloc_3948_, 3, v___y_3941_);
lean_ctor_set(v_reuseFailAlloc_3948_, 4, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
v___jp_3950_:
{
lean_object* v___x_3952_; lean_object* v___x_3954_; 
v___x_3952_ = lean_nat_add(v___x_3937_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec(v___x_3937_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v_l_3928_);
lean_ctor_set(v___x_3902_, 3, v_impl_3906_);
lean_ctor_set(v___x_3902_, 0, v___x_3952_);
v___x_3954_ = v___x_3902_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3952_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_3958_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_3958_, 3, v_impl_3906_);
lean_ctor_set(v_reuseFailAlloc_3958_, 4, v_l_3928_);
v___x_3954_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_object* v___x_3955_; 
v___x_3955_ = lean_nat_add(v___x_3907_, v_size_3930_);
if (lean_obj_tag(v_r_3929_) == 0)
{
lean_object* v_size_3956_; 
v_size_3956_ = lean_ctor_get(v_r_3929_, 0);
lean_inc(v_size_3956_);
v___y_3940_ = v___x_3955_;
v___y_3941_ = v___x_3954_;
v___y_3942_ = v_size_3956_;
goto v___jp_3939_;
}
else
{
lean_object* v___x_3957_; 
v___x_3957_ = lean_unsigned_to_nat(0u);
v___y_3940_ = v___x_3955_;
v___y_3941_ = v___x_3954_;
v___y_3942_ = v___x_3957_;
goto v___jp_3939_;
}
}
}
}
}
else
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3971_; 
lean_del_object(v___x_3902_);
v___x_3967_ = lean_nat_add(v___x_3907_, v_size_3908_);
lean_dec(v_size_3908_);
v___x_3968_ = lean_nat_add(v___x_3967_, v_size_3909_);
lean_dec(v_size_3909_);
v___x_3969_ = lean_nat_add(v___x_3967_, v_size_3925_);
lean_dec(v___x_3967_);
lean_inc_ref(v_impl_3906_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v_l_3912_);
lean_ctor_set(v___x_3923_, 3, v_impl_3906_);
lean_ctor_set(v___x_3923_, 2, v_v_3898_);
lean_ctor_set(v___x_3923_, 1, v_k_3897_);
lean_ctor_set(v___x_3923_, 0, v___x_3969_);
v___x_3971_ = v___x_3923_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3969_);
lean_ctor_set(v_reuseFailAlloc_3984_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_3984_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_3984_, 3, v_impl_3906_);
lean_ctor_set(v_reuseFailAlloc_3984_, 4, v_l_3912_);
v___x_3971_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
v_isSharedCheck_3978_ = !lean_is_exclusive(v_impl_3906_);
if (v_isSharedCheck_3978_ == 0)
{
lean_object* v_unused_3979_; lean_object* v_unused_3980_; lean_object* v_unused_3981_; lean_object* v_unused_3982_; lean_object* v_unused_3983_; 
v_unused_3979_ = lean_ctor_get(v_impl_3906_, 4);
lean_dec(v_unused_3979_);
v_unused_3980_ = lean_ctor_get(v_impl_3906_, 3);
lean_dec(v_unused_3980_);
v_unused_3981_ = lean_ctor_get(v_impl_3906_, 2);
lean_dec(v_unused_3981_);
v_unused_3982_ = lean_ctor_get(v_impl_3906_, 1);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_impl_3906_, 0);
lean_dec(v_unused_3983_);
v___x_3973_ = v_impl_3906_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_dec(v_impl_3906_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 4, v_r_3913_);
lean_ctor_set(v___x_3973_, 3, v___x_3971_);
lean_ctor_set(v___x_3973_, 2, v_v_3911_);
lean_ctor_set(v___x_3973_, 1, v_k_3910_);
lean_ctor_set(v___x_3973_, 0, v___x_3968_);
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3968_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_k_3910_);
lean_ctor_set(v_reuseFailAlloc_3977_, 2, v_v_3911_);
lean_ctor_set(v_reuseFailAlloc_3977_, 3, v___x_3971_);
lean_ctor_set(v_reuseFailAlloc_3977_, 4, v_r_3913_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3991_; lean_object* v___x_3992_; lean_object* v___x_3994_; 
v_size_3991_ = lean_ctor_get(v_impl_3906_, 0);
lean_inc(v_size_3991_);
v___x_3992_ = lean_nat_add(v___x_3907_, v_size_3991_);
lean_dec(v_size_3991_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 3, v_impl_3906_);
lean_ctor_set(v___x_3902_, 0, v___x_3992_);
v___x_3994_ = v___x_3902_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3992_);
lean_ctor_set(v_reuseFailAlloc_3995_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_3995_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_3995_, 3, v_impl_3906_);
lean_ctor_set(v_reuseFailAlloc_3995_, 4, v_r_3900_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
else
{
if (lean_obj_tag(v_r_3900_) == 0)
{
lean_object* v_l_3996_; 
v_l_3996_ = lean_ctor_get(v_r_3900_, 3);
lean_inc(v_l_3996_);
if (lean_obj_tag(v_l_3996_) == 0)
{
lean_object* v_r_3997_; 
v_r_3997_ = lean_ctor_get(v_r_3900_, 4);
lean_inc(v_r_3997_);
if (lean_obj_tag(v_r_3997_) == 0)
{
lean_object* v_size_3998_; lean_object* v_k_3999_; lean_object* v_v_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4013_; 
v_size_3998_ = lean_ctor_get(v_r_3900_, 0);
v_k_3999_ = lean_ctor_get(v_r_3900_, 1);
v_v_4000_ = lean_ctor_get(v_r_3900_, 2);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_r_3900_);
if (v_isSharedCheck_4013_ == 0)
{
lean_object* v_unused_4014_; lean_object* v_unused_4015_; 
v_unused_4014_ = lean_ctor_get(v_r_3900_, 4);
lean_dec(v_unused_4014_);
v_unused_4015_ = lean_ctor_get(v_r_3900_, 3);
lean_dec(v_unused_4015_);
v___x_4002_ = v_r_3900_;
v_isShared_4003_ = v_isSharedCheck_4013_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_v_4000_);
lean_inc(v_k_3999_);
lean_inc(v_size_3998_);
lean_dec(v_r_3900_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4013_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v_size_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4008_; 
v_size_4004_ = lean_ctor_get(v_l_3996_, 0);
v___x_4005_ = lean_nat_add(v___x_3907_, v_size_3998_);
lean_dec(v_size_3998_);
v___x_4006_ = lean_nat_add(v___x_3907_, v_size_4004_);
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 4, v_l_3996_);
lean_ctor_set(v___x_4002_, 3, v_impl_3906_);
lean_ctor_set(v___x_4002_, 2, v_v_3898_);
lean_ctor_set(v___x_4002_, 1, v_k_3897_);
lean_ctor_set(v___x_4002_, 0, v___x_4006_);
v___x_4008_ = v___x_4002_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4006_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4012_, 3, v_impl_3906_);
lean_ctor_set(v_reuseFailAlloc_4012_, 4, v_l_3996_);
v___x_4008_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
lean_object* v___x_4010_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v_r_3997_);
lean_ctor_set(v___x_3902_, 3, v___x_4008_);
lean_ctor_set(v___x_3902_, 2, v_v_4000_);
lean_ctor_set(v___x_3902_, 1, v_k_3999_);
lean_ctor_set(v___x_3902_, 0, v___x_4005_);
v___x_4010_ = v___x_3902_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4005_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v_k_3999_);
lean_ctor_set(v_reuseFailAlloc_4011_, 2, v_v_4000_);
lean_ctor_set(v_reuseFailAlloc_4011_, 3, v___x_4008_);
lean_ctor_set(v_reuseFailAlloc_4011_, 4, v_r_3997_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
else
{
lean_object* v_k_4016_; lean_object* v_v_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4040_; 
v_k_4016_ = lean_ctor_get(v_r_3900_, 1);
v_v_4017_ = lean_ctor_get(v_r_3900_, 2);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_r_3900_);
if (v_isSharedCheck_4040_ == 0)
{
lean_object* v_unused_4041_; lean_object* v_unused_4042_; lean_object* v_unused_4043_; 
v_unused_4041_ = lean_ctor_get(v_r_3900_, 4);
lean_dec(v_unused_4041_);
v_unused_4042_ = lean_ctor_get(v_r_3900_, 3);
lean_dec(v_unused_4042_);
v_unused_4043_ = lean_ctor_get(v_r_3900_, 0);
lean_dec(v_unused_4043_);
v___x_4019_ = v_r_3900_;
v_isShared_4020_ = v_isSharedCheck_4040_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_v_4017_);
lean_inc(v_k_4016_);
lean_dec(v_r_3900_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4040_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v_k_4021_; lean_object* v_v_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4036_; 
v_k_4021_ = lean_ctor_get(v_l_3996_, 1);
v_v_4022_ = lean_ctor_get(v_l_3996_, 2);
v_isSharedCheck_4036_ = !lean_is_exclusive(v_l_3996_);
if (v_isSharedCheck_4036_ == 0)
{
lean_object* v_unused_4037_; lean_object* v_unused_4038_; lean_object* v_unused_4039_; 
v_unused_4037_ = lean_ctor_get(v_l_3996_, 4);
lean_dec(v_unused_4037_);
v_unused_4038_ = lean_ctor_get(v_l_3996_, 3);
lean_dec(v_unused_4038_);
v_unused_4039_ = lean_ctor_get(v_l_3996_, 0);
lean_dec(v_unused_4039_);
v___x_4024_ = v_l_3996_;
v_isShared_4025_ = v_isSharedCheck_4036_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_v_4022_);
lean_inc(v_k_4021_);
lean_dec(v_l_3996_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4036_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4026_; lean_object* v___x_4028_; 
v___x_4026_ = lean_unsigned_to_nat(3u);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 4, v_r_3997_);
lean_ctor_set(v___x_4024_, 3, v_r_3997_);
lean_ctor_set(v___x_4024_, 2, v_v_3898_);
lean_ctor_set(v___x_4024_, 1, v_k_3897_);
lean_ctor_set(v___x_4024_, 0, v___x_3907_);
v___x_4028_ = v___x_4024_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_3907_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4035_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4035_, 3, v_r_3997_);
lean_ctor_set(v_reuseFailAlloc_4035_, 4, v_r_3997_);
v___x_4028_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4030_; 
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 3, v_r_3997_);
lean_ctor_set(v___x_4019_, 0, v___x_3907_);
v___x_4030_ = v___x_4019_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_3907_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v_k_4016_);
lean_ctor_set(v_reuseFailAlloc_4034_, 2, v_v_4017_);
lean_ctor_set(v_reuseFailAlloc_4034_, 3, v_r_3997_);
lean_ctor_set(v_reuseFailAlloc_4034_, 4, v_r_3997_);
v___x_4030_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4032_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v___x_4030_);
lean_ctor_set(v___x_3902_, 3, v___x_4028_);
lean_ctor_set(v___x_3902_, 2, v_v_4022_);
lean_ctor_set(v___x_3902_, 1, v_k_4021_);
lean_ctor_set(v___x_3902_, 0, v___x_4026_);
v___x_4032_ = v___x_3902_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4026_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_k_4021_);
lean_ctor_set(v_reuseFailAlloc_4033_, 2, v_v_4022_);
lean_ctor_set(v_reuseFailAlloc_4033_, 3, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4033_, 4, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_4044_; 
v_r_4044_ = lean_ctor_get(v_r_3900_, 4);
lean_inc(v_r_4044_);
if (lean_obj_tag(v_r_4044_) == 0)
{
lean_object* v_k_4045_; lean_object* v_v_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4057_; 
v_k_4045_ = lean_ctor_get(v_r_3900_, 1);
v_v_4046_ = lean_ctor_get(v_r_3900_, 2);
v_isSharedCheck_4057_ = !lean_is_exclusive(v_r_3900_);
if (v_isSharedCheck_4057_ == 0)
{
lean_object* v_unused_4058_; lean_object* v_unused_4059_; lean_object* v_unused_4060_; 
v_unused_4058_ = lean_ctor_get(v_r_3900_, 4);
lean_dec(v_unused_4058_);
v_unused_4059_ = lean_ctor_get(v_r_3900_, 3);
lean_dec(v_unused_4059_);
v_unused_4060_ = lean_ctor_get(v_r_3900_, 0);
lean_dec(v_unused_4060_);
v___x_4048_ = v_r_3900_;
v_isShared_4049_ = v_isSharedCheck_4057_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_v_4046_);
lean_inc(v_k_4045_);
lean_dec(v_r_3900_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4057_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4050_; lean_object* v___x_4052_; 
v___x_4050_ = lean_unsigned_to_nat(3u);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 4, v_l_3996_);
lean_ctor_set(v___x_4048_, 2, v_v_3898_);
lean_ctor_set(v___x_4048_, 1, v_k_3897_);
lean_ctor_set(v___x_4048_, 0, v___x_3907_);
v___x_4052_ = v___x_4048_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_3907_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4056_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4056_, 3, v_l_3996_);
lean_ctor_set(v_reuseFailAlloc_4056_, 4, v_l_3996_);
v___x_4052_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4054_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v_r_4044_);
lean_ctor_set(v___x_3902_, 3, v___x_4052_);
lean_ctor_set(v___x_3902_, 2, v_v_4046_);
lean_ctor_set(v___x_3902_, 1, v_k_4045_);
lean_ctor_set(v___x_3902_, 0, v___x_4050_);
v___x_4054_ = v___x_3902_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4050_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v_k_4045_);
lean_ctor_set(v_reuseFailAlloc_4055_, 2, v_v_4046_);
lean_ctor_set(v_reuseFailAlloc_4055_, 3, v___x_4052_);
lean_ctor_set(v_reuseFailAlloc_4055_, 4, v_r_4044_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
else
{
lean_object* v_size_4061_; lean_object* v_k_4062_; lean_object* v_v_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4074_; 
v_size_4061_ = lean_ctor_get(v_r_3900_, 0);
v_k_4062_ = lean_ctor_get(v_r_3900_, 1);
v_v_4063_ = lean_ctor_get(v_r_3900_, 2);
v_isSharedCheck_4074_ = !lean_is_exclusive(v_r_3900_);
if (v_isSharedCheck_4074_ == 0)
{
lean_object* v_unused_4075_; lean_object* v_unused_4076_; 
v_unused_4075_ = lean_ctor_get(v_r_3900_, 4);
lean_dec(v_unused_4075_);
v_unused_4076_ = lean_ctor_get(v_r_3900_, 3);
lean_dec(v_unused_4076_);
v___x_4065_ = v_r_3900_;
v_isShared_4066_ = v_isSharedCheck_4074_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_v_4063_);
lean_inc(v_k_4062_);
lean_inc(v_size_4061_);
lean_dec(v_r_3900_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4074_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 3, v_r_4044_);
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_size_4061_);
lean_ctor_set(v_reuseFailAlloc_4073_, 1, v_k_4062_);
lean_ctor_set(v_reuseFailAlloc_4073_, 2, v_v_4063_);
lean_ctor_set(v_reuseFailAlloc_4073_, 3, v_r_4044_);
lean_ctor_set(v_reuseFailAlloc_4073_, 4, v_r_4044_);
v___x_4068_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
lean_object* v___x_4069_; lean_object* v___x_4071_; 
v___x_4069_ = lean_unsigned_to_nat(2u);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v___x_4068_);
lean_ctor_set(v___x_3902_, 3, v_r_4044_);
lean_ctor_set(v___x_3902_, 0, v___x_4069_);
v___x_4071_ = v___x_3902_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v___x_4069_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4072_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4072_, 3, v_r_4044_);
lean_ctor_set(v_reuseFailAlloc_4072_, 4, v___x_4068_);
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
lean_object* v___x_4078_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 3, v_r_3900_);
lean_ctor_set(v___x_3902_, 0, v___x_3907_);
v___x_4078_ = v___x_3902_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_3907_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4079_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4079_, 3, v_r_3900_);
lean_ctor_set(v_reuseFailAlloc_4079_, 4, v_r_3900_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3902_);
lean_dec(v_v_3898_);
lean_dec(v_k_3897_);
lean_dec(v_k_3895_);
lean_dec_ref(v_cmp_3894_);
if (lean_obj_tag(v_l_3899_) == 0)
{
if (lean_obj_tag(v_r_3900_) == 0)
{
lean_object* v_size_4080_; lean_object* v_k_4081_; lean_object* v_v_4082_; lean_object* v_l_4083_; lean_object* v_r_4084_; lean_object* v_size_4085_; lean_object* v_k_4086_; lean_object* v_v_4087_; lean_object* v_l_4088_; lean_object* v_r_4089_; lean_object* v___x_4090_; uint8_t v___x_4091_; 
v_size_4080_ = lean_ctor_get(v_l_3899_, 0);
v_k_4081_ = lean_ctor_get(v_l_3899_, 1);
v_v_4082_ = lean_ctor_get(v_l_3899_, 2);
v_l_4083_ = lean_ctor_get(v_l_3899_, 3);
v_r_4084_ = lean_ctor_get(v_l_3899_, 4);
lean_inc(v_r_4084_);
v_size_4085_ = lean_ctor_get(v_r_3900_, 0);
v_k_4086_ = lean_ctor_get(v_r_3900_, 1);
v_v_4087_ = lean_ctor_get(v_r_3900_, 2);
v_l_4088_ = lean_ctor_get(v_r_3900_, 3);
lean_inc(v_l_4088_);
v_r_4089_ = lean_ctor_get(v_r_3900_, 4);
v___x_4090_ = lean_unsigned_to_nat(1u);
v___x_4091_ = lean_nat_dec_lt(v_size_4080_, v_size_4085_);
if (v___x_4091_ == 0)
{
lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4227_; 
lean_inc(v_l_4083_);
lean_inc(v_v_4082_);
lean_inc(v_k_4081_);
v_isSharedCheck_4227_ = !lean_is_exclusive(v_l_3899_);
if (v_isSharedCheck_4227_ == 0)
{
lean_object* v_unused_4228_; lean_object* v_unused_4229_; lean_object* v_unused_4230_; lean_object* v_unused_4231_; lean_object* v_unused_4232_; 
v_unused_4228_ = lean_ctor_get(v_l_3899_, 4);
lean_dec(v_unused_4228_);
v_unused_4229_ = lean_ctor_get(v_l_3899_, 3);
lean_dec(v_unused_4229_);
v_unused_4230_ = lean_ctor_get(v_l_3899_, 2);
lean_dec(v_unused_4230_);
v_unused_4231_ = lean_ctor_get(v_l_3899_, 1);
lean_dec(v_unused_4231_);
v_unused_4232_ = lean_ctor_get(v_l_3899_, 0);
lean_dec(v_unused_4232_);
v___x_4093_ = v_l_3899_;
v_isShared_4094_ = v_isSharedCheck_4227_;
goto v_resetjp_4092_;
}
else
{
lean_dec(v_l_3899_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4227_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4095_; lean_object* v_tree_4096_; 
v___x_4095_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_4081_, v_v_4082_, v_l_4083_, v_r_4084_);
v_tree_4096_ = lean_ctor_get(v___x_4095_, 2);
lean_inc(v_tree_4096_);
if (lean_obj_tag(v_tree_4096_) == 0)
{
lean_object* v_k_4097_; lean_object* v_v_4098_; lean_object* v_size_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; uint8_t v___x_4102_; 
v_k_4097_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_k_4097_);
v_v_4098_ = lean_ctor_get(v___x_4095_, 1);
lean_inc(v_v_4098_);
lean_dec_ref(v___x_4095_);
v_size_4099_ = lean_ctor_get(v_tree_4096_, 0);
v___x_4100_ = lean_unsigned_to_nat(3u);
v___x_4101_ = lean_nat_mul(v___x_4100_, v_size_4099_);
v___x_4102_ = lean_nat_dec_lt(v___x_4101_, v_size_4085_);
lean_dec(v___x_4101_);
if (v___x_4102_ == 0)
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4106_; 
lean_dec(v_l_4088_);
v___x_4103_ = lean_nat_add(v___x_4090_, v_size_4099_);
v___x_4104_ = lean_nat_add(v___x_4103_, v_size_4085_);
lean_dec(v___x_4103_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 4, v_r_3900_);
lean_ctor_set(v___x_4093_, 3, v_tree_4096_);
lean_ctor_set(v___x_4093_, 2, v_v_4098_);
lean_ctor_set(v___x_4093_, 1, v_k_4097_);
lean_ctor_set(v___x_4093_, 0, v___x_4104_);
v___x_4106_ = v___x_4093_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4104_);
lean_ctor_set(v_reuseFailAlloc_4107_, 1, v_k_4097_);
lean_ctor_set(v_reuseFailAlloc_4107_, 2, v_v_4098_);
lean_ctor_set(v_reuseFailAlloc_4107_, 3, v_tree_4096_);
lean_ctor_set(v_reuseFailAlloc_4107_, 4, v_r_3900_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
else
{
lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4162_; 
lean_inc(v_r_4089_);
lean_inc(v_v_4087_);
lean_inc(v_k_4086_);
lean_inc(v_size_4085_);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_r_3900_);
if (v_isSharedCheck_4162_ == 0)
{
lean_object* v_unused_4163_; lean_object* v_unused_4164_; lean_object* v_unused_4165_; lean_object* v_unused_4166_; lean_object* v_unused_4167_; 
v_unused_4163_ = lean_ctor_get(v_r_3900_, 4);
lean_dec(v_unused_4163_);
v_unused_4164_ = lean_ctor_get(v_r_3900_, 3);
lean_dec(v_unused_4164_);
v_unused_4165_ = lean_ctor_get(v_r_3900_, 2);
lean_dec(v_unused_4165_);
v_unused_4166_ = lean_ctor_get(v_r_3900_, 1);
lean_dec(v_unused_4166_);
v_unused_4167_ = lean_ctor_get(v_r_3900_, 0);
lean_dec(v_unused_4167_);
v___x_4109_ = v_r_3900_;
v_isShared_4110_ = v_isSharedCheck_4162_;
goto v_resetjp_4108_;
}
else
{
lean_dec(v_r_3900_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4162_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v_size_4111_; lean_object* v_k_4112_; lean_object* v_v_4113_; lean_object* v_l_4114_; lean_object* v_r_4115_; lean_object* v_size_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; uint8_t v___x_4119_; 
v_size_4111_ = lean_ctor_get(v_l_4088_, 0);
v_k_4112_ = lean_ctor_get(v_l_4088_, 1);
v_v_4113_ = lean_ctor_get(v_l_4088_, 2);
v_l_4114_ = lean_ctor_get(v_l_4088_, 3);
v_r_4115_ = lean_ctor_get(v_l_4088_, 4);
v_size_4116_ = lean_ctor_get(v_r_4089_, 0);
v___x_4117_ = lean_unsigned_to_nat(2u);
v___x_4118_ = lean_nat_mul(v___x_4117_, v_size_4116_);
v___x_4119_ = lean_nat_dec_lt(v_size_4111_, v___x_4118_);
lean_dec(v___x_4118_);
if (v___x_4119_ == 0)
{
lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4147_; 
lean_inc(v_r_4115_);
lean_inc(v_l_4114_);
lean_inc(v_v_4113_);
lean_inc(v_k_4112_);
v_isSharedCheck_4147_ = !lean_is_exclusive(v_l_4088_);
if (v_isSharedCheck_4147_ == 0)
{
lean_object* v_unused_4148_; lean_object* v_unused_4149_; lean_object* v_unused_4150_; lean_object* v_unused_4151_; lean_object* v_unused_4152_; 
v_unused_4148_ = lean_ctor_get(v_l_4088_, 4);
lean_dec(v_unused_4148_);
v_unused_4149_ = lean_ctor_get(v_l_4088_, 3);
lean_dec(v_unused_4149_);
v_unused_4150_ = lean_ctor_get(v_l_4088_, 2);
lean_dec(v_unused_4150_);
v_unused_4151_ = lean_ctor_get(v_l_4088_, 1);
lean_dec(v_unused_4151_);
v_unused_4152_ = lean_ctor_get(v_l_4088_, 0);
lean_dec(v_unused_4152_);
v___x_4121_ = v_l_4088_;
v_isShared_4122_ = v_isSharedCheck_4147_;
goto v_resetjp_4120_;
}
else
{
lean_dec(v_l_4088_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4147_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4137_; 
v___x_4123_ = lean_nat_add(v___x_4090_, v_size_4099_);
v___x_4124_ = lean_nat_add(v___x_4123_, v_size_4085_);
lean_dec(v_size_4085_);
if (lean_obj_tag(v_l_4114_) == 0)
{
lean_object* v_size_4145_; 
v_size_4145_ = lean_ctor_get(v_l_4114_, 0);
lean_inc(v_size_4145_);
v___y_4137_ = v_size_4145_;
goto v___jp_4136_;
}
else
{
lean_object* v___x_4146_; 
v___x_4146_ = lean_unsigned_to_nat(0u);
v___y_4137_ = v___x_4146_;
goto v___jp_4136_;
}
v___jp_4125_:
{
lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4129_ = lean_nat_add(v___y_4126_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec(v___y_4126_);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 4, v_r_4089_);
lean_ctor_set(v___x_4121_, 3, v_r_4115_);
lean_ctor_set(v___x_4121_, 2, v_v_4087_);
lean_ctor_set(v___x_4121_, 1, v_k_4086_);
lean_ctor_set(v___x_4121_, 0, v___x_4129_);
v___x_4131_ = v___x_4121_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4135_, 1, v_k_4086_);
lean_ctor_set(v_reuseFailAlloc_4135_, 2, v_v_4087_);
lean_ctor_set(v_reuseFailAlloc_4135_, 3, v_r_4115_);
lean_ctor_set(v_reuseFailAlloc_4135_, 4, v_r_4089_);
v___x_4131_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
lean_object* v___x_4133_; 
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 4, v___x_4131_);
lean_ctor_set(v___x_4109_, 3, v___y_4127_);
lean_ctor_set(v___x_4109_, 2, v_v_4113_);
lean_ctor_set(v___x_4109_, 1, v_k_4112_);
lean_ctor_set(v___x_4109_, 0, v___x_4124_);
v___x_4133_ = v___x_4109_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4134_, 1, v_k_4112_);
lean_ctor_set(v_reuseFailAlloc_4134_, 2, v_v_4113_);
lean_ctor_set(v_reuseFailAlloc_4134_, 3, v___y_4127_);
lean_ctor_set(v_reuseFailAlloc_4134_, 4, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
v___jp_4136_:
{
lean_object* v___x_4138_; lean_object* v___x_4140_; 
v___x_4138_ = lean_nat_add(v___x_4123_, v___y_4137_);
lean_dec(v___y_4137_);
lean_dec(v___x_4123_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 4, v_l_4114_);
lean_ctor_set(v___x_4093_, 3, v_tree_4096_);
lean_ctor_set(v___x_4093_, 2, v_v_4098_);
lean_ctor_set(v___x_4093_, 1, v_k_4097_);
lean_ctor_set(v___x_4093_, 0, v___x_4138_);
v___x_4140_ = v___x_4093_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4138_);
lean_ctor_set(v_reuseFailAlloc_4144_, 1, v_k_4097_);
lean_ctor_set(v_reuseFailAlloc_4144_, 2, v_v_4098_);
lean_ctor_set(v_reuseFailAlloc_4144_, 3, v_tree_4096_);
lean_ctor_set(v_reuseFailAlloc_4144_, 4, v_l_4114_);
v___x_4140_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
lean_object* v___x_4141_; 
v___x_4141_ = lean_nat_add(v___x_4090_, v_size_4116_);
if (lean_obj_tag(v_r_4115_) == 0)
{
lean_object* v_size_4142_; 
v_size_4142_ = lean_ctor_get(v_r_4115_, 0);
lean_inc(v_size_4142_);
v___y_4126_ = v___x_4141_;
v___y_4127_ = v___x_4140_;
v___y_4128_ = v_size_4142_;
goto v___jp_4125_;
}
else
{
lean_object* v___x_4143_; 
v___x_4143_ = lean_unsigned_to_nat(0u);
v___y_4126_ = v___x_4141_;
v___y_4127_ = v___x_4140_;
v___y_4128_ = v___x_4143_;
goto v___jp_4125_;
}
}
}
}
}
else
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4157_; 
v___x_4153_ = lean_nat_add(v___x_4090_, v_size_4099_);
v___x_4154_ = lean_nat_add(v___x_4153_, v_size_4085_);
lean_dec(v_size_4085_);
v___x_4155_ = lean_nat_add(v___x_4153_, v_size_4111_);
lean_dec(v___x_4153_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 4, v_l_4088_);
lean_ctor_set(v___x_4109_, 3, v_tree_4096_);
lean_ctor_set(v___x_4109_, 2, v_v_4098_);
lean_ctor_set(v___x_4109_, 1, v_k_4097_);
lean_ctor_set(v___x_4109_, 0, v___x_4155_);
v___x_4157_ = v___x_4109_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4155_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v_k_4097_);
lean_ctor_set(v_reuseFailAlloc_4161_, 2, v_v_4098_);
lean_ctor_set(v_reuseFailAlloc_4161_, 3, v_tree_4096_);
lean_ctor_set(v_reuseFailAlloc_4161_, 4, v_l_4088_);
v___x_4157_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4159_; 
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 4, v_r_4089_);
lean_ctor_set(v___x_4093_, 3, v___x_4157_);
lean_ctor_set(v___x_4093_, 2, v_v_4087_);
lean_ctor_set(v___x_4093_, 1, v_k_4086_);
lean_ctor_set(v___x_4093_, 0, v___x_4154_);
v___x_4159_ = v___x_4093_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4154_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v_k_4086_);
lean_ctor_set(v_reuseFailAlloc_4160_, 2, v_v_4087_);
lean_ctor_set(v_reuseFailAlloc_4160_, 3, v___x_4157_);
lean_ctor_set(v_reuseFailAlloc_4160_, 4, v_r_4089_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
}
}
else
{
lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4221_; 
lean_inc(v_r_4089_);
lean_inc(v_v_4087_);
lean_inc(v_k_4086_);
lean_inc(v_size_4085_);
v_isSharedCheck_4221_ = !lean_is_exclusive(v_r_3900_);
if (v_isSharedCheck_4221_ == 0)
{
lean_object* v_unused_4222_; lean_object* v_unused_4223_; lean_object* v_unused_4224_; lean_object* v_unused_4225_; lean_object* v_unused_4226_; 
v_unused_4222_ = lean_ctor_get(v_r_3900_, 4);
lean_dec(v_unused_4222_);
v_unused_4223_ = lean_ctor_get(v_r_3900_, 3);
lean_dec(v_unused_4223_);
v_unused_4224_ = lean_ctor_get(v_r_3900_, 2);
lean_dec(v_unused_4224_);
v_unused_4225_ = lean_ctor_get(v_r_3900_, 1);
lean_dec(v_unused_4225_);
v_unused_4226_ = lean_ctor_get(v_r_3900_, 0);
lean_dec(v_unused_4226_);
v___x_4169_ = v_r_3900_;
v_isShared_4170_ = v_isSharedCheck_4221_;
goto v_resetjp_4168_;
}
else
{
lean_dec(v_r_3900_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4221_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
if (lean_obj_tag(v_l_4088_) == 0)
{
if (lean_obj_tag(v_r_4089_) == 0)
{
lean_object* v_k_4171_; lean_object* v_v_4172_; lean_object* v_size_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4177_; 
v_k_4171_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_k_4171_);
v_v_4172_ = lean_ctor_get(v___x_4095_, 1);
lean_inc(v_v_4172_);
lean_dec_ref(v___x_4095_);
v_size_4173_ = lean_ctor_get(v_l_4088_, 0);
v___x_4174_ = lean_nat_add(v___x_4090_, v_size_4085_);
lean_dec(v_size_4085_);
v___x_4175_ = lean_nat_add(v___x_4090_, v_size_4173_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 4, v_l_4088_);
lean_ctor_set(v___x_4169_, 3, v_tree_4096_);
lean_ctor_set(v___x_4169_, 2, v_v_4172_);
lean_ctor_set(v___x_4169_, 1, v_k_4171_);
lean_ctor_set(v___x_4169_, 0, v___x_4175_);
v___x_4177_ = v___x_4169_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4175_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v_k_4171_);
lean_ctor_set(v_reuseFailAlloc_4181_, 2, v_v_4172_);
lean_ctor_set(v_reuseFailAlloc_4181_, 3, v_tree_4096_);
lean_ctor_set(v_reuseFailAlloc_4181_, 4, v_l_4088_);
v___x_4177_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
lean_object* v___x_4179_; 
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 4, v_r_4089_);
lean_ctor_set(v___x_4093_, 3, v___x_4177_);
lean_ctor_set(v___x_4093_, 2, v_v_4087_);
lean_ctor_set(v___x_4093_, 1, v_k_4086_);
lean_ctor_set(v___x_4093_, 0, v___x_4174_);
v___x_4179_ = v___x_4093_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4174_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v_k_4086_);
lean_ctor_set(v_reuseFailAlloc_4180_, 2, v_v_4087_);
lean_ctor_set(v_reuseFailAlloc_4180_, 3, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4180_, 4, v_r_4089_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
else
{
lean_object* v_k_4182_; lean_object* v_v_4183_; lean_object* v_k_4184_; lean_object* v_v_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4199_; 
lean_dec(v_size_4085_);
v_k_4182_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_k_4182_);
v_v_4183_ = lean_ctor_get(v___x_4095_, 1);
lean_inc(v_v_4183_);
lean_dec_ref(v___x_4095_);
v_k_4184_ = lean_ctor_get(v_l_4088_, 1);
v_v_4185_ = lean_ctor_get(v_l_4088_, 2);
v_isSharedCheck_4199_ = !lean_is_exclusive(v_l_4088_);
if (v_isSharedCheck_4199_ == 0)
{
lean_object* v_unused_4200_; lean_object* v_unused_4201_; lean_object* v_unused_4202_; 
v_unused_4200_ = lean_ctor_get(v_l_4088_, 4);
lean_dec(v_unused_4200_);
v_unused_4201_ = lean_ctor_get(v_l_4088_, 3);
lean_dec(v_unused_4201_);
v_unused_4202_ = lean_ctor_get(v_l_4088_, 0);
lean_dec(v_unused_4202_);
v___x_4187_ = v_l_4088_;
v_isShared_4188_ = v_isSharedCheck_4199_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_v_4185_);
lean_inc(v_k_4184_);
lean_dec(v_l_4088_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4199_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4189_; lean_object* v___x_4191_; 
v___x_4189_ = lean_unsigned_to_nat(3u);
if (v_isShared_4188_ == 0)
{
lean_ctor_set(v___x_4187_, 4, v_r_4089_);
lean_ctor_set(v___x_4187_, 3, v_r_4089_);
lean_ctor_set(v___x_4187_, 2, v_v_4183_);
lean_ctor_set(v___x_4187_, 1, v_k_4182_);
lean_ctor_set(v___x_4187_, 0, v___x_4090_);
v___x_4191_ = v___x_4187_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4198_, 1, v_k_4182_);
lean_ctor_set(v_reuseFailAlloc_4198_, 2, v_v_4183_);
lean_ctor_set(v_reuseFailAlloc_4198_, 3, v_r_4089_);
lean_ctor_set(v_reuseFailAlloc_4198_, 4, v_r_4089_);
v___x_4191_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4193_; 
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 3, v_r_4089_);
lean_ctor_set(v___x_4169_, 0, v___x_4090_);
v___x_4193_ = v___x_4169_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4197_, 1, v_k_4086_);
lean_ctor_set(v_reuseFailAlloc_4197_, 2, v_v_4087_);
lean_ctor_set(v_reuseFailAlloc_4197_, 3, v_r_4089_);
lean_ctor_set(v_reuseFailAlloc_4197_, 4, v_r_4089_);
v___x_4193_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
lean_object* v___x_4195_; 
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 4, v___x_4193_);
lean_ctor_set(v___x_4093_, 3, v___x_4191_);
lean_ctor_set(v___x_4093_, 2, v_v_4185_);
lean_ctor_set(v___x_4093_, 1, v_k_4184_);
lean_ctor_set(v___x_4093_, 0, v___x_4189_);
v___x_4195_ = v___x_4093_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4189_);
lean_ctor_set(v_reuseFailAlloc_4196_, 1, v_k_4184_);
lean_ctor_set(v_reuseFailAlloc_4196_, 2, v_v_4185_);
lean_ctor_set(v_reuseFailAlloc_4196_, 3, v___x_4191_);
lean_ctor_set(v_reuseFailAlloc_4196_, 4, v___x_4193_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4089_) == 0)
{
lean_object* v_k_4203_; lean_object* v_v_4204_; lean_object* v___x_4205_; lean_object* v___x_4207_; 
lean_dec(v_size_4085_);
v_k_4203_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_k_4203_);
v_v_4204_ = lean_ctor_get(v___x_4095_, 1);
lean_inc(v_v_4204_);
lean_dec_ref(v___x_4095_);
v___x_4205_ = lean_unsigned_to_nat(3u);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 4, v_l_4088_);
lean_ctor_set(v___x_4169_, 2, v_v_4204_);
lean_ctor_set(v___x_4169_, 1, v_k_4203_);
lean_ctor_set(v___x_4169_, 0, v___x_4090_);
v___x_4207_ = v___x_4169_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4211_, 1, v_k_4203_);
lean_ctor_set(v_reuseFailAlloc_4211_, 2, v_v_4204_);
lean_ctor_set(v_reuseFailAlloc_4211_, 3, v_l_4088_);
lean_ctor_set(v_reuseFailAlloc_4211_, 4, v_l_4088_);
v___x_4207_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
lean_object* v___x_4209_; 
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 4, v_r_4089_);
lean_ctor_set(v___x_4093_, 3, v___x_4207_);
lean_ctor_set(v___x_4093_, 2, v_v_4087_);
lean_ctor_set(v___x_4093_, 1, v_k_4086_);
lean_ctor_set(v___x_4093_, 0, v___x_4205_);
v___x_4209_ = v___x_4093_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4205_);
lean_ctor_set(v_reuseFailAlloc_4210_, 1, v_k_4086_);
lean_ctor_set(v_reuseFailAlloc_4210_, 2, v_v_4087_);
lean_ctor_set(v_reuseFailAlloc_4210_, 3, v___x_4207_);
lean_ctor_set(v_reuseFailAlloc_4210_, 4, v_r_4089_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
else
{
lean_object* v_k_4212_; lean_object* v_v_4213_; lean_object* v___x_4215_; 
v_k_4212_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_k_4212_);
v_v_4213_ = lean_ctor_get(v___x_4095_, 1);
lean_inc(v_v_4213_);
lean_dec_ref(v___x_4095_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 3, v_r_4089_);
v___x_4215_ = v___x_4169_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_size_4085_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_k_4086_);
lean_ctor_set(v_reuseFailAlloc_4220_, 2, v_v_4087_);
lean_ctor_set(v_reuseFailAlloc_4220_, 3, v_r_4089_);
lean_ctor_set(v_reuseFailAlloc_4220_, 4, v_r_4089_);
v___x_4215_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
lean_object* v___x_4216_; lean_object* v___x_4218_; 
v___x_4216_ = lean_unsigned_to_nat(2u);
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 4, v___x_4215_);
lean_ctor_set(v___x_4093_, 3, v_r_4089_);
lean_ctor_set(v___x_4093_, 2, v_v_4213_);
lean_ctor_set(v___x_4093_, 1, v_k_4212_);
lean_ctor_set(v___x_4093_, 0, v___x_4216_);
v___x_4218_ = v___x_4093_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
lean_ctor_set(v_reuseFailAlloc_4219_, 1, v_k_4212_);
lean_ctor_set(v_reuseFailAlloc_4219_, 2, v_v_4213_);
lean_ctor_set(v_reuseFailAlloc_4219_, 3, v_r_4089_);
lean_ctor_set(v_reuseFailAlloc_4219_, 4, v___x_4215_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
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
lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4385_; 
lean_inc(v_r_4089_);
lean_inc(v_v_4087_);
lean_inc(v_k_4086_);
v_isSharedCheck_4385_ = !lean_is_exclusive(v_r_3900_);
if (v_isSharedCheck_4385_ == 0)
{
lean_object* v_unused_4386_; lean_object* v_unused_4387_; lean_object* v_unused_4388_; lean_object* v_unused_4389_; lean_object* v_unused_4390_; 
v_unused_4386_ = lean_ctor_get(v_r_3900_, 4);
lean_dec(v_unused_4386_);
v_unused_4387_ = lean_ctor_get(v_r_3900_, 3);
lean_dec(v_unused_4387_);
v_unused_4388_ = lean_ctor_get(v_r_3900_, 2);
lean_dec(v_unused_4388_);
v_unused_4389_ = lean_ctor_get(v_r_3900_, 1);
lean_dec(v_unused_4389_);
v_unused_4390_ = lean_ctor_get(v_r_3900_, 0);
lean_dec(v_unused_4390_);
v___x_4234_ = v_r_3900_;
v_isShared_4235_ = v_isSharedCheck_4385_;
goto v_resetjp_4233_;
}
else
{
lean_dec(v_r_3900_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4385_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4236_; lean_object* v_tree_4237_; 
v___x_4236_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_4086_, v_v_4087_, v_l_4088_, v_r_4089_);
v_tree_4237_ = lean_ctor_get(v___x_4236_, 2);
lean_inc(v_tree_4237_);
if (lean_obj_tag(v_tree_4237_) == 0)
{
lean_object* v_k_4238_; lean_object* v_v_4239_; lean_object* v_size_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; uint8_t v___x_4243_; 
v_k_4238_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_k_4238_);
v_v_4239_ = lean_ctor_get(v___x_4236_, 1);
lean_inc(v_v_4239_);
lean_dec_ref(v___x_4236_);
v_size_4240_ = lean_ctor_get(v_tree_4237_, 0);
v___x_4241_ = lean_unsigned_to_nat(3u);
v___x_4242_ = lean_nat_mul(v___x_4241_, v_size_4240_);
v___x_4243_ = lean_nat_dec_lt(v___x_4242_, v_size_4080_);
lean_dec(v___x_4242_);
if (v___x_4243_ == 0)
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4247_; 
lean_dec(v_r_4084_);
v___x_4244_ = lean_nat_add(v___x_4090_, v_size_4080_);
v___x_4245_ = lean_nat_add(v___x_4244_, v_size_4240_);
lean_dec(v___x_4244_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 4, v_tree_4237_);
lean_ctor_set(v___x_4234_, 3, v_l_3899_);
lean_ctor_set(v___x_4234_, 2, v_v_4239_);
lean_ctor_set(v___x_4234_, 1, v_k_4238_);
lean_ctor_set(v___x_4234_, 0, v___x_4245_);
v___x_4247_ = v___x_4234_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4245_);
lean_ctor_set(v_reuseFailAlloc_4248_, 1, v_k_4238_);
lean_ctor_set(v_reuseFailAlloc_4248_, 2, v_v_4239_);
lean_ctor_set(v_reuseFailAlloc_4248_, 3, v_l_3899_);
lean_ctor_set(v_reuseFailAlloc_4248_, 4, v_tree_4237_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
else
{
lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4314_; 
lean_inc(v_l_4083_);
lean_inc(v_v_4082_);
lean_inc(v_k_4081_);
lean_inc(v_size_4080_);
v_isSharedCheck_4314_ = !lean_is_exclusive(v_l_3899_);
if (v_isSharedCheck_4314_ == 0)
{
lean_object* v_unused_4315_; lean_object* v_unused_4316_; lean_object* v_unused_4317_; lean_object* v_unused_4318_; lean_object* v_unused_4319_; 
v_unused_4315_ = lean_ctor_get(v_l_3899_, 4);
lean_dec(v_unused_4315_);
v_unused_4316_ = lean_ctor_get(v_l_3899_, 3);
lean_dec(v_unused_4316_);
v_unused_4317_ = lean_ctor_get(v_l_3899_, 2);
lean_dec(v_unused_4317_);
v_unused_4318_ = lean_ctor_get(v_l_3899_, 1);
lean_dec(v_unused_4318_);
v_unused_4319_ = lean_ctor_get(v_l_3899_, 0);
lean_dec(v_unused_4319_);
v___x_4250_ = v_l_3899_;
v_isShared_4251_ = v_isSharedCheck_4314_;
goto v_resetjp_4249_;
}
else
{
lean_dec(v_l_3899_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4314_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v_size_4252_; lean_object* v_size_4253_; lean_object* v_k_4254_; lean_object* v_v_4255_; lean_object* v_l_4256_; lean_object* v_r_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; uint8_t v___x_4260_; 
v_size_4252_ = lean_ctor_get(v_l_4083_, 0);
v_size_4253_ = lean_ctor_get(v_r_4084_, 0);
v_k_4254_ = lean_ctor_get(v_r_4084_, 1);
v_v_4255_ = lean_ctor_get(v_r_4084_, 2);
v_l_4256_ = lean_ctor_get(v_r_4084_, 3);
v_r_4257_ = lean_ctor_get(v_r_4084_, 4);
v___x_4258_ = lean_unsigned_to_nat(2u);
v___x_4259_ = lean_nat_mul(v___x_4258_, v_size_4252_);
v___x_4260_ = lean_nat_dec_lt(v_size_4253_, v___x_4259_);
lean_dec(v___x_4259_);
if (v___x_4260_ == 0)
{
lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4298_; 
lean_inc(v_r_4257_);
lean_inc(v_l_4256_);
lean_inc(v_v_4255_);
lean_inc(v_k_4254_);
lean_del_object(v___x_4250_);
v_isSharedCheck_4298_ = !lean_is_exclusive(v_r_4084_);
if (v_isSharedCheck_4298_ == 0)
{
lean_object* v_unused_4299_; lean_object* v_unused_4300_; lean_object* v_unused_4301_; lean_object* v_unused_4302_; lean_object* v_unused_4303_; 
v_unused_4299_ = lean_ctor_get(v_r_4084_, 4);
lean_dec(v_unused_4299_);
v_unused_4300_ = lean_ctor_get(v_r_4084_, 3);
lean_dec(v_unused_4300_);
v_unused_4301_ = lean_ctor_get(v_r_4084_, 2);
lean_dec(v_unused_4301_);
v_unused_4302_ = lean_ctor_get(v_r_4084_, 1);
lean_dec(v_unused_4302_);
v_unused_4303_ = lean_ctor_get(v_r_4084_, 0);
lean_dec(v_unused_4303_);
v___x_4262_ = v_r_4084_;
v_isShared_4263_ = v_isSharedCheck_4298_;
goto v_resetjp_4261_;
}
else
{
lean_dec(v_r_4084_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4298_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___x_4286_; lean_object* v___y_4288_; 
v___x_4264_ = lean_nat_add(v___x_4090_, v_size_4080_);
lean_dec(v_size_4080_);
v___x_4265_ = lean_nat_add(v___x_4264_, v_size_4240_);
lean_dec(v___x_4264_);
v___x_4286_ = lean_nat_add(v___x_4090_, v_size_4252_);
if (lean_obj_tag(v_l_4256_) == 0)
{
lean_object* v_size_4296_; 
v_size_4296_ = lean_ctor_get(v_l_4256_, 0);
lean_inc(v_size_4296_);
v___y_4288_ = v_size_4296_;
goto v___jp_4287_;
}
else
{
lean_object* v___x_4297_; 
v___x_4297_ = lean_unsigned_to_nat(0u);
v___y_4288_ = v___x_4297_;
goto v___jp_4287_;
}
v___jp_4266_:
{
lean_object* v___x_4270_; lean_object* v___x_4272_; 
v___x_4270_ = lean_nat_add(v___y_4268_, v___y_4269_);
lean_dec(v___y_4269_);
lean_dec(v___y_4268_);
lean_inc_ref(v_tree_4237_);
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 4, v_tree_4237_);
lean_ctor_set(v___x_4262_, 3, v_r_4257_);
lean_ctor_set(v___x_4262_, 2, v_v_4239_);
lean_ctor_set(v___x_4262_, 1, v_k_4238_);
lean_ctor_set(v___x_4262_, 0, v___x_4270_);
v___x_4272_ = v___x_4262_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v___x_4270_);
lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_k_4238_);
lean_ctor_set(v_reuseFailAlloc_4285_, 2, v_v_4239_);
lean_ctor_set(v_reuseFailAlloc_4285_, 3, v_r_4257_);
lean_ctor_set(v_reuseFailAlloc_4285_, 4, v_tree_4237_);
v___x_4272_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
v_isSharedCheck_4279_ = !lean_is_exclusive(v_tree_4237_);
if (v_isSharedCheck_4279_ == 0)
{
lean_object* v_unused_4280_; lean_object* v_unused_4281_; lean_object* v_unused_4282_; lean_object* v_unused_4283_; lean_object* v_unused_4284_; 
v_unused_4280_ = lean_ctor_get(v_tree_4237_, 4);
lean_dec(v_unused_4280_);
v_unused_4281_ = lean_ctor_get(v_tree_4237_, 3);
lean_dec(v_unused_4281_);
v_unused_4282_ = lean_ctor_get(v_tree_4237_, 2);
lean_dec(v_unused_4282_);
v_unused_4283_ = lean_ctor_get(v_tree_4237_, 1);
lean_dec(v_unused_4283_);
v_unused_4284_ = lean_ctor_get(v_tree_4237_, 0);
lean_dec(v_unused_4284_);
v___x_4274_ = v_tree_4237_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_dec(v_tree_4237_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
lean_ctor_set(v___x_4274_, 4, v___x_4272_);
lean_ctor_set(v___x_4274_, 3, v___y_4267_);
lean_ctor_set(v___x_4274_, 2, v_v_4255_);
lean_ctor_set(v___x_4274_, 1, v_k_4254_);
lean_ctor_set(v___x_4274_, 0, v___x_4265_);
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4265_);
lean_ctor_set(v_reuseFailAlloc_4278_, 1, v_k_4254_);
lean_ctor_set(v_reuseFailAlloc_4278_, 2, v_v_4255_);
lean_ctor_set(v_reuseFailAlloc_4278_, 3, v___y_4267_);
lean_ctor_set(v_reuseFailAlloc_4278_, 4, v___x_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
v___jp_4287_:
{
lean_object* v___x_4289_; lean_object* v___x_4291_; 
v___x_4289_ = lean_nat_add(v___x_4286_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec(v___x_4286_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 4, v_l_4256_);
lean_ctor_set(v___x_4234_, 3, v_l_4083_);
lean_ctor_set(v___x_4234_, 2, v_v_4082_);
lean_ctor_set(v___x_4234_, 1, v_k_4081_);
lean_ctor_set(v___x_4234_, 0, v___x_4289_);
v___x_4291_ = v___x_4234_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4289_);
lean_ctor_set(v_reuseFailAlloc_4295_, 1, v_k_4081_);
lean_ctor_set(v_reuseFailAlloc_4295_, 2, v_v_4082_);
lean_ctor_set(v_reuseFailAlloc_4295_, 3, v_l_4083_);
lean_ctor_set(v_reuseFailAlloc_4295_, 4, v_l_4256_);
v___x_4291_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
lean_object* v___x_4292_; 
v___x_4292_ = lean_nat_add(v___x_4090_, v_size_4240_);
if (lean_obj_tag(v_r_4257_) == 0)
{
lean_object* v_size_4293_; 
v_size_4293_ = lean_ctor_get(v_r_4257_, 0);
lean_inc(v_size_4293_);
v___y_4267_ = v___x_4291_;
v___y_4268_ = v___x_4292_;
v___y_4269_ = v_size_4293_;
goto v___jp_4266_;
}
else
{
lean_object* v___x_4294_; 
v___x_4294_ = lean_unsigned_to_nat(0u);
v___y_4267_ = v___x_4291_;
v___y_4268_ = v___x_4292_;
v___y_4269_ = v___x_4294_;
goto v___jp_4266_;
}
}
}
}
}
else
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4309_; 
v___x_4304_ = lean_nat_add(v___x_4090_, v_size_4080_);
lean_dec(v_size_4080_);
v___x_4305_ = lean_nat_add(v___x_4304_, v_size_4240_);
lean_dec(v___x_4304_);
v___x_4306_ = lean_nat_add(v___x_4090_, v_size_4240_);
v___x_4307_ = lean_nat_add(v___x_4306_, v_size_4253_);
lean_dec(v___x_4306_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 4, v_tree_4237_);
lean_ctor_set(v___x_4234_, 3, v_r_4084_);
lean_ctor_set(v___x_4234_, 2, v_v_4239_);
lean_ctor_set(v___x_4234_, 1, v_k_4238_);
lean_ctor_set(v___x_4234_, 0, v___x_4307_);
v___x_4309_ = v___x_4234_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v___x_4307_);
lean_ctor_set(v_reuseFailAlloc_4313_, 1, v_k_4238_);
lean_ctor_set(v_reuseFailAlloc_4313_, 2, v_v_4239_);
lean_ctor_set(v_reuseFailAlloc_4313_, 3, v_r_4084_);
lean_ctor_set(v_reuseFailAlloc_4313_, 4, v_tree_4237_);
v___x_4309_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
lean_object* v___x_4311_; 
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 4, v___x_4309_);
lean_ctor_set(v___x_4250_, 0, v___x_4305_);
v___x_4311_ = v___x_4250_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4305_);
lean_ctor_set(v_reuseFailAlloc_4312_, 1, v_k_4081_);
lean_ctor_set(v_reuseFailAlloc_4312_, 2, v_v_4082_);
lean_ctor_set(v_reuseFailAlloc_4312_, 3, v_l_4083_);
lean_ctor_set(v_reuseFailAlloc_4312_, 4, v___x_4309_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_4083_) == 0)
{
lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4343_; 
lean_inc_ref(v_l_4083_);
lean_inc(v_v_4082_);
lean_inc(v_k_4081_);
lean_inc(v_size_4080_);
v_isSharedCheck_4343_ = !lean_is_exclusive(v_l_3899_);
if (v_isSharedCheck_4343_ == 0)
{
lean_object* v_unused_4344_; lean_object* v_unused_4345_; lean_object* v_unused_4346_; lean_object* v_unused_4347_; lean_object* v_unused_4348_; 
v_unused_4344_ = lean_ctor_get(v_l_3899_, 4);
lean_dec(v_unused_4344_);
v_unused_4345_ = lean_ctor_get(v_l_3899_, 3);
lean_dec(v_unused_4345_);
v_unused_4346_ = lean_ctor_get(v_l_3899_, 2);
lean_dec(v_unused_4346_);
v_unused_4347_ = lean_ctor_get(v_l_3899_, 1);
lean_dec(v_unused_4347_);
v_unused_4348_ = lean_ctor_get(v_l_3899_, 0);
lean_dec(v_unused_4348_);
v___x_4321_ = v_l_3899_;
v_isShared_4322_ = v_isSharedCheck_4343_;
goto v_resetjp_4320_;
}
else
{
lean_dec(v_l_3899_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4343_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
if (lean_obj_tag(v_r_4084_) == 0)
{
lean_object* v_k_4323_; lean_object* v_v_4324_; lean_object* v_size_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4329_; 
v_k_4323_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_k_4323_);
v_v_4324_ = lean_ctor_get(v___x_4236_, 1);
lean_inc(v_v_4324_);
lean_dec_ref(v___x_4236_);
v_size_4325_ = lean_ctor_get(v_r_4084_, 0);
v___x_4326_ = lean_nat_add(v___x_4090_, v_size_4080_);
lean_dec(v_size_4080_);
v___x_4327_ = lean_nat_add(v___x_4090_, v_size_4325_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 4, v_tree_4237_);
lean_ctor_set(v___x_4234_, 3, v_r_4084_);
lean_ctor_set(v___x_4234_, 2, v_v_4324_);
lean_ctor_set(v___x_4234_, 1, v_k_4323_);
lean_ctor_set(v___x_4234_, 0, v___x_4327_);
v___x_4329_ = v___x_4234_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4327_);
lean_ctor_set(v_reuseFailAlloc_4333_, 1, v_k_4323_);
lean_ctor_set(v_reuseFailAlloc_4333_, 2, v_v_4324_);
lean_ctor_set(v_reuseFailAlloc_4333_, 3, v_r_4084_);
lean_ctor_set(v_reuseFailAlloc_4333_, 4, v_tree_4237_);
v___x_4329_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
lean_object* v___x_4331_; 
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 4, v___x_4329_);
lean_ctor_set(v___x_4321_, 0, v___x_4326_);
v___x_4331_ = v___x_4321_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4326_);
lean_ctor_set(v_reuseFailAlloc_4332_, 1, v_k_4081_);
lean_ctor_set(v_reuseFailAlloc_4332_, 2, v_v_4082_);
lean_ctor_set(v_reuseFailAlloc_4332_, 3, v_l_4083_);
lean_ctor_set(v_reuseFailAlloc_4332_, 4, v___x_4329_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
else
{
lean_object* v_k_4334_; lean_object* v_v_4335_; lean_object* v___x_4336_; lean_object* v___x_4338_; 
lean_dec(v_size_4080_);
v_k_4334_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_k_4334_);
v_v_4335_ = lean_ctor_get(v___x_4236_, 1);
lean_inc(v_v_4335_);
lean_dec_ref(v___x_4236_);
v___x_4336_ = lean_unsigned_to_nat(3u);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 4, v_r_4084_);
lean_ctor_set(v___x_4234_, 3, v_r_4084_);
lean_ctor_set(v___x_4234_, 2, v_v_4335_);
lean_ctor_set(v___x_4234_, 1, v_k_4334_);
lean_ctor_set(v___x_4234_, 0, v___x_4090_);
v___x_4338_ = v___x_4234_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4342_, 1, v_k_4334_);
lean_ctor_set(v_reuseFailAlloc_4342_, 2, v_v_4335_);
lean_ctor_set(v_reuseFailAlloc_4342_, 3, v_r_4084_);
lean_ctor_set(v_reuseFailAlloc_4342_, 4, v_r_4084_);
v___x_4338_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
lean_object* v___x_4340_; 
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 4, v___x_4338_);
lean_ctor_set(v___x_4321_, 0, v___x_4336_);
v___x_4340_ = v___x_4321_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v___x_4336_);
lean_ctor_set(v_reuseFailAlloc_4341_, 1, v_k_4081_);
lean_ctor_set(v_reuseFailAlloc_4341_, 2, v_v_4082_);
lean_ctor_set(v_reuseFailAlloc_4341_, 3, v_l_4083_);
lean_ctor_set(v_reuseFailAlloc_4341_, 4, v___x_4338_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4084_) == 0)
{
lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4373_; 
lean_inc(v_l_4083_);
lean_inc(v_v_4082_);
lean_inc(v_k_4081_);
v_isSharedCheck_4373_ = !lean_is_exclusive(v_l_3899_);
if (v_isSharedCheck_4373_ == 0)
{
lean_object* v_unused_4374_; lean_object* v_unused_4375_; lean_object* v_unused_4376_; lean_object* v_unused_4377_; lean_object* v_unused_4378_; 
v_unused_4374_ = lean_ctor_get(v_l_3899_, 4);
lean_dec(v_unused_4374_);
v_unused_4375_ = lean_ctor_get(v_l_3899_, 3);
lean_dec(v_unused_4375_);
v_unused_4376_ = lean_ctor_get(v_l_3899_, 2);
lean_dec(v_unused_4376_);
v_unused_4377_ = lean_ctor_get(v_l_3899_, 1);
lean_dec(v_unused_4377_);
v_unused_4378_ = lean_ctor_get(v_l_3899_, 0);
lean_dec(v_unused_4378_);
v___x_4350_ = v_l_3899_;
v_isShared_4351_ = v_isSharedCheck_4373_;
goto v_resetjp_4349_;
}
else
{
lean_dec(v_l_3899_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4373_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v_k_4352_; lean_object* v_v_4353_; lean_object* v_k_4354_; lean_object* v_v_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4369_; 
v_k_4352_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_k_4352_);
v_v_4353_ = lean_ctor_get(v___x_4236_, 1);
lean_inc(v_v_4353_);
lean_dec_ref(v___x_4236_);
v_k_4354_ = lean_ctor_get(v_r_4084_, 1);
v_v_4355_ = lean_ctor_get(v_r_4084_, 2);
v_isSharedCheck_4369_ = !lean_is_exclusive(v_r_4084_);
if (v_isSharedCheck_4369_ == 0)
{
lean_object* v_unused_4370_; lean_object* v_unused_4371_; lean_object* v_unused_4372_; 
v_unused_4370_ = lean_ctor_get(v_r_4084_, 4);
lean_dec(v_unused_4370_);
v_unused_4371_ = lean_ctor_get(v_r_4084_, 3);
lean_dec(v_unused_4371_);
v_unused_4372_ = lean_ctor_get(v_r_4084_, 0);
lean_dec(v_unused_4372_);
v___x_4357_ = v_r_4084_;
v_isShared_4358_ = v_isSharedCheck_4369_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_v_4355_);
lean_inc(v_k_4354_);
lean_dec(v_r_4084_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4369_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4359_; lean_object* v___x_4361_; 
v___x_4359_ = lean_unsigned_to_nat(3u);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 4, v_l_4083_);
lean_ctor_set(v___x_4357_, 3, v_l_4083_);
lean_ctor_set(v___x_4357_, 2, v_v_4082_);
lean_ctor_set(v___x_4357_, 1, v_k_4081_);
lean_ctor_set(v___x_4357_, 0, v___x_4090_);
v___x_4361_ = v___x_4357_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4368_, 1, v_k_4081_);
lean_ctor_set(v_reuseFailAlloc_4368_, 2, v_v_4082_);
lean_ctor_set(v_reuseFailAlloc_4368_, 3, v_l_4083_);
lean_ctor_set(v_reuseFailAlloc_4368_, 4, v_l_4083_);
v___x_4361_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4363_; 
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 4, v_l_4083_);
lean_ctor_set(v___x_4234_, 3, v_l_4083_);
lean_ctor_set(v___x_4234_, 2, v_v_4353_);
lean_ctor_set(v___x_4234_, 1, v_k_4352_);
lean_ctor_set(v___x_4234_, 0, v___x_4090_);
v___x_4363_ = v___x_4234_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4367_, 1, v_k_4352_);
lean_ctor_set(v_reuseFailAlloc_4367_, 2, v_v_4353_);
lean_ctor_set(v_reuseFailAlloc_4367_, 3, v_l_4083_);
lean_ctor_set(v_reuseFailAlloc_4367_, 4, v_l_4083_);
v___x_4363_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4365_; 
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 4, v___x_4363_);
lean_ctor_set(v___x_4350_, 3, v___x_4361_);
lean_ctor_set(v___x_4350_, 2, v_v_4355_);
lean_ctor_set(v___x_4350_, 1, v_k_4354_);
lean_ctor_set(v___x_4350_, 0, v___x_4359_);
v___x_4365_ = v___x_4350_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v___x_4359_);
lean_ctor_set(v_reuseFailAlloc_4366_, 1, v_k_4354_);
lean_ctor_set(v_reuseFailAlloc_4366_, 2, v_v_4355_);
lean_ctor_set(v_reuseFailAlloc_4366_, 3, v___x_4361_);
lean_ctor_set(v_reuseFailAlloc_4366_, 4, v___x_4363_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
}
}
else
{
lean_object* v_k_4379_; lean_object* v_v_4380_; lean_object* v___x_4381_; lean_object* v___x_4383_; 
v_k_4379_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_k_4379_);
v_v_4380_ = lean_ctor_get(v___x_4236_, 1);
lean_inc(v_v_4380_);
lean_dec_ref(v___x_4236_);
v___x_4381_ = lean_unsigned_to_nat(2u);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 4, v_r_4084_);
lean_ctor_set(v___x_4234_, 3, v_l_3899_);
lean_ctor_set(v___x_4234_, 2, v_v_4380_);
lean_ctor_set(v___x_4234_, 1, v_k_4379_);
lean_ctor_set(v___x_4234_, 0, v___x_4381_);
v___x_4383_ = v___x_4234_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4381_);
lean_ctor_set(v_reuseFailAlloc_4384_, 1, v_k_4379_);
lean_ctor_set(v_reuseFailAlloc_4384_, 2, v_v_4380_);
lean_ctor_set(v_reuseFailAlloc_4384_, 3, v_l_3899_);
lean_ctor_set(v_reuseFailAlloc_4384_, 4, v_r_4084_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
}
}
}
else
{
return v_l_3899_;
}
}
else
{
return v_r_3900_;
}
}
default: 
{
lean_object* v_impl_4391_; lean_object* v___x_4392_; 
v_impl_4391_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_3894_, v_k_3895_, v_r_3900_);
v___x_4392_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_4391_) == 0)
{
if (lean_obj_tag(v_l_3899_) == 0)
{
lean_object* v_size_4393_; lean_object* v_size_4394_; lean_object* v_k_4395_; lean_object* v_v_4396_; lean_object* v_l_4397_; lean_object* v_r_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; uint8_t v___x_4401_; 
v_size_4393_ = lean_ctor_get(v_impl_4391_, 0);
lean_inc(v_size_4393_);
v_size_4394_ = lean_ctor_get(v_l_3899_, 0);
v_k_4395_ = lean_ctor_get(v_l_3899_, 1);
v_v_4396_ = lean_ctor_get(v_l_3899_, 2);
v_l_4397_ = lean_ctor_get(v_l_3899_, 3);
v_r_4398_ = lean_ctor_get(v_l_3899_, 4);
lean_inc(v_r_4398_);
v___x_4399_ = lean_unsigned_to_nat(3u);
v___x_4400_ = lean_nat_mul(v___x_4399_, v_size_4393_);
v___x_4401_ = lean_nat_dec_lt(v___x_4400_, v_size_4394_);
lean_dec(v___x_4400_);
if (v___x_4401_ == 0)
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4405_; 
lean_dec(v_r_4398_);
v___x_4402_ = lean_nat_add(v___x_4392_, v_size_4394_);
v___x_4403_ = lean_nat_add(v___x_4402_, v_size_4393_);
lean_dec(v_size_4393_);
lean_dec(v___x_4402_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v_impl_4391_);
lean_ctor_set(v___x_3902_, 0, v___x_4403_);
v___x_4405_ = v___x_3902_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4403_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4406_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4406_, 3, v_l_3899_);
lean_ctor_set(v_reuseFailAlloc_4406_, 4, v_impl_4391_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
else
{
lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4472_; 
lean_inc(v_l_4397_);
lean_inc(v_v_4396_);
lean_inc(v_k_4395_);
lean_inc(v_size_4394_);
v_isSharedCheck_4472_ = !lean_is_exclusive(v_l_3899_);
if (v_isSharedCheck_4472_ == 0)
{
lean_object* v_unused_4473_; lean_object* v_unused_4474_; lean_object* v_unused_4475_; lean_object* v_unused_4476_; lean_object* v_unused_4477_; 
v_unused_4473_ = lean_ctor_get(v_l_3899_, 4);
lean_dec(v_unused_4473_);
v_unused_4474_ = lean_ctor_get(v_l_3899_, 3);
lean_dec(v_unused_4474_);
v_unused_4475_ = lean_ctor_get(v_l_3899_, 2);
lean_dec(v_unused_4475_);
v_unused_4476_ = lean_ctor_get(v_l_3899_, 1);
lean_dec(v_unused_4476_);
v_unused_4477_ = lean_ctor_get(v_l_3899_, 0);
lean_dec(v_unused_4477_);
v___x_4408_ = v_l_3899_;
v_isShared_4409_ = v_isSharedCheck_4472_;
goto v_resetjp_4407_;
}
else
{
lean_dec(v_l_3899_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4472_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v_size_4410_; lean_object* v_size_4411_; lean_object* v_k_4412_; lean_object* v_v_4413_; lean_object* v_l_4414_; lean_object* v_r_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; uint8_t v___x_4418_; 
v_size_4410_ = lean_ctor_get(v_l_4397_, 0);
v_size_4411_ = lean_ctor_get(v_r_4398_, 0);
v_k_4412_ = lean_ctor_get(v_r_4398_, 1);
v_v_4413_ = lean_ctor_get(v_r_4398_, 2);
v_l_4414_ = lean_ctor_get(v_r_4398_, 3);
v_r_4415_ = lean_ctor_get(v_r_4398_, 4);
v___x_4416_ = lean_unsigned_to_nat(2u);
v___x_4417_ = lean_nat_mul(v___x_4416_, v_size_4410_);
v___x_4418_ = lean_nat_dec_lt(v_size_4411_, v___x_4417_);
lean_dec(v___x_4417_);
if (v___x_4418_ == 0)
{
lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4447_; 
lean_inc(v_r_4415_);
lean_inc(v_l_4414_);
lean_inc(v_v_4413_);
lean_inc(v_k_4412_);
v_isSharedCheck_4447_ = !lean_is_exclusive(v_r_4398_);
if (v_isSharedCheck_4447_ == 0)
{
lean_object* v_unused_4448_; lean_object* v_unused_4449_; lean_object* v_unused_4450_; lean_object* v_unused_4451_; lean_object* v_unused_4452_; 
v_unused_4448_ = lean_ctor_get(v_r_4398_, 4);
lean_dec(v_unused_4448_);
v_unused_4449_ = lean_ctor_get(v_r_4398_, 3);
lean_dec(v_unused_4449_);
v_unused_4450_ = lean_ctor_get(v_r_4398_, 2);
lean_dec(v_unused_4450_);
v_unused_4451_ = lean_ctor_get(v_r_4398_, 1);
lean_dec(v_unused_4451_);
v_unused_4452_ = lean_ctor_get(v_r_4398_, 0);
lean_dec(v_unused_4452_);
v___x_4420_ = v_r_4398_;
v_isShared_4421_ = v_isSharedCheck_4447_;
goto v_resetjp_4419_;
}
else
{
lean_dec(v_r_4398_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4447_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___x_4435_; lean_object* v___y_4437_; 
v___x_4422_ = lean_nat_add(v___x_4392_, v_size_4394_);
lean_dec(v_size_4394_);
v___x_4423_ = lean_nat_add(v___x_4422_, v_size_4393_);
lean_dec(v___x_4422_);
v___x_4435_ = lean_nat_add(v___x_4392_, v_size_4410_);
if (lean_obj_tag(v_l_4414_) == 0)
{
lean_object* v_size_4445_; 
v_size_4445_ = lean_ctor_get(v_l_4414_, 0);
lean_inc(v_size_4445_);
v___y_4437_ = v_size_4445_;
goto v___jp_4436_;
}
else
{
lean_object* v___x_4446_; 
v___x_4446_ = lean_unsigned_to_nat(0u);
v___y_4437_ = v___x_4446_;
goto v___jp_4436_;
}
v___jp_4424_:
{
lean_object* v___x_4428_; lean_object* v___x_4430_; 
v___x_4428_ = lean_nat_add(v___y_4425_, v___y_4427_);
lean_dec(v___y_4427_);
lean_dec(v___y_4425_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 4, v_impl_4391_);
lean_ctor_set(v___x_4420_, 3, v_r_4415_);
lean_ctor_set(v___x_4420_, 2, v_v_3898_);
lean_ctor_set(v___x_4420_, 1, v_k_3897_);
lean_ctor_set(v___x_4420_, 0, v___x_4428_);
v___x_4430_ = v___x_4420_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4428_);
lean_ctor_set(v_reuseFailAlloc_4434_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4434_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4434_, 3, v_r_4415_);
lean_ctor_set(v_reuseFailAlloc_4434_, 4, v_impl_4391_);
v___x_4430_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
lean_object* v___x_4432_; 
if (v_isShared_4409_ == 0)
{
lean_ctor_set(v___x_4408_, 4, v___x_4430_);
lean_ctor_set(v___x_4408_, 3, v___y_4426_);
lean_ctor_set(v___x_4408_, 2, v_v_4413_);
lean_ctor_set(v___x_4408_, 1, v_k_4412_);
lean_ctor_set(v___x_4408_, 0, v___x_4423_);
v___x_4432_ = v___x_4408_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4423_);
lean_ctor_set(v_reuseFailAlloc_4433_, 1, v_k_4412_);
lean_ctor_set(v_reuseFailAlloc_4433_, 2, v_v_4413_);
lean_ctor_set(v_reuseFailAlloc_4433_, 3, v___y_4426_);
lean_ctor_set(v_reuseFailAlloc_4433_, 4, v___x_4430_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
v___jp_4436_:
{
lean_object* v___x_4438_; lean_object* v___x_4440_; 
v___x_4438_ = lean_nat_add(v___x_4435_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec(v___x_4435_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v_l_4414_);
lean_ctor_set(v___x_3902_, 3, v_l_4397_);
lean_ctor_set(v___x_3902_, 2, v_v_4396_);
lean_ctor_set(v___x_3902_, 1, v_k_4395_);
lean_ctor_set(v___x_3902_, 0, v___x_4438_);
v___x_4440_ = v___x_3902_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4438_);
lean_ctor_set(v_reuseFailAlloc_4444_, 1, v_k_4395_);
lean_ctor_set(v_reuseFailAlloc_4444_, 2, v_v_4396_);
lean_ctor_set(v_reuseFailAlloc_4444_, 3, v_l_4397_);
lean_ctor_set(v_reuseFailAlloc_4444_, 4, v_l_4414_);
v___x_4440_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
lean_object* v___x_4441_; 
v___x_4441_ = lean_nat_add(v___x_4392_, v_size_4393_);
lean_dec(v_size_4393_);
if (lean_obj_tag(v_r_4415_) == 0)
{
lean_object* v_size_4442_; 
v_size_4442_ = lean_ctor_get(v_r_4415_, 0);
lean_inc(v_size_4442_);
v___y_4425_ = v___x_4441_;
v___y_4426_ = v___x_4440_;
v___y_4427_ = v_size_4442_;
goto v___jp_4424_;
}
else
{
lean_object* v___x_4443_; 
v___x_4443_ = lean_unsigned_to_nat(0u);
v___y_4425_ = v___x_4441_;
v___y_4426_ = v___x_4440_;
v___y_4427_ = v___x_4443_;
goto v___jp_4424_;
}
}
}
}
}
else
{
lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4458_; 
lean_del_object(v___x_3902_);
v___x_4453_ = lean_nat_add(v___x_4392_, v_size_4394_);
lean_dec(v_size_4394_);
v___x_4454_ = lean_nat_add(v___x_4453_, v_size_4393_);
lean_dec(v___x_4453_);
v___x_4455_ = lean_nat_add(v___x_4392_, v_size_4393_);
lean_dec(v_size_4393_);
v___x_4456_ = lean_nat_add(v___x_4455_, v_size_4411_);
lean_dec(v___x_4455_);
lean_inc_ref(v_impl_4391_);
if (v_isShared_4409_ == 0)
{
lean_ctor_set(v___x_4408_, 4, v_impl_4391_);
lean_ctor_set(v___x_4408_, 3, v_r_4398_);
lean_ctor_set(v___x_4408_, 2, v_v_3898_);
lean_ctor_set(v___x_4408_, 1, v_k_3897_);
lean_ctor_set(v___x_4408_, 0, v___x_4456_);
v___x_4458_ = v___x_4408_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4456_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4471_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4471_, 3, v_r_4398_);
lean_ctor_set(v_reuseFailAlloc_4471_, 4, v_impl_4391_);
v___x_4458_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
v_isSharedCheck_4465_ = !lean_is_exclusive(v_impl_4391_);
if (v_isSharedCheck_4465_ == 0)
{
lean_object* v_unused_4466_; lean_object* v_unused_4467_; lean_object* v_unused_4468_; lean_object* v_unused_4469_; lean_object* v_unused_4470_; 
v_unused_4466_ = lean_ctor_get(v_impl_4391_, 4);
lean_dec(v_unused_4466_);
v_unused_4467_ = lean_ctor_get(v_impl_4391_, 3);
lean_dec(v_unused_4467_);
v_unused_4468_ = lean_ctor_get(v_impl_4391_, 2);
lean_dec(v_unused_4468_);
v_unused_4469_ = lean_ctor_get(v_impl_4391_, 1);
lean_dec(v_unused_4469_);
v_unused_4470_ = lean_ctor_get(v_impl_4391_, 0);
lean_dec(v_unused_4470_);
v___x_4460_ = v_impl_4391_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_dec(v_impl_4391_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 4, v___x_4458_);
lean_ctor_set(v___x_4460_, 3, v_l_4397_);
lean_ctor_set(v___x_4460_, 2, v_v_4396_);
lean_ctor_set(v___x_4460_, 1, v_k_4395_);
lean_ctor_set(v___x_4460_, 0, v___x_4454_);
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4454_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v_k_4395_);
lean_ctor_set(v_reuseFailAlloc_4464_, 2, v_v_4396_);
lean_ctor_set(v_reuseFailAlloc_4464_, 3, v_l_4397_);
lean_ctor_set(v_reuseFailAlloc_4464_, 4, v___x_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_4478_; lean_object* v___x_4479_; lean_object* v___x_4481_; 
v_size_4478_ = lean_ctor_get(v_impl_4391_, 0);
lean_inc(v_size_4478_);
v___x_4479_ = lean_nat_add(v___x_4392_, v_size_4478_);
lean_dec(v_size_4478_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v_impl_4391_);
lean_ctor_set(v___x_3902_, 0, v___x_4479_);
v___x_4481_ = v___x_3902_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4479_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4482_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4482_, 3, v_l_3899_);
lean_ctor_set(v_reuseFailAlloc_4482_, 4, v_impl_4391_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
else
{
if (lean_obj_tag(v_l_3899_) == 0)
{
lean_object* v_l_4483_; 
v_l_4483_ = lean_ctor_get(v_l_3899_, 3);
if (lean_obj_tag(v_l_4483_) == 0)
{
lean_object* v_r_4484_; 
lean_inc_ref(v_l_4483_);
v_r_4484_ = lean_ctor_get(v_l_3899_, 4);
lean_inc(v_r_4484_);
if (lean_obj_tag(v_r_4484_) == 0)
{
lean_object* v_size_4485_; lean_object* v_k_4486_; lean_object* v_v_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4500_; 
v_size_4485_ = lean_ctor_get(v_l_3899_, 0);
v_k_4486_ = lean_ctor_get(v_l_3899_, 1);
v_v_4487_ = lean_ctor_get(v_l_3899_, 2);
v_isSharedCheck_4500_ = !lean_is_exclusive(v_l_3899_);
if (v_isSharedCheck_4500_ == 0)
{
lean_object* v_unused_4501_; lean_object* v_unused_4502_; 
v_unused_4501_ = lean_ctor_get(v_l_3899_, 4);
lean_dec(v_unused_4501_);
v_unused_4502_ = lean_ctor_get(v_l_3899_, 3);
lean_dec(v_unused_4502_);
v___x_4489_ = v_l_3899_;
v_isShared_4490_ = v_isSharedCheck_4500_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_v_4487_);
lean_inc(v_k_4486_);
lean_inc(v_size_4485_);
lean_dec(v_l_3899_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4500_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v_size_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4495_; 
v_size_4491_ = lean_ctor_get(v_r_4484_, 0);
v___x_4492_ = lean_nat_add(v___x_4392_, v_size_4485_);
lean_dec(v_size_4485_);
v___x_4493_ = lean_nat_add(v___x_4392_, v_size_4491_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 4, v_impl_4391_);
lean_ctor_set(v___x_4489_, 3, v_r_4484_);
lean_ctor_set(v___x_4489_, 2, v_v_3898_);
lean_ctor_set(v___x_4489_, 1, v_k_3897_);
lean_ctor_set(v___x_4489_, 0, v___x_4493_);
v___x_4495_ = v___x_4489_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4493_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4499_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4499_, 3, v_r_4484_);
lean_ctor_set(v_reuseFailAlloc_4499_, 4, v_impl_4391_);
v___x_4495_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
lean_object* v___x_4497_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v___x_4495_);
lean_ctor_set(v___x_3902_, 3, v_l_4483_);
lean_ctor_set(v___x_3902_, 2, v_v_4487_);
lean_ctor_set(v___x_3902_, 1, v_k_4486_);
lean_ctor_set(v___x_3902_, 0, v___x_4492_);
v___x_4497_ = v___x_3902_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4492_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v_k_4486_);
lean_ctor_set(v_reuseFailAlloc_4498_, 2, v_v_4487_);
lean_ctor_set(v_reuseFailAlloc_4498_, 3, v_l_4483_);
lean_ctor_set(v_reuseFailAlloc_4498_, 4, v___x_4495_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
else
{
lean_object* v_k_4503_; lean_object* v_v_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4515_; 
v_k_4503_ = lean_ctor_get(v_l_3899_, 1);
v_v_4504_ = lean_ctor_get(v_l_3899_, 2);
v_isSharedCheck_4515_ = !lean_is_exclusive(v_l_3899_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; lean_object* v_unused_4517_; lean_object* v_unused_4518_; 
v_unused_4516_ = lean_ctor_get(v_l_3899_, 4);
lean_dec(v_unused_4516_);
v_unused_4517_ = lean_ctor_get(v_l_3899_, 3);
lean_dec(v_unused_4517_);
v_unused_4518_ = lean_ctor_get(v_l_3899_, 0);
lean_dec(v_unused_4518_);
v___x_4506_ = v_l_3899_;
v_isShared_4507_ = v_isSharedCheck_4515_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_v_4504_);
lean_inc(v_k_4503_);
lean_dec(v_l_3899_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4515_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4508_ = lean_unsigned_to_nat(3u);
if (v_isShared_4507_ == 0)
{
lean_ctor_set(v___x_4506_, 3, v_r_4484_);
lean_ctor_set(v___x_4506_, 2, v_v_3898_);
lean_ctor_set(v___x_4506_, 1, v_k_3897_);
lean_ctor_set(v___x_4506_, 0, v___x_4392_);
v___x_4510_ = v___x_4506_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4392_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4514_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4514_, 3, v_r_4484_);
lean_ctor_set(v_reuseFailAlloc_4514_, 4, v_r_4484_);
v___x_4510_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4512_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v___x_4510_);
lean_ctor_set(v___x_3902_, 3, v_l_4483_);
lean_ctor_set(v___x_3902_, 2, v_v_4504_);
lean_ctor_set(v___x_3902_, 1, v_k_4503_);
lean_ctor_set(v___x_3902_, 0, v___x_4508_);
v___x_4512_ = v___x_3902_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v_k_4503_);
lean_ctor_set(v_reuseFailAlloc_4513_, 2, v_v_4504_);
lean_ctor_set(v_reuseFailAlloc_4513_, 3, v_l_4483_);
lean_ctor_set(v_reuseFailAlloc_4513_, 4, v___x_4510_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
}
else
{
lean_object* v_r_4519_; 
v_r_4519_ = lean_ctor_get(v_l_3899_, 4);
lean_inc(v_r_4519_);
if (lean_obj_tag(v_r_4519_) == 0)
{
lean_object* v_k_4520_; lean_object* v_v_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4544_; 
lean_inc(v_l_4483_);
v_k_4520_ = lean_ctor_get(v_l_3899_, 1);
v_v_4521_ = lean_ctor_get(v_l_3899_, 2);
v_isSharedCheck_4544_ = !lean_is_exclusive(v_l_3899_);
if (v_isSharedCheck_4544_ == 0)
{
lean_object* v_unused_4545_; lean_object* v_unused_4546_; lean_object* v_unused_4547_; 
v_unused_4545_ = lean_ctor_get(v_l_3899_, 4);
lean_dec(v_unused_4545_);
v_unused_4546_ = lean_ctor_get(v_l_3899_, 3);
lean_dec(v_unused_4546_);
v_unused_4547_ = lean_ctor_get(v_l_3899_, 0);
lean_dec(v_unused_4547_);
v___x_4523_ = v_l_3899_;
v_isShared_4524_ = v_isSharedCheck_4544_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_v_4521_);
lean_inc(v_k_4520_);
lean_dec(v_l_3899_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4544_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v_k_4525_; lean_object* v_v_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4540_; 
v_k_4525_ = lean_ctor_get(v_r_4519_, 1);
v_v_4526_ = lean_ctor_get(v_r_4519_, 2);
v_isSharedCheck_4540_ = !lean_is_exclusive(v_r_4519_);
if (v_isSharedCheck_4540_ == 0)
{
lean_object* v_unused_4541_; lean_object* v_unused_4542_; lean_object* v_unused_4543_; 
v_unused_4541_ = lean_ctor_get(v_r_4519_, 4);
lean_dec(v_unused_4541_);
v_unused_4542_ = lean_ctor_get(v_r_4519_, 3);
lean_dec(v_unused_4542_);
v_unused_4543_ = lean_ctor_get(v_r_4519_, 0);
lean_dec(v_unused_4543_);
v___x_4528_ = v_r_4519_;
v_isShared_4529_ = v_isSharedCheck_4540_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_v_4526_);
lean_inc(v_k_4525_);
lean_dec(v_r_4519_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4540_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4530_; lean_object* v___x_4532_; 
v___x_4530_ = lean_unsigned_to_nat(3u);
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 4, v_l_4483_);
lean_ctor_set(v___x_4528_, 3, v_l_4483_);
lean_ctor_set(v___x_4528_, 2, v_v_4521_);
lean_ctor_set(v___x_4528_, 1, v_k_4520_);
lean_ctor_set(v___x_4528_, 0, v___x_4392_);
v___x_4532_ = v___x_4528_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4392_);
lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_k_4520_);
lean_ctor_set(v_reuseFailAlloc_4539_, 2, v_v_4521_);
lean_ctor_set(v_reuseFailAlloc_4539_, 3, v_l_4483_);
lean_ctor_set(v_reuseFailAlloc_4539_, 4, v_l_4483_);
v___x_4532_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
lean_object* v___x_4534_; 
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 4, v_l_4483_);
lean_ctor_set(v___x_4523_, 2, v_v_3898_);
lean_ctor_set(v___x_4523_, 1, v_k_3897_);
lean_ctor_set(v___x_4523_, 0, v___x_4392_);
v___x_4534_ = v___x_4523_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v___x_4392_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4538_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4538_, 3, v_l_4483_);
lean_ctor_set(v_reuseFailAlloc_4538_, 4, v_l_4483_);
v___x_4534_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
lean_object* v___x_4536_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v___x_4534_);
lean_ctor_set(v___x_3902_, 3, v___x_4532_);
lean_ctor_set(v___x_3902_, 2, v_v_4526_);
lean_ctor_set(v___x_3902_, 1, v_k_4525_);
lean_ctor_set(v___x_3902_, 0, v___x_4530_);
v___x_4536_ = v___x_3902_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4530_);
lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_k_4525_);
lean_ctor_set(v_reuseFailAlloc_4537_, 2, v_v_4526_);
lean_ctor_set(v_reuseFailAlloc_4537_, 3, v___x_4532_);
lean_ctor_set(v_reuseFailAlloc_4537_, 4, v___x_4534_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
}
}
else
{
lean_object* v___x_4548_; lean_object* v___x_4550_; 
v___x_4548_ = lean_unsigned_to_nat(2u);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v_r_4519_);
lean_ctor_set(v___x_3902_, 0, v___x_4548_);
v___x_4550_ = v___x_3902_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4548_);
lean_ctor_set(v_reuseFailAlloc_4551_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4551_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4551_, 3, v_l_3899_);
lean_ctor_set(v_reuseFailAlloc_4551_, 4, v_r_4519_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
else
{
lean_object* v___x_4553_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v_l_3899_);
lean_ctor_set(v___x_3902_, 0, v___x_4392_);
v___x_4553_ = v___x_3902_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4392_);
lean_ctor_set(v_reuseFailAlloc_4554_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_4554_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_4554_, 3, v_l_3899_);
lean_ctor_set(v_reuseFailAlloc_4554_, 4, v_l_3899_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_3895_);
lean_dec_ref(v_cmp_3894_);
return v_t_3896_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(lean_object* v_cmp_4557_, lean_object* v_init_4558_, lean_object* v_x_4559_){
_start:
{
if (lean_obj_tag(v_x_4559_) == 0)
{
lean_object* v_k_4560_; lean_object* v_l_4561_; lean_object* v_r_4562_; lean_object* v___x_4563_; lean_object* v_a_4564_; lean_object* v_r_4565_; 
v_k_4560_ = lean_ctor_get(v_x_4559_, 1);
lean_inc(v_k_4560_);
v_l_4561_ = lean_ctor_get(v_x_4559_, 3);
lean_inc(v_l_4561_);
v_r_4562_ = lean_ctor_get(v_x_4559_, 4);
lean_inc(v_r_4562_);
lean_dec_ref_known(v_x_4559_, 5);
lean_inc_ref_n(v_cmp_4557_, 2);
v___x_4563_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4557_, v_init_4558_, v_l_4561_);
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref(v___x_4563_);
v_r_4565_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_4557_, v_k_4560_, v_a_4564_);
v_init_4558_ = v_r_4565_;
v_x_4559_ = v_r_4562_;
goto _start;
}
else
{
lean_object* v___x_4567_; 
lean_dec_ref(v_cmp_4557_);
v___x_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4567_, 0, v_init_4558_);
return v___x_4567_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(lean_object* v_cmp_4568_, lean_object* v_t_u2082_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v_t_4572_){
_start:
{
if (lean_obj_tag(v_t_4572_) == 0)
{
lean_object* v_k_4573_; lean_object* v_v_4574_; lean_object* v_l_4575_; lean_object* v_r_4576_; uint8_t v___x_4581_; 
v_k_4573_ = lean_ctor_get(v_t_4572_, 1);
lean_inc_n(v_k_4573_, 2);
v_v_4574_ = lean_ctor_get(v_t_4572_, 2);
lean_inc(v_v_4574_);
v_l_4575_ = lean_ctor_get(v_t_4572_, 3);
lean_inc(v_l_4575_);
v_r_4576_ = lean_ctor_get(v_t_4572_, 4);
lean_inc(v_r_4576_);
lean_dec_ref_known(v_t_4572_, 5);
lean_inc(v_t_u2082_4569_);
lean_inc_ref(v_cmp_4568_);
v___x_4581_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_4568_, v_k_4573_, v_t_u2082_4569_);
if (v___x_4581_ == 0)
{
uint8_t v___x_4582_; 
v___x_4582_ = lean_nat_dec_le(v___y_4570_, v___y_4571_);
if (v___x_4582_ == 0)
{
lean_dec(v_v_4574_);
lean_dec(v_k_4573_);
goto v___jp_4577_;
}
else
{
lean_object* v_impl_4583_; lean_object* v_impl_4584_; lean_object* v___x_4585_; 
lean_inc(v_t_u2082_4569_);
lean_inc_ref(v_cmp_4568_);
v_impl_4583_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4568_, v_t_u2082_4569_, v___y_4570_, v___y_4571_, v_l_4575_);
v_impl_4584_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4568_, v_t_u2082_4569_, v___y_4570_, v___y_4571_, v_r_4576_);
v___x_4585_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_4573_, v_v_4574_, v_impl_4583_, v_impl_4584_);
return v___x_4585_;
}
}
else
{
lean_dec(v_v_4574_);
lean_dec(v_k_4573_);
goto v___jp_4577_;
}
v___jp_4577_:
{
lean_object* v_impl_4578_; lean_object* v_impl_4579_; lean_object* v___x_4580_; 
lean_inc(v_t_u2082_4569_);
lean_inc_ref(v_cmp_4568_);
v_impl_4578_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4568_, v_t_u2082_4569_, v___y_4570_, v___y_4571_, v_l_4575_);
v_impl_4579_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4568_, v_t_u2082_4569_, v___y_4570_, v___y_4571_, v_r_4576_);
v___x_4580_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_4578_, v_impl_4579_);
return v___x_4580_;
}
}
else
{
lean_dec(v_t_u2082_4569_);
lean_dec_ref(v_cmp_4568_);
return v_t_4572_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg___boxed(lean_object* v_cmp_4586_, lean_object* v_t_u2082_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v_t_4590_){
_start:
{
lean_object* v_res_4591_; 
v_res_4591_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4586_, v_t_u2082_4587_, v___y_4588_, v___y_4589_, v_t_4590_);
lean_dec(v___y_4589_);
lean_dec(v___y_4588_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object* v_cmp_4592_, lean_object* v_t_u2081_4593_, lean_object* v_t_u2082_4594_){
_start:
{
lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v___y_4603_; 
if (lean_obj_tag(v_t_u2081_4593_) == 0)
{
lean_object* v_size_4606_; 
v_size_4606_ = lean_ctor_get(v_t_u2081_4593_, 0);
lean_inc(v_size_4606_);
v___y_4603_ = v_size_4606_;
goto v___jp_4602_;
}
else
{
lean_object* v___x_4607_; 
v___x_4607_ = lean_unsigned_to_nat(0u);
v___y_4603_ = v___x_4607_;
goto v___jp_4602_;
}
v___jp_4595_:
{
uint8_t v___x_4598_; 
v___x_4598_ = lean_nat_dec_le(v___y_4596_, v___y_4597_);
if (v___x_4598_ == 0)
{
lean_object* v___x_4599_; lean_object* v_a_4600_; 
lean_dec(v___y_4597_);
lean_dec(v___y_4596_);
v___x_4599_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4592_, v_t_u2081_4593_, v_t_u2082_4594_);
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_a_4600_);
lean_dec_ref(v___x_4599_);
return v_a_4600_;
}
else
{
lean_object* v___x_4601_; 
v___x_4601_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4592_, v_t_u2082_4594_, v___y_4596_, v___y_4597_, v_t_u2081_4593_);
lean_dec(v___y_4597_);
lean_dec(v___y_4596_);
return v___x_4601_;
}
}
v___jp_4602_:
{
if (lean_obj_tag(v_t_u2082_4594_) == 0)
{
lean_object* v_size_4604_; 
v_size_4604_ = lean_ctor_get(v_t_u2082_4594_, 0);
lean_inc(v_size_4604_);
v___y_4596_ = v___y_4603_;
v___y_4597_ = v_size_4604_;
goto v___jp_4595_;
}
else
{
lean_object* v___x_4605_; 
v___x_4605_ = lean_unsigned_to_nat(0u);
v___y_4596_ = v___y_4603_;
v___y_4597_ = v___x_4605_;
goto v___jp_4595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff___redArg(lean_object* v_cmp_4608_, lean_object* v_t_u2081_4609_, lean_object* v_t_u2082_4610_){
_start:
{
lean_object* v___x_4611_; 
v___x_4611_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4608_, v_t_u2081_4609_, v_t_u2082_4610_);
return v___x_4611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff(lean_object* v_00_u03b1_4612_, lean_object* v_00_u03b2_4613_, lean_object* v_cmp_4614_, lean_object* v_t_u2081_4615_, lean_object* v_t_u2082_4616_){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4614_, v_t_u2081_4615_, v_t_u2082_4616_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0(lean_object* v_00_u03b1_4618_, lean_object* v_cmp_4619_, lean_object* v_00_u03b2_4620_, lean_object* v_t_u2081_4621_, lean_object* v_t_u2082_4622_, lean_object* v_h_u2081_4623_){
_start:
{
lean_object* v___x_4624_; 
v___x_4624_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4619_, v_t_u2081_4621_, v_t_u2082_4622_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0(lean_object* v_00_u03b1_4625_, lean_object* v_cmp_4626_, lean_object* v_00_u03b2_4627_, lean_object* v_k_4628_, lean_object* v_t_4629_, lean_object* v_h_4630_){
_start:
{
lean_object* v___x_4631_; 
v___x_4631_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_4626_, v_k_4628_, v_t_4629_);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1(lean_object* v_00_u03b1_4632_, lean_object* v_00_u03b2_4633_, lean_object* v_cmp_4634_, lean_object* v_init_4635_, lean_object* v_x_4636_){
_start:
{
lean_object* v___x_4637_; 
v___x_4637_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4634_, v_init_4635_, v_x_4636_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2(lean_object* v_00_u03b1_4638_, lean_object* v_00_u03b2_4639_, lean_object* v_cmp_4640_, lean_object* v_t_u2082_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v_t_4644_, lean_object* v_hl_4645_){
_start:
{
lean_object* v___x_4646_; 
v___x_4646_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4640_, v_t_u2082_4641_, v___y_4642_, v___y_4643_, v_t_4644_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4647_, lean_object* v_00_u03b2_4648_, lean_object* v_cmp_4649_, lean_object* v_t_u2082_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v_t_4653_, lean_object* v_hl_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2(v_00_u03b1_4647_, v_00_u03b2_4648_, v_cmp_4649_, v_t_u2082_4650_, v___y_4651_, v___y_4652_, v_t_4653_, v_hl_4654_);
lean_dec(v___y_4652_);
lean_dec(v___y_4651_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSDiff___redArg(lean_object* v_cmp_4656_){
_start:
{
lean_object* v___x_4657_; 
v___x_4657_ = lean_alloc_closure((void*)(l_Std_DTreeMap_diff), 5, 3);
lean_closure_set(v___x_4657_, 0, lean_box(0));
lean_closure_set(v___x_4657_, 1, lean_box(0));
lean_closure_set(v___x_4657_, 2, v_cmp_4656_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSDiff(lean_object* v_00_u03b1_4658_, lean_object* v_00_u03b2_4659_, lean_object* v_cmp_4660_){
_start:
{
lean_object* v___x_4661_; 
v___x_4661_ = lean_alloc_closure((void*)(l_Std_DTreeMap_diff), 5, 3);
lean_closure_set(v___x_4661_, 0, lean_box(0));
lean_closure_set(v___x_4661_, 1, lean_box(0));
lean_closure_set(v___x_4661_, 2, v_cmp_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_4662_, lean_object* v_a_4663_, lean_object* v_____s_4664_){
_start:
{
lean_object* v_r_4665_; lean_object* v___x_4666_; 
v_r_4665_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_4662_, v_a_4663_, v_____s_4664_);
v___x_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4666_, 0, v_r_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany___redArg(lean_object* v_cmp_4667_, lean_object* v_inst_4668_, lean_object* v_t_4669_, lean_object* v_l_4670_){
_start:
{
lean_object* v___f_4671_; lean_object* v___x_4672_; 
v___f_4671_ = lean_alloc_closure((void*)(l_Std_DTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4671_, 0, v_cmp_4667_);
v___x_4672_ = lean_apply_4(v_inst_4668_, lean_box(0), v_l_4670_, v_t_4669_, v___f_4671_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany(lean_object* v_00_u03b1_4673_, lean_object* v_00_u03b2_4674_, lean_object* v_cmp_4675_, lean_object* v_00_u03c1_4676_, lean_object* v_inst_4677_, lean_object* v_t_4678_, lean_object* v_l_4679_){
_start:
{
lean_object* v___f_4680_; lean_object* v___x_4681_; 
v___f_4680_ = lean_alloc_closure((void*)(l_Std_DTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4680_, 0, v_cmp_4675_);
v___x_4681_ = lean_apply_4(v_inst_4677_, lean_box(0), v_l_4679_, v_t_4678_, v___f_4680_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany___redArg___lam__0(lean_object* v_cmp_4682_, lean_object* v_x_4683_, lean_object* v_____s_4684_){
_start:
{
lean_object* v_fst_4685_; lean_object* v_snd_4686_; lean_object* v_r_4687_; lean_object* v___x_4688_; 
v_fst_4685_ = lean_ctor_get(v_x_4683_, 0);
lean_inc(v_fst_4685_);
v_snd_4686_ = lean_ctor_get(v_x_4683_, 1);
lean_inc(v_snd_4686_);
lean_dec_ref(v_x_4683_);
v_r_4687_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4682_, v_fst_4685_, v_snd_4686_, v_____s_4684_);
v___x_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4688_, 0, v_r_4687_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany___redArg(lean_object* v_cmp_4689_, lean_object* v_inst_4690_, lean_object* v_t_4691_, lean_object* v_l_4692_){
_start:
{
lean_object* v___f_4693_; lean_object* v___x_4694_; 
v___f_4693_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4693_, 0, v_cmp_4689_);
v___x_4694_ = lean_apply_4(v_inst_4690_, lean_box(0), v_l_4692_, v_t_4691_, v___f_4693_);
return v___x_4694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany(lean_object* v_00_u03b1_4695_, lean_object* v_cmp_4696_, lean_object* v_00_u03b2_4697_, lean_object* v_00_u03c1_4698_, lean_object* v_inst_4699_, lean_object* v_t_4700_, lean_object* v_l_4701_){
_start:
{
lean_object* v___f_4702_; lean_object* v___x_4703_; 
v___f_4702_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4702_, 0, v_cmp_4696_);
v___x_4703_ = lean_apply_4(v_inst_4699_, lean_box(0), v_l_4701_, v_t_4700_, v___f_4702_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_4704_, lean_object* v_a_4705_, lean_object* v_____s_4706_){
_start:
{
uint8_t v___x_4707_; 
lean_inc(v_____s_4706_);
lean_inc(v_a_4705_);
lean_inc_ref(v_cmp_4704_);
v___x_4707_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4704_, v_a_4705_, v_____s_4706_);
if (v___x_4707_ == 0)
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4708_ = lean_box(0);
v___x_4709_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4704_, v_a_4705_, v___x_4708_, v_____s_4706_);
v___x_4710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
return v___x_4710_;
}
else
{
lean_object* v___x_4711_; 
lean_dec(v_a_4705_);
lean_dec_ref(v_cmp_4704_);
v___x_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4711_, 0, v_____s_4706_);
return v___x_4711_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_4712_, lean_object* v_inst_4713_, lean_object* v_t_4714_, lean_object* v_l_4715_){
_start:
{
lean_object* v___f_4716_; lean_object* v___x_4717_; 
v___f_4716_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4716_, 0, v_cmp_4712_);
v___x_4717_ = lean_apply_4(v_inst_4713_, lean_box(0), v_l_4715_, v_t_4714_, v___f_4716_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_4718_, lean_object* v_cmp_4719_, lean_object* v_00_u03c1_4720_, lean_object* v_inst_4721_, lean_object* v_t_4722_, lean_object* v_l_4723_){
_start:
{
lean_object* v___f_4724_; lean_object* v___x_4725_; 
v___f_4724_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4724_, 0, v_cmp_4719_);
v___x_4725_ = lean_apply_4(v_inst_4721_, lean_box(0), v_l_4723_, v_t_4722_, v___f_4724_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1(lean_object* v___f_4729_, lean_object* v___x_4730_, lean_object* v_m_4731_, lean_object* v_prec_4732_){
_start:
{
lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4733_ = ((lean_object*)(l_Std_DTreeMap_instRepr___redArg___lam__1___closed__1));
v___x_4734_ = lean_box(0);
v___x_4735_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_4736_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_4735_, v___f_4729_, v___x_4734_, v_m_4731_);
v___x_4737_ = l_List_repr___redArg(v___x_4730_, v___x_4736_);
v___x_4738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4733_);
lean_ctor_set(v___x_4738_, 1, v___x_4737_);
v___x_4739_ = l_Repr_addAppParen(v___x_4738_, v_prec_4732_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1___boxed(lean_object* v___f_4740_, lean_object* v___x_4741_, lean_object* v_m_4742_, lean_object* v_prec_4743_){
_start:
{
lean_object* v_res_4744_; 
v_res_4744_ = l_Std_DTreeMap_instRepr___redArg___lam__1(v___f_4740_, v___x_4741_, v_m_4742_, v_prec_4743_);
lean_dec(v_prec_4743_);
return v_res_4744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg(lean_object* v_inst_4745_, lean_object* v_inst_4746_){
_start:
{
lean_object* v___f_4747_; lean_object* v___x_4748_; lean_object* v___f_4749_; 
v___f_4747_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_4748_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_4748_, 0, lean_box(0));
lean_closure_set(v___x_4748_, 1, lean_box(0));
lean_closure_set(v___x_4748_, 2, v_inst_4745_);
lean_closure_set(v___x_4748_, 3, v_inst_4746_);
v___f_4749_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4749_, 0, v___f_4747_);
lean_closure_set(v___f_4749_, 1, v___x_4748_);
return v___f_4749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr(lean_object* v_00_u03b1_4750_, lean_object* v_00_u03b2_4751_, lean_object* v_cmp_4752_, lean_object* v_inst_4753_, lean_object* v_inst_4754_){
_start:
{
lean_object* v___x_4755_; 
v___x_4755_ = l_Std_DTreeMap_instRepr___redArg(v_inst_4753_, v_inst_4754_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___boxed(lean_object* v_00_u03b1_4756_, lean_object* v_00_u03b2_4757_, lean_object* v_cmp_4758_, lean_object* v_inst_4759_, lean_object* v_inst_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l_Std_DTreeMap_instRepr(v_00_u03b1_4756_, v_00_u03b2_4757_, v_cmp_4758_, v_inst_4759_, v_inst_4760_);
lean_dec_ref(v_cmp_4758_);
return v_res_4761_;
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
