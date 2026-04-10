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
v_currMacroScope_165_ = lean_ctor_get(v_a_158_, 2);
v_ref_166_ = lean_ctor_get(v_a_158_, 5);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = l_Lean_Syntax_getArg(v_x_157_, v___x_167_);
v___x_169_ = lean_unsigned_to_nat(2u);
v___x_170_ = l_Lean_Syntax_getArg(v_x_157_, v___x_169_);
lean_dec(v_x_157_);
v___x_171_ = 0;
v___x_172_ = l_Lean_SourceInfo_fromRef(v_ref_166_, v___x_171_);
v___x_173_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2));
v___x_174_ = lean_obj_once(&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4, &l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4_once, _init_l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4);
v___x_175_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_165_);
lean_inc(v_quotContext_164_);
v___x_176_ = l_Lean_addMacroScope(v_quotContext_164_, v___x_175_, v_currMacroScope_165_);
v___x_177_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__10));
lean_inc_n(v___x_172_, 2);
v___x_178_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_178_, 0, v___x_172_);
lean_ctor_set(v___x_178_, 1, v___x_174_);
lean_ctor_set(v___x_178_, 2, v___x_176_);
lean_ctor_set(v___x_178_, 3, v___x_177_);
v___x_179_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__9));
v___x_180_ = l_Lean_Syntax_node2(v___x_172_, v___x_179_, v___x_168_, v___x_170_);
v___x_181_ = l_Lean_Syntax_node2(v___x_172_, v___x_173_, v___x_178_, v___x_180_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_a_159_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___boxed(lean_object* v_x_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1(v_x_183_, v_a_184_, v_a_185_);
lean_dec_ref(v_a_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(lean_object* v_x_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2));
lean_inc(v_x_190_);
v___x_194_ = l_Lean_Syntax_isOfKind(v_x_190_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v_x_190_);
v___x_195_ = lean_box(0);
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_192_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = l_Lean_Syntax_getArg(v_x_190_, v___x_197_);
v___x_199_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__1));
lean_inc(v___x_198_);
v___x_200_ = l_Lean_Syntax_isOfKind(v___x_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v___x_198_);
lean_dec(v_x_190_);
v___x_201_ = lean_box(0);
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_a_192_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = l_Lean_Syntax_getArg(v_x_190_, v___x_203_);
lean_dec(v_x_190_);
v___x_205_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_204_);
v___x_206_ = l_Lean_Syntax_matchesNull(v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v___x_204_);
lean_dec(v___x_198_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_a_192_);
return v___x_208_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_ref_211_; uint8_t v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_209_ = l_Lean_Syntax_getArg(v___x_204_, v___x_197_);
v___x_210_ = l_Lean_Syntax_getArg(v___x_204_, v___x_203_);
lean_dec(v___x_204_);
v_ref_211_ = l_Lean_replaceRef(v___x_198_, v_a_191_);
lean_dec(v___x_198_);
v___x_212_ = 0;
v___x_213_ = l_Lean_SourceInfo_fromRef(v_ref_211_, v___x_212_);
lean_dec(v_ref_211_);
v___x_214_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__3));
v___x_215_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__6));
lean_inc(v___x_213_);
v___x_216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_213_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = l_Lean_Syntax_node3(v___x_213_, v___x_214_, v___x_209_, v___x_216_, v___x_210_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_a_192_);
return v___x_218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___boxed(lean_object* v_x_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(v_x_219_, v_a_220_, v_a_221_);
lean_dec(v_a_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insert___redArg(lean_object* v_cmp_223_, lean_object* v_t_224_, lean_object* v_a_225_, lean_object* v_b_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_223_, v_a_225_, v_b_226_, v_t_224_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insert(lean_object* v_00_u03b1_228_, lean_object* v_00_u03b2_229_, lean_object* v_cmp_230_, lean_object* v_t_231_, lean_object* v_a_232_, lean_object* v_b_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_230_, v_a_232_, v_b_233_, v_t_231_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma___redArg___lam__0(lean_object* v_cmp_235_, lean_object* v_e_236_){
_start:
{
lean_object* v_fst_237_; lean_object* v_snd_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_fst_237_ = lean_ctor_get(v_e_236_, 0);
lean_inc(v_fst_237_);
v_snd_238_ = lean_ctor_get(v_e_236_, 1);
lean_inc(v_snd_238_);
lean_dec_ref(v_e_236_);
v___x_239_ = lean_box(1);
v___x_240_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_235_, v_fst_237_, v_snd_238_, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma___redArg(lean_object* v_cmp_241_){
_start:
{
lean_object* v___f_242_; 
v___f_242_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_242_, 0, v_cmp_241_);
return v___f_242_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma(lean_object* v_00_u03b1_243_, lean_object* v_00_u03b2_244_, lean_object* v_cmp_245_){
_start:
{
lean_object* v___f_246_; 
v___f_246_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_246_, 0, v_cmp_245_);
return v___f_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma___redArg___lam__0(lean_object* v_cmp_247_, lean_object* v_e_248_, lean_object* v_s_249_){
_start:
{
lean_object* v_fst_250_; lean_object* v_snd_251_; lean_object* v___x_252_; 
v_fst_250_ = lean_ctor_get(v_e_248_, 0);
lean_inc(v_fst_250_);
v_snd_251_ = lean_ctor_get(v_e_248_, 1);
lean_inc(v_snd_251_);
lean_dec_ref(v_e_248_);
v___x_252_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_247_, v_fst_250_, v_snd_251_, v_s_249_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma___redArg(lean_object* v_cmp_253_){
_start:
{
lean_object* v___f_254_; 
v___f_254_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_254_, 0, v_cmp_253_);
return v___f_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma(lean_object* v_00_u03b1_255_, lean_object* v_00_u03b2_256_, lean_object* v_cmp_257_){
_start:
{
lean_object* v___f_258_; 
v___f_258_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_258_, 0, v_cmp_257_);
return v___f_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertIfNew___redArg(lean_object* v_cmp_259_, lean_object* v_t_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
uint8_t v___x_263_; 
lean_inc(v_t_260_);
lean_inc(v_a_261_);
lean_inc_ref(v_cmp_259_);
v___x_263_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_259_, v_a_261_, v_t_260_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
v___x_264_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_259_, v_a_261_, v_b_262_, v_t_260_);
return v___x_264_;
}
else
{
lean_dec(v_b_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_cmp_259_);
return v_t_260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertIfNew(lean_object* v_00_u03b1_265_, lean_object* v_00_u03b2_266_, lean_object* v_cmp_267_, lean_object* v_t_268_, lean_object* v_a_269_, lean_object* v_b_270_){
_start:
{
uint8_t v___x_271_; 
lean_inc(v_t_268_);
lean_inc(v_a_269_);
lean_inc_ref(v_cmp_267_);
v___x_271_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_267_, v_a_269_, v_t_268_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_267_, v_a_269_, v_b_270_, v_t_268_);
return v___x_272_;
}
else
{
lean_dec(v_b_270_);
lean_dec(v_a_269_);
lean_dec_ref(v_cmp_267_);
return v_t_268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsert___redArg(lean_object* v_cmp_273_, lean_object* v_t_274_, lean_object* v_a_275_, lean_object* v_b_276_){
_start:
{
lean_object* v_sz_277_; lean_object* v_m_278_; lean_object* v___y_280_; 
v_sz_277_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_274_);
v_m_278_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_273_, v_a_275_, v_b_276_, v_t_274_);
if (lean_obj_tag(v_m_278_) == 0)
{
lean_object* v_size_284_; 
v_size_284_ = lean_ctor_get(v_m_278_, 0);
lean_inc(v_size_284_);
v___y_280_ = v_size_284_;
goto v___jp_279_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___y_280_ = v___x_285_;
goto v___jp_279_;
}
v___jp_279_:
{
uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_nat_dec_eq(v_sz_277_, v___y_280_);
lean_dec(v___y_280_);
lean_dec(v_sz_277_);
v___x_282_ = lean_box(v___x_281_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_m_278_);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsert(lean_object* v_00_u03b1_286_, lean_object* v_00_u03b2_287_, lean_object* v_cmp_288_, lean_object* v_t_289_, lean_object* v_a_290_, lean_object* v_b_291_){
_start:
{
lean_object* v_sz_292_; lean_object* v_m_293_; lean_object* v___y_295_; 
v_sz_292_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_289_);
v_m_293_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_288_, v_a_290_, v_b_291_, v_t_289_);
if (lean_obj_tag(v_m_293_) == 0)
{
lean_object* v_size_299_; 
v_size_299_ = lean_ctor_get(v_m_293_, 0);
lean_inc(v_size_299_);
v___y_295_ = v_size_299_;
goto v___jp_294_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = lean_unsigned_to_nat(0u);
v___y_295_ = v___x_300_;
goto v___jp_294_;
}
v___jp_294_:
{
uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_nat_dec_eq(v_sz_292_, v___y_295_);
lean_dec(v___y_295_);
lean_dec(v_sz_292_);
v___x_297_ = lean_box(v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_m_293_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_301_, lean_object* v_t_302_, lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
uint8_t v___x_305_; 
lean_inc(v_t_302_);
lean_inc(v_a_303_);
lean_inc_ref(v_cmp_301_);
v___x_305_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_301_, v_a_303_, v_t_302_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_301_, v_a_303_, v_b_304_, v_t_302_);
v___x_307_ = lean_box(v___x_305_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_306_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v_b_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_cmp_301_);
v___x_309_ = lean_box(v___x_305_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v_t_302_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_311_, lean_object* v_00_u03b2_312_, lean_object* v_cmp_313_, lean_object* v_t_314_, lean_object* v_a_315_, lean_object* v_b_316_){
_start:
{
uint8_t v___x_317_; 
lean_inc(v_t_314_);
lean_inc(v_a_315_);
lean_inc_ref(v_cmp_313_);
v___x_317_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_313_, v_a_315_, v_t_314_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_313_, v_a_315_, v_b_316_, v_t_314_);
v___x_319_ = lean_box(v___x_317_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec(v_b_316_);
lean_dec(v_a_315_);
lean_dec_ref(v_cmp_313_);
v___x_321_ = lean_box(v___x_317_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v_t_314_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_323_, lean_object* v_t_324_, lean_object* v_a_325_, lean_object* v_b_326_){
_start:
{
lean_object* v___x_327_; 
lean_inc(v_a_325_);
lean_inc(v_t_324_);
lean_inc_ref(v_cmp_323_);
v___x_327_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_323_, v_t_324_, v_a_325_);
if (lean_obj_tag(v___x_327_) == 0)
{
uint8_t v___x_328_; 
lean_inc(v_t_324_);
lean_inc(v_a_325_);
lean_inc_ref(v_cmp_323_);
v___x_328_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_323_, v_a_325_, v_t_324_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_323_, v_a_325_, v_b_326_, v_t_324_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_327_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; 
lean_dec(v_b_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_cmp_323_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_327_);
lean_ctor_set(v___x_331_, 1, v_t_324_);
return v___x_331_;
}
}
else
{
lean_object* v___x_332_; 
lean_dec(v_b_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_cmp_323_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_327_);
lean_ctor_set(v___x_332_, 1, v_t_324_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_333_, lean_object* v_00_u03b2_334_, lean_object* v_cmp_335_, lean_object* v_inst_336_, lean_object* v_t_337_, lean_object* v_a_338_, lean_object* v_b_339_){
_start:
{
lean_object* v___x_340_; 
lean_inc(v_a_338_);
lean_inc(v_t_337_);
lean_inc_ref(v_cmp_335_);
v___x_340_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_335_, v_t_337_, v_a_338_);
if (lean_obj_tag(v___x_340_) == 0)
{
uint8_t v___x_341_; 
lean_inc(v_t_337_);
lean_inc(v_a_338_);
lean_inc_ref(v_cmp_335_);
v___x_341_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_335_, v_a_338_, v_t_337_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_335_, v_a_338_, v_b_339_, v_t_337_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_340_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; 
lean_dec(v_b_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_cmp_335_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_340_);
lean_ctor_set(v___x_344_, 1, v_t_337_);
return v___x_344_;
}
}
else
{
lean_object* v___x_345_; 
lean_dec(v_b_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_cmp_335_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_340_);
lean_ctor_set(v___x_345_, 1, v_t_337_);
return v___x_345_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_contains___redArg(lean_object* v_cmp_346_, lean_object* v_t_347_, lean_object* v_a_348_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_346_, v_a_348_, v_t_347_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_contains___redArg___boxed(lean_object* v_cmp_350_, lean_object* v_t_351_, lean_object* v_a_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Std_DTreeMap_contains___redArg(v_cmp_350_, v_t_351_, v_a_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_contains(lean_object* v_00_u03b1_355_, lean_object* v_00_u03b2_356_, lean_object* v_cmp_357_, lean_object* v_t_358_, lean_object* v_a_359_){
_start:
{
uint8_t v___x_360_; 
v___x_360_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_357_, v_a_359_, v_t_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_contains___boxed(lean_object* v_00_u03b1_361_, lean_object* v_00_u03b2_362_, lean_object* v_cmp_363_, lean_object* v_t_364_, lean_object* v_a_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Std_DTreeMap_contains(v_00_u03b1_361_, v_00_u03b2_362_, v_cmp_363_, v_t_364_, v_a_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_cmp_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___boxed(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_cmp_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_DTreeMap_instMembership(v_00_u03b1_372_, v_00_u03b2_373_, v_cmp_374_);
lean_dec_ref(v_cmp_374_);
return v_res_375_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableMem___redArg(lean_object* v_cmp_376_, lean_object* v_m_377_, lean_object* v_a_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_376_, v_a_378_, v_m_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_380_, lean_object* v_m_381_, lean_object* v_a_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_Std_DTreeMap_instDecidableMem___redArg(v_cmp_380_, v_m_381_, v_a_382_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableMem(lean_object* v_00_u03b1_385_, lean_object* v_00_u03b2_386_, lean_object* v_cmp_387_, lean_object* v_m_388_, lean_object* v_a_389_){
_start:
{
uint8_t v___x_390_; 
v___x_390_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_387_, v_a_389_, v_m_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_391_, lean_object* v_00_u03b2_392_, lean_object* v_cmp_393_, lean_object* v_m_394_, lean_object* v_a_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Std_DTreeMap_instDecidableMem(v_00_u03b1_391_, v_00_u03b2_392_, v_cmp_393_, v_m_394_, v_a_395_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___redArg(lean_object* v_t_398_){
_start:
{
if (lean_obj_tag(v_t_398_) == 0)
{
lean_object* v_size_399_; 
v_size_399_ = lean_ctor_get(v_t_398_, 0);
lean_inc(v_size_399_);
return v_size_399_;
}
else
{
lean_object* v___x_400_; 
v___x_400_ = lean_unsigned_to_nat(0u);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___redArg___boxed(lean_object* v_t_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Std_DTreeMap_size___redArg(v_t_401_);
lean_dec(v_t_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_cmp_405_, lean_object* v_t_406_){
_start:
{
if (lean_obj_tag(v_t_406_) == 0)
{
lean_object* v_size_407_; 
v_size_407_ = lean_ctor_get(v_t_406_, 0);
lean_inc(v_size_407_);
return v_size_407_;
}
else
{
lean_object* v___x_408_; 
v___x_408_ = lean_unsigned_to_nat(0u);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___boxed(lean_object* v_00_u03b1_409_, lean_object* v_00_u03b2_410_, lean_object* v_cmp_411_, lean_object* v_t_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_DTreeMap_size(v_00_u03b1_409_, v_00_u03b2_410_, v_cmp_411_, v_t_412_);
lean_dec(v_t_412_);
lean_dec_ref(v_cmp_411_);
return v_res_413_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_isEmpty___redArg(lean_object* v_t_414_){
_start:
{
if (lean_obj_tag(v_t_414_) == 0)
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
else
{
uint8_t v___x_416_; 
v___x_416_ = 1;
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isEmpty___redArg___boxed(lean_object* v_t_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Std_DTreeMap_isEmpty___redArg(v_t_417_);
lean_dec(v_t_417_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_isEmpty(lean_object* v_00_u03b1_420_, lean_object* v_00_u03b2_421_, lean_object* v_cmp_422_, lean_object* v_t_423_){
_start:
{
if (lean_obj_tag(v_t_423_) == 0)
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
else
{
uint8_t v___x_425_; 
v___x_425_ = 1;
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_426_, lean_object* v_00_u03b2_427_, lean_object* v_cmp_428_, lean_object* v_t_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_Std_DTreeMap_isEmpty(v_00_u03b1_426_, v_00_u03b2_427_, v_cmp_428_, v_t_429_);
lean_dec(v_t_429_);
lean_dec_ref(v_cmp_428_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_erase___redArg(lean_object* v_cmp_432_, lean_object* v_t_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_432_, v_a_434_, v_t_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_erase(lean_object* v_00_u03b1_436_, lean_object* v_00_u03b2_437_, lean_object* v_cmp_438_, lean_object* v_t_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_438_, v_a_440_, v_t_439_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x3f___redArg(lean_object* v_cmp_442_, lean_object* v_t_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_442_, v_t_443_, v_a_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x3f(lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_cmp_448_, lean_object* v_inst_449_, lean_object* v_t_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_448_, v_t_450_, v_a_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get___redArg(lean_object* v_cmp_453_, lean_object* v_t_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_453_, v_t_454_, v_a_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get(lean_object* v_00_u03b1_457_, lean_object* v_00_u03b2_458_, lean_object* v_cmp_459_, lean_object* v_inst_460_, lean_object* v_t_461_, lean_object* v_a_462_, lean_object* v_h_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_459_, v_t_461_, v_a_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___redArg(lean_object* v_cmp_465_, lean_object* v_t_466_, lean_object* v_a_467_, lean_object* v_inst_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_465_, v_t_466_, v_a_467_, v_inst_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___redArg___boxed(lean_object* v_cmp_470_, lean_object* v_t_471_, lean_object* v_a_472_, lean_object* v_inst_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_DTreeMap_get_x21___redArg(v_cmp_470_, v_t_471_, v_a_472_, v_inst_473_);
lean_dec(v_inst_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21(lean_object* v_00_u03b1_475_, lean_object* v_00_u03b2_476_, lean_object* v_cmp_477_, lean_object* v_inst_478_, lean_object* v_t_479_, lean_object* v_a_480_, lean_object* v_inst_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_477_, v_t_479_, v_a_480_, v_inst_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___boxed(lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_cmp_485_, lean_object* v_inst_486_, lean_object* v_t_487_, lean_object* v_a_488_, lean_object* v_inst_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_DTreeMap_get_x21(v_00_u03b1_483_, v_00_u03b2_484_, v_cmp_485_, v_inst_486_, v_t_487_, v_a_488_, v_inst_489_);
lean_dec(v_inst_489_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg(lean_object* v_cmp_491_, lean_object* v_t_492_, lean_object* v_a_493_, lean_object* v_fallback_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_491_, v_t_492_, v_a_493_, v_fallback_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg___boxed(lean_object* v_cmp_496_, lean_object* v_t_497_, lean_object* v_a_498_, lean_object* v_fallback_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_DTreeMap_getD___redArg(v_cmp_496_, v_t_497_, v_a_498_, v_fallback_499_);
lean_dec(v_fallback_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD(lean_object* v_00_u03b1_501_, lean_object* v_00_u03b2_502_, lean_object* v_cmp_503_, lean_object* v_inst_504_, lean_object* v_t_505_, lean_object* v_a_506_, lean_object* v_fallback_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_503_, v_t_505_, v_a_506_, v_fallback_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___boxed(lean_object* v_00_u03b1_509_, lean_object* v_00_u03b2_510_, lean_object* v_cmp_511_, lean_object* v_inst_512_, lean_object* v_t_513_, lean_object* v_a_514_, lean_object* v_fallback_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_DTreeMap_getD(v_00_u03b1_509_, v_00_u03b2_510_, v_cmp_511_, v_inst_512_, v_t_513_, v_a_514_, v_fallback_515_);
lean_dec(v_fallback_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f___redArg(lean_object* v_cmp_517_, lean_object* v_t_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_517_, v_t_518_, v_a_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f(lean_object* v_00_u03b1_521_, lean_object* v_00_u03b2_522_, lean_object* v_cmp_523_, lean_object* v_t_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_523_, v_t_524_, v_a_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey___redArg(lean_object* v_cmp_527_, lean_object* v_t_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_527_, v_t_528_, v_a_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey(lean_object* v_00_u03b1_531_, lean_object* v_00_u03b2_532_, lean_object* v_cmp_533_, lean_object* v_t_534_, lean_object* v_a_535_, lean_object* v_h_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_533_, v_t_534_, v_a_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___redArg(lean_object* v_cmp_538_, lean_object* v_inst_539_, lean_object* v_t_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_538_, v_t_540_, v_a_541_, v_inst_539_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___redArg___boxed(lean_object* v_cmp_543_, lean_object* v_inst_544_, lean_object* v_t_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_DTreeMap_getKey_x21___redArg(v_cmp_543_, v_inst_544_, v_t_545_, v_a_546_);
lean_dec(v_inst_544_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21(lean_object* v_00_u03b1_548_, lean_object* v_00_u03b2_549_, lean_object* v_cmp_550_, lean_object* v_inst_551_, lean_object* v_t_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_550_, v_t_552_, v_a_553_, v_inst_551_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___boxed(lean_object* v_00_u03b1_555_, lean_object* v_00_u03b2_556_, lean_object* v_cmp_557_, lean_object* v_inst_558_, lean_object* v_t_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DTreeMap_getKey_x21(v_00_u03b1_555_, v_00_u03b2_556_, v_cmp_557_, v_inst_558_, v_t_559_, v_a_560_);
lean_dec(v_inst_558_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___redArg(lean_object* v_cmp_562_, lean_object* v_t_563_, lean_object* v_a_564_, lean_object* v_fallback_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_562_, v_t_563_, v_a_564_, v_fallback_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_567_, lean_object* v_t_568_, lean_object* v_a_569_, lean_object* v_fallback_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Std_DTreeMap_getKeyD___redArg(v_cmp_567_, v_t_568_, v_a_569_, v_fallback_570_);
lean_dec(v_fallback_570_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD(lean_object* v_00_u03b1_572_, lean_object* v_00_u03b2_573_, lean_object* v_cmp_574_, lean_object* v_t_575_, lean_object* v_a_576_, lean_object* v_fallback_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_574_, v_t_575_, v_a_576_, v_fallback_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_579_, lean_object* v_00_u03b2_580_, lean_object* v_cmp_581_, lean_object* v_t_582_, lean_object* v_a_583_, lean_object* v_fallback_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DTreeMap_getKeyD(v_00_u03b1_579_, v_00_u03b2_580_, v_cmp_581_, v_t_582_, v_a_583_, v_fallback_584_);
lean_dec(v_fallback_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x3f___redArg(lean_object* v_cmp_586_, lean_object* v_t_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_586_, v_t_587_, v_a_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x3f(lean_object* v_00_u03b1_590_, lean_object* v_00_u03b2_591_, lean_object* v_cmp_592_, lean_object* v_t_593_, lean_object* v_a_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_592_, v_t_593_, v_a_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry___redArg(lean_object* v_cmp_596_, lean_object* v_t_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_596_, v_t_597_, v_a_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry(lean_object* v_00_u03b1_600_, lean_object* v_00_u03b2_601_, lean_object* v_cmp_602_, lean_object* v_t_603_, lean_object* v_a_604_, lean_object* v_h_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_602_, v_t_603_, v_a_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___redArg(lean_object* v_cmp_607_, lean_object* v_t_608_, lean_object* v_a_609_, lean_object* v_fallback_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_607_, v_t_608_, v_a_609_, v_fallback_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___redArg___boxed(lean_object* v_cmp_612_, lean_object* v_t_613_, lean_object* v_a_614_, lean_object* v_fallback_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_DTreeMap_getEntryD___redArg(v_cmp_612_, v_t_613_, v_a_614_, v_fallback_615_);
lean_dec_ref(v_fallback_615_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_cmp_619_, lean_object* v_t_620_, lean_object* v_a_621_, lean_object* v_fallback_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_619_, v_t_620_, v_a_621_, v_fallback_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___boxed(lean_object* v_00_u03b1_624_, lean_object* v_00_u03b2_625_, lean_object* v_cmp_626_, lean_object* v_t_627_, lean_object* v_a_628_, lean_object* v_fallback_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_DTreeMap_getEntryD(v_00_u03b1_624_, v_00_u03b2_625_, v_cmp_626_, v_t_627_, v_a_628_, v_fallback_629_);
lean_dec_ref(v_fallback_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___redArg(lean_object* v_cmp_631_, lean_object* v_inst_632_, lean_object* v_t_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_631_, v_inst_632_, v_t_633_, v_a_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___redArg___boxed(lean_object* v_cmp_636_, lean_object* v_inst_637_, lean_object* v_t_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_DTreeMap_getEntry_x21___redArg(v_cmp_636_, v_inst_637_, v_t_638_, v_a_639_);
lean_dec_ref(v_inst_637_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21(lean_object* v_00_u03b1_641_, lean_object* v_00_u03b2_642_, lean_object* v_cmp_643_, lean_object* v_inst_644_, lean_object* v_t_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_643_, v_inst_644_, v_t_645_, v_a_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___boxed(lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_cmp_650_, lean_object* v_inst_651_, lean_object* v_t_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_DTreeMap_getEntry_x21(v_00_u03b1_648_, v_00_u03b2_649_, v_cmp_650_, v_inst_651_, v_t_652_, v_a_653_);
lean_dec_ref(v_inst_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___redArg(lean_object* v_t_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_DTreeMap_minEntry_x3f___redArg(v_t_657_);
lean_dec(v_t_657_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f(lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_cmp_661_, lean_object* v_t_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_cmp_666_, lean_object* v_t_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_DTreeMap_minEntry_x3f(v_00_u03b1_664_, v_00_u03b2_665_, v_cmp_666_, v_t_667_);
lean_dec(v_t_667_);
lean_dec_ref(v_cmp_666_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___redArg(lean_object* v_t_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___redArg___boxed(lean_object* v_t_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Std_DTreeMap_minEntry___redArg(v_t_671_);
lean_dec(v_t_671_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry(lean_object* v_00_u03b1_673_, lean_object* v_00_u03b2_674_, lean_object* v_cmp_675_, lean_object* v_t_676_, lean_object* v_h_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___boxed(lean_object* v_00_u03b1_679_, lean_object* v_00_u03b2_680_, lean_object* v_cmp_681_, lean_object* v_t_682_, lean_object* v_h_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_DTreeMap_minEntry(v_00_u03b1_679_, v_00_u03b2_680_, v_cmp_681_, v_t_682_, v_h_683_);
lean_dec(v_t_682_);
lean_dec_ref(v_cmp_681_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___redArg(lean_object* v_inst_685_, lean_object* v_t_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_685_, v_t_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_688_, lean_object* v_t_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_DTreeMap_minEntry_x21___redArg(v_inst_688_, v_t_689_);
lean_dec(v_t_689_);
lean_dec_ref(v_inst_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21(lean_object* v_00_u03b1_691_, lean_object* v_00_u03b2_692_, lean_object* v_cmp_693_, lean_object* v_inst_694_, lean_object* v_t_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_694_, v_t_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_697_, lean_object* v_00_u03b2_698_, lean_object* v_cmp_699_, lean_object* v_inst_700_, lean_object* v_t_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_DTreeMap_minEntry_x21(v_00_u03b1_697_, v_00_u03b2_698_, v_cmp_699_, v_inst_700_, v_t_701_);
lean_dec(v_t_701_);
lean_dec_ref(v_inst_700_);
lean_dec_ref(v_cmp_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___redArg(lean_object* v_t_703_, lean_object* v_fallback_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_703_, v_fallback_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___redArg___boxed(lean_object* v_t_706_, lean_object* v_fallback_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Std_DTreeMap_minEntryD___redArg(v_t_706_, v_fallback_707_);
lean_dec_ref(v_fallback_707_);
lean_dec(v_t_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD(lean_object* v_00_u03b1_709_, lean_object* v_00_u03b2_710_, lean_object* v_cmp_711_, lean_object* v_t_712_, lean_object* v_fallback_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_712_, v_fallback_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_715_, lean_object* v_00_u03b2_716_, lean_object* v_cmp_717_, lean_object* v_t_718_, lean_object* v_fallback_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_DTreeMap_minEntryD(v_00_u03b1_715_, v_00_u03b2_716_, v_cmp_717_, v_t_718_, v_fallback_719_);
lean_dec_ref(v_fallback_719_);
lean_dec(v_t_718_);
lean_dec_ref(v_cmp_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___redArg(lean_object* v_t_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Std_DTreeMap_maxEntry_x3f___redArg(v_t_723_);
lean_dec(v_t_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_725_, lean_object* v_00_u03b2_726_, lean_object* v_cmp_727_, lean_object* v_t_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_730_, lean_object* v_00_u03b2_731_, lean_object* v_cmp_732_, lean_object* v_t_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_DTreeMap_maxEntry_x3f(v_00_u03b1_730_, v_00_u03b2_731_, v_cmp_732_, v_t_733_);
lean_dec(v_t_733_);
lean_dec_ref(v_cmp_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___redArg(lean_object* v_t_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___redArg___boxed(lean_object* v_t_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_DTreeMap_maxEntry___redArg(v_t_737_);
lean_dec(v_t_737_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry(lean_object* v_00_u03b1_739_, lean_object* v_00_u03b2_740_, lean_object* v_cmp_741_, lean_object* v_t_742_, lean_object* v_h_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_745_, lean_object* v_00_u03b2_746_, lean_object* v_cmp_747_, lean_object* v_t_748_, lean_object* v_h_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_DTreeMap_maxEntry(v_00_u03b1_745_, v_00_u03b2_746_, v_cmp_747_, v_t_748_, v_h_749_);
lean_dec(v_t_748_);
lean_dec_ref(v_cmp_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___redArg(lean_object* v_inst_751_, lean_object* v_t_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_751_, v_t_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_754_, lean_object* v_t_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_DTreeMap_maxEntry_x21___redArg(v_inst_754_, v_t_755_);
lean_dec(v_t_755_);
lean_dec_ref(v_inst_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21(lean_object* v_00_u03b1_757_, lean_object* v_00_u03b2_758_, lean_object* v_cmp_759_, lean_object* v_inst_760_, lean_object* v_t_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_760_, v_t_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_cmp_765_, lean_object* v_inst_766_, lean_object* v_t_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_DTreeMap_maxEntry_x21(v_00_u03b1_763_, v_00_u03b2_764_, v_cmp_765_, v_inst_766_, v_t_767_);
lean_dec(v_t_767_);
lean_dec_ref(v_inst_766_);
lean_dec_ref(v_cmp_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___redArg(lean_object* v_t_769_, lean_object* v_fallback_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_769_, v_fallback_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_772_, lean_object* v_fallback_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_DTreeMap_maxEntryD___redArg(v_t_772_, v_fallback_773_);
lean_dec_ref(v_fallback_773_);
lean_dec(v_t_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD(lean_object* v_00_u03b1_775_, lean_object* v_00_u03b2_776_, lean_object* v_cmp_777_, lean_object* v_t_778_, lean_object* v_fallback_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_778_, v_fallback_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_781_, lean_object* v_00_u03b2_782_, lean_object* v_cmp_783_, lean_object* v_t_784_, lean_object* v_fallback_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_DTreeMap_maxEntryD(v_00_u03b1_781_, v_00_u03b2_782_, v_cmp_783_, v_t_784_, v_fallback_785_);
lean_dec_ref(v_fallback_785_);
lean_dec(v_t_784_);
lean_dec_ref(v_cmp_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___redArg(lean_object* v_t_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_DTreeMap_minKey_x3f___redArg(v_t_789_);
lean_dec(v_t_789_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f(lean_object* v_00_u03b1_791_, lean_object* v_00_u03b2_792_, lean_object* v_cmp_793_, lean_object* v_t_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_796_, lean_object* v_00_u03b2_797_, lean_object* v_cmp_798_, lean_object* v_t_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_DTreeMap_minKey_x3f(v_00_u03b1_796_, v_00_u03b2_797_, v_cmp_798_, v_t_799_);
lean_dec(v_t_799_);
lean_dec_ref(v_cmp_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___redArg(lean_object* v_t_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___redArg___boxed(lean_object* v_t_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_DTreeMap_minKey___redArg(v_t_803_);
lean_dec(v_t_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey(lean_object* v_00_u03b1_805_, lean_object* v_00_u03b2_806_, lean_object* v_cmp_807_, lean_object* v_t_808_, lean_object* v_h_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___boxed(lean_object* v_00_u03b1_811_, lean_object* v_00_u03b2_812_, lean_object* v_cmp_813_, lean_object* v_t_814_, lean_object* v_h_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_DTreeMap_minKey(v_00_u03b1_811_, v_00_u03b2_812_, v_cmp_813_, v_t_814_, v_h_815_);
lean_dec(v_t_814_);
lean_dec_ref(v_cmp_813_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___redArg(lean_object* v_inst_817_, lean_object* v_t_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_817_, v_t_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_820_, lean_object* v_t_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DTreeMap_minKey_x21___redArg(v_inst_820_, v_t_821_);
lean_dec(v_t_821_);
lean_dec(v_inst_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21(lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_cmp_825_, lean_object* v_inst_826_, lean_object* v_t_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_826_, v_t_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_cmp_831_, lean_object* v_inst_832_, lean_object* v_t_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_DTreeMap_minKey_x21(v_00_u03b1_829_, v_00_u03b2_830_, v_cmp_831_, v_inst_832_, v_t_833_);
lean_dec(v_t_833_);
lean_dec(v_inst_832_);
lean_dec_ref(v_cmp_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___redArg(lean_object* v_t_835_, lean_object* v_fallback_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_835_, v_fallback_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___redArg___boxed(lean_object* v_t_838_, lean_object* v_fallback_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_DTreeMap_minKeyD___redArg(v_t_838_, v_fallback_839_);
lean_dec(v_fallback_839_);
lean_dec(v_t_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD(lean_object* v_00_u03b1_841_, lean_object* v_00_u03b2_842_, lean_object* v_cmp_843_, lean_object* v_t_844_, lean_object* v_fallback_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_844_, v_fallback_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_847_, lean_object* v_00_u03b2_848_, lean_object* v_cmp_849_, lean_object* v_t_850_, lean_object* v_fallback_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_DTreeMap_minKeyD(v_00_u03b1_847_, v_00_u03b2_848_, v_cmp_849_, v_t_850_, v_fallback_851_);
lean_dec(v_fallback_851_);
lean_dec(v_t_850_);
lean_dec_ref(v_cmp_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___redArg(lean_object* v_t_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DTreeMap_maxKey_x3f___redArg(v_t_855_);
lean_dec(v_t_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f(lean_object* v_00_u03b1_857_, lean_object* v_00_u03b2_858_, lean_object* v_cmp_859_, lean_object* v_t_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_862_, lean_object* v_00_u03b2_863_, lean_object* v_cmp_864_, lean_object* v_t_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_DTreeMap_maxKey_x3f(v_00_u03b1_862_, v_00_u03b2_863_, v_cmp_864_, v_t_865_);
lean_dec(v_t_865_);
lean_dec_ref(v_cmp_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___redArg(lean_object* v_t_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___redArg___boxed(lean_object* v_t_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_DTreeMap_maxKey___redArg(v_t_869_);
lean_dec(v_t_869_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey(lean_object* v_00_u03b1_871_, lean_object* v_00_u03b2_872_, lean_object* v_cmp_873_, lean_object* v_t_874_, lean_object* v_h_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___boxed(lean_object* v_00_u03b1_877_, lean_object* v_00_u03b2_878_, lean_object* v_cmp_879_, lean_object* v_t_880_, lean_object* v_h_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Std_DTreeMap_maxKey(v_00_u03b1_877_, v_00_u03b2_878_, v_cmp_879_, v_t_880_, v_h_881_);
lean_dec(v_t_880_);
lean_dec_ref(v_cmp_879_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___redArg(lean_object* v_inst_883_, lean_object* v_t_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_883_, v_t_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_886_, lean_object* v_t_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Std_DTreeMap_maxKey_x21___redArg(v_inst_886_, v_t_887_);
lean_dec(v_t_887_);
lean_dec(v_inst_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21(lean_object* v_00_u03b1_889_, lean_object* v_00_u03b2_890_, lean_object* v_cmp_891_, lean_object* v_inst_892_, lean_object* v_t_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_892_, v_t_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_895_, lean_object* v_00_u03b2_896_, lean_object* v_cmp_897_, lean_object* v_inst_898_, lean_object* v_t_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Std_DTreeMap_maxKey_x21(v_00_u03b1_895_, v_00_u03b2_896_, v_cmp_897_, v_inst_898_, v_t_899_);
lean_dec(v_t_899_);
lean_dec(v_inst_898_);
lean_dec_ref(v_cmp_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___redArg(lean_object* v_t_901_, lean_object* v_fallback_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_901_, v_fallback_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_904_, lean_object* v_fallback_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_DTreeMap_maxKeyD___redArg(v_t_904_, v_fallback_905_);
lean_dec(v_fallback_905_);
lean_dec(v_t_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_cmp_909_, lean_object* v_t_910_, lean_object* v_fallback_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_910_, v_fallback_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_913_, lean_object* v_00_u03b2_914_, lean_object* v_cmp_915_, lean_object* v_t_916_, lean_object* v_fallback_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Std_DTreeMap_maxKeyD(v_00_u03b1_913_, v_00_u03b2_914_, v_cmp_915_, v_t_916_, v_fallback_917_);
lean_dec(v_fallback_917_);
lean_dec(v_t_916_);
lean_dec_ref(v_cmp_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_919_, lean_object* v_n_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_919_, v_n_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_922_, lean_object* v_n_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Std_DTreeMap_entryAtIdx_x3f___redArg(v_t_922_, v_n_923_);
lean_dec(v_t_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_cmp_927_, lean_object* v_t_928_, lean_object* v_n_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_928_, v_n_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_931_, lean_object* v_00_u03b2_932_, lean_object* v_cmp_933_, lean_object* v_t_934_, lean_object* v_n_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Std_DTreeMap_entryAtIdx_x3f(v_00_u03b1_931_, v_00_u03b2_932_, v_cmp_933_, v_t_934_, v_n_935_);
lean_dec(v_t_934_);
lean_dec_ref(v_cmp_933_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___redArg(lean_object* v_t_937_, lean_object* v_n_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_937_, v_n_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_940_, lean_object* v_n_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_DTreeMap_entryAtIdx___redArg(v_t_940_, v_n_941_);
lean_dec(v_t_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx(lean_object* v_00_u03b1_943_, lean_object* v_00_u03b2_944_, lean_object* v_cmp_945_, lean_object* v_t_946_, lean_object* v_n_947_, lean_object* v_h_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_946_, v_n_947_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_950_, lean_object* v_00_u03b2_951_, lean_object* v_cmp_952_, lean_object* v_t_953_, lean_object* v_n_954_, lean_object* v_h_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_DTreeMap_entryAtIdx(v_00_u03b1_950_, v_00_u03b2_951_, v_cmp_952_, v_t_953_, v_n_954_, v_h_955_);
lean_dec(v_t_953_);
lean_dec_ref(v_cmp_952_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_957_, lean_object* v_t_958_, lean_object* v_n_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_957_, v_t_958_, v_n_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_961_, lean_object* v_t_962_, lean_object* v_n_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_DTreeMap_entryAtIdx_x21___redArg(v_inst_961_, v_t_962_, v_n_963_);
lean_dec(v_t_962_);
lean_dec_ref(v_inst_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_965_, lean_object* v_00_u03b2_966_, lean_object* v_cmp_967_, lean_object* v_inst_968_, lean_object* v_t_969_, lean_object* v_n_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_968_, v_t_969_, v_n_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_972_, lean_object* v_00_u03b2_973_, lean_object* v_cmp_974_, lean_object* v_inst_975_, lean_object* v_t_976_, lean_object* v_n_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_DTreeMap_entryAtIdx_x21(v_00_u03b1_972_, v_00_u03b2_973_, v_cmp_974_, v_inst_975_, v_t_976_, v_n_977_);
lean_dec(v_t_976_);
lean_dec_ref(v_inst_975_);
lean_dec_ref(v_cmp_974_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___redArg(lean_object* v_t_979_, lean_object* v_n_980_, lean_object* v_fallback_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_979_, v_n_980_, v_fallback_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_983_, lean_object* v_n_984_, lean_object* v_fallback_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Std_DTreeMap_entryAtIdxD___redArg(v_t_983_, v_n_984_, v_fallback_985_);
lean_dec_ref(v_fallback_985_);
lean_dec(v_t_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD(lean_object* v_00_u03b1_987_, lean_object* v_00_u03b2_988_, lean_object* v_cmp_989_, lean_object* v_t_990_, lean_object* v_n_991_, lean_object* v_fallback_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_990_, v_n_991_, v_fallback_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_994_, lean_object* v_00_u03b2_995_, lean_object* v_cmp_996_, lean_object* v_t_997_, lean_object* v_n_998_, lean_object* v_fallback_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_DTreeMap_entryAtIdxD(v_00_u03b1_994_, v_00_u03b2_995_, v_cmp_996_, v_t_997_, v_n_998_, v_fallback_999_);
lean_dec_ref(v_fallback_999_);
lean_dec(v_t_997_);
lean_dec_ref(v_cmp_996_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_1001_, lean_object* v_n_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_1001_, v_n_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_1004_, lean_object* v_n_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Std_DTreeMap_keyAtIdx_x3f___redArg(v_t_1004_, v_n_1005_);
lean_dec(v_t_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_1007_, lean_object* v_00_u03b2_1008_, lean_object* v_cmp_1009_, lean_object* v_t_1010_, lean_object* v_n_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_1010_, v_n_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_1013_, lean_object* v_00_u03b2_1014_, lean_object* v_cmp_1015_, lean_object* v_t_1016_, lean_object* v_n_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Std_DTreeMap_keyAtIdx_x3f(v_00_u03b1_1013_, v_00_u03b2_1014_, v_cmp_1015_, v_t_1016_, v_n_1017_);
lean_dec(v_t_1016_);
lean_dec_ref(v_cmp_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___redArg(lean_object* v_t_1019_, lean_object* v_n_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1019_, v_n_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_1022_, lean_object* v_n_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_DTreeMap_keyAtIdx___redArg(v_t_1022_, v_n_1023_);
lean_dec(v_t_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx(lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_cmp_1027_, lean_object* v_t_1028_, lean_object* v_n_1029_, lean_object* v_h_1030_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1028_, v_n_1029_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_1032_, lean_object* v_00_u03b2_1033_, lean_object* v_cmp_1034_, lean_object* v_t_1035_, lean_object* v_n_1036_, lean_object* v_h_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Std_DTreeMap_keyAtIdx(v_00_u03b1_1032_, v_00_u03b2_1033_, v_cmp_1034_, v_t_1035_, v_n_1036_, v_h_1037_);
lean_dec(v_t_1035_);
lean_dec_ref(v_cmp_1034_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_1039_, lean_object* v_t_1040_, lean_object* v_n_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1039_, v_t_1040_, v_n_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_1043_, lean_object* v_t_1044_, lean_object* v_n_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Std_DTreeMap_keyAtIdx_x21___redArg(v_inst_1043_, v_t_1044_, v_n_1045_);
lean_dec(v_t_1044_);
lean_dec(v_inst_1043_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_1047_, lean_object* v_00_u03b2_1048_, lean_object* v_cmp_1049_, lean_object* v_inst_1050_, lean_object* v_t_1051_, lean_object* v_n_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1050_, v_t_1051_, v_n_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_1054_, lean_object* v_00_u03b2_1055_, lean_object* v_cmp_1056_, lean_object* v_inst_1057_, lean_object* v_t_1058_, lean_object* v_n_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Std_DTreeMap_keyAtIdx_x21(v_00_u03b1_1054_, v_00_u03b2_1055_, v_cmp_1056_, v_inst_1057_, v_t_1058_, v_n_1059_);
lean_dec(v_t_1058_);
lean_dec(v_inst_1057_);
lean_dec_ref(v_cmp_1056_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___redArg(lean_object* v_t_1061_, lean_object* v_n_1062_, lean_object* v_fallback_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1061_, v_n_1062_, v_fallback_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_1065_, lean_object* v_n_1066_, lean_object* v_fallback_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_DTreeMap_keyAtIdxD___redArg(v_t_1065_, v_n_1066_, v_fallback_1067_);
lean_dec(v_fallback_1067_);
lean_dec(v_t_1065_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD(lean_object* v_00_u03b1_1069_, lean_object* v_00_u03b2_1070_, lean_object* v_cmp_1071_, lean_object* v_t_1072_, lean_object* v_n_1073_, lean_object* v_fallback_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1072_, v_n_1073_, v_fallback_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_1076_, lean_object* v_00_u03b2_1077_, lean_object* v_cmp_1078_, lean_object* v_t_1079_, lean_object* v_n_1080_, lean_object* v_fallback_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Std_DTreeMap_keyAtIdxD(v_00_u03b1_1076_, v_00_u03b2_1077_, v_cmp_1078_, v_t_1079_, v_n_1080_, v_fallback_1081_);
lean_dec(v_fallback_1081_);
lean_dec(v_t_1079_);
lean_dec_ref(v_cmp_1078_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1083_, lean_object* v_t_1084_, lean_object* v_k_1085_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_box(0);
v___x_1087_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1083_, v_k_1085_, v___x_1086_, v_t_1084_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1088_, lean_object* v_00_u03b2_1089_, lean_object* v_cmp_1090_, lean_object* v_t_1091_, lean_object* v_k_1092_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_box(0);
v___x_1094_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1090_, v_k_1092_, v___x_1093_, v_t_1091_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1095_, lean_object* v_t_1096_, lean_object* v_k_1097_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_box(0);
v___x_1099_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1095_, v_k_1097_, v___x_1098_, v_t_1096_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1100_, lean_object* v_00_u03b2_1101_, lean_object* v_cmp_1102_, lean_object* v_t_1103_, lean_object* v_k_1104_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_box(0);
v___x_1106_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1102_, v_k_1104_, v___x_1105_, v_t_1103_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1107_, lean_object* v_t_1108_, lean_object* v_k_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1107_, v_k_1109_, v___x_1110_, v_t_1108_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1112_, lean_object* v_00_u03b2_1113_, lean_object* v_cmp_1114_, lean_object* v_t_1115_, lean_object* v_k_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_box(0);
v___x_1118_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1114_, v_k_1116_, v___x_1117_, v_t_1115_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1119_, lean_object* v_t_1120_, lean_object* v_k_1121_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_box(0);
v___x_1123_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1119_, v_k_1121_, v___x_1122_, v_t_1120_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1124_, lean_object* v_00_u03b2_1125_, lean_object* v_cmp_1126_, lean_object* v_t_1127_, lean_object* v_k_1128_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_box(0);
v___x_1130_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1126_, v_k_1128_, v___x_1129_, v_t_1127_);
return v___x_1130_;
}
}
static lean_object* _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1134_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1135_ = lean_unsigned_to_nat(14u);
v___x_1136_ = lean_unsigned_to_nat(22u);
v___x_1137_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1138_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1139_ = l_mkPanicMessageWithDecl(v___x_1138_, v___x_1137_, v___x_1136_, v___x_1135_, v___x_1134_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1140_, lean_object* v_inst_1141_, lean_object* v_t_1142_, lean_object* v_k_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_box(0);
v___x_1145_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1140_, v_k_1143_, v___x_1144_, v_t_1142_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1147_ = l_panic___redArg(v_inst_1141_, v___x_1146_);
return v___x_1147_;
}
else
{
lean_object* v_val_1148_; 
v_val_1148_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_val_1148_);
lean_dec_ref(v___x_1145_);
return v_val_1148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1149_, lean_object* v_inst_1150_, lean_object* v_t_1151_, lean_object* v_k_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Std_DTreeMap_getEntryGE_x21___redArg(v_cmp_1149_, v_inst_1150_, v_t_1151_, v_k_1152_);
lean_dec_ref(v_inst_1150_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1154_, lean_object* v_00_u03b2_1155_, lean_object* v_cmp_1156_, lean_object* v_inst_1157_, lean_object* v_t_1158_, lean_object* v_k_1159_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_box(0);
v___x_1161_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1156_, v_k_1159_, v___x_1160_, v_t_1158_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1163_ = l_panic___redArg(v_inst_1157_, v___x_1162_);
return v___x_1163_;
}
else
{
lean_object* v_val_1164_; 
v_val_1164_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_val_1164_);
lean_dec_ref(v___x_1161_);
return v_val_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1165_, lean_object* v_00_u03b2_1166_, lean_object* v_cmp_1167_, lean_object* v_inst_1168_, lean_object* v_t_1169_, lean_object* v_k_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Std_DTreeMap_getEntryGE_x21(v_00_u03b1_1165_, v_00_u03b2_1166_, v_cmp_1167_, v_inst_1168_, v_t_1169_, v_k_1170_);
lean_dec_ref(v_inst_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1172_, lean_object* v_inst_1173_, lean_object* v_t_1174_, lean_object* v_k_1175_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_box(0);
v___x_1177_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1172_, v_k_1175_, v___x_1176_, v_t_1174_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1179_ = l_panic___redArg(v_inst_1173_, v___x_1178_);
return v___x_1179_;
}
else
{
lean_object* v_val_1180_; 
v_val_1180_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_val_1180_);
lean_dec_ref(v___x_1177_);
return v_val_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1181_, lean_object* v_inst_1182_, lean_object* v_t_1183_, lean_object* v_k_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Std_DTreeMap_getEntryGT_x21___redArg(v_cmp_1181_, v_inst_1182_, v_t_1183_, v_k_1184_);
lean_dec_ref(v_inst_1182_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1186_, lean_object* v_00_u03b2_1187_, lean_object* v_cmp_1188_, lean_object* v_inst_1189_, lean_object* v_t_1190_, lean_object* v_k_1191_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_box(0);
v___x_1193_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1188_, v_k_1191_, v___x_1192_, v_t_1190_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1195_ = l_panic___redArg(v_inst_1189_, v___x_1194_);
return v___x_1195_;
}
else
{
lean_object* v_val_1196_; 
v_val_1196_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_val_1196_);
lean_dec_ref(v___x_1193_);
return v_val_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1197_, lean_object* v_00_u03b2_1198_, lean_object* v_cmp_1199_, lean_object* v_inst_1200_, lean_object* v_t_1201_, lean_object* v_k_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Std_DTreeMap_getEntryGT_x21(v_00_u03b1_1197_, v_00_u03b2_1198_, v_cmp_1199_, v_inst_1200_, v_t_1201_, v_k_1202_);
lean_dec_ref(v_inst_1200_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1204_, lean_object* v_inst_1205_, lean_object* v_t_1206_, lean_object* v_k_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1204_, v_k_1207_, v___x_1208_, v_t_1206_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1211_ = l_panic___redArg(v_inst_1205_, v___x_1210_);
return v___x_1211_;
}
else
{
lean_object* v_val_1212_; 
v_val_1212_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_val_1212_);
lean_dec_ref(v___x_1209_);
return v_val_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1213_, lean_object* v_inst_1214_, lean_object* v_t_1215_, lean_object* v_k_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_DTreeMap_getEntryLE_x21___redArg(v_cmp_1213_, v_inst_1214_, v_t_1215_, v_k_1216_);
lean_dec_ref(v_inst_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1218_, lean_object* v_00_u03b2_1219_, lean_object* v_cmp_1220_, lean_object* v_inst_1221_, lean_object* v_t_1222_, lean_object* v_k_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = lean_box(0);
v___x_1225_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1220_, v_k_1223_, v___x_1224_, v_t_1222_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1229_, lean_object* v_00_u03b2_1230_, lean_object* v_cmp_1231_, lean_object* v_inst_1232_, lean_object* v_t_1233_, lean_object* v_k_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Std_DTreeMap_getEntryLE_x21(v_00_u03b1_1229_, v_00_u03b2_1230_, v_cmp_1231_, v_inst_1232_, v_t_1233_, v_k_1234_);
lean_dec_ref(v_inst_1232_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1236_, lean_object* v_inst_1237_, lean_object* v_t_1238_, lean_object* v_k_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1236_, v_k_1239_, v___x_1240_, v_t_1238_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1243_ = l_panic___redArg(v_inst_1237_, v___x_1242_);
return v___x_1243_;
}
else
{
lean_object* v_val_1244_; 
v_val_1244_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_val_1244_);
lean_dec_ref(v___x_1241_);
return v_val_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1245_, lean_object* v_inst_1246_, lean_object* v_t_1247_, lean_object* v_k_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_DTreeMap_getEntryLT_x21___redArg(v_cmp_1245_, v_inst_1246_, v_t_1247_, v_k_1248_);
lean_dec_ref(v_inst_1246_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1250_, lean_object* v_00_u03b2_1251_, lean_object* v_cmp_1252_, lean_object* v_inst_1253_, lean_object* v_t_1254_, lean_object* v_k_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_box(0);
v___x_1257_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1252_, v_k_1255_, v___x_1256_, v_t_1254_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1259_ = l_panic___redArg(v_inst_1253_, v___x_1258_);
return v___x_1259_;
}
else
{
lean_object* v_val_1260_; 
v_val_1260_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_val_1260_);
lean_dec_ref(v___x_1257_);
return v_val_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1261_, lean_object* v_00_u03b2_1262_, lean_object* v_cmp_1263_, lean_object* v_inst_1264_, lean_object* v_t_1265_, lean_object* v_k_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_DTreeMap_getEntryLT_x21(v_00_u03b1_1261_, v_00_u03b2_1262_, v_cmp_1263_, v_inst_1264_, v_t_1265_, v_k_1266_);
lean_dec_ref(v_inst_1264_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___redArg(lean_object* v_cmp_1268_, lean_object* v_t_1269_, lean_object* v_k_1270_, lean_object* v_fallback_1271_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_box(0);
v___x_1273_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1268_, v_k_1270_, v___x_1272_, v_t_1269_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_inc_ref(v_fallback_1271_);
return v_fallback_1271_;
}
else
{
lean_object* v_val_1274_; 
v_val_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_val_1274_);
lean_dec_ref(v___x_1273_);
return v_val_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1275_, lean_object* v_t_1276_, lean_object* v_k_1277_, lean_object* v_fallback_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Std_DTreeMap_getEntryGED___redArg(v_cmp_1275_, v_t_1276_, v_k_1277_, v_fallback_1278_);
lean_dec_ref(v_fallback_1278_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED(lean_object* v_00_u03b1_1280_, lean_object* v_00_u03b2_1281_, lean_object* v_cmp_1282_, lean_object* v_t_1283_, lean_object* v_k_1284_, lean_object* v_fallback_1285_){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_box(0);
v___x_1287_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1282_, v_k_1284_, v___x_1286_, v_t_1283_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_inc_ref(v_fallback_1285_);
return v_fallback_1285_;
}
else
{
lean_object* v_val_1288_; 
v_val_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_val_1288_);
lean_dec_ref(v___x_1287_);
return v_val_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1289_, lean_object* v_00_u03b2_1290_, lean_object* v_cmp_1291_, lean_object* v_t_1292_, lean_object* v_k_1293_, lean_object* v_fallback_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Std_DTreeMap_getEntryGED(v_00_u03b1_1289_, v_00_u03b2_1290_, v_cmp_1291_, v_t_1292_, v_k_1293_, v_fallback_1294_);
lean_dec_ref(v_fallback_1294_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1296_, lean_object* v_t_1297_, lean_object* v_k_1298_, lean_object* v_fallback_1299_){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = lean_box(0);
v___x_1301_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1296_, v_k_1298_, v___x_1300_, v_t_1297_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_inc_ref(v_fallback_1299_);
return v_fallback_1299_;
}
else
{
lean_object* v_val_1302_; 
v_val_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_val_1302_);
lean_dec_ref(v___x_1301_);
return v_val_1302_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1303_, lean_object* v_t_1304_, lean_object* v_k_1305_, lean_object* v_fallback_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Std_DTreeMap_getEntryGTD___redArg(v_cmp_1303_, v_t_1304_, v_k_1305_, v_fallback_1306_);
lean_dec_ref(v_fallback_1306_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD(lean_object* v_00_u03b1_1308_, lean_object* v_00_u03b2_1309_, lean_object* v_cmp_1310_, lean_object* v_t_1311_, lean_object* v_k_1312_, lean_object* v_fallback_1313_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_box(0);
v___x_1315_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1310_, v_k_1312_, v___x_1314_, v_t_1311_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_inc_ref(v_fallback_1313_);
return v_fallback_1313_;
}
else
{
lean_object* v_val_1316_; 
v_val_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_val_1316_);
lean_dec_ref(v___x_1315_);
return v_val_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_00_u03b2_1318_, lean_object* v_cmp_1319_, lean_object* v_t_1320_, lean_object* v_k_1321_, lean_object* v_fallback_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Std_DTreeMap_getEntryGTD(v_00_u03b1_1317_, v_00_u03b2_1318_, v_cmp_1319_, v_t_1320_, v_k_1321_, v_fallback_1322_);
lean_dec_ref(v_fallback_1322_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___redArg(lean_object* v_cmp_1324_, lean_object* v_t_1325_, lean_object* v_k_1326_, lean_object* v_fallback_1327_){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_box(0);
v___x_1329_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1324_, v_k_1326_, v___x_1328_, v_t_1325_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_inc_ref(v_fallback_1327_);
return v_fallback_1327_;
}
else
{
lean_object* v_val_1330_; 
v_val_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_val_1330_);
lean_dec_ref(v___x_1329_);
return v_val_1330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1331_, lean_object* v_t_1332_, lean_object* v_k_1333_, lean_object* v_fallback_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_DTreeMap_getEntryLED___redArg(v_cmp_1331_, v_t_1332_, v_k_1333_, v_fallback_1334_);
lean_dec_ref(v_fallback_1334_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED(lean_object* v_00_u03b1_1336_, lean_object* v_00_u03b2_1337_, lean_object* v_cmp_1338_, lean_object* v_t_1339_, lean_object* v_k_1340_, lean_object* v_fallback_1341_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_box(0);
v___x_1343_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1338_, v_k_1340_, v___x_1342_, v_t_1339_);
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
lean_dec_ref(v___x_1343_);
return v_val_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_00_u03b2_1346_, lean_object* v_cmp_1347_, lean_object* v_t_1348_, lean_object* v_k_1349_, lean_object* v_fallback_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Std_DTreeMap_getEntryLED(v_00_u03b1_1345_, v_00_u03b2_1346_, v_cmp_1347_, v_t_1348_, v_k_1349_, v_fallback_1350_);
lean_dec_ref(v_fallback_1350_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1352_, lean_object* v_t_1353_, lean_object* v_k_1354_, lean_object* v_fallback_1355_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_box(0);
v___x_1357_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1352_, v_k_1354_, v___x_1356_, v_t_1353_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_inc_ref(v_fallback_1355_);
return v_fallback_1355_;
}
else
{
lean_object* v_val_1358_; 
v_val_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_val_1358_);
lean_dec_ref(v___x_1357_);
return v_val_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1359_, lean_object* v_t_1360_, lean_object* v_k_1361_, lean_object* v_fallback_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Std_DTreeMap_getEntryLTD___redArg(v_cmp_1359_, v_t_1360_, v_k_1361_, v_fallback_1362_);
lean_dec_ref(v_fallback_1362_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD(lean_object* v_00_u03b1_1364_, lean_object* v_00_u03b2_1365_, lean_object* v_cmp_1366_, lean_object* v_t_1367_, lean_object* v_k_1368_, lean_object* v_fallback_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_box(0);
v___x_1371_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1366_, v_k_1368_, v___x_1370_, v_t_1367_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_inc_ref(v_fallback_1369_);
return v_fallback_1369_;
}
else
{
lean_object* v_val_1372_; 
v_val_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_val_1372_);
lean_dec_ref(v___x_1371_);
return v_val_1372_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1373_, lean_object* v_00_u03b2_1374_, lean_object* v_cmp_1375_, lean_object* v_t_1376_, lean_object* v_k_1377_, lean_object* v_fallback_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_DTreeMap_getEntryLTD(v_00_u03b1_1373_, v_00_u03b2_1374_, v_cmp_1375_, v_t_1376_, v_k_1377_, v_fallback_1378_);
lean_dec_ref(v_fallback_1378_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1380_, lean_object* v_t_1381_, lean_object* v_k_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1380_, v_k_1382_, v___x_1383_, v_t_1381_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1385_, lean_object* v_00_u03b2_1386_, lean_object* v_cmp_1387_, lean_object* v_t_1388_, lean_object* v_k_1389_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_box(0);
v___x_1391_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1387_, v_k_1389_, v___x_1390_, v_t_1388_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1392_, lean_object* v_t_1393_, lean_object* v_k_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_box(0);
v___x_1396_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1392_, v_k_1394_, v___x_1395_, v_t_1393_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1397_, lean_object* v_00_u03b2_1398_, lean_object* v_cmp_1399_, lean_object* v_t_1400_, lean_object* v_k_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1399_, v_k_1401_, v___x_1402_, v_t_1400_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1404_, lean_object* v_t_1405_, lean_object* v_k_1406_){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_box(0);
v___x_1408_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1404_, v_k_1406_, v___x_1407_, v_t_1405_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1409_, lean_object* v_00_u03b2_1410_, lean_object* v_cmp_1411_, lean_object* v_t_1412_, lean_object* v_k_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1411_, v_k_1413_, v___x_1414_, v_t_1412_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1416_, lean_object* v_t_1417_, lean_object* v_k_1418_){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_box(0);
v___x_1420_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1416_, v_k_1418_, v___x_1419_, v_t_1417_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1421_, lean_object* v_00_u03b2_1422_, lean_object* v_cmp_1423_, lean_object* v_t_1424_, lean_object* v_k_1425_){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_box(0);
v___x_1427_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1423_, v_k_1425_, v___x_1426_, v_t_1424_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1428_, lean_object* v_inst_1429_, lean_object* v_t_1430_, lean_object* v_k_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_box(0);
v___x_1433_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1428_, v_k_1431_, v___x_1432_, v_t_1430_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1435_ = l_panic___redArg(v_inst_1429_, v___x_1434_);
return v___x_1435_;
}
else
{
lean_object* v_val_1436_; 
v_val_1436_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_val_1436_);
lean_dec_ref(v___x_1433_);
return v_val_1436_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1437_, lean_object* v_inst_1438_, lean_object* v_t_1439_, lean_object* v_k_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Std_DTreeMap_getKeyGE_x21___redArg(v_cmp_1437_, v_inst_1438_, v_t_1439_, v_k_1440_);
lean_dec(v_inst_1438_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1442_, lean_object* v_00_u03b2_1443_, lean_object* v_cmp_1444_, lean_object* v_inst_1445_, lean_object* v_t_1446_, lean_object* v_k_1447_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1444_, v_k_1447_, v___x_1448_, v_t_1446_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1451_ = l_panic___redArg(v_inst_1445_, v___x_1450_);
return v___x_1451_;
}
else
{
lean_object* v_val_1452_; 
v_val_1452_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_val_1452_);
lean_dec_ref(v___x_1449_);
return v_val_1452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1453_, lean_object* v_00_u03b2_1454_, lean_object* v_cmp_1455_, lean_object* v_inst_1456_, lean_object* v_t_1457_, lean_object* v_k_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Std_DTreeMap_getKeyGE_x21(v_00_u03b1_1453_, v_00_u03b2_1454_, v_cmp_1455_, v_inst_1456_, v_t_1457_, v_k_1458_);
lean_dec(v_inst_1456_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1460_, lean_object* v_inst_1461_, lean_object* v_t_1462_, lean_object* v_k_1463_){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = lean_box(0);
v___x_1465_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1460_, v_k_1463_, v___x_1464_, v_t_1462_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1467_ = l_panic___redArg(v_inst_1461_, v___x_1466_);
return v___x_1467_;
}
else
{
lean_object* v_val_1468_; 
v_val_1468_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_val_1468_);
lean_dec_ref(v___x_1465_);
return v_val_1468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1469_, lean_object* v_inst_1470_, lean_object* v_t_1471_, lean_object* v_k_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Std_DTreeMap_getKeyGT_x21___redArg(v_cmp_1469_, v_inst_1470_, v_t_1471_, v_k_1472_);
lean_dec(v_inst_1470_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1474_, lean_object* v_00_u03b2_1475_, lean_object* v_cmp_1476_, lean_object* v_inst_1477_, lean_object* v_t_1478_, lean_object* v_k_1479_){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_box(0);
v___x_1481_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1476_, v_k_1479_, v___x_1480_, v_t_1478_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1483_ = l_panic___redArg(v_inst_1477_, v___x_1482_);
return v___x_1483_;
}
else
{
lean_object* v_val_1484_; 
v_val_1484_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_val_1484_);
lean_dec_ref(v___x_1481_);
return v_val_1484_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1485_, lean_object* v_00_u03b2_1486_, lean_object* v_cmp_1487_, lean_object* v_inst_1488_, lean_object* v_t_1489_, lean_object* v_k_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Std_DTreeMap_getKeyGT_x21(v_00_u03b1_1485_, v_00_u03b2_1486_, v_cmp_1487_, v_inst_1488_, v_t_1489_, v_k_1490_);
lean_dec(v_inst_1488_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1492_, lean_object* v_inst_1493_, lean_object* v_t_1494_, lean_object* v_k_1495_){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_box(0);
v___x_1497_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1492_, v_k_1495_, v___x_1496_, v_t_1494_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1499_ = l_panic___redArg(v_inst_1493_, v___x_1498_);
return v___x_1499_;
}
else
{
lean_object* v_val_1500_; 
v_val_1500_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1500_);
lean_dec_ref(v___x_1497_);
return v_val_1500_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1501_, lean_object* v_inst_1502_, lean_object* v_t_1503_, lean_object* v_k_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Std_DTreeMap_getKeyLE_x21___redArg(v_cmp_1501_, v_inst_1502_, v_t_1503_, v_k_1504_);
lean_dec(v_inst_1502_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1506_, lean_object* v_00_u03b2_1507_, lean_object* v_cmp_1508_, lean_object* v_inst_1509_, lean_object* v_t_1510_, lean_object* v_k_1511_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1508_, v_k_1511_, v___x_1512_, v_t_1510_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1515_ = l_panic___redArg(v_inst_1509_, v___x_1514_);
return v___x_1515_;
}
else
{
lean_object* v_val_1516_; 
v_val_1516_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_val_1516_);
lean_dec_ref(v___x_1513_);
return v_val_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1517_, lean_object* v_00_u03b2_1518_, lean_object* v_cmp_1519_, lean_object* v_inst_1520_, lean_object* v_t_1521_, lean_object* v_k_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Std_DTreeMap_getKeyLE_x21(v_00_u03b1_1517_, v_00_u03b2_1518_, v_cmp_1519_, v_inst_1520_, v_t_1521_, v_k_1522_);
lean_dec(v_inst_1520_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1524_, lean_object* v_inst_1525_, lean_object* v_t_1526_, lean_object* v_k_1527_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_box(0);
v___x_1529_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1524_, v_k_1527_, v___x_1528_, v_t_1526_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1531_ = l_panic___redArg(v_inst_1525_, v___x_1530_);
return v___x_1531_;
}
else
{
lean_object* v_val_1532_; 
v_val_1532_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_val_1532_);
lean_dec_ref(v___x_1529_);
return v_val_1532_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1533_, lean_object* v_inst_1534_, lean_object* v_t_1535_, lean_object* v_k_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Std_DTreeMap_getKeyLT_x21___redArg(v_cmp_1533_, v_inst_1534_, v_t_1535_, v_k_1536_);
lean_dec(v_inst_1534_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1538_, lean_object* v_00_u03b2_1539_, lean_object* v_cmp_1540_, lean_object* v_inst_1541_, lean_object* v_t_1542_, lean_object* v_k_1543_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_box(0);
v___x_1545_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1540_, v_k_1543_, v___x_1544_, v_t_1542_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1547_ = l_panic___redArg(v_inst_1541_, v___x_1546_);
return v___x_1547_;
}
else
{
lean_object* v_val_1548_; 
v_val_1548_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_val_1548_);
lean_dec_ref(v___x_1545_);
return v_val_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1549_, lean_object* v_00_u03b2_1550_, lean_object* v_cmp_1551_, lean_object* v_inst_1552_, lean_object* v_t_1553_, lean_object* v_k_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Std_DTreeMap_getKeyLT_x21(v_00_u03b1_1549_, v_00_u03b2_1550_, v_cmp_1551_, v_inst_1552_, v_t_1553_, v_k_1554_);
lean_dec(v_inst_1552_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___redArg(lean_object* v_cmp_1556_, lean_object* v_t_1557_, lean_object* v_k_1558_, lean_object* v_fallback_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_box(0);
v___x_1561_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1556_, v_k_1558_, v___x_1560_, v_t_1557_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_inc(v_fallback_1559_);
return v_fallback_1559_;
}
else
{
lean_object* v_val_1562_; 
v_val_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_val_1562_);
lean_dec_ref(v___x_1561_);
return v_val_1562_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1563_, lean_object* v_t_1564_, lean_object* v_k_1565_, lean_object* v_fallback_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Std_DTreeMap_getKeyGED___redArg(v_cmp_1563_, v_t_1564_, v_k_1565_, v_fallback_1566_);
lean_dec(v_fallback_1566_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED(lean_object* v_00_u03b1_1568_, lean_object* v_00_u03b2_1569_, lean_object* v_cmp_1570_, lean_object* v_t_1571_, lean_object* v_k_1572_, lean_object* v_fallback_1573_){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_box(0);
v___x_1575_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1570_, v_k_1572_, v___x_1574_, v_t_1571_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_inc(v_fallback_1573_);
return v_fallback_1573_;
}
else
{
lean_object* v_val_1576_; 
v_val_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_val_1576_);
lean_dec_ref(v___x_1575_);
return v_val_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1577_, lean_object* v_00_u03b2_1578_, lean_object* v_cmp_1579_, lean_object* v_t_1580_, lean_object* v_k_1581_, lean_object* v_fallback_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Std_DTreeMap_getKeyGED(v_00_u03b1_1577_, v_00_u03b2_1578_, v_cmp_1579_, v_t_1580_, v_k_1581_, v_fallback_1582_);
lean_dec(v_fallback_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1584_, lean_object* v_t_1585_, lean_object* v_k_1586_, lean_object* v_fallback_1587_){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_box(0);
v___x_1589_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1584_, v_k_1586_, v___x_1588_, v_t_1585_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_inc(v_fallback_1587_);
return v_fallback_1587_;
}
else
{
lean_object* v_val_1590_; 
v_val_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_val_1590_);
lean_dec_ref(v___x_1589_);
return v_val_1590_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1591_, lean_object* v_t_1592_, lean_object* v_k_1593_, lean_object* v_fallback_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Std_DTreeMap_getKeyGTD___redArg(v_cmp_1591_, v_t_1592_, v_k_1593_, v_fallback_1594_);
lean_dec(v_fallback_1594_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD(lean_object* v_00_u03b1_1596_, lean_object* v_00_u03b2_1597_, lean_object* v_cmp_1598_, lean_object* v_t_1599_, lean_object* v_k_1600_, lean_object* v_fallback_1601_){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_box(0);
v___x_1603_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1598_, v_k_1600_, v___x_1602_, v_t_1599_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_inc(v_fallback_1601_);
return v_fallback_1601_;
}
else
{
lean_object* v_val_1604_; 
v_val_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_val_1604_);
lean_dec_ref(v___x_1603_);
return v_val_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1605_, lean_object* v_00_u03b2_1606_, lean_object* v_cmp_1607_, lean_object* v_t_1608_, lean_object* v_k_1609_, lean_object* v_fallback_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Std_DTreeMap_getKeyGTD(v_00_u03b1_1605_, v_00_u03b2_1606_, v_cmp_1607_, v_t_1608_, v_k_1609_, v_fallback_1610_);
lean_dec(v_fallback_1610_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___redArg(lean_object* v_cmp_1612_, lean_object* v_t_1613_, lean_object* v_k_1614_, lean_object* v_fallback_1615_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_box(0);
v___x_1617_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1612_, v_k_1614_, v___x_1616_, v_t_1613_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_inc(v_fallback_1615_);
return v_fallback_1615_;
}
else
{
lean_object* v_val_1618_; 
v_val_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_val_1618_);
lean_dec_ref(v___x_1617_);
return v_val_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1619_, lean_object* v_t_1620_, lean_object* v_k_1621_, lean_object* v_fallback_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Std_DTreeMap_getKeyLED___redArg(v_cmp_1619_, v_t_1620_, v_k_1621_, v_fallback_1622_);
lean_dec(v_fallback_1622_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED(lean_object* v_00_u03b1_1624_, lean_object* v_00_u03b2_1625_, lean_object* v_cmp_1626_, lean_object* v_t_1627_, lean_object* v_k_1628_, lean_object* v_fallback_1629_){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_box(0);
v___x_1631_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1626_, v_k_1628_, v___x_1630_, v_t_1627_);
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
lean_dec_ref(v___x_1631_);
return v_val_1632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1633_, lean_object* v_00_u03b2_1634_, lean_object* v_cmp_1635_, lean_object* v_t_1636_, lean_object* v_k_1637_, lean_object* v_fallback_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Std_DTreeMap_getKeyLED(v_00_u03b1_1633_, v_00_u03b2_1634_, v_cmp_1635_, v_t_1636_, v_k_1637_, v_fallback_1638_);
lean_dec(v_fallback_1638_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1640_, lean_object* v_t_1641_, lean_object* v_k_1642_, lean_object* v_fallback_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = lean_box(0);
v___x_1645_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1640_, v_k_1642_, v___x_1644_, v_t_1641_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_inc(v_fallback_1643_);
return v_fallback_1643_;
}
else
{
lean_object* v_val_1646_; 
v_val_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_val_1646_);
lean_dec_ref(v___x_1645_);
return v_val_1646_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1647_, lean_object* v_t_1648_, lean_object* v_k_1649_, lean_object* v_fallback_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Std_DTreeMap_getKeyLTD___redArg(v_cmp_1647_, v_t_1648_, v_k_1649_, v_fallback_1650_);
lean_dec(v_fallback_1650_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD(lean_object* v_00_u03b1_1652_, lean_object* v_00_u03b2_1653_, lean_object* v_cmp_1654_, lean_object* v_t_1655_, lean_object* v_k_1656_, lean_object* v_fallback_1657_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_box(0);
v___x_1659_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1654_, v_k_1656_, v___x_1658_, v_t_1655_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_inc(v_fallback_1657_);
return v_fallback_1657_;
}
else
{
lean_object* v_val_1660_; 
v_val_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_val_1660_);
lean_dec_ref(v___x_1659_);
return v_val_1660_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1661_, lean_object* v_00_u03b2_1662_, lean_object* v_cmp_1663_, lean_object* v_t_1664_, lean_object* v_k_1665_, lean_object* v_fallback_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Std_DTreeMap_getKeyLTD(v_00_u03b1_1661_, v_00_u03b2_1662_, v_cmp_1663_, v_t_1664_, v_k_1665_, v_fallback_1666_);
lean_dec(v_fallback_1666_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1668_, lean_object* v_t_1669_, lean_object* v_a_1670_, lean_object* v_b_1671_){
_start:
{
lean_object* v___x_1672_; 
lean_inc(v_a_1670_);
lean_inc(v_t_1669_);
lean_inc_ref(v_cmp_1668_);
v___x_1672_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1668_, v_t_1669_, v_a_1670_);
if (lean_obj_tag(v___x_1672_) == 0)
{
uint8_t v___x_1673_; 
lean_inc(v_t_1669_);
lean_inc(v_a_1670_);
lean_inc_ref(v_cmp_1668_);
v___x_1673_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1668_, v_a_1670_, v_t_1669_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1668_, v_a_1670_, v_b_1671_, v_t_1669_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1672_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
return v___x_1675_;
}
else
{
lean_object* v___x_1676_; 
lean_dec(v_b_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_cmp_1668_);
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1672_);
lean_ctor_set(v___x_1676_, 1, v_t_1669_);
return v___x_1676_;
}
}
else
{
lean_object* v___x_1677_; 
lean_dec(v_b_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_cmp_1668_);
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1672_);
lean_ctor_set(v___x_1677_, 1, v_t_1669_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1678_, lean_object* v_cmp_1679_, lean_object* v_00_u03b2_1680_, lean_object* v_t_1681_, lean_object* v_a_1682_, lean_object* v_b_1683_){
_start:
{
lean_object* v___x_1684_; 
lean_inc(v_a_1682_);
lean_inc(v_t_1681_);
lean_inc_ref(v_cmp_1679_);
v___x_1684_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1679_, v_t_1681_, v_a_1682_);
if (lean_obj_tag(v___x_1684_) == 0)
{
uint8_t v___x_1685_; 
lean_inc(v_t_1681_);
lean_inc(v_a_1682_);
lean_inc_ref(v_cmp_1679_);
v___x_1685_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1679_, v_a_1682_, v_t_1681_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1679_, v_a_1682_, v_b_1683_, v_t_1681_);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1684_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
return v___x_1687_;
}
else
{
lean_object* v___x_1688_; 
lean_dec(v_b_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_cmp_1679_);
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1684_);
lean_ctor_set(v___x_1688_, 1, v_t_1681_);
return v___x_1688_;
}
}
else
{
lean_object* v___x_1689_; 
lean_dec(v_b_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_cmp_1679_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1684_);
lean_ctor_set(v___x_1689_, 1, v_t_1681_);
return v___x_1689_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x3f___redArg(lean_object* v_cmp_1690_, lean_object* v_t_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1690_, v_t_1691_, v_a_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x3f(lean_object* v_00_u03b1_1694_, lean_object* v_cmp_1695_, lean_object* v_00_u03b2_1696_, lean_object* v_t_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1695_, v_t_1697_, v_a_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get___redArg(lean_object* v_cmp_1700_, lean_object* v_t_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1700_, v_t_1701_, v_a_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get(lean_object* v_00_u03b1_1704_, lean_object* v_cmp_1705_, lean_object* v_00_u03b2_1706_, lean_object* v_t_1707_, lean_object* v_a_1708_, lean_object* v_h_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1705_, v_t_1707_, v_a_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___redArg(lean_object* v_cmp_1711_, lean_object* v_inst_1712_, lean_object* v_t_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1711_, v_inst_1712_, v_t_1713_, v_a_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___redArg___boxed(lean_object* v_cmp_1716_, lean_object* v_inst_1717_, lean_object* v_t_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Std_DTreeMap_Const_get_x21___redArg(v_cmp_1716_, v_inst_1717_, v_t_1718_, v_a_1719_);
lean_dec(v_inst_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21(lean_object* v_00_u03b1_1721_, lean_object* v_cmp_1722_, lean_object* v_00_u03b2_1723_, lean_object* v_inst_1724_, lean_object* v_t_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1722_, v_inst_1724_, v_t_1725_, v_a_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___boxed(lean_object* v_00_u03b1_1728_, lean_object* v_cmp_1729_, lean_object* v_00_u03b2_1730_, lean_object* v_inst_1731_, lean_object* v_t_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Std_DTreeMap_Const_get_x21(v_00_u03b1_1728_, v_cmp_1729_, v_00_u03b2_1730_, v_inst_1731_, v_t_1732_, v_a_1733_);
lean_dec(v_inst_1731_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___redArg(lean_object* v_cmp_1735_, lean_object* v_t_1736_, lean_object* v_a_1737_, lean_object* v_fallback_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1735_, v_t_1736_, v_a_1737_, v_fallback_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___redArg___boxed(lean_object* v_cmp_1740_, lean_object* v_t_1741_, lean_object* v_a_1742_, lean_object* v_fallback_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Std_DTreeMap_Const_getD___redArg(v_cmp_1740_, v_t_1741_, v_a_1742_, v_fallback_1743_);
lean_dec(v_fallback_1743_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD(lean_object* v_00_u03b1_1745_, lean_object* v_cmp_1746_, lean_object* v_00_u03b2_1747_, lean_object* v_t_1748_, lean_object* v_a_1749_, lean_object* v_fallback_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1746_, v_t_1748_, v_a_1749_, v_fallback_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___boxed(lean_object* v_00_u03b1_1752_, lean_object* v_cmp_1753_, lean_object* v_00_u03b2_1754_, lean_object* v_t_1755_, lean_object* v_a_1756_, lean_object* v_fallback_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Std_DTreeMap_Const_getD(v_00_u03b1_1752_, v_cmp_1753_, v_00_u03b2_1754_, v_t_1755_, v_a_1756_, v_fallback_1757_);
lean_dec(v_fallback_1757_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___redArg(lean_object* v_t_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Std_DTreeMap_Const_minEntry_x3f___redArg(v_t_1761_);
lean_dec(v_t_1761_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f(lean_object* v_00_u03b1_1763_, lean_object* v_cmp_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_t_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1768_, lean_object* v_cmp_1769_, lean_object* v_00_u03b2_1770_, lean_object* v_t_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Std_DTreeMap_Const_minEntry_x3f(v_00_u03b1_1768_, v_cmp_1769_, v_00_u03b2_1770_, v_t_1771_);
lean_dec(v_t_1771_);
lean_dec_ref(v_cmp_1769_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___redArg(lean_object* v_t_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___redArg___boxed(lean_object* v_t_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_DTreeMap_Const_minEntry___redArg(v_t_1775_);
lean_dec(v_t_1775_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry(lean_object* v_00_u03b1_1777_, lean_object* v_cmp_1778_, lean_object* v_00_u03b2_1779_, lean_object* v_t_1780_, lean_object* v_h_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___boxed(lean_object* v_00_u03b1_1783_, lean_object* v_cmp_1784_, lean_object* v_00_u03b2_1785_, lean_object* v_t_1786_, lean_object* v_h_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Std_DTreeMap_Const_minEntry(v_00_u03b1_1783_, v_cmp_1784_, v_00_u03b2_1785_, v_t_1786_, v_h_1787_);
lean_dec(v_t_1786_);
lean_dec_ref(v_cmp_1784_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___redArg(lean_object* v_inst_1789_, lean_object* v_t_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1789_, v_t_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1792_, lean_object* v_t_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_DTreeMap_Const_minEntry_x21___redArg(v_inst_1792_, v_t_1793_);
lean_dec(v_t_1793_);
lean_dec_ref(v_inst_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21(lean_object* v_00_u03b1_1795_, lean_object* v_cmp_1796_, lean_object* v_00_u03b2_1797_, lean_object* v_inst_1798_, lean_object* v_t_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1798_, v_t_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_cmp_1802_, lean_object* v_00_u03b2_1803_, lean_object* v_inst_1804_, lean_object* v_t_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Std_DTreeMap_Const_minEntry_x21(v_00_u03b1_1801_, v_cmp_1802_, v_00_u03b2_1803_, v_inst_1804_, v_t_1805_);
lean_dec(v_t_1805_);
lean_dec_ref(v_inst_1804_);
lean_dec_ref(v_cmp_1802_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___redArg(lean_object* v_t_1807_, lean_object* v_fallback_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1807_, v_fallback_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___redArg___boxed(lean_object* v_t_1810_, lean_object* v_fallback_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Std_DTreeMap_Const_minEntryD___redArg(v_t_1810_, v_fallback_1811_);
lean_dec_ref(v_fallback_1811_);
lean_dec(v_t_1810_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD(lean_object* v_00_u03b1_1813_, lean_object* v_cmp_1814_, lean_object* v_00_u03b2_1815_, lean_object* v_t_1816_, lean_object* v_fallback_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1816_, v_fallback_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_cmp_1820_, lean_object* v_00_u03b2_1821_, lean_object* v_t_1822_, lean_object* v_fallback_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Std_DTreeMap_Const_minEntryD(v_00_u03b1_1819_, v_cmp_1820_, v_00_u03b2_1821_, v_t_1822_, v_fallback_1823_);
lean_dec_ref(v_fallback_1823_);
lean_dec(v_t_1822_);
lean_dec_ref(v_cmp_1820_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___redArg(lean_object* v_t_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Std_DTreeMap_Const_maxEntry_x3f___redArg(v_t_1827_);
lean_dec(v_t_1827_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f(lean_object* v_00_u03b1_1829_, lean_object* v_cmp_1830_, lean_object* v_00_u03b2_1831_, lean_object* v_t_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1834_, lean_object* v_cmp_1835_, lean_object* v_00_u03b2_1836_, lean_object* v_t_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Std_DTreeMap_Const_maxEntry_x3f(v_00_u03b1_1834_, v_cmp_1835_, v_00_u03b2_1836_, v_t_1837_);
lean_dec(v_t_1837_);
lean_dec_ref(v_cmp_1835_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___redArg(lean_object* v_t_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___redArg___boxed(lean_object* v_t_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Std_DTreeMap_Const_maxEntry___redArg(v_t_1841_);
lean_dec(v_t_1841_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry(lean_object* v_00_u03b1_1843_, lean_object* v_cmp_1844_, lean_object* v_00_u03b2_1845_, lean_object* v_t_1846_, lean_object* v_h_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1846_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___boxed(lean_object* v_00_u03b1_1849_, lean_object* v_cmp_1850_, lean_object* v_00_u03b2_1851_, lean_object* v_t_1852_, lean_object* v_h_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Std_DTreeMap_Const_maxEntry(v_00_u03b1_1849_, v_cmp_1850_, v_00_u03b2_1851_, v_t_1852_, v_h_1853_);
lean_dec(v_t_1852_);
lean_dec_ref(v_cmp_1850_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___redArg(lean_object* v_inst_1855_, lean_object* v_t_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1855_, v_t_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_1858_, lean_object* v_t_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Std_DTreeMap_Const_maxEntry_x21___redArg(v_inst_1858_, v_t_1859_);
lean_dec(v_t_1859_);
lean_dec_ref(v_inst_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21(lean_object* v_00_u03b1_1861_, lean_object* v_cmp_1862_, lean_object* v_00_u03b2_1863_, lean_object* v_inst_1864_, lean_object* v_t_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1864_, v_t_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_1867_, lean_object* v_cmp_1868_, lean_object* v_00_u03b2_1869_, lean_object* v_inst_1870_, lean_object* v_t_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Std_DTreeMap_Const_maxEntry_x21(v_00_u03b1_1867_, v_cmp_1868_, v_00_u03b2_1869_, v_inst_1870_, v_t_1871_);
lean_dec(v_t_1871_);
lean_dec_ref(v_inst_1870_);
lean_dec_ref(v_cmp_1868_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___redArg(lean_object* v_t_1873_, lean_object* v_fallback_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1873_, v_fallback_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___redArg___boxed(lean_object* v_t_1876_, lean_object* v_fallback_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Std_DTreeMap_Const_maxEntryD___redArg(v_t_1876_, v_fallback_1877_);
lean_dec_ref(v_fallback_1877_);
lean_dec(v_t_1876_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD(lean_object* v_00_u03b1_1879_, lean_object* v_cmp_1880_, lean_object* v_00_u03b2_1881_, lean_object* v_t_1882_, lean_object* v_fallback_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1882_, v_fallback_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___boxed(lean_object* v_00_u03b1_1885_, lean_object* v_cmp_1886_, lean_object* v_00_u03b2_1887_, lean_object* v_t_1888_, lean_object* v_fallback_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Std_DTreeMap_Const_maxEntryD(v_00_u03b1_1885_, v_cmp_1886_, v_00_u03b2_1887_, v_t_1888_, v_fallback_1889_);
lean_dec_ref(v_fallback_1889_);
lean_dec(v_t_1888_);
lean_dec_ref(v_cmp_1886_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(lean_object* v_t_1891_, lean_object* v_n_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1891_, v_n_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_1894_, lean_object* v_n_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(v_t_1894_, v_n_1895_);
lean_dec(v_t_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_1897_, lean_object* v_cmp_1898_, lean_object* v_00_u03b2_1899_, lean_object* v_t_1900_, lean_object* v_n_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1900_, v_n_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1903_, lean_object* v_cmp_1904_, lean_object* v_00_u03b2_1905_, lean_object* v_t_1906_, lean_object* v_n_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Std_DTreeMap_Const_entryAtIdx_x3f(v_00_u03b1_1903_, v_cmp_1904_, v_00_u03b2_1905_, v_t_1906_, v_n_1907_);
lean_dec(v_t_1906_);
lean_dec_ref(v_cmp_1904_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___redArg(lean_object* v_t_1909_, lean_object* v_n_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_1909_, v_n_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___redArg___boxed(lean_object* v_t_1912_, lean_object* v_n_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Std_DTreeMap_Const_entryAtIdx___redArg(v_t_1912_, v_n_1913_);
lean_dec(v_t_1912_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx(lean_object* v_00_u03b1_1915_, lean_object* v_cmp_1916_, lean_object* v_00_u03b2_1917_, lean_object* v_t_1918_, lean_object* v_n_1919_, lean_object* v_h_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_1918_, v_n_1919_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_1922_, lean_object* v_cmp_1923_, lean_object* v_00_u03b2_1924_, lean_object* v_t_1925_, lean_object* v_n_1926_, lean_object* v_h_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Std_DTreeMap_Const_entryAtIdx(v_00_u03b1_1922_, v_cmp_1923_, v_00_u03b2_1924_, v_t_1925_, v_n_1926_, v_h_1927_);
lean_dec(v_t_1925_);
lean_dec_ref(v_cmp_1923_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(lean_object* v_inst_1929_, lean_object* v_t_1930_, lean_object* v_n_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1929_, v_t_1930_, v_n_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_1933_, lean_object* v_t_1934_, lean_object* v_n_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(v_inst_1933_, v_t_1934_, v_n_1935_);
lean_dec(v_t_1934_);
lean_dec_ref(v_inst_1933_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21(lean_object* v_00_u03b1_1937_, lean_object* v_cmp_1938_, lean_object* v_00_u03b2_1939_, lean_object* v_inst_1940_, lean_object* v_t_1941_, lean_object* v_n_1942_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1940_, v_t_1941_, v_n_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_1944_, lean_object* v_cmp_1945_, lean_object* v_00_u03b2_1946_, lean_object* v_inst_1947_, lean_object* v_t_1948_, lean_object* v_n_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Std_DTreeMap_Const_entryAtIdx_x21(v_00_u03b1_1944_, v_cmp_1945_, v_00_u03b2_1946_, v_inst_1947_, v_t_1948_, v_n_1949_);
lean_dec(v_t_1948_);
lean_dec_ref(v_inst_1947_);
lean_dec_ref(v_cmp_1945_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___redArg(lean_object* v_t_1951_, lean_object* v_n_1952_, lean_object* v_fallback_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1951_, v_n_1952_, v_fallback_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_1955_, lean_object* v_n_1956_, lean_object* v_fallback_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Std_DTreeMap_Const_entryAtIdxD___redArg(v_t_1955_, v_n_1956_, v_fallback_1957_);
lean_dec_ref(v_fallback_1957_);
lean_dec(v_t_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD(lean_object* v_00_u03b1_1959_, lean_object* v_cmp_1960_, lean_object* v_00_u03b2_1961_, lean_object* v_t_1962_, lean_object* v_n_1963_, lean_object* v_fallback_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1962_, v_n_1963_, v_fallback_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_1966_, lean_object* v_cmp_1967_, lean_object* v_00_u03b2_1968_, lean_object* v_t_1969_, lean_object* v_n_1970_, lean_object* v_fallback_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Std_DTreeMap_Const_entryAtIdxD(v_00_u03b1_1966_, v_cmp_1967_, v_00_u03b2_1968_, v_t_1969_, v_n_1970_, v_fallback_1971_);
lean_dec_ref(v_fallback_1971_);
lean_dec(v_t_1969_);
lean_dec_ref(v_cmp_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_1973_, lean_object* v_t_1974_, lean_object* v_k_1975_){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_box(0);
v___x_1977_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1973_, v_k_1975_, v___x_1976_, v_t_1974_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x3f(lean_object* v_00_u03b1_1978_, lean_object* v_cmp_1979_, lean_object* v_00_u03b2_1980_, lean_object* v_t_1981_, lean_object* v_k_1982_){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = lean_box(0);
v___x_1984_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1979_, v_k_1982_, v___x_1983_, v_t_1981_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_1985_, lean_object* v_t_1986_, lean_object* v_k_1987_){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = lean_box(0);
v___x_1989_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1985_, v_k_1987_, v___x_1988_, v_t_1986_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x3f(lean_object* v_00_u03b1_1990_, lean_object* v_cmp_1991_, lean_object* v_00_u03b2_1992_, lean_object* v_t_1993_, lean_object* v_k_1994_){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_box(0);
v___x_1996_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1991_, v_k_1994_, v___x_1995_, v_t_1993_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_1997_, lean_object* v_t_1998_, lean_object* v_k_1999_){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_box(0);
v___x_2001_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1997_, v_k_1999_, v___x_2000_, v_t_1998_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x3f(lean_object* v_00_u03b1_2002_, lean_object* v_cmp_2003_, lean_object* v_00_u03b2_2004_, lean_object* v_t_2005_, lean_object* v_k_2006_){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_box(0);
v___x_2008_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2003_, v_k_2006_, v___x_2007_, v_t_2005_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_2009_, lean_object* v_t_2010_, lean_object* v_k_2011_){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_box(0);
v___x_2013_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2009_, v_k_2011_, v___x_2012_, v_t_2010_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x3f(lean_object* v_00_u03b1_2014_, lean_object* v_cmp_2015_, lean_object* v_00_u03b2_2016_, lean_object* v_t_2017_, lean_object* v_k_2018_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_box(0);
v___x_2020_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2015_, v_k_2018_, v___x_2019_, v_t_2017_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___redArg(lean_object* v_cmp_2021_, lean_object* v_inst_2022_, lean_object* v_t_2023_, lean_object* v_k_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_box(0);
v___x_2026_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2021_, v_k_2024_, v___x_2025_, v_t_2023_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2028_ = l_panic___redArg(v_inst_2022_, v___x_2027_);
return v___x_2028_;
}
else
{
lean_object* v_val_2029_; 
v_val_2029_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_val_2029_);
lean_dec_ref(v___x_2026_);
return v_val_2029_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_2030_, lean_object* v_inst_2031_, lean_object* v_t_2032_, lean_object* v_k_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Std_DTreeMap_Const_getEntryGE_x21___redArg(v_cmp_2030_, v_inst_2031_, v_t_2032_, v_k_2033_);
lean_dec_ref(v_inst_2031_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21(lean_object* v_00_u03b1_2035_, lean_object* v_cmp_2036_, lean_object* v_00_u03b2_2037_, lean_object* v_inst_2038_, lean_object* v_t_2039_, lean_object* v_k_2040_){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_box(0);
v___x_2042_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2036_, v_k_2040_, v___x_2041_, v_t_2039_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2044_ = l_panic___redArg(v_inst_2038_, v___x_2043_);
return v___x_2044_;
}
else
{
lean_object* v_val_2045_; 
v_val_2045_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_val_2045_);
lean_dec_ref(v___x_2042_);
return v_val_2045_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_2046_, lean_object* v_cmp_2047_, lean_object* v_00_u03b2_2048_, lean_object* v_inst_2049_, lean_object* v_t_2050_, lean_object* v_k_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Std_DTreeMap_Const_getEntryGE_x21(v_00_u03b1_2046_, v_cmp_2047_, v_00_u03b2_2048_, v_inst_2049_, v_t_2050_, v_k_2051_);
lean_dec_ref(v_inst_2049_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___redArg(lean_object* v_cmp_2053_, lean_object* v_inst_2054_, lean_object* v_t_2055_, lean_object* v_k_2056_){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = lean_box(0);
v___x_2058_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2053_, v_k_2056_, v___x_2057_, v_t_2055_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2060_ = l_panic___redArg(v_inst_2054_, v___x_2059_);
return v___x_2060_;
}
else
{
lean_object* v_val_2061_; 
v_val_2061_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_val_2061_);
lean_dec_ref(v___x_2058_);
return v_val_2061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_2062_, lean_object* v_inst_2063_, lean_object* v_t_2064_, lean_object* v_k_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Std_DTreeMap_Const_getEntryGT_x21___redArg(v_cmp_2062_, v_inst_2063_, v_t_2064_, v_k_2065_);
lean_dec_ref(v_inst_2063_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21(lean_object* v_00_u03b1_2067_, lean_object* v_cmp_2068_, lean_object* v_00_u03b2_2069_, lean_object* v_inst_2070_, lean_object* v_t_2071_, lean_object* v_k_2072_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_box(0);
v___x_2074_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2068_, v_k_2072_, v___x_2073_, v_t_2071_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2076_ = l_panic___redArg(v_inst_2070_, v___x_2075_);
return v___x_2076_;
}
else
{
lean_object* v_val_2077_; 
v_val_2077_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_val_2077_);
lean_dec_ref(v___x_2074_);
return v_val_2077_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_2078_, lean_object* v_cmp_2079_, lean_object* v_00_u03b2_2080_, lean_object* v_inst_2081_, lean_object* v_t_2082_, lean_object* v_k_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Std_DTreeMap_Const_getEntryGT_x21(v_00_u03b1_2078_, v_cmp_2079_, v_00_u03b2_2080_, v_inst_2081_, v_t_2082_, v_k_2083_);
lean_dec_ref(v_inst_2081_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___redArg(lean_object* v_cmp_2085_, lean_object* v_inst_2086_, lean_object* v_t_2087_, lean_object* v_k_2088_){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_box(0);
v___x_2090_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2085_, v_k_2088_, v___x_2089_, v_t_2087_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2092_ = l_panic___redArg(v_inst_2086_, v___x_2091_);
return v___x_2092_;
}
else
{
lean_object* v_val_2093_; 
v_val_2093_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_val_2093_);
lean_dec_ref(v___x_2090_);
return v_val_2093_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_2094_, lean_object* v_inst_2095_, lean_object* v_t_2096_, lean_object* v_k_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Std_DTreeMap_Const_getEntryLE_x21___redArg(v_cmp_2094_, v_inst_2095_, v_t_2096_, v_k_2097_);
lean_dec_ref(v_inst_2095_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21(lean_object* v_00_u03b1_2099_, lean_object* v_cmp_2100_, lean_object* v_00_u03b2_2101_, lean_object* v_inst_2102_, lean_object* v_t_2103_, lean_object* v_k_2104_){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2100_, v_k_2104_, v___x_2105_, v_t_2103_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2108_ = l_panic___redArg(v_inst_2102_, v___x_2107_);
return v___x_2108_;
}
else
{
lean_object* v_val_2109_; 
v_val_2109_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_val_2109_);
lean_dec_ref(v___x_2106_);
return v_val_2109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2110_, lean_object* v_cmp_2111_, lean_object* v_00_u03b2_2112_, lean_object* v_inst_2113_, lean_object* v_t_2114_, lean_object* v_k_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Std_DTreeMap_Const_getEntryLE_x21(v_00_u03b1_2110_, v_cmp_2111_, v_00_u03b2_2112_, v_inst_2113_, v_t_2114_, v_k_2115_);
lean_dec_ref(v_inst_2113_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___redArg(lean_object* v_cmp_2117_, lean_object* v_inst_2118_, lean_object* v_t_2119_, lean_object* v_k_2120_){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_box(0);
v___x_2122_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2117_, v_k_2120_, v___x_2121_, v_t_2119_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2124_ = l_panic___redArg(v_inst_2118_, v___x_2123_);
return v___x_2124_;
}
else
{
lean_object* v_val_2125_; 
v_val_2125_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_val_2125_);
lean_dec_ref(v___x_2122_);
return v_val_2125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_2126_, lean_object* v_inst_2127_, lean_object* v_t_2128_, lean_object* v_k_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Std_DTreeMap_Const_getEntryLT_x21___redArg(v_cmp_2126_, v_inst_2127_, v_t_2128_, v_k_2129_);
lean_dec_ref(v_inst_2127_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21(lean_object* v_00_u03b1_2131_, lean_object* v_cmp_2132_, lean_object* v_00_u03b2_2133_, lean_object* v_inst_2134_, lean_object* v_t_2135_, lean_object* v_k_2136_){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = lean_box(0);
v___x_2138_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2132_, v_k_2136_, v___x_2137_, v_t_2135_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2140_ = l_panic___redArg(v_inst_2134_, v___x_2139_);
return v___x_2140_;
}
else
{
lean_object* v_val_2141_; 
v_val_2141_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_val_2141_);
lean_dec_ref(v___x_2138_);
return v_val_2141_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2142_, lean_object* v_cmp_2143_, lean_object* v_00_u03b2_2144_, lean_object* v_inst_2145_, lean_object* v_t_2146_, lean_object* v_k_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Std_DTreeMap_Const_getEntryLT_x21(v_00_u03b1_2142_, v_cmp_2143_, v_00_u03b2_2144_, v_inst_2145_, v_t_2146_, v_k_2147_);
lean_dec_ref(v_inst_2145_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___redArg(lean_object* v_cmp_2149_, lean_object* v_t_2150_, lean_object* v_k_2151_, lean_object* v_fallback_2152_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_box(0);
v___x_2154_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2149_, v_k_2151_, v___x_2153_, v_t_2150_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_inc_ref(v_fallback_2152_);
return v_fallback_2152_;
}
else
{
lean_object* v_val_2155_; 
v_val_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_val_2155_);
lean_dec_ref(v___x_2154_);
return v_val_2155_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2156_, lean_object* v_t_2157_, lean_object* v_k_2158_, lean_object* v_fallback_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Std_DTreeMap_Const_getEntryGED___redArg(v_cmp_2156_, v_t_2157_, v_k_2158_, v_fallback_2159_);
lean_dec_ref(v_fallback_2159_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED(lean_object* v_00_u03b1_2161_, lean_object* v_cmp_2162_, lean_object* v_00_u03b2_2163_, lean_object* v_t_2164_, lean_object* v_k_2165_, lean_object* v_fallback_2166_){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = lean_box(0);
v___x_2168_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2162_, v_k_2165_, v___x_2167_, v_t_2164_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_inc_ref(v_fallback_2166_);
return v_fallback_2166_;
}
else
{
lean_object* v_val_2169_; 
v_val_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_val_2169_);
lean_dec_ref(v___x_2168_);
return v_val_2169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2170_, lean_object* v_cmp_2171_, lean_object* v_00_u03b2_2172_, lean_object* v_t_2173_, lean_object* v_k_2174_, lean_object* v_fallback_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Std_DTreeMap_Const_getEntryGED(v_00_u03b1_2170_, v_cmp_2171_, v_00_u03b2_2172_, v_t_2173_, v_k_2174_, v_fallback_2175_);
lean_dec_ref(v_fallback_2175_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___redArg(lean_object* v_cmp_2177_, lean_object* v_t_2178_, lean_object* v_k_2179_, lean_object* v_fallback_2180_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_box(0);
v___x_2182_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2177_, v_k_2179_, v___x_2181_, v_t_2178_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_inc_ref(v_fallback_2180_);
return v_fallback_2180_;
}
else
{
lean_object* v_val_2183_; 
v_val_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_val_2183_);
lean_dec_ref(v___x_2182_);
return v_val_2183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2184_, lean_object* v_t_2185_, lean_object* v_k_2186_, lean_object* v_fallback_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Std_DTreeMap_Const_getEntryGTD___redArg(v_cmp_2184_, v_t_2185_, v_k_2186_, v_fallback_2187_);
lean_dec_ref(v_fallback_2187_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD(lean_object* v_00_u03b1_2189_, lean_object* v_cmp_2190_, lean_object* v_00_u03b2_2191_, lean_object* v_t_2192_, lean_object* v_k_2193_, lean_object* v_fallback_2194_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = lean_box(0);
v___x_2196_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2190_, v_k_2193_, v___x_2195_, v_t_2192_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_inc_ref(v_fallback_2194_);
return v_fallback_2194_;
}
else
{
lean_object* v_val_2197_; 
v_val_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_val_2197_);
lean_dec_ref(v___x_2196_);
return v_val_2197_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2198_, lean_object* v_cmp_2199_, lean_object* v_00_u03b2_2200_, lean_object* v_t_2201_, lean_object* v_k_2202_, lean_object* v_fallback_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Std_DTreeMap_Const_getEntryGTD(v_00_u03b1_2198_, v_cmp_2199_, v_00_u03b2_2200_, v_t_2201_, v_k_2202_, v_fallback_2203_);
lean_dec_ref(v_fallback_2203_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___redArg(lean_object* v_cmp_2205_, lean_object* v_t_2206_, lean_object* v_k_2207_, lean_object* v_fallback_2208_){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_box(0);
v___x_2210_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2205_, v_k_2207_, v___x_2209_, v_t_2206_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_inc_ref(v_fallback_2208_);
return v_fallback_2208_;
}
else
{
lean_object* v_val_2211_; 
v_val_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_val_2211_);
lean_dec_ref(v___x_2210_);
return v_val_2211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2212_, lean_object* v_t_2213_, lean_object* v_k_2214_, lean_object* v_fallback_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Std_DTreeMap_Const_getEntryLED___redArg(v_cmp_2212_, v_t_2213_, v_k_2214_, v_fallback_2215_);
lean_dec_ref(v_fallback_2215_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED(lean_object* v_00_u03b1_2217_, lean_object* v_cmp_2218_, lean_object* v_00_u03b2_2219_, lean_object* v_t_2220_, lean_object* v_k_2221_, lean_object* v_fallback_2222_){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_box(0);
v___x_2224_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2218_, v_k_2221_, v___x_2223_, v_t_2220_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_inc_ref(v_fallback_2222_);
return v_fallback_2222_;
}
else
{
lean_object* v_val_2225_; 
v_val_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_val_2225_);
lean_dec_ref(v___x_2224_);
return v_val_2225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2226_, lean_object* v_cmp_2227_, lean_object* v_00_u03b2_2228_, lean_object* v_t_2229_, lean_object* v_k_2230_, lean_object* v_fallback_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Std_DTreeMap_Const_getEntryLED(v_00_u03b1_2226_, v_cmp_2227_, v_00_u03b2_2228_, v_t_2229_, v_k_2230_, v_fallback_2231_);
lean_dec_ref(v_fallback_2231_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___redArg(lean_object* v_cmp_2233_, lean_object* v_t_2234_, lean_object* v_k_2235_, lean_object* v_fallback_2236_){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_box(0);
v___x_2238_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2233_, v_k_2235_, v___x_2237_, v_t_2234_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_inc_ref(v_fallback_2236_);
return v_fallback_2236_;
}
else
{
lean_object* v_val_2239_; 
v_val_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_val_2239_);
lean_dec_ref(v___x_2238_);
return v_val_2239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2240_, lean_object* v_t_2241_, lean_object* v_k_2242_, lean_object* v_fallback_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Std_DTreeMap_Const_getEntryLTD___redArg(v_cmp_2240_, v_t_2241_, v_k_2242_, v_fallback_2243_);
lean_dec_ref(v_fallback_2243_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD(lean_object* v_00_u03b1_2245_, lean_object* v_cmp_2246_, lean_object* v_00_u03b2_2247_, lean_object* v_t_2248_, lean_object* v_k_2249_, lean_object* v_fallback_2250_){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_box(0);
v___x_2252_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2246_, v_k_2249_, v___x_2251_, v_t_2248_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2254_, lean_object* v_cmp_2255_, lean_object* v_00_u03b2_2256_, lean_object* v_t_2257_, lean_object* v_k_2258_, lean_object* v_fallback_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Std_DTreeMap_Const_getEntryLTD(v_00_u03b1_2254_, v_cmp_2255_, v_00_u03b2_2256_, v_t_2257_, v_k_2258_, v_fallback_2259_);
lean_dec_ref(v_fallback_2259_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter___redArg(lean_object* v_f_2261_, lean_object* v_t_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2261_, v_t_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter(lean_object* v_00_u03b1_2264_, lean_object* v_00_u03b2_2265_, lean_object* v_cmp_2266_, lean_object* v_f_2267_, lean_object* v_t_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2267_, v_t_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter___boxed(lean_object* v_00_u03b1_2270_, lean_object* v_00_u03b2_2271_, lean_object* v_cmp_2272_, lean_object* v_f_2273_, lean_object* v_t_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Std_DTreeMap_filter(v_00_u03b1_2270_, v_00_u03b2_2271_, v_cmp_2272_, v_f_2273_, v_t_2274_);
lean_dec_ref(v_cmp_2272_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM___redArg(lean_object* v_inst_2276_, lean_object* v_f_2277_, lean_object* v_init_2278_, lean_object* v_t_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2276_, v_f_2277_, v_init_2278_, v_t_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM(lean_object* v_00_u03b1_2281_, lean_object* v_00_u03b2_2282_, lean_object* v_cmp_2283_, lean_object* v_00_u03b4_2284_, lean_object* v_m_2285_, lean_object* v_inst_2286_, lean_object* v_f_2287_, lean_object* v_init_2288_, lean_object* v_t_2289_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2286_, v_f_2287_, v_init_2288_, v_t_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM___boxed(lean_object* v_00_u03b1_2291_, lean_object* v_00_u03b2_2292_, lean_object* v_cmp_2293_, lean_object* v_00_u03b4_2294_, lean_object* v_m_2295_, lean_object* v_inst_2296_, lean_object* v_f_2297_, lean_object* v_init_2298_, lean_object* v_t_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Std_DTreeMap_foldlM(v_00_u03b1_2291_, v_00_u03b2_2292_, v_cmp_2293_, v_00_u03b4_2294_, v_m_2295_, v_inst_2296_, v_f_2297_, v_init_2298_, v_t_2299_);
lean_dec_ref(v_cmp_2293_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl___redArg(lean_object* v_f_2301_, lean_object* v_init_2302_, lean_object* v_t_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2301_, v_init_2302_, v_t_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl(lean_object* v_00_u03b1_2305_, lean_object* v_00_u03b2_2306_, lean_object* v_cmp_2307_, lean_object* v_00_u03b4_2308_, lean_object* v_f_2309_, lean_object* v_init_2310_, lean_object* v_t_2311_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2309_, v_init_2310_, v_t_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl___boxed(lean_object* v_00_u03b1_2313_, lean_object* v_00_u03b2_2314_, lean_object* v_cmp_2315_, lean_object* v_00_u03b4_2316_, lean_object* v_f_2317_, lean_object* v_init_2318_, lean_object* v_t_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Std_DTreeMap_foldl(v_00_u03b1_2313_, v_00_u03b2_2314_, v_cmp_2315_, v_00_u03b4_2316_, v_f_2317_, v_init_2318_, v_t_2319_);
lean_dec_ref(v_cmp_2315_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM___redArg(lean_object* v_inst_2321_, lean_object* v_f_2322_, lean_object* v_init_2323_, lean_object* v_t_2324_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2321_, v_f_2322_, v_init_2323_, v_t_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM(lean_object* v_00_u03b1_2326_, lean_object* v_00_u03b2_2327_, lean_object* v_cmp_2328_, lean_object* v_00_u03b4_2329_, lean_object* v_m_2330_, lean_object* v_inst_2331_, lean_object* v_f_2332_, lean_object* v_init_2333_, lean_object* v_t_2334_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2331_, v_f_2332_, v_init_2333_, v_t_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM___boxed(lean_object* v_00_u03b1_2336_, lean_object* v_00_u03b2_2337_, lean_object* v_cmp_2338_, lean_object* v_00_u03b4_2339_, lean_object* v_m_2340_, lean_object* v_inst_2341_, lean_object* v_f_2342_, lean_object* v_init_2343_, lean_object* v_t_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Std_DTreeMap_foldrM(v_00_u03b1_2336_, v_00_u03b2_2337_, v_cmp_2338_, v_00_u03b4_2339_, v_m_2340_, v_inst_2341_, v_f_2342_, v_init_2343_, v_t_2344_);
lean_dec_ref(v_cmp_2338_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___redArg___lam__0(lean_object* v_f_2346_, lean_object* v_x1_2347_, lean_object* v_x2_2348_, lean_object* v_x3_2349_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_apply_3(v_f_2346_, v_x1_2347_, v_x2_2348_, v_x3_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___redArg(lean_object* v_f_2370_, lean_object* v_init_2371_, lean_object* v_t_2372_){
_start:
{
lean_object* v___f_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___f_2373_ = lean_alloc_closure((void*)(l_Std_DTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2373_, 0, v_f_2370_);
v___x_2374_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2375_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2374_, v___f_2373_, v_init_2371_, v_t_2372_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr(lean_object* v_00_u03b1_2376_, lean_object* v_00_u03b2_2377_, lean_object* v_cmp_2378_, lean_object* v_00_u03b4_2379_, lean_object* v_f_2380_, lean_object* v_init_2381_, lean_object* v_t_2382_){
_start:
{
lean_object* v___f_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___f_2383_ = lean_alloc_closure((void*)(l_Std_DTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2383_, 0, v_f_2380_);
v___x_2384_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2385_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2384_, v___f_2383_, v_init_2381_, v_t_2382_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___boxed(lean_object* v_00_u03b1_2386_, lean_object* v_00_u03b2_2387_, lean_object* v_cmp_2388_, lean_object* v_00_u03b4_2389_, lean_object* v_f_2390_, lean_object* v_init_2391_, lean_object* v_t_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Std_DTreeMap_foldr(v_00_u03b1_2386_, v_00_u03b2_2387_, v_cmp_2388_, v_00_u03b4_2389_, v_f_2390_, v_init_2391_, v_t_2392_);
lean_dec_ref(v_cmp_2388_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition___redArg___lam__0(lean_object* v_f_2394_, lean_object* v_cmp_2395_, lean_object* v_x_2396_, lean_object* v_a_2397_, lean_object* v_b_2398_){
_start:
{
lean_object* v_fst_2399_; lean_object* v_snd_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2414_; 
v_fst_2399_ = lean_ctor_get(v_x_2396_, 0);
v_snd_2400_ = lean_ctor_get(v_x_2396_, 1);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_x_2396_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2402_ = v_x_2396_;
v_isShared_2403_ = v_isSharedCheck_2414_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_snd_2400_);
lean_inc(v_fst_2399_);
lean_dec(v_x_2396_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2414_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
lean_inc(v_b_2398_);
lean_inc(v_a_2397_);
v___x_2404_ = lean_apply_2(v_f_2394_, v_a_2397_, v_b_2398_);
v___x_2405_ = lean_unbox(v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2406_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2395_, v_a_2397_, v_b_2398_, v_snd_2400_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 1, v___x_2406_);
v___x_2408_ = v___x_2402_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_fst_2399_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
else
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2410_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2395_, v_a_2397_, v_b_2398_, v_fst_2399_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2410_);
v___x_2412_ = v___x_2402_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_snd_2400_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition___redArg(lean_object* v_cmp_2417_, lean_object* v_f_2418_, lean_object* v_t_2419_){
_start:
{
lean_object* v___f_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___f_2420_ = lean_alloc_closure((void*)(l_Std_DTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2420_, 0, v_f_2418_);
lean_closure_set(v___f_2420_, 1, v_cmp_2417_);
v___x_2421_ = ((lean_object*)(l_Std_DTreeMap_partition___redArg___closed__0));
v___x_2422_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2420_, v___x_2421_, v_t_2419_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition(lean_object* v_00_u03b1_2423_, lean_object* v_00_u03b2_2424_, lean_object* v_cmp_2425_, lean_object* v_f_2426_, lean_object* v_t_2427_){
_start:
{
lean_object* v___f_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___f_2428_ = lean_alloc_closure((void*)(l_Std_DTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2428_, 0, v_f_2426_);
lean_closure_set(v___f_2428_, 1, v_cmp_2425_);
v___x_2429_ = ((lean_object*)(l_Std_DTreeMap_partition___redArg___closed__0));
v___x_2430_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2428_, v___x_2429_, v_t_2427_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___redArg___lam__0(lean_object* v_f_2431_, lean_object* v_x_2432_, lean_object* v_k_2433_, lean_object* v_v_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_apply_2(v_f_2431_, v_k_2433_, v_v_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___redArg(lean_object* v_inst_2436_, lean_object* v_f_2437_, lean_object* v_t_2438_){
_start:
{
lean_object* v___f_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___f_2439_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2439_, 0, v_f_2437_);
v___x_2440_ = lean_box(0);
v___x_2441_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2436_, v___f_2439_, v___x_2440_, v_t_2438_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM(lean_object* v_00_u03b1_2442_, lean_object* v_00_u03b2_2443_, lean_object* v_cmp_2444_, lean_object* v_m_2445_, lean_object* v_inst_2446_, lean_object* v_f_2447_, lean_object* v_t_2448_){
_start:
{
lean_object* v___f_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___f_2449_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2449_, 0, v_f_2447_);
v___x_2450_ = lean_box(0);
v___x_2451_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2446_, v___f_2449_, v___x_2450_, v_t_2448_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___boxed(lean_object* v_00_u03b1_2452_, lean_object* v_00_u03b2_2453_, lean_object* v_cmp_2454_, lean_object* v_m_2455_, lean_object* v_inst_2456_, lean_object* v_f_2457_, lean_object* v_t_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Std_DTreeMap_forM(v_00_u03b1_2452_, v_00_u03b2_2453_, v_cmp_2454_, v_m_2455_, v_inst_2456_, v_f_2457_, v_t_2458_);
lean_dec_ref(v_cmp_2454_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___redArg___lam__0(lean_object* v_toPure_2460_, lean_object* v_____do__lift_2461_){
_start:
{
lean_object* v_a_2462_; lean_object* v___x_2463_; 
v_a_2462_ = lean_ctor_get(v_____do__lift_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref(v_____do__lift_2461_);
v___x_2463_ = lean_apply_2(v_toPure_2460_, lean_box(0), v_a_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___redArg(lean_object* v_inst_2464_, lean_object* v_f_2465_, lean_object* v_init_2466_, lean_object* v_t_2467_){
_start:
{
lean_object* v_toApplicative_2468_; lean_object* v_toBind_2469_; lean_object* v_toPure_2470_; lean_object* v___x_2471_; lean_object* v___f_2472_; lean_object* v___x_2473_; 
v_toApplicative_2468_ = lean_ctor_get(v_inst_2464_, 0);
v_toBind_2469_ = lean_ctor_get(v_inst_2464_, 1);
lean_inc(v_toBind_2469_);
v_toPure_2470_ = lean_ctor_get(v_toApplicative_2468_, 1);
lean_inc(v_toPure_2470_);
v___x_2471_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2464_, v_f_2465_, v_init_2466_, v_t_2467_);
v___f_2472_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2472_, 0, v_toPure_2470_);
v___x_2473_ = lean_apply_4(v_toBind_2469_, lean_box(0), lean_box(0), v___x_2471_, v___f_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn(lean_object* v_00_u03b1_2474_, lean_object* v_00_u03b2_2475_, lean_object* v_cmp_2476_, lean_object* v_00_u03b4_2477_, lean_object* v_m_2478_, lean_object* v_inst_2479_, lean_object* v_f_2480_, lean_object* v_init_2481_, lean_object* v_t_2482_){
_start:
{
lean_object* v_toApplicative_2483_; lean_object* v_toBind_2484_; lean_object* v_toPure_2485_; lean_object* v___x_2486_; lean_object* v___f_2487_; lean_object* v___x_2488_; 
v_toApplicative_2483_ = lean_ctor_get(v_inst_2479_, 0);
v_toBind_2484_ = lean_ctor_get(v_inst_2479_, 1);
lean_inc(v_toBind_2484_);
v_toPure_2485_ = lean_ctor_get(v_toApplicative_2483_, 1);
lean_inc(v_toPure_2485_);
v___x_2486_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2479_, v_f_2480_, v_init_2481_, v_t_2482_);
v___f_2487_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2487_, 0, v_toPure_2485_);
v___x_2488_ = lean_apply_4(v_toBind_2484_, lean_box(0), lean_box(0), v___x_2486_, v___f_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___boxed(lean_object* v_00_u03b1_2489_, lean_object* v_00_u03b2_2490_, lean_object* v_cmp_2491_, lean_object* v_00_u03b4_2492_, lean_object* v_m_2493_, lean_object* v_inst_2494_, lean_object* v_f_2495_, lean_object* v_init_2496_, lean_object* v_t_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Std_DTreeMap_forIn(v_00_u03b1_2489_, v_00_u03b2_2490_, v_cmp_2491_, v_00_u03b4_2492_, v_m_2493_, v_inst_2494_, v_f_2495_, v_init_2496_, v_t_2497_);
lean_dec_ref(v_cmp_2491_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_2499_, lean_object* v_x_2500_, lean_object* v_k_2501_, lean_object* v_v_2502_){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v_k_2501_);
lean_ctor_set(v___x_2503_, 1, v_v_2502_);
v___x_2504_ = lean_apply_1(v_f_2499_, v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1(lean_object* v_inst_2505_, lean_object* v_t_2506_, lean_object* v_f_2507_){
_start:
{
lean_object* v___f_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___f_2508_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2508_, 0, v_f_2507_);
v___x_2509_ = lean_box(0);
v___x_2510_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2505_, v___f_2508_, v___x_2509_, v_t_2506_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg(lean_object* v_inst_2511_){
_start:
{
lean_object* v___f_2512_; 
v___f_2512_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2512_, 0, v_inst_2511_);
return v___f_2512_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad(lean_object* v_00_u03b1_2513_, lean_object* v_00_u03b2_2514_, lean_object* v_cmp_2515_, lean_object* v_m_2516_, lean_object* v_inst_2517_){
_start:
{
lean_object* v___f_2518_; 
v___f_2518_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2518_, 0, v_inst_2517_);
return v___f_2518_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___boxed(lean_object* v_00_u03b1_2519_, lean_object* v_00_u03b2_2520_, lean_object* v_cmp_2521_, lean_object* v_m_2522_, lean_object* v_inst_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Std_DTreeMap_instForMSigmaOfMonad(v_00_u03b1_2519_, v_00_u03b2_2520_, v_cmp_2521_, v_m_2522_, v_inst_2523_);
lean_dec_ref(v_cmp_2521_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_2525_, lean_object* v_a_2526_, lean_object* v_b_2527_, lean_object* v_acc_2528_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2529_, 0, v_a_2526_);
lean_ctor_set(v___x_2529_, 1, v_b_2527_);
v___x_2530_ = lean_apply_2(v_f_2525_, v___x_2529_, v_acc_2528_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_2531_, lean_object* v_00_u03b2_2532_, lean_object* v_m_2533_, lean_object* v_init_2534_, lean_object* v_f_2535_){
_start:
{
lean_object* v_toApplicative_2536_; lean_object* v_toBind_2537_; lean_object* v_toPure_2538_; lean_object* v___f_2539_; lean_object* v___x_2540_; lean_object* v___f_2541_; lean_object* v___x_2542_; 
v_toApplicative_2536_ = lean_ctor_get(v_inst_2531_, 0);
v_toBind_2537_ = lean_ctor_get(v_inst_2531_, 1);
lean_inc(v_toBind_2537_);
v_toPure_2538_ = lean_ctor_get(v_toApplicative_2536_, 1);
lean_inc(v_toPure_2538_);
v___f_2539_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2539_, 0, v_f_2535_);
v___x_2540_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2531_, v___f_2539_, v_init_2534_, v_m_2533_);
v___f_2541_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2541_, 0, v_toPure_2538_);
v___x_2542_ = lean_apply_4(v_toBind_2537_, lean_box(0), lean_box(0), v___x_2540_, v___f_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg(lean_object* v_inst_2543_){
_start:
{
lean_object* v___f_2544_; 
v___f_2544_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2544_, 0, v_inst_2543_);
return v___f_2544_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad(lean_object* v_00_u03b1_2545_, lean_object* v_00_u03b2_2546_, lean_object* v_cmp_2547_, lean_object* v_m_2548_, lean_object* v_inst_2549_){
_start:
{
lean_object* v___f_2550_; 
v___f_2550_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2550_, 0, v_inst_2549_);
return v___f_2550_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___boxed(lean_object* v_00_u03b1_2551_, lean_object* v_00_u03b2_2552_, lean_object* v_cmp_2553_, lean_object* v_m_2554_, lean_object* v_inst_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Std_DTreeMap_instForInSigmaOfMonad(v_00_u03b1_2551_, v_00_u03b2_2552_, v_cmp_2553_, v_m_2554_, v_inst_2555_);
lean_dec_ref(v_cmp_2553_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2557_, lean_object* v_x_2558_, lean_object* v_k_2559_, lean_object* v_v_2560_){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v_k_2559_);
lean_ctor_set(v___x_2561_, 1, v_v_2560_);
v___x_2562_ = lean_apply_1(v_f_2557_, v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___redArg(lean_object* v_inst_2563_, lean_object* v_f_2564_, lean_object* v_t_2565_){
_start:
{
lean_object* v___f_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___f_2566_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2566_, 0, v_f_2564_);
v___x_2567_ = lean_box(0);
v___x_2568_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2563_, v___f_2566_, v___x_2567_, v_t_2565_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried(lean_object* v_00_u03b1_2569_, lean_object* v_cmp_2570_, lean_object* v_m_2571_, lean_object* v_inst_2572_, lean_object* v_00_u03b2_2573_, lean_object* v_f_2574_, lean_object* v_t_2575_){
_start:
{
lean_object* v___f_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___f_2576_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2576_, 0, v_f_2574_);
v___x_2577_ = lean_box(0);
v___x_2578_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2572_, v___f_2576_, v___x_2577_, v_t_2575_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2579_, lean_object* v_cmp_2580_, lean_object* v_m_2581_, lean_object* v_inst_2582_, lean_object* v_00_u03b2_2583_, lean_object* v_f_2584_, lean_object* v_t_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Std_DTreeMap_Const_forMUncurried(v_00_u03b1_2579_, v_cmp_2580_, v_m_2581_, v_inst_2582_, v_00_u03b2_2583_, v_f_2584_, v_t_2585_);
lean_dec_ref(v_cmp_2580_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2587_, lean_object* v_a_2588_, lean_object* v_b_2589_, lean_object* v_acc_2590_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_a_2588_);
lean_ctor_set(v___x_2591_, 1, v_b_2589_);
v___x_2592_ = lean_apply_2(v_f_2587_, v___x_2591_, v_acc_2590_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___redArg(lean_object* v_inst_2593_, lean_object* v_f_2594_, lean_object* v_init_2595_, lean_object* v_t_2596_){
_start:
{
lean_object* v_toApplicative_2597_; lean_object* v_toBind_2598_; lean_object* v_toPure_2599_; lean_object* v___f_2600_; lean_object* v___x_2601_; lean_object* v___f_2602_; lean_object* v___x_2603_; 
v_toApplicative_2597_ = lean_ctor_get(v_inst_2593_, 0);
v_toBind_2598_ = lean_ctor_get(v_inst_2593_, 1);
lean_inc(v_toBind_2598_);
v_toPure_2599_ = lean_ctor_get(v_toApplicative_2597_, 1);
lean_inc(v_toPure_2599_);
v___f_2600_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2600_, 0, v_f_2594_);
v___x_2601_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2593_, v___f_2600_, v_init_2595_, v_t_2596_);
v___f_2602_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2602_, 0, v_toPure_2599_);
v___x_2603_ = lean_apply_4(v_toBind_2598_, lean_box(0), lean_box(0), v___x_2601_, v___f_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried(lean_object* v_00_u03b1_2604_, lean_object* v_cmp_2605_, lean_object* v_00_u03b4_2606_, lean_object* v_m_2607_, lean_object* v_inst_2608_, lean_object* v_00_u03b2_2609_, lean_object* v_f_2610_, lean_object* v_init_2611_, lean_object* v_t_2612_){
_start:
{
lean_object* v_toApplicative_2613_; lean_object* v_toBind_2614_; lean_object* v_toPure_2615_; lean_object* v___f_2616_; lean_object* v___x_2617_; lean_object* v___f_2618_; lean_object* v___x_2619_; 
v_toApplicative_2613_ = lean_ctor_get(v_inst_2608_, 0);
v_toBind_2614_ = lean_ctor_get(v_inst_2608_, 1);
lean_inc(v_toBind_2614_);
v_toPure_2615_ = lean_ctor_get(v_toApplicative_2613_, 1);
lean_inc(v_toPure_2615_);
v___f_2616_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2616_, 0, v_f_2610_);
v___x_2617_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2608_, v___f_2616_, v_init_2611_, v_t_2612_);
v___f_2618_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2618_, 0, v_toPure_2615_);
v___x_2619_ = lean_apply_4(v_toBind_2614_, lean_box(0), lean_box(0), v___x_2617_, v___f_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2620_, lean_object* v_cmp_2621_, lean_object* v_00_u03b4_2622_, lean_object* v_m_2623_, lean_object* v_inst_2624_, lean_object* v_00_u03b2_2625_, lean_object* v_f_2626_, lean_object* v_init_2627_, lean_object* v_t_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Std_DTreeMap_Const_forInUncurried(v_00_u03b1_2620_, v_cmp_2621_, v_00_u03b4_2622_, v_m_2623_, v_inst_2624_, v_00_u03b2_2625_, v_f_2626_, v_init_2627_, v_t_2628_);
lean_dec_ref(v_cmp_2621_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___lam__0(lean_object* v_p_2630_, lean_object* v___x_2631_, lean_object* v___x_2632_, lean_object* v_a_2633_, lean_object* v_b_2634_, lean_object* v_acc_2635_){
_start:
{
lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = lean_apply_2(v_p_2630_, v_a_2633_, v_b_2634_);
v___x_2637_ = lean_unbox(v___x_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2631_);
return v___x_2638_;
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_dec_ref(v___x_2631_);
v___x_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2636_);
v___x_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
lean_ctor_set(v___x_2640_, 1, v___x_2632_);
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
return v___x_2641_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2642_, lean_object* v___x_2643_, lean_object* v___x_2644_, lean_object* v_a_2645_, lean_object* v_b_2646_, lean_object* v_acc_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Std_DTreeMap_any___redArg___lam__0(v_p_2642_, v___x_2643_, v___x_2644_, v_a_2645_, v_b_2646_, v_acc_2647_);
lean_dec_ref(v_acc_2647_);
return v_res_2648_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_any___redArg(lean_object* v_t_2652_, lean_object* v_p_2653_){
_start:
{
lean_object* v___y_2655_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___f_2663_; lean_object* v___x_2664_; lean_object* v_a_2665_; 
v___x_2660_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2661_ = lean_box(0);
v___x_2662_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2663_ = lean_alloc_closure((void*)(l_Std_DTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2663_, 0, v_p_2653_);
lean_closure_set(v___f_2663_, 1, v___x_2662_);
lean_closure_set(v___f_2663_, 2, v___x_2661_);
v___x_2664_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2660_, v___f_2663_, v___x_2662_, v_t_2652_);
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___y_2655_ = v_a_2665_;
goto v___jp_2654_;
v___jp_2654_:
{
lean_object* v_fst_2656_; 
v_fst_2656_ = lean_ctor_get(v___y_2655_, 0);
lean_inc(v_fst_2656_);
lean_dec_ref(v___y_2655_);
if (lean_obj_tag(v_fst_2656_) == 0)
{
uint8_t v___x_2657_; 
v___x_2657_ = 0;
return v___x_2657_;
}
else
{
lean_object* v_val_2658_; uint8_t v___x_2659_; 
v_val_2658_ = lean_ctor_get(v_fst_2656_, 0);
lean_inc(v_val_2658_);
lean_dec_ref(v_fst_2656_);
v___x_2659_ = lean_unbox(v_val_2658_);
lean_dec(v_val_2658_);
return v___x_2659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___boxed(lean_object* v_t_2666_, lean_object* v_p_2667_){
_start:
{
uint8_t v_res_2668_; lean_object* v_r_2669_; 
v_res_2668_ = l_Std_DTreeMap_any___redArg(v_t_2666_, v_p_2667_);
v_r_2669_ = lean_box(v_res_2668_);
return v_r_2669_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_any(lean_object* v_00_u03b1_2670_, lean_object* v_00_u03b2_2671_, lean_object* v_cmp_2672_, lean_object* v_t_2673_, lean_object* v_p_2674_){
_start:
{
lean_object* v___y_2676_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___f_2684_; lean_object* v___x_2685_; lean_object* v_a_2686_; 
v___x_2681_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2682_ = lean_box(0);
v___x_2683_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2684_ = lean_alloc_closure((void*)(l_Std_DTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2684_, 0, v_p_2674_);
lean_closure_set(v___f_2684_, 1, v___x_2683_);
lean_closure_set(v___f_2684_, 2, v___x_2682_);
v___x_2685_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2681_, v___f_2684_, v___x_2683_, v_t_2673_);
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___y_2676_ = v_a_2686_;
goto v___jp_2675_;
v___jp_2675_:
{
lean_object* v_fst_2677_; 
v_fst_2677_ = lean_ctor_get(v___y_2676_, 0);
lean_inc(v_fst_2677_);
lean_dec_ref(v___y_2676_);
if (lean_obj_tag(v_fst_2677_) == 0)
{
uint8_t v___x_2678_; 
v___x_2678_ = 0;
return v___x_2678_;
}
else
{
lean_object* v_val_2679_; uint8_t v___x_2680_; 
v_val_2679_ = lean_ctor_get(v_fst_2677_, 0);
lean_inc(v_val_2679_);
lean_dec_ref(v_fst_2677_);
v___x_2680_ = lean_unbox(v_val_2679_);
lean_dec(v_val_2679_);
return v___x_2680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___boxed(lean_object* v_00_u03b1_2687_, lean_object* v_00_u03b2_2688_, lean_object* v_cmp_2689_, lean_object* v_t_2690_, lean_object* v_p_2691_){
_start:
{
uint8_t v_res_2692_; lean_object* v_r_2693_; 
v_res_2692_ = l_Std_DTreeMap_any(v_00_u03b1_2687_, v_00_u03b2_2688_, v_cmp_2689_, v_t_2690_, v_p_2691_);
lean_dec_ref(v_cmp_2689_);
v_r_2693_ = lean_box(v_res_2692_);
return v_r_2693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___lam__0(lean_object* v_p_2694_, lean_object* v___x_2695_, lean_object* v___x_2696_, lean_object* v_a_2697_, lean_object* v_b_2698_, lean_object* v_acc_2699_){
_start:
{
lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2700_ = lean_apply_2(v_p_2694_, v_a_2697_, v_b_2698_);
v___x_2701_ = lean_unbox(v___x_2700_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
lean_dec_ref(v___x_2696_);
v___x_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v___x_2695_);
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
return v___x_2704_;
}
else
{
lean_object* v___x_2705_; 
v___x_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2696_);
return v___x_2705_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_2706_, lean_object* v___x_2707_, lean_object* v___x_2708_, lean_object* v_a_2709_, lean_object* v_b_2710_, lean_object* v_acc_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Std_DTreeMap_all___redArg___lam__0(v_p_2706_, v___x_2707_, v___x_2708_, v_a_2709_, v_b_2710_, v_acc_2711_);
lean_dec_ref(v_acc_2711_);
return v_res_2712_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_all___redArg(lean_object* v_t_2713_, lean_object* v_p_2714_){
_start:
{
lean_object* v___y_2716_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___f_2724_; lean_object* v___x_2725_; lean_object* v_a_2726_; 
v___x_2721_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2722_ = lean_box(0);
v___x_2723_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2724_ = lean_alloc_closure((void*)(l_Std_DTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2724_, 0, v_p_2714_);
lean_closure_set(v___f_2724_, 1, v___x_2722_);
lean_closure_set(v___f_2724_, 2, v___x_2723_);
v___x_2725_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2721_, v___f_2724_, v___x_2723_, v_t_2713_);
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___y_2716_ = v_a_2726_;
goto v___jp_2715_;
v___jp_2715_:
{
lean_object* v_fst_2717_; 
v_fst_2717_ = lean_ctor_get(v___y_2716_, 0);
lean_inc(v_fst_2717_);
lean_dec_ref(v___y_2716_);
if (lean_obj_tag(v_fst_2717_) == 0)
{
uint8_t v___x_2718_; 
v___x_2718_ = 1;
return v___x_2718_;
}
else
{
lean_object* v_val_2719_; uint8_t v___x_2720_; 
v_val_2719_ = lean_ctor_get(v_fst_2717_, 0);
lean_inc(v_val_2719_);
lean_dec_ref(v_fst_2717_);
v___x_2720_ = lean_unbox(v_val_2719_);
lean_dec(v_val_2719_);
return v___x_2720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___boxed(lean_object* v_t_2727_, lean_object* v_p_2728_){
_start:
{
uint8_t v_res_2729_; lean_object* v_r_2730_; 
v_res_2729_ = l_Std_DTreeMap_all___redArg(v_t_2727_, v_p_2728_);
v_r_2730_ = lean_box(v_res_2729_);
return v_r_2730_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_all(lean_object* v_00_u03b1_2731_, lean_object* v_00_u03b2_2732_, lean_object* v_cmp_2733_, lean_object* v_t_2734_, lean_object* v_p_2735_){
_start:
{
lean_object* v___y_2737_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___f_2745_; lean_object* v___x_2746_; lean_object* v_a_2747_; 
v___x_2742_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2743_ = lean_box(0);
v___x_2744_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2745_ = lean_alloc_closure((void*)(l_Std_DTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2745_, 0, v_p_2735_);
lean_closure_set(v___f_2745_, 1, v___x_2743_);
lean_closure_set(v___f_2745_, 2, v___x_2744_);
v___x_2746_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2742_, v___f_2745_, v___x_2744_, v_t_2734_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___y_2737_ = v_a_2747_;
goto v___jp_2736_;
v___jp_2736_:
{
lean_object* v_fst_2738_; 
v_fst_2738_ = lean_ctor_get(v___y_2737_, 0);
lean_inc(v_fst_2738_);
lean_dec_ref(v___y_2737_);
if (lean_obj_tag(v_fst_2738_) == 0)
{
uint8_t v___x_2739_; 
v___x_2739_ = 1;
return v___x_2739_;
}
else
{
lean_object* v_val_2740_; uint8_t v___x_2741_; 
v_val_2740_ = lean_ctor_get(v_fst_2738_, 0);
lean_inc(v_val_2740_);
lean_dec_ref(v_fst_2738_);
v___x_2741_ = lean_unbox(v_val_2740_);
lean_dec(v_val_2740_);
return v___x_2741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___boxed(lean_object* v_00_u03b1_2748_, lean_object* v_00_u03b2_2749_, lean_object* v_cmp_2750_, lean_object* v_t_2751_, lean_object* v_p_2752_){
_start:
{
uint8_t v_res_2753_; lean_object* v_r_2754_; 
v_res_2753_ = l_Std_DTreeMap_all(v_00_u03b1_2748_, v_00_u03b2_2749_, v_cmp_2750_, v_t_2751_, v_p_2752_);
lean_dec_ref(v_cmp_2750_);
v_r_2754_ = lean_box(v_res_2753_);
return v_r_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg___lam__0(lean_object* v_x1_2755_, lean_object* v_x2_2756_, lean_object* v_x3_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2758_, 0, v_x1_2755_);
lean_ctor_set(v___x_2758_, 1, v_x3_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_2759_, lean_object* v_x2_2760_, lean_object* v_x3_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Std_DTreeMap_keys___redArg___lam__0(v_x1_2759_, v_x2_2760_, v_x3_2761_);
lean_dec(v_x2_2760_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg(lean_object* v_t_2764_){
_start:
{
lean_object* v___f_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___f_2765_ = ((lean_object*)(l_Std_DTreeMap_keys___redArg___closed__0));
v___x_2766_ = lean_box(0);
v___x_2767_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2768_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2767_, v___f_2765_, v___x_2766_, v_t_2764_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys(lean_object* v_00_u03b1_2769_, lean_object* v_00_u03b2_2770_, lean_object* v_cmp_2771_, lean_object* v_t_2772_){
_start:
{
lean_object* v___f_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___f_2773_ = ((lean_object*)(l_Std_DTreeMap_keys___redArg___closed__0));
v___x_2774_ = lean_box(0);
v___x_2775_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2776_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2775_, v___f_2773_, v___x_2774_, v_t_2772_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___boxed(lean_object* v_00_u03b1_2777_, lean_object* v_00_u03b2_2778_, lean_object* v_cmp_2779_, lean_object* v_t_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Std_DTreeMap_keys(v_00_u03b1_2777_, v_00_u03b2_2778_, v_cmp_2779_, v_t_2780_);
lean_dec_ref(v_cmp_2779_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg___lam__0(lean_object* v_l_2782_, lean_object* v_k_2783_, lean_object* v_x_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_array_push(v_l_2782_, v_k_2783_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_2786_, lean_object* v_k_2787_, lean_object* v_x_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Std_DTreeMap_keysArray___redArg___lam__0(v_l_2786_, v_k_2787_, v_x_2788_);
lean_dec(v_x_2788_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg(lean_object* v_t_2791_){
_start:
{
lean_object* v___f_2792_; lean_object* v___y_2794_; 
v___f_2792_ = ((lean_object*)(l_Std_DTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2791_) == 0)
{
lean_object* v_size_2797_; 
v_size_2797_ = lean_ctor_get(v_t_2791_, 0);
lean_inc(v_size_2797_);
v___y_2794_ = v_size_2797_;
goto v___jp_2793_;
}
else
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_unsigned_to_nat(0u);
v___y_2794_ = v___x_2798_;
goto v___jp_2793_;
}
v___jp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_mk_empty_array_with_capacity(v___y_2794_);
lean_dec(v___y_2794_);
v___x_2796_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2792_, v___x_2795_, v_t_2791_);
return v___x_2796_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray(lean_object* v_00_u03b1_2799_, lean_object* v_00_u03b2_2800_, lean_object* v_cmp_2801_, lean_object* v_t_2802_){
_start:
{
lean_object* v___f_2803_; lean_object* v___y_2805_; 
v___f_2803_ = ((lean_object*)(l_Std_DTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2802_) == 0)
{
lean_object* v_size_2808_; 
v_size_2808_ = lean_ctor_get(v_t_2802_, 0);
lean_inc(v_size_2808_);
v___y_2805_ = v_size_2808_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2809_; 
v___x_2809_ = lean_unsigned_to_nat(0u);
v___y_2805_ = v___x_2809_;
goto v___jp_2804_;
}
v___jp_2804_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_mk_empty_array_with_capacity(v___y_2805_);
lean_dec(v___y_2805_);
v___x_2807_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2803_, v___x_2806_, v_t_2802_);
return v___x_2807_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___boxed(lean_object* v_00_u03b1_2810_, lean_object* v_00_u03b2_2811_, lean_object* v_cmp_2812_, lean_object* v_t_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Std_DTreeMap_keysArray(v_00_u03b1_2810_, v_00_u03b2_2811_, v_cmp_2812_, v_t_2813_);
lean_dec_ref(v_cmp_2812_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg___lam__0(lean_object* v_x1_2815_, lean_object* v_x2_2816_, lean_object* v_x3_2817_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2818_, 0, v_x2_2816_);
lean_ctor_set(v___x_2818_, 1, v_x3_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_2819_, lean_object* v_x2_2820_, lean_object* v_x3_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Std_DTreeMap_values___redArg___lam__0(v_x1_2819_, v_x2_2820_, v_x3_2821_);
lean_dec(v_x1_2819_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg(lean_object* v_t_2824_){
_start:
{
lean_object* v___f_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___f_2825_ = ((lean_object*)(l_Std_DTreeMap_values___redArg___closed__0));
v___x_2826_ = lean_box(0);
v___x_2827_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2828_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2827_, v___f_2825_, v___x_2826_, v_t_2824_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values(lean_object* v_00_u03b1_2829_, lean_object* v_cmp_2830_, lean_object* v_00_u03b2_2831_, lean_object* v_t_2832_){
_start:
{
lean_object* v___f_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___f_2833_ = ((lean_object*)(l_Std_DTreeMap_values___redArg___closed__0));
v___x_2834_ = lean_box(0);
v___x_2835_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2836_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2835_, v___f_2833_, v___x_2834_, v_t_2832_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___boxed(lean_object* v_00_u03b1_2837_, lean_object* v_cmp_2838_, lean_object* v_00_u03b2_2839_, lean_object* v_t_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Std_DTreeMap_values(v_00_u03b1_2837_, v_cmp_2838_, v_00_u03b2_2839_, v_t_2840_);
lean_dec_ref(v_cmp_2838_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_2842_, lean_object* v_x_2843_, lean_object* v_v_2844_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_array_push(v_l_2842_, v_v_2844_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2846_, lean_object* v_x_2847_, lean_object* v_v_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Std_DTreeMap_valuesArray___redArg___lam__0(v_l_2846_, v_x_2847_, v_v_2848_);
lean_dec(v_x_2847_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg(lean_object* v_t_2851_){
_start:
{
lean_object* v___f_2852_; lean_object* v___y_2854_; 
v___f_2852_ = ((lean_object*)(l_Std_DTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2851_) == 0)
{
lean_object* v_size_2857_; 
v_size_2857_ = lean_ctor_get(v_t_2851_, 0);
lean_inc(v_size_2857_);
v___y_2854_ = v_size_2857_;
goto v___jp_2853_;
}
else
{
lean_object* v___x_2858_; 
v___x_2858_ = lean_unsigned_to_nat(0u);
v___y_2854_ = v___x_2858_;
goto v___jp_2853_;
}
v___jp_2853_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = lean_mk_empty_array_with_capacity(v___y_2854_);
lean_dec(v___y_2854_);
v___x_2856_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2852_, v___x_2855_, v_t_2851_);
return v___x_2856_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray(lean_object* v_00_u03b1_2859_, lean_object* v_cmp_2860_, lean_object* v_00_u03b2_2861_, lean_object* v_t_2862_){
_start:
{
lean_object* v___f_2863_; lean_object* v___y_2865_; 
v___f_2863_ = ((lean_object*)(l_Std_DTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2862_) == 0)
{
lean_object* v_size_2868_; 
v_size_2868_ = lean_ctor_get(v_t_2862_, 0);
lean_inc(v_size_2868_);
v___y_2865_ = v_size_2868_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_2869_; 
v___x_2869_ = lean_unsigned_to_nat(0u);
v___y_2865_ = v___x_2869_;
goto v___jp_2864_;
}
v___jp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_mk_empty_array_with_capacity(v___y_2865_);
lean_dec(v___y_2865_);
v___x_2867_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2863_, v___x_2866_, v_t_2862_);
return v___x_2867_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_2870_, lean_object* v_cmp_2871_, lean_object* v_00_u03b2_2872_, lean_object* v_t_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Std_DTreeMap_valuesArray(v_00_u03b1_2870_, v_cmp_2871_, v_00_u03b2_2872_, v_t_2873_);
lean_dec_ref(v_cmp_2871_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___redArg___lam__0(lean_object* v_x1_2875_, lean_object* v_x2_2876_, lean_object* v_x3_2877_){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2878_, 0, v_x1_2875_);
lean_ctor_set(v___x_2878_, 1, v_x2_2876_);
v___x_2879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
lean_ctor_set(v___x_2879_, 1, v_x3_2877_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___redArg(lean_object* v_t_2881_){
_start:
{
lean_object* v___f_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___f_2882_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_2883_ = lean_box(0);
v___x_2884_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2885_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2884_, v___f_2882_, v___x_2883_, v_t_2881_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList(lean_object* v_00_u03b1_2886_, lean_object* v_00_u03b2_2887_, lean_object* v_cmp_2888_, lean_object* v_t_2889_){
_start:
{
lean_object* v___f_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___f_2890_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_2891_ = lean_box(0);
v___x_2892_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2893_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2892_, v___f_2890_, v___x_2891_, v_t_2889_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___boxed(lean_object* v_00_u03b1_2894_, lean_object* v_00_u03b2_2895_, lean_object* v_cmp_2896_, lean_object* v_t_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Std_DTreeMap_toList(v_00_u03b1_2894_, v_00_u03b2_2895_, v_cmp_2896_, v_t_2897_);
lean_dec_ref(v_cmp_2896_);
return v_res_2898_;
}
}
static lean_object* _init_l_Std_DTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_2900_, lean_object* v_a_2901_, lean_object* v_x_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_fst_2904_; lean_object* v_snd_2905_; lean_object* v_r_2906_; lean_object* v___x_2907_; 
v_fst_2904_ = lean_ctor_get(v_a_2901_, 0);
lean_inc(v_fst_2904_);
v_snd_2905_ = lean_ctor_get(v_a_2901_, 1);
lean_inc(v_snd_2905_);
lean_dec_ref(v_a_2901_);
v_r_2906_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2900_, v_fst_2904_, v_snd_2905_, v___y_2903_);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_r_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg(lean_object* v_l_2908_, lean_object* v_cmp_2909_){
_start:
{
lean_object* v___f_2910_; lean_object* v___x_2911_; lean_object* v_r_2912_; lean_object* v___x_2913_; 
v___f_2910_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2910_, 0, v_cmp_2909_);
v___x_2911_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2912_ = lean_box(1);
v___x_2913_ = l_List_forIn_x27_loop___redArg(v___x_2911_, v___f_2910_, v_l_2908_, v_r_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList(lean_object* v_00_u03b1_2914_, lean_object* v_00_u03b2_2915_, lean_object* v_l_2916_, lean_object* v_cmp_2917_){
_start:
{
lean_object* v___f_2918_; lean_object* v___x_2919_; lean_object* v_r_2920_; lean_object* v___x_2921_; 
v___f_2918_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2918_, 0, v_cmp_2917_);
v___x_2919_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2920_ = lean_box(1);
v___x_2921_ = l_List_forIn_x27_loop___redArg(v___x_2919_, v___f_2918_, v_l_2916_, v_r_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___redArg___lam__0(lean_object* v_l_2922_, lean_object* v_k_2923_, lean_object* v_v_2924_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v_k_2923_);
lean_ctor_set(v___x_2925_, 1, v_v_2924_);
v___x_2926_ = lean_array_push(v_l_2922_, v___x_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___redArg(lean_object* v_t_2928_){
_start:
{
lean_object* v___f_2929_; lean_object* v___y_2931_; 
v___f_2929_ = ((lean_object*)(l_Std_DTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2928_) == 0)
{
lean_object* v_size_2934_; 
v_size_2934_ = lean_ctor_get(v_t_2928_, 0);
lean_inc(v_size_2934_);
v___y_2931_ = v_size_2934_;
goto v___jp_2930_;
}
else
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_unsigned_to_nat(0u);
v___y_2931_ = v___x_2935_;
goto v___jp_2930_;
}
v___jp_2930_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = lean_mk_empty_array_with_capacity(v___y_2931_);
lean_dec(v___y_2931_);
v___x_2933_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2929_, v___x_2932_, v_t_2928_);
return v___x_2933_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray(lean_object* v_00_u03b1_2936_, lean_object* v_00_u03b2_2937_, lean_object* v_cmp_2938_, lean_object* v_t_2939_){
_start:
{
lean_object* v___f_2940_; lean_object* v___y_2942_; 
v___f_2940_ = ((lean_object*)(l_Std_DTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2939_) == 0)
{
lean_object* v_size_2945_; 
v_size_2945_ = lean_ctor_get(v_t_2939_, 0);
lean_inc(v_size_2945_);
v___y_2942_ = v_size_2945_;
goto v___jp_2941_;
}
else
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_unsigned_to_nat(0u);
v___y_2942_ = v___x_2946_;
goto v___jp_2941_;
}
v___jp_2941_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = lean_mk_empty_array_with_capacity(v___y_2942_);
lean_dec(v___y_2942_);
v___x_2944_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2940_, v___x_2943_, v_t_2939_);
return v___x_2944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___boxed(lean_object* v_00_u03b1_2947_, lean_object* v_00_u03b2_2948_, lean_object* v_cmp_2949_, lean_object* v_t_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Std_DTreeMap_toArray(v_00_u03b1_2947_, v_00_u03b2_2948_, v_cmp_2949_, v_t_2950_);
lean_dec_ref(v_cmp_2949_);
return v_res_2951_;
}
}
static lean_object* _init_l_Std_DTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray___redArg(lean_object* v_a_2953_, lean_object* v_cmp_2954_){
_start:
{
lean_object* v___f_2955_; lean_object* v___x_2956_; lean_object* v_r_2957_; size_t v_sz_2958_; size_t v___x_2959_; lean_object* v___x_2960_; 
v___f_2955_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2955_, 0, v_cmp_2954_);
v___x_2956_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2957_ = lean_box(1);
v_sz_2958_ = lean_array_size(v_a_2953_);
v___x_2959_ = ((size_t)0ULL);
v___x_2960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2956_, v_a_2953_, v___f_2955_, v_sz_2958_, v___x_2959_, v_r_2957_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray(lean_object* v_00_u03b1_2961_, lean_object* v_00_u03b2_2962_, lean_object* v_a_2963_, lean_object* v_cmp_2964_){
_start:
{
lean_object* v___f_2965_; lean_object* v___x_2966_; lean_object* v_r_2967_; size_t v_sz_2968_; size_t v___x_2969_; lean_object* v___x_2970_; 
v___f_2965_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2965_, 0, v_cmp_2964_);
v___x_2966_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2967_ = lean_box(1);
v_sz_2968_ = lean_array_size(v_a_2963_);
v___x_2969_ = ((size_t)0ULL);
v___x_2970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2966_, v_a_2963_, v___f_2965_, v_sz_2968_, v___x_2969_, v_r_2967_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_modify___redArg(lean_object* v_cmp_2971_, lean_object* v_t_2972_, lean_object* v_a_2973_, lean_object* v_f_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2971_, v_a_2973_, v_f_2974_, v_t_2972_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_modify(lean_object* v_00_u03b1_2976_, lean_object* v_00_u03b2_2977_, lean_object* v_cmp_2978_, lean_object* v_inst_2979_, lean_object* v_t_2980_, lean_object* v_a_2981_, lean_object* v_f_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2978_, v_a_2981_, v_f_2982_, v_t_2980_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_alter___redArg(lean_object* v_cmp_2984_, lean_object* v_t_2985_, lean_object* v_a_2986_, lean_object* v_f_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_2984_, v_a_2986_, v_f_2987_, v_t_2985_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_alter(lean_object* v_00_u03b1_2989_, lean_object* v_00_u03b2_2990_, lean_object* v_cmp_2991_, lean_object* v_inst_2992_, lean_object* v_t_2993_, lean_object* v_a_2994_, lean_object* v_f_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_2991_, v_a_2994_, v_f_2995_, v_t_2993_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2997_, lean_object* v_mergeFn_2998_, lean_object* v_a_2999_, lean_object* v_x_3000_){
_start:
{
if (lean_obj_tag(v_x_3000_) == 0)
{
lean_object* v___x_3001_; 
lean_dec(v_a_2999_);
lean_dec(v_mergeFn_2998_);
v___x_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_b_u2082_2997_);
return v___x_3001_;
}
else
{
lean_object* v_val_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3010_; 
v_val_3002_ = lean_ctor_get(v_x_3000_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_x_3000_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3004_ = v_x_3000_;
v_isShared_3005_ = v_isSharedCheck_3010_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_val_3002_);
lean_dec(v_x_3000_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3010_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; lean_object* v___x_3008_; 
v___x_3006_ = lean_apply_3(v_mergeFn_2998_, v_a_2999_, v_val_3002_, v_b_u2082_2997_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3006_);
v___x_3008_ = v___x_3004_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3011_, lean_object* v_cmp_3012_, lean_object* v_t_3013_, lean_object* v_a_3014_, lean_object* v_b_u2082_3015_){
_start:
{
lean_object* v___f_3016_; lean_object* v___x_3017_; 
lean_inc(v_a_3014_);
v___f_3016_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3016_, 0, v_b_u2082_3015_);
lean_closure_set(v___f_3016_, 1, v_mergeFn_3011_);
lean_closure_set(v___f_3016_, 2, v_a_3014_);
v___x_3017_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3012_, v_a_3014_, v___f_3016_, v_t_3013_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg(lean_object* v_cmp_3018_, lean_object* v_mergeFn_3019_, lean_object* v_t_u2081_3020_, lean_object* v_t_u2082_3021_){
_start:
{
lean_object* v___f_3022_; lean_object* v___x_3023_; 
v___f_3022_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3022_, 0, v_mergeFn_3019_);
lean_closure_set(v___f_3022_, 1, v_cmp_3018_);
v___x_3023_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3022_, v_t_u2081_3020_, v_t_u2082_3021_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith(lean_object* v_00_u03b1_3024_, lean_object* v_00_u03b2_3025_, lean_object* v_cmp_3026_, lean_object* v_inst_3027_, lean_object* v_mergeFn_3028_, lean_object* v_t_u2081_3029_, lean_object* v_t_u2082_3030_){
_start:
{
lean_object* v___f_3031_; lean_object* v___x_3032_; 
v___f_3031_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3031_, 0, v_mergeFn_3028_);
lean_closure_set(v___f_3031_, 1, v_cmp_3026_);
v___x_3032_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3031_, v_t_u2081_3029_, v_t_u2082_3030_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___redArg___lam__0(lean_object* v_x1_3033_, lean_object* v_x2_3034_, lean_object* v_x3_3035_){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v_x1_3033_);
lean_ctor_set(v___x_3036_, 1, v_x2_3034_);
v___x_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v_x3_3035_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___redArg(lean_object* v_t_3039_){
_start:
{
lean_object* v___f_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___f_3040_ = ((lean_object*)(l_Std_DTreeMap_Const_toList___redArg___closed__0));
v___x_3041_ = lean_box(0);
v___x_3042_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_3043_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3042_, v___f_3040_, v___x_3041_, v_t_3039_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList(lean_object* v_00_u03b1_3044_, lean_object* v_cmp_3045_, lean_object* v_00_u03b2_3046_, lean_object* v_t_3047_){
_start:
{
lean_object* v___f_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___f_3048_ = ((lean_object*)(l_Std_DTreeMap_Const_toList___redArg___closed__0));
v___x_3049_ = lean_box(0);
v___x_3050_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_3051_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3050_, v___f_3048_, v___x_3049_, v_t_3047_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___boxed(lean_object* v_00_u03b1_3052_, lean_object* v_cmp_3053_, lean_object* v_00_u03b2_3054_, lean_object* v_t_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Std_DTreeMap_Const_toList(v_00_u03b1_3052_, v_cmp_3053_, v_00_u03b2_3054_, v_t_3055_);
lean_dec_ref(v_cmp_3053_);
return v_res_3056_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg___lam__0(lean_object* v_cmp_3058_, lean_object* v_a_3059_, lean_object* v_x_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_fst_3062_; lean_object* v_snd_3063_; lean_object* v_r_3064_; lean_object* v___x_3065_; 
v_fst_3062_ = lean_ctor_get(v_a_3059_, 0);
lean_inc(v_fst_3062_);
v_snd_3063_ = lean_ctor_get(v_a_3059_, 1);
lean_inc(v_snd_3063_);
lean_dec_ref(v_a_3059_);
v_r_3064_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3058_, v_fst_3062_, v_snd_3063_, v___y_3061_);
v___x_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3065_, 0, v_r_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg(lean_object* v_l_3066_, lean_object* v_cmp_3067_){
_start:
{
lean_object* v___f_3068_; lean_object* v___x_3069_; lean_object* v_r_3070_; lean_object* v___x_3071_; 
v___f_3068_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3068_, 0, v_cmp_3067_);
v___x_3069_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3070_ = lean_box(1);
v___x_3071_ = l_List_forIn_x27_loop___redArg(v___x_3069_, v___f_3068_, v_l_3066_, v_r_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList(lean_object* v_00_u03b1_3072_, lean_object* v_00_u03b2_3073_, lean_object* v_l_3074_, lean_object* v_cmp_3075_){
_start:
{
lean_object* v___f_3076_; lean_object* v___x_3077_; lean_object* v_r_3078_; lean_object* v___x_3079_; 
v___f_3076_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3076_, 0, v_cmp_3075_);
v___x_3077_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3078_ = lean_box(1);
v___x_3079_ = l_List_forIn_x27_loop___redArg(v___x_3077_, v___f_3076_, v_l_3074_, v_r_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___redArg___lam__0(lean_object* v_acc_3080_, lean_object* v_k_3081_, lean_object* v_v_3082_){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3083_, 0, v_k_3081_);
lean_ctor_set(v___x_3083_, 1, v_v_3082_);
v___x_3084_ = lean_array_push(v_acc_3080_, v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___redArg(lean_object* v_t_3088_){
_start:
{
lean_object* v___f_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___f_3089_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__0));
v___x_3090_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__1));
v___x_3091_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3089_, v___x_3090_, v_t_3088_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray(lean_object* v_00_u03b1_3092_, lean_object* v_cmp_3093_, lean_object* v_00_u03b2_3094_, lean_object* v_t_3095_){
_start:
{
lean_object* v___f_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___f_3096_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__0));
v___x_3097_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__1));
v___x_3098_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3096_, v___x_3097_, v_t_3095_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___boxed(lean_object* v_00_u03b1_3099_, lean_object* v_cmp_3100_, lean_object* v_00_u03b2_3101_, lean_object* v_t_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Std_DTreeMap_Const_toArray(v_00_u03b1_3099_, v_cmp_3100_, v_00_u03b2_3101_, v_t_3102_);
lean_dec_ref(v_cmp_3100_);
return v_res_3103_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray___redArg(lean_object* v_a_3105_, lean_object* v_cmp_3106_){
_start:
{
lean_object* v___f_3107_; lean_object* v___x_3108_; lean_object* v_r_3109_; size_t v_sz_3110_; size_t v___x_3111_; lean_object* v___x_3112_; 
v___f_3107_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3107_, 0, v_cmp_3106_);
v___x_3108_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3109_ = lean_box(1);
v_sz_3110_ = lean_array_size(v_a_3105_);
v___x_3111_ = ((size_t)0ULL);
v___x_3112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3108_, v_a_3105_, v___f_3107_, v_sz_3110_, v___x_3111_, v_r_3109_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray(lean_object* v_00_u03b1_3113_, lean_object* v_00_u03b2_3114_, lean_object* v_a_3115_, lean_object* v_cmp_3116_){
_start:
{
lean_object* v___f_3117_; lean_object* v___x_3118_; lean_object* v_r_3119_; size_t v_sz_3120_; size_t v___x_3121_; lean_object* v___x_3122_; 
v___f_3117_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3117_, 0, v_cmp_3116_);
v___x_3118_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3119_ = lean_box(1);
v_sz_3120_ = lean_array_size(v_a_3115_);
v___x_3121_ = ((size_t)0ULL);
v___x_3122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3118_, v_a_3115_, v___f_3117_, v_sz_3120_, v___x_3121_, v_r_3119_);
return v___x_3122_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_3124_, lean_object* v_a_3125_, lean_object* v_x_3126_, lean_object* v___y_3127_){
_start:
{
uint8_t v___x_3128_; 
lean_inc(v___y_3127_);
lean_inc(v_a_3125_);
lean_inc_ref(v_cmp_3124_);
v___x_3128_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3124_, v_a_3125_, v___y_3127_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = lean_box(0);
v___x_3130_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3124_, v_a_3125_, v___x_3129_, v___y_3127_);
v___x_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
return v___x_3131_;
}
else
{
lean_object* v___x_3132_; 
lean_dec(v_a_3125_);
lean_dec_ref(v_cmp_3124_);
v___x_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___y_3127_);
return v___x_3132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg(lean_object* v_l_3133_, lean_object* v_cmp_3134_){
_start:
{
lean_object* v___f_3135_; lean_object* v___x_3136_; lean_object* v_r_3137_; lean_object* v___x_3138_; 
v___f_3135_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3135_, 0, v_cmp_3134_);
v___x_3136_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3137_ = lean_box(1);
v___x_3138_ = l_List_forIn_x27_loop___redArg(v___x_3136_, v___f_3135_, v_l_3133_, v_r_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList(lean_object* v_00_u03b1_3139_, lean_object* v_l_3140_, lean_object* v_cmp_3141_){
_start:
{
lean_object* v___f_3142_; lean_object* v___x_3143_; lean_object* v_r_3144_; lean_object* v___x_3145_; 
v___f_3142_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3142_, 0, v_cmp_3141_);
v___x_3143_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3144_ = lean_box(1);
v___x_3145_ = l_List_forIn_x27_loop___redArg(v___x_3143_, v___f_3142_, v_l_3140_, v_r_3144_);
return v___x_3145_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__26, &l_Std_DTreeMap___auto__1___closed__26_once, _init_l_Std_DTreeMap___auto__1___closed__26);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray___redArg(lean_object* v_a_3147_, lean_object* v_cmp_3148_){
_start:
{
lean_object* v___f_3149_; lean_object* v___x_3150_; lean_object* v_r_3151_; size_t v_sz_3152_; size_t v___x_3153_; lean_object* v___x_3154_; 
v___f_3149_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3149_, 0, v_cmp_3148_);
v___x_3150_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3151_ = lean_box(1);
v_sz_3152_ = lean_array_size(v_a_3147_);
v___x_3153_ = ((size_t)0ULL);
v___x_3154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3150_, v_a_3147_, v___f_3149_, v_sz_3152_, v___x_3153_, v_r_3151_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray(lean_object* v_00_u03b1_3155_, lean_object* v_a_3156_, lean_object* v_cmp_3157_){
_start:
{
lean_object* v___f_3158_; lean_object* v___x_3159_; lean_object* v_r_3160_; size_t v_sz_3161_; size_t v___x_3162_; lean_object* v___x_3163_; 
v___f_3158_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3158_, 0, v_cmp_3157_);
v___x_3159_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3160_ = lean_box(1);
v_sz_3161_ = lean_array_size(v_a_3156_);
v___x_3162_ = ((size_t)0ULL);
v___x_3163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3159_, v_a_3156_, v___f_3158_, v_sz_3161_, v___x_3162_, v_r_3160_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_modify___redArg(lean_object* v_cmp_3164_, lean_object* v_t_3165_, lean_object* v_a_3166_, lean_object* v_f_3167_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3164_, v_a_3166_, v_f_3167_, v_t_3165_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_modify(lean_object* v_00_u03b1_3169_, lean_object* v_cmp_3170_, lean_object* v_00_u03b2_3171_, lean_object* v_t_3172_, lean_object* v_a_3173_, lean_object* v_f_3174_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3170_, v_a_3173_, v_f_3174_, v_t_3172_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_alter___redArg(lean_object* v_cmp_3176_, lean_object* v_t_3177_, lean_object* v_a_3178_, lean_object* v_f_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3176_, v_a_3178_, v_f_3179_, v_t_3177_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_alter(lean_object* v_00_u03b1_3181_, lean_object* v_cmp_3182_, lean_object* v_00_u03b2_3183_, lean_object* v_t_3184_, lean_object* v_a_3185_, lean_object* v_f_3186_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3182_, v_a_3185_, v_f_3186_, v_t_3184_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3188_, lean_object* v_cmp_3189_, lean_object* v_t_3190_, lean_object* v_a_3191_, lean_object* v_b_u2082_3192_){
_start:
{
lean_object* v___f_3193_; lean_object* v___x_3194_; 
lean_inc(v_a_3191_);
v___f_3193_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3193_, 0, v_b_u2082_3192_);
lean_closure_set(v___f_3193_, 1, v_mergeFn_3188_);
lean_closure_set(v___f_3193_, 2, v_a_3191_);
v___x_3194_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3189_, v_a_3191_, v___f_3193_, v_t_3190_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith___redArg(lean_object* v_cmp_3195_, lean_object* v_mergeFn_3196_, lean_object* v_t_u2081_3197_, lean_object* v_t_u2082_3198_){
_start:
{
lean_object* v___f_3199_; lean_object* v___x_3200_; 
v___f_3199_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3199_, 0, v_mergeFn_3196_);
lean_closure_set(v___f_3199_, 1, v_cmp_3195_);
v___x_3200_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3199_, v_t_u2081_3197_, v_t_u2082_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith(lean_object* v_00_u03b1_3201_, lean_object* v_cmp_3202_, lean_object* v_00_u03b2_3203_, lean_object* v_mergeFn_3204_, lean_object* v_t_u2081_3205_, lean_object* v_t_u2082_3206_){
_start:
{
lean_object* v___f_3207_; lean_object* v___x_3208_; 
v___f_3207_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3207_, 0, v_mergeFn_3204_);
lean_closure_set(v___f_3207_, 1, v_cmp_3202_);
v___x_3208_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3207_, v_t_u2081_3205_, v_t_u2082_3206_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_3209_, lean_object* v_x_3210_, lean_object* v_____s_3211_){
_start:
{
lean_object* v_fst_3212_; lean_object* v_snd_3213_; lean_object* v_r_3214_; lean_object* v___x_3215_; 
v_fst_3212_ = lean_ctor_get(v_x_3210_, 0);
lean_inc(v_fst_3212_);
v_snd_3213_ = lean_ctor_get(v_x_3210_, 1);
lean_inc(v_snd_3213_);
lean_dec_ref(v_x_3210_);
v_r_3214_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3209_, v_fst_3212_, v_snd_3213_, v_____s_3211_);
v___x_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3215_, 0, v_r_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany___redArg(lean_object* v_cmp_3216_, lean_object* v_inst_3217_, lean_object* v_t_3218_, lean_object* v_l_3219_){
_start:
{
lean_object* v___f_3220_; lean_object* v___x_3221_; 
v___f_3220_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3220_, 0, v_cmp_3216_);
v___x_3221_ = lean_apply_4(v_inst_3217_, lean_box(0), v_l_3219_, v_t_3218_, v___f_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany(lean_object* v_00_u03b1_3222_, lean_object* v_00_u03b2_3223_, lean_object* v_cmp_3224_, lean_object* v_00_u03c1_3225_, lean_object* v_inst_3226_, lean_object* v_t_3227_, lean_object* v_l_3228_){
_start:
{
lean_object* v___f_3229_; lean_object* v___x_3230_; 
v___f_3229_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3229_, 0, v_cmp_3224_);
v___x_3230_ = lean_apply_4(v_inst_3226_, lean_box(0), v_l_3228_, v_t_3227_, v___f_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew___redArg___lam__0(lean_object* v_cmp_3231_, lean_object* v_x_3232_, lean_object* v_____s_3233_){
_start:
{
lean_object* v_fst_3234_; lean_object* v_snd_3235_; uint8_t v___x_3236_; 
v_fst_3234_ = lean_ctor_get(v_x_3232_, 0);
lean_inc_n(v_fst_3234_, 2);
v_snd_3235_ = lean_ctor_get(v_x_3232_, 1);
lean_inc(v_snd_3235_);
lean_dec_ref(v_x_3232_);
lean_inc(v_____s_3233_);
lean_inc_ref(v_cmp_3231_);
v___x_3236_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3231_, v_fst_3234_, v_____s_3233_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3231_, v_fst_3234_, v_snd_3235_, v_____s_3233_);
v___x_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
return v___x_3238_;
}
else
{
lean_object* v___x_3239_; 
lean_dec(v_snd_3235_);
lean_dec(v_fst_3234_);
lean_dec_ref(v_cmp_3231_);
v___x_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3239_, 0, v_____s_3233_);
return v___x_3239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew___redArg(lean_object* v_cmp_3240_, lean_object* v_inst_3241_, lean_object* v_t_3242_, lean_object* v_l_3243_){
_start:
{
lean_object* v___f_3244_; lean_object* v___x_3245_; 
v___f_3244_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertManyIfNew___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3244_, 0, v_cmp_3240_);
v___x_3245_ = lean_apply_4(v_inst_3241_, lean_box(0), v_l_3243_, v_t_3242_, v___f_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew(lean_object* v_00_u03b1_3246_, lean_object* v_00_u03b2_3247_, lean_object* v_cmp_3248_, lean_object* v_00_u03c1_3249_, lean_object* v_inst_3250_, lean_object* v_t_3251_, lean_object* v_l_3252_){
_start:
{
lean_object* v___f_3253_; lean_object* v___x_3254_; 
v___f_3253_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertManyIfNew___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3253_, 0, v_cmp_3248_);
v___x_3254_ = lean_apply_4(v_inst_3250_, lean_box(0), v_l_3252_, v_t_3251_, v___f_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(lean_object* v_cmp_3255_, lean_object* v_k_3256_, lean_object* v_v_3257_, lean_object* v_t_3258_){
_start:
{
if (lean_obj_tag(v_t_3258_) == 0)
{
lean_object* v_size_3259_; lean_object* v_k_3260_; lean_object* v_v_3261_; lean_object* v_l_3262_; lean_object* v_r_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3544_; 
v_size_3259_ = lean_ctor_get(v_t_3258_, 0);
v_k_3260_ = lean_ctor_get(v_t_3258_, 1);
v_v_3261_ = lean_ctor_get(v_t_3258_, 2);
v_l_3262_ = lean_ctor_get(v_t_3258_, 3);
v_r_3263_ = lean_ctor_get(v_t_3258_, 4);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_t_3258_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3265_ = v_t_3258_;
v_isShared_3266_ = v_isSharedCheck_3544_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_r_3263_);
lean_inc(v_l_3262_);
lean_inc(v_v_3261_);
lean_inc(v_k_3260_);
lean_inc(v_size_3259_);
lean_dec(v_t_3258_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3544_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3267_; uint8_t v___x_3268_; 
lean_inc_ref(v_cmp_3255_);
lean_inc(v_k_3260_);
lean_inc(v_k_3256_);
v___x_3267_ = lean_apply_2(v_cmp_3255_, v_k_3256_, v_k_3260_);
v___x_3268_ = lean_unbox(v___x_3267_);
switch(v___x_3268_)
{
case 0:
{
lean_object* v_impl_3269_; lean_object* v___x_3270_; 
lean_dec(v_size_3259_);
v_impl_3269_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3255_, v_k_3256_, v_v_3257_, v_l_3262_);
v___x_3270_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3263_) == 0)
{
lean_object* v_size_3271_; lean_object* v_size_3272_; lean_object* v_k_3273_; lean_object* v_v_3274_; lean_object* v_l_3275_; lean_object* v_r_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; 
v_size_3271_ = lean_ctor_get(v_r_3263_, 0);
v_size_3272_ = lean_ctor_get(v_impl_3269_, 0);
lean_inc(v_size_3272_);
v_k_3273_ = lean_ctor_get(v_impl_3269_, 1);
lean_inc(v_k_3273_);
v_v_3274_ = lean_ctor_get(v_impl_3269_, 2);
lean_inc(v_v_3274_);
v_l_3275_ = lean_ctor_get(v_impl_3269_, 3);
lean_inc(v_l_3275_);
v_r_3276_ = lean_ctor_get(v_impl_3269_, 4);
lean_inc(v_r_3276_);
v___x_3277_ = lean_unsigned_to_nat(3u);
v___x_3278_ = lean_nat_mul(v___x_3277_, v_size_3271_);
v___x_3279_ = lean_nat_dec_lt(v___x_3278_, v_size_3272_);
lean_dec(v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
lean_dec(v_r_3276_);
lean_dec(v_l_3275_);
lean_dec(v_v_3274_);
lean_dec(v_k_3273_);
v___x_3280_ = lean_nat_add(v___x_3270_, v_size_3272_);
lean_dec(v_size_3272_);
v___x_3281_ = lean_nat_add(v___x_3280_, v_size_3271_);
lean_dec(v___x_3280_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 3, v_impl_3269_);
lean_ctor_set(v___x_3265_, 0, v___x_3281_);
v___x_3283_ = v___x_3265_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_k_3260_);
lean_ctor_set(v_reuseFailAlloc_3284_, 2, v_v_3261_);
lean_ctor_set(v_reuseFailAlloc_3284_, 3, v_impl_3269_);
lean_ctor_set(v_reuseFailAlloc_3284_, 4, v_r_3263_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
else
{
lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3350_; 
v_isSharedCheck_3350_ = !lean_is_exclusive(v_impl_3269_);
if (v_isSharedCheck_3350_ == 0)
{
lean_object* v_unused_3351_; lean_object* v_unused_3352_; lean_object* v_unused_3353_; lean_object* v_unused_3354_; lean_object* v_unused_3355_; 
v_unused_3351_ = lean_ctor_get(v_impl_3269_, 4);
lean_dec(v_unused_3351_);
v_unused_3352_ = lean_ctor_get(v_impl_3269_, 3);
lean_dec(v_unused_3352_);
v_unused_3353_ = lean_ctor_get(v_impl_3269_, 2);
lean_dec(v_unused_3353_);
v_unused_3354_ = lean_ctor_get(v_impl_3269_, 1);
lean_dec(v_unused_3354_);
v_unused_3355_ = lean_ctor_get(v_impl_3269_, 0);
lean_dec(v_unused_3355_);
v___x_3286_ = v_impl_3269_;
v_isShared_3287_ = v_isSharedCheck_3350_;
goto v_resetjp_3285_;
}
else
{
lean_dec(v_impl_3269_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3350_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v_size_3288_; lean_object* v_size_3289_; lean_object* v_k_3290_; lean_object* v_v_3291_; lean_object* v_l_3292_; lean_object* v_r_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v_size_3288_ = lean_ctor_get(v_l_3275_, 0);
v_size_3289_ = lean_ctor_get(v_r_3276_, 0);
v_k_3290_ = lean_ctor_get(v_r_3276_, 1);
v_v_3291_ = lean_ctor_get(v_r_3276_, 2);
v_l_3292_ = lean_ctor_get(v_r_3276_, 3);
v_r_3293_ = lean_ctor_get(v_r_3276_, 4);
v___x_3294_ = lean_unsigned_to_nat(2u);
v___x_3295_ = lean_nat_mul(v___x_3294_, v_size_3288_);
v___x_3296_ = lean_nat_dec_lt(v_size_3289_, v___x_3295_);
lean_dec(v___x_3295_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3325_; 
lean_inc(v_r_3293_);
lean_inc(v_l_3292_);
lean_inc(v_v_3291_);
lean_inc(v_k_3290_);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_r_3276_);
if (v_isSharedCheck_3325_ == 0)
{
lean_object* v_unused_3326_; lean_object* v_unused_3327_; lean_object* v_unused_3328_; lean_object* v_unused_3329_; lean_object* v_unused_3330_; 
v_unused_3326_ = lean_ctor_get(v_r_3276_, 4);
lean_dec(v_unused_3326_);
v_unused_3327_ = lean_ctor_get(v_r_3276_, 3);
lean_dec(v_unused_3327_);
v_unused_3328_ = lean_ctor_get(v_r_3276_, 2);
lean_dec(v_unused_3328_);
v_unused_3329_ = lean_ctor_get(v_r_3276_, 1);
lean_dec(v_unused_3329_);
v_unused_3330_ = lean_ctor_get(v_r_3276_, 0);
lean_dec(v_unused_3330_);
v___x_3298_ = v_r_3276_;
v_isShared_3299_ = v_isSharedCheck_3325_;
goto v_resetjp_3297_;
}
else
{
lean_dec(v_r_3276_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3325_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___x_3313_; lean_object* v___y_3315_; 
v___x_3300_ = lean_nat_add(v___x_3270_, v_size_3272_);
lean_dec(v_size_3272_);
v___x_3301_ = lean_nat_add(v___x_3300_, v_size_3271_);
lean_dec(v___x_3300_);
v___x_3313_ = lean_nat_add(v___x_3270_, v_size_3288_);
if (lean_obj_tag(v_l_3292_) == 0)
{
lean_object* v_size_3323_; 
v_size_3323_ = lean_ctor_get(v_l_3292_, 0);
lean_inc(v_size_3323_);
v___y_3315_ = v_size_3323_;
goto v___jp_3314_;
}
else
{
lean_object* v___x_3324_; 
v___x_3324_ = lean_unsigned_to_nat(0u);
v___y_3315_ = v___x_3324_;
goto v___jp_3314_;
}
v___jp_3302_:
{
lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3306_ = lean_nat_add(v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec(v___y_3304_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 4, v_r_3263_);
lean_ctor_set(v___x_3298_, 3, v_r_3293_);
lean_ctor_set(v___x_3298_, 2, v_v_3261_);
lean_ctor_set(v___x_3298_, 1, v_k_3260_);
lean_ctor_set(v___x_3298_, 0, v___x_3306_);
v___x_3308_ = v___x_3298_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3306_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v_k_3260_);
lean_ctor_set(v_reuseFailAlloc_3312_, 2, v_v_3261_);
lean_ctor_set(v_reuseFailAlloc_3312_, 3, v_r_3293_);
lean_ctor_set(v_reuseFailAlloc_3312_, 4, v_r_3263_);
v___x_3308_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3310_; 
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 4, v___x_3308_);
lean_ctor_set(v___x_3286_, 3, v___y_3303_);
lean_ctor_set(v___x_3286_, 2, v_v_3291_);
lean_ctor_set(v___x_3286_, 1, v_k_3290_);
lean_ctor_set(v___x_3286_, 0, v___x_3301_);
v___x_3310_ = v___x_3286_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3301_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v_k_3290_);
lean_ctor_set(v_reuseFailAlloc_3311_, 2, v_v_3291_);
lean_ctor_set(v_reuseFailAlloc_3311_, 3, v___y_3303_);
lean_ctor_set(v_reuseFailAlloc_3311_, 4, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
v___jp_3314_:
{
lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3316_ = lean_nat_add(v___x_3313_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec(v___x_3313_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 4, v_l_3292_);
lean_ctor_set(v___x_3265_, 3, v_l_3275_);
lean_ctor_set(v___x_3265_, 2, v_v_3274_);
lean_ctor_set(v___x_3265_, 1, v_k_3273_);
lean_ctor_set(v___x_3265_, 0, v___x_3316_);
v___x_3318_ = v___x_3265_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v_k_3273_);
lean_ctor_set(v_reuseFailAlloc_3322_, 2, v_v_3274_);
lean_ctor_set(v_reuseFailAlloc_3322_, 3, v_l_3275_);
lean_ctor_set(v_reuseFailAlloc_3322_, 4, v_l_3292_);
v___x_3318_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_nat_add(v___x_3270_, v_size_3271_);
if (lean_obj_tag(v_r_3293_) == 0)
{
lean_object* v_size_3320_; 
v_size_3320_ = lean_ctor_get(v_r_3293_, 0);
lean_inc(v_size_3320_);
v___y_3303_ = v___x_3318_;
v___y_3304_ = v___x_3319_;
v___y_3305_ = v_size_3320_;
goto v___jp_3302_;
}
else
{
lean_object* v___x_3321_; 
v___x_3321_ = lean_unsigned_to_nat(0u);
v___y_3303_ = v___x_3318_;
v___y_3304_ = v___x_3319_;
v___y_3305_ = v___x_3321_;
goto v___jp_3302_;
}
}
}
}
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; 
lean_del_object(v___x_3265_);
v___x_3331_ = lean_nat_add(v___x_3270_, v_size_3272_);
lean_dec(v_size_3272_);
v___x_3332_ = lean_nat_add(v___x_3331_, v_size_3271_);
lean_dec(v___x_3331_);
v___x_3333_ = lean_nat_add(v___x_3270_, v_size_3271_);
v___x_3334_ = lean_nat_add(v___x_3333_, v_size_3289_);
lean_dec(v___x_3333_);
lean_inc_ref(v_r_3263_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 4, v_r_3263_);
lean_ctor_set(v___x_3286_, 3, v_r_3276_);
lean_ctor_set(v___x_3286_, 2, v_v_3261_);
lean_ctor_set(v___x_3286_, 1, v_k_3260_);
lean_ctor_set(v___x_3286_, 0, v___x_3334_);
v___x_3336_ = v___x_3286_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_k_3260_);
lean_ctor_set(v_reuseFailAlloc_3349_, 2, v_v_3261_);
lean_ctor_set(v_reuseFailAlloc_3349_, 3, v_r_3276_);
lean_ctor_set(v_reuseFailAlloc_3349_, 4, v_r_3263_);
v___x_3336_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
v_isSharedCheck_3343_ = !lean_is_exclusive(v_r_3263_);
if (v_isSharedCheck_3343_ == 0)
{
lean_object* v_unused_3344_; lean_object* v_unused_3345_; lean_object* v_unused_3346_; lean_object* v_unused_3347_; lean_object* v_unused_3348_; 
v_unused_3344_ = lean_ctor_get(v_r_3263_, 4);
lean_dec(v_unused_3344_);
v_unused_3345_ = lean_ctor_get(v_r_3263_, 3);
lean_dec(v_unused_3345_);
v_unused_3346_ = lean_ctor_get(v_r_3263_, 2);
lean_dec(v_unused_3346_);
v_unused_3347_ = lean_ctor_get(v_r_3263_, 1);
lean_dec(v_unused_3347_);
v_unused_3348_ = lean_ctor_get(v_r_3263_, 0);
lean_dec(v_unused_3348_);
v___x_3338_ = v_r_3263_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_dec(v_r_3263_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 4, v___x_3336_);
lean_ctor_set(v___x_3338_, 3, v_l_3275_);
lean_ctor_set(v___x_3338_, 2, v_v_3274_);
lean_ctor_set(v___x_3338_, 1, v_k_3273_);
lean_ctor_set(v___x_3338_, 0, v___x_3332_);
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_k_3273_);
lean_ctor_set(v_reuseFailAlloc_3342_, 2, v_v_3274_);
lean_ctor_set(v_reuseFailAlloc_3342_, 3, v_l_3275_);
lean_ctor_set(v_reuseFailAlloc_3342_, 4, v___x_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3356_; 
v_l_3356_ = lean_ctor_get(v_impl_3269_, 3);
lean_inc(v_l_3356_);
if (lean_obj_tag(v_l_3356_) == 0)
{
lean_object* v_r_3357_; lean_object* v_k_3358_; lean_object* v_v_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3370_; 
v_r_3357_ = lean_ctor_get(v_impl_3269_, 4);
v_k_3358_ = lean_ctor_get(v_impl_3269_, 1);
v_v_3359_ = lean_ctor_get(v_impl_3269_, 2);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_impl_3269_);
if (v_isSharedCheck_3370_ == 0)
{
lean_object* v_unused_3371_; lean_object* v_unused_3372_; 
v_unused_3371_ = lean_ctor_get(v_impl_3269_, 3);
lean_dec(v_unused_3371_);
v_unused_3372_ = lean_ctor_get(v_impl_3269_, 0);
lean_dec(v_unused_3372_);
v___x_3361_ = v_impl_3269_;
v_isShared_3362_ = v_isSharedCheck_3370_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_r_3357_);
lean_inc(v_v_3359_);
lean_inc(v_k_3358_);
lean_dec(v_impl_3269_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3370_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3363_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3357_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 3, v_r_3357_);
lean_ctor_set(v___x_3361_, 2, v_v_3261_);
lean_ctor_set(v___x_3361_, 1, v_k_3260_);
lean_ctor_set(v___x_3361_, 0, v___x_3270_);
v___x_3365_ = v___x_3361_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_k_3260_);
lean_ctor_set(v_reuseFailAlloc_3369_, 2, v_v_3261_);
lean_ctor_set(v_reuseFailAlloc_3369_, 3, v_r_3357_);
lean_ctor_set(v_reuseFailAlloc_3369_, 4, v_r_3357_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3367_; 
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 4, v___x_3365_);
lean_ctor_set(v___x_3265_, 3, v_l_3356_);
lean_ctor_set(v___x_3265_, 2, v_v_3359_);
lean_ctor_set(v___x_3265_, 1, v_k_3358_);
lean_ctor_set(v___x_3265_, 0, v___x_3363_);
v___x_3367_ = v___x_3265_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_k_3358_);
lean_ctor_set(v_reuseFailAlloc_3368_, 2, v_v_3359_);
lean_ctor_set(v_reuseFailAlloc_3368_, 3, v_l_3356_);
lean_ctor_set(v_reuseFailAlloc_3368_, 4, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
else
{
lean_object* v_r_3373_; 
v_r_3373_ = lean_ctor_get(v_impl_3269_, 4);
lean_inc(v_r_3373_);
if (lean_obj_tag(v_r_3373_) == 0)
{
lean_object* v_k_3374_; lean_object* v_v_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3398_; 
v_k_3374_ = lean_ctor_get(v_impl_3269_, 1);
v_v_3375_ = lean_ctor_get(v_impl_3269_, 2);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_impl_3269_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; lean_object* v_unused_3400_; lean_object* v_unused_3401_; 
v_unused_3399_ = lean_ctor_get(v_impl_3269_, 4);
lean_dec(v_unused_3399_);
v_unused_3400_ = lean_ctor_get(v_impl_3269_, 3);
lean_dec(v_unused_3400_);
v_unused_3401_ = lean_ctor_get(v_impl_3269_, 0);
lean_dec(v_unused_3401_);
v___x_3377_ = v_impl_3269_;
v_isShared_3378_ = v_isSharedCheck_3398_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_v_3375_);
lean_inc(v_k_3374_);
lean_dec(v_impl_3269_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3398_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v_k_3379_; lean_object* v_v_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3394_; 
v_k_3379_ = lean_ctor_get(v_r_3373_, 1);
v_v_3380_ = lean_ctor_get(v_r_3373_, 2);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_r_3373_);
if (v_isSharedCheck_3394_ == 0)
{
lean_object* v_unused_3395_; lean_object* v_unused_3396_; lean_object* v_unused_3397_; 
v_unused_3395_ = lean_ctor_get(v_r_3373_, 4);
lean_dec(v_unused_3395_);
v_unused_3396_ = lean_ctor_get(v_r_3373_, 3);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v_r_3373_, 0);
lean_dec(v_unused_3397_);
v___x_3382_ = v_r_3373_;
v_isShared_3383_ = v_isSharedCheck_3394_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_v_3380_);
lean_inc(v_k_3379_);
lean_dec(v_r_3373_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3394_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; lean_object* v___x_3386_; 
v___x_3384_ = lean_unsigned_to_nat(3u);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 4, v_l_3356_);
lean_ctor_set(v___x_3382_, 3, v_l_3356_);
lean_ctor_set(v___x_3382_, 2, v_v_3375_);
lean_ctor_set(v___x_3382_, 1, v_k_3374_);
lean_ctor_set(v___x_3382_, 0, v___x_3270_);
v___x_3386_ = v___x_3382_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_k_3374_);
lean_ctor_set(v_reuseFailAlloc_3393_, 2, v_v_3375_);
lean_ctor_set(v_reuseFailAlloc_3393_, 3, v_l_3356_);
lean_ctor_set(v_reuseFailAlloc_3393_, 4, v_l_3356_);
v___x_3386_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
lean_object* v___x_3388_; 
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 4, v_l_3356_);
lean_ctor_set(v___x_3377_, 2, v_v_3261_);
lean_ctor_set(v___x_3377_, 1, v_k_3260_);
lean_ctor_set(v___x_3377_, 0, v___x_3270_);
v___x_3388_ = v___x_3377_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_k_3260_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_v_3261_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_l_3356_);
lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_l_3356_);
v___x_3388_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3390_; 
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 4, v___x_3388_);
lean_ctor_set(v___x_3265_, 3, v___x_3386_);
lean_ctor_set(v___x_3265_, 2, v_v_3380_);
lean_ctor_set(v___x_3265_, 1, v_k_3379_);
lean_ctor_set(v___x_3265_, 0, v___x_3384_);
v___x_3390_ = v___x_3265_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_k_3379_);
lean_ctor_set(v_reuseFailAlloc_3391_, 2, v_v_3380_);
lean_ctor_set(v_reuseFailAlloc_3391_, 3, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3391_, 4, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3404_; 
v___x_3402_ = lean_unsigned_to_nat(2u);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 4, v_r_3373_);
lean_ctor_set(v___x_3265_, 3, v_impl_3269_);
lean_ctor_set(v___x_3265_, 0, v___x_3402_);
v___x_3404_ = v___x_3265_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_k_3260_);
lean_ctor_set(v_reuseFailAlloc_3405_, 2, v_v_3261_);
lean_ctor_set(v_reuseFailAlloc_3405_, 3, v_impl_3269_);
lean_ctor_set(v_reuseFailAlloc_3405_, 4, v_r_3373_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3407_; 
lean_dec(v_v_3261_);
lean_dec(v_k_3260_);
lean_dec_ref(v_cmp_3255_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 2, v_v_3257_);
lean_ctor_set(v___x_3265_, 1, v_k_3256_);
v___x_3407_ = v___x_3265_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_size_3259_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_k_3256_);
lean_ctor_set(v_reuseFailAlloc_3408_, 2, v_v_3257_);
lean_ctor_set(v_reuseFailAlloc_3408_, 3, v_l_3262_);
lean_ctor_set(v_reuseFailAlloc_3408_, 4, v_r_3263_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
default: 
{
lean_object* v_impl_3409_; lean_object* v___x_3410_; 
lean_dec(v_size_3259_);
v_impl_3409_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3255_, v_k_3256_, v_v_3257_, v_r_3263_);
v___x_3410_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3262_) == 0)
{
lean_object* v_size_3411_; lean_object* v_size_3412_; lean_object* v_k_3413_; lean_object* v_v_3414_; lean_object* v_l_3415_; lean_object* v_r_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v_size_3411_ = lean_ctor_get(v_l_3262_, 0);
v_size_3412_ = lean_ctor_get(v_impl_3409_, 0);
lean_inc(v_size_3412_);
v_k_3413_ = lean_ctor_get(v_impl_3409_, 1);
lean_inc(v_k_3413_);
v_v_3414_ = lean_ctor_get(v_impl_3409_, 2);
lean_inc(v_v_3414_);
v_l_3415_ = lean_ctor_get(v_impl_3409_, 3);
lean_inc(v_l_3415_);
v_r_3416_ = lean_ctor_get(v_impl_3409_, 4);
lean_inc(v_r_3416_);
v___x_3417_ = lean_unsigned_to_nat(3u);
v___x_3418_ = lean_nat_mul(v___x_3417_, v_size_3411_);
v___x_3419_ = lean_nat_dec_lt(v___x_3418_, v_size_3412_);
lean_dec(v___x_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3423_; 
lean_dec(v_r_3416_);
lean_dec(v_l_3415_);
lean_dec(v_v_3414_);
lean_dec(v_k_3413_);
v___x_3420_ = lean_nat_add(v___x_3410_, v_size_3411_);
v___x_3421_ = lean_nat_add(v___x_3420_, v_size_3412_);
lean_dec(v_size_3412_);
lean_dec(v___x_3420_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 4, v_impl_3409_);
lean_ctor_set(v___x_3265_, 0, v___x_3421_);
v___x_3423_ = v___x_3265_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3421_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_k_3260_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_v_3261_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v_l_3262_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v_impl_3409_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
else
{
lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3488_; 
v_isSharedCheck_3488_ = !lean_is_exclusive(v_impl_3409_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; lean_object* v_unused_3490_; lean_object* v_unused_3491_; lean_object* v_unused_3492_; lean_object* v_unused_3493_; 
v_unused_3489_ = lean_ctor_get(v_impl_3409_, 4);
lean_dec(v_unused_3489_);
v_unused_3490_ = lean_ctor_get(v_impl_3409_, 3);
lean_dec(v_unused_3490_);
v_unused_3491_ = lean_ctor_get(v_impl_3409_, 2);
lean_dec(v_unused_3491_);
v_unused_3492_ = lean_ctor_get(v_impl_3409_, 1);
lean_dec(v_unused_3492_);
v_unused_3493_ = lean_ctor_get(v_impl_3409_, 0);
lean_dec(v_unused_3493_);
v___x_3426_ = v_impl_3409_;
v_isShared_3427_ = v_isSharedCheck_3488_;
goto v_resetjp_3425_;
}
else
{
lean_dec(v_impl_3409_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3488_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_size_3428_; lean_object* v_k_3429_; lean_object* v_v_3430_; lean_object* v_l_3431_; lean_object* v_r_3432_; lean_object* v_size_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v_size_3428_ = lean_ctor_get(v_l_3415_, 0);
v_k_3429_ = lean_ctor_get(v_l_3415_, 1);
v_v_3430_ = lean_ctor_get(v_l_3415_, 2);
v_l_3431_ = lean_ctor_get(v_l_3415_, 3);
v_r_3432_ = lean_ctor_get(v_l_3415_, 4);
v_size_3433_ = lean_ctor_get(v_r_3416_, 0);
v___x_3434_ = lean_unsigned_to_nat(2u);
v___x_3435_ = lean_nat_mul(v___x_3434_, v_size_3433_);
v___x_3436_ = lean_nat_dec_lt(v_size_3428_, v___x_3435_);
lean_dec(v___x_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3464_; 
lean_inc(v_r_3432_);
lean_inc(v_l_3431_);
lean_inc(v_v_3430_);
lean_inc(v_k_3429_);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_l_3415_);
if (v_isSharedCheck_3464_ == 0)
{
lean_object* v_unused_3465_; lean_object* v_unused_3466_; lean_object* v_unused_3467_; lean_object* v_unused_3468_; lean_object* v_unused_3469_; 
v_unused_3465_ = lean_ctor_get(v_l_3415_, 4);
lean_dec(v_unused_3465_);
v_unused_3466_ = lean_ctor_get(v_l_3415_, 3);
lean_dec(v_unused_3466_);
v_unused_3467_ = lean_ctor_get(v_l_3415_, 2);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v_l_3415_, 1);
lean_dec(v_unused_3468_);
v_unused_3469_ = lean_ctor_get(v_l_3415_, 0);
lean_dec(v_unused_3469_);
v___x_3438_ = v_l_3415_;
v_isShared_3439_ = v_isSharedCheck_3464_;
goto v_resetjp_3437_;
}
else
{
lean_dec(v_l_3415_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3464_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3454_; 
v___x_3440_ = lean_nat_add(v___x_3410_, v_size_3411_);
v___x_3441_ = lean_nat_add(v___x_3440_, v_size_3412_);
lean_dec(v_size_3412_);
if (lean_obj_tag(v_l_3431_) == 0)
{
lean_object* v_size_3462_; 
v_size_3462_ = lean_ctor_get(v_l_3431_, 0);
lean_inc(v_size_3462_);
v___y_3454_ = v_size_3462_;
goto v___jp_3453_;
}
else
{
lean_object* v___x_3463_; 
v___x_3463_ = lean_unsigned_to_nat(0u);
v___y_3454_ = v___x_3463_;
goto v___jp_3453_;
}
v___jp_3442_:
{
lean_object* v___x_3446_; lean_object* v___x_3448_; 
v___x_3446_ = lean_nat_add(v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec(v___y_3444_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 4, v_r_3416_);
lean_ctor_set(v___x_3438_, 3, v_r_3432_);
lean_ctor_set(v___x_3438_, 2, v_v_3414_);
lean_ctor_set(v___x_3438_, 1, v_k_3413_);
lean_ctor_set(v___x_3438_, 0, v___x_3446_);
v___x_3448_ = v___x_3438_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3446_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_k_3413_);
lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_v_3414_);
lean_ctor_set(v_reuseFailAlloc_3452_, 3, v_r_3432_);
lean_ctor_set(v_reuseFailAlloc_3452_, 4, v_r_3416_);
v___x_3448_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3450_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 4, v___x_3448_);
lean_ctor_set(v___x_3426_, 3, v___y_3443_);
lean_ctor_set(v___x_3426_, 2, v_v_3430_);
lean_ctor_set(v___x_3426_, 1, v_k_3429_);
lean_ctor_set(v___x_3426_, 0, v___x_3441_);
v___x_3450_ = v___x_3426_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3451_, 3, v___y_3443_);
lean_ctor_set(v_reuseFailAlloc_3451_, 4, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
v___jp_3453_:
{
lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3455_ = lean_nat_add(v___x_3440_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec(v___x_3440_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 4, v_l_3431_);
lean_ctor_set(v___x_3265_, 0, v___x_3455_);
v___x_3457_ = v___x_3265_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_k_3260_);
lean_ctor_set(v_reuseFailAlloc_3461_, 2, v_v_3261_);
lean_ctor_set(v_reuseFailAlloc_3461_, 3, v_l_3262_);
lean_ctor_set(v_reuseFailAlloc_3461_, 4, v_l_3431_);
v___x_3457_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_nat_add(v___x_3410_, v_size_3433_);
if (lean_obj_tag(v_r_3432_) == 0)
{
lean_object* v_size_3459_; 
v_size_3459_ = lean_ctor_get(v_r_3432_, 0);
lean_inc(v_size_3459_);
v___y_3443_ = v___x_3457_;
v___y_3444_ = v___x_3458_;
v___y_3445_ = v_size_3459_;
goto v___jp_3442_;
}
else
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_unsigned_to_nat(0u);
v___y_3443_ = v___x_3457_;
v___y_3444_ = v___x_3458_;
v___y_3445_ = v___x_3460_;
goto v___jp_3442_;
}
}
}
}
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3474_; 
lean_del_object(v___x_3265_);
v___x_3470_ = lean_nat_add(v___x_3410_, v_size_3411_);
v___x_3471_ = lean_nat_add(v___x_3470_, v_size_3412_);
lean_dec(v_size_3412_);
v___x_3472_ = lean_nat_add(v___x_3470_, v_size_3428_);
lean_dec(v___x_3470_);
lean_inc_ref(v_l_3262_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 4, v_l_3415_);
lean_ctor_set(v___x_3426_, 3, v_l_3262_);
lean_ctor_set(v___x_3426_, 2, v_v_3261_);
lean_ctor_set(v___x_3426_, 1, v_k_3260_);
lean_ctor_set(v___x_3426_, 0, v___x_3472_);
v___x_3474_ = v___x_3426_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3472_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_k_3260_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v_v_3261_);
lean_ctor_set(v_reuseFailAlloc_3487_, 3, v_l_3262_);
lean_ctor_set(v_reuseFailAlloc_3487_, 4, v_l_3415_);
v___x_3474_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
v_isSharedCheck_3481_ = !lean_is_exclusive(v_l_3262_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; lean_object* v_unused_3483_; lean_object* v_unused_3484_; lean_object* v_unused_3485_; lean_object* v_unused_3486_; 
v_unused_3482_ = lean_ctor_get(v_l_3262_, 4);
lean_dec(v_unused_3482_);
v_unused_3483_ = lean_ctor_get(v_l_3262_, 3);
lean_dec(v_unused_3483_);
v_unused_3484_ = lean_ctor_get(v_l_3262_, 2);
lean_dec(v_unused_3484_);
v_unused_3485_ = lean_ctor_get(v_l_3262_, 1);
lean_dec(v_unused_3485_);
v_unused_3486_ = lean_ctor_get(v_l_3262_, 0);
lean_dec(v_unused_3486_);
v___x_3476_ = v_l_3262_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_dec(v_l_3262_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v_r_3416_);
lean_ctor_set(v___x_3476_, 3, v___x_3474_);
lean_ctor_set(v___x_3476_, 2, v_v_3414_);
lean_ctor_set(v___x_3476_, 1, v_k_3413_);
lean_ctor_set(v___x_3476_, 0, v___x_3471_);
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_k_3413_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_v_3414_);
lean_ctor_set(v_reuseFailAlloc_3480_, 3, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3480_, 4, v_r_3416_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3494_; 
v_l_3494_ = lean_ctor_get(v_impl_3409_, 3);
lean_inc(v_l_3494_);
if (lean_obj_tag(v_l_3494_) == 0)
{
lean_object* v_r_3495_; lean_object* v_k_3496_; lean_object* v_v_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3520_; 
v_r_3495_ = lean_ctor_get(v_impl_3409_, 4);
v_k_3496_ = lean_ctor_get(v_impl_3409_, 1);
v_v_3497_ = lean_ctor_get(v_impl_3409_, 2);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_impl_3409_);
if (v_isSharedCheck_3520_ == 0)
{
lean_object* v_unused_3521_; lean_object* v_unused_3522_; 
v_unused_3521_ = lean_ctor_get(v_impl_3409_, 3);
lean_dec(v_unused_3521_);
v_unused_3522_ = lean_ctor_get(v_impl_3409_, 0);
lean_dec(v_unused_3522_);
v___x_3499_ = v_impl_3409_;
v_isShared_3500_ = v_isSharedCheck_3520_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_r_3495_);
lean_inc(v_v_3497_);
lean_inc(v_k_3496_);
lean_dec(v_impl_3409_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3520_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v_k_3501_; lean_object* v_v_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3516_; 
v_k_3501_ = lean_ctor_get(v_l_3494_, 1);
v_v_3502_ = lean_ctor_get(v_l_3494_, 2);
v_isSharedCheck_3516_ = !lean_is_exclusive(v_l_3494_);
if (v_isSharedCheck_3516_ == 0)
{
lean_object* v_unused_3517_; lean_object* v_unused_3518_; lean_object* v_unused_3519_; 
v_unused_3517_ = lean_ctor_get(v_l_3494_, 4);
lean_dec(v_unused_3517_);
v_unused_3518_ = lean_ctor_get(v_l_3494_, 3);
lean_dec(v_unused_3518_);
v_unused_3519_ = lean_ctor_get(v_l_3494_, 0);
lean_dec(v_unused_3519_);
v___x_3504_ = v_l_3494_;
v_isShared_3505_ = v_isSharedCheck_3516_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_v_3502_);
lean_inc(v_k_3501_);
lean_dec(v_l_3494_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3516_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3506_; lean_object* v___x_3508_; 
v___x_3506_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3495_, 2);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 4, v_r_3495_);
lean_ctor_set(v___x_3504_, 3, v_r_3495_);
lean_ctor_set(v___x_3504_, 2, v_v_3261_);
lean_ctor_set(v___x_3504_, 1, v_k_3260_);
lean_ctor_set(v___x_3504_, 0, v___x_3410_);
v___x_3508_ = v___x_3504_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3410_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_k_3260_);
lean_ctor_set(v_reuseFailAlloc_3515_, 2, v_v_3261_);
lean_ctor_set(v_reuseFailAlloc_3515_, 3, v_r_3495_);
lean_ctor_set(v_reuseFailAlloc_3515_, 4, v_r_3495_);
v___x_3508_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
lean_object* v___x_3510_; 
lean_inc(v_r_3495_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 3, v_r_3495_);
lean_ctor_set(v___x_3499_, 0, v___x_3410_);
v___x_3510_ = v___x_3499_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3410_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_k_3496_);
lean_ctor_set(v_reuseFailAlloc_3514_, 2, v_v_3497_);
lean_ctor_set(v_reuseFailAlloc_3514_, 3, v_r_3495_);
lean_ctor_set(v_reuseFailAlloc_3514_, 4, v_r_3495_);
v___x_3510_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3512_; 
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 4, v___x_3510_);
lean_ctor_set(v___x_3265_, 3, v___x_3508_);
lean_ctor_set(v___x_3265_, 2, v_v_3502_);
lean_ctor_set(v___x_3265_, 1, v_k_3501_);
lean_ctor_set(v___x_3265_, 0, v___x_3506_);
v___x_3512_ = v___x_3265_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3506_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_k_3501_);
lean_ctor_set(v_reuseFailAlloc_3513_, 2, v_v_3502_);
lean_ctor_set(v_reuseFailAlloc_3513_, 3, v___x_3508_);
lean_ctor_set(v_reuseFailAlloc_3513_, 4, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
}
}
else
{
lean_object* v_r_3523_; 
v_r_3523_ = lean_ctor_get(v_impl_3409_, 4);
lean_inc(v_r_3523_);
if (lean_obj_tag(v_r_3523_) == 0)
{
lean_object* v_k_3524_; lean_object* v_v_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3536_; 
v_k_3524_ = lean_ctor_get(v_impl_3409_, 1);
v_v_3525_ = lean_ctor_get(v_impl_3409_, 2);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_impl_3409_);
if (v_isSharedCheck_3536_ == 0)
{
lean_object* v_unused_3537_; lean_object* v_unused_3538_; lean_object* v_unused_3539_; 
v_unused_3537_ = lean_ctor_get(v_impl_3409_, 4);
lean_dec(v_unused_3537_);
v_unused_3538_ = lean_ctor_get(v_impl_3409_, 3);
lean_dec(v_unused_3538_);
v_unused_3539_ = lean_ctor_get(v_impl_3409_, 0);
lean_dec(v_unused_3539_);
v___x_3527_ = v_impl_3409_;
v_isShared_3528_ = v_isSharedCheck_3536_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_v_3525_);
lean_inc(v_k_3524_);
lean_dec(v_impl_3409_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3536_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3529_ = lean_unsigned_to_nat(3u);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 4, v_l_3494_);
lean_ctor_set(v___x_3527_, 2, v_v_3261_);
lean_ctor_set(v___x_3527_, 1, v_k_3260_);
lean_ctor_set(v___x_3527_, 0, v___x_3410_);
v___x_3531_ = v___x_3527_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3410_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_k_3260_);
lean_ctor_set(v_reuseFailAlloc_3535_, 2, v_v_3261_);
lean_ctor_set(v_reuseFailAlloc_3535_, 3, v_l_3494_);
lean_ctor_set(v_reuseFailAlloc_3535_, 4, v_l_3494_);
v___x_3531_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3533_; 
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 4, v_r_3523_);
lean_ctor_set(v___x_3265_, 3, v___x_3531_);
lean_ctor_set(v___x_3265_, 2, v_v_3525_);
lean_ctor_set(v___x_3265_, 1, v_k_3524_);
lean_ctor_set(v___x_3265_, 0, v___x_3529_);
v___x_3533_ = v___x_3265_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3529_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_k_3524_);
lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_v_3525_);
lean_ctor_set(v_reuseFailAlloc_3534_, 3, v___x_3531_);
lean_ctor_set(v_reuseFailAlloc_3534_, 4, v_r_3523_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3542_; 
v___x_3540_ = lean_unsigned_to_nat(2u);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 4, v_impl_3409_);
lean_ctor_set(v___x_3265_, 3, v_r_3523_);
lean_ctor_set(v___x_3265_, 0, v___x_3540_);
v___x_3542_ = v___x_3265_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3540_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_k_3260_);
lean_ctor_set(v_reuseFailAlloc_3543_, 2, v_v_3261_);
lean_ctor_set(v_reuseFailAlloc_3543_, 3, v_r_3523_);
lean_ctor_set(v_reuseFailAlloc_3543_, 4, v_impl_3409_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
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
lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec_ref(v_cmp_3255_);
v___x_3545_ = lean_unsigned_to_nat(1u);
v___x_3546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
lean_ctor_set(v___x_3546_, 1, v_k_3256_);
lean_ctor_set(v___x_3546_, 2, v_v_3257_);
lean_ctor_set(v___x_3546_, 3, v_t_3258_);
lean_ctor_set(v___x_3546_, 4, v_t_3258_);
return v___x_3546_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(lean_object* v_cmp_3547_, lean_object* v_init_3548_, lean_object* v_x_3549_){
_start:
{
if (lean_obj_tag(v_x_3549_) == 0)
{
lean_object* v_k_3550_; lean_object* v_v_3551_; lean_object* v_l_3552_; lean_object* v_r_3553_; lean_object* v___x_3554_; lean_object* v_a_3555_; lean_object* v_r_3556_; 
v_k_3550_ = lean_ctor_get(v_x_3549_, 1);
lean_inc(v_k_3550_);
v_v_3551_ = lean_ctor_get(v_x_3549_, 2);
lean_inc(v_v_3551_);
v_l_3552_ = lean_ctor_get(v_x_3549_, 3);
lean_inc(v_l_3552_);
v_r_3553_ = lean_ctor_get(v_x_3549_, 4);
lean_inc(v_r_3553_);
lean_dec_ref(v_x_3549_);
lean_inc_ref_n(v_cmp_3547_, 2);
v___x_3554_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3547_, v_init_3548_, v_l_3552_);
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref(v___x_3554_);
v_r_3556_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3547_, v_k_3550_, v_v_3551_, v_a_3555_);
v_init_3548_ = v_r_3556_;
v_x_3549_ = v_r_3553_;
goto _start;
}
else
{
lean_object* v___x_3558_; 
lean_dec_ref(v_cmp_3547_);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v_init_3548_);
return v___x_3558_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(lean_object* v_cmp_3559_, lean_object* v_k_3560_, lean_object* v_t_3561_){
_start:
{
if (lean_obj_tag(v_t_3561_) == 0)
{
lean_object* v_k_3562_; lean_object* v_l_3563_; lean_object* v_r_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; 
v_k_3562_ = lean_ctor_get(v_t_3561_, 1);
lean_inc(v_k_3562_);
v_l_3563_ = lean_ctor_get(v_t_3561_, 3);
lean_inc(v_l_3563_);
v_r_3564_ = lean_ctor_get(v_t_3561_, 4);
lean_inc(v_r_3564_);
lean_dec_ref(v_t_3561_);
lean_inc_ref(v_cmp_3559_);
lean_inc(v_k_3560_);
v___x_3565_ = lean_apply_2(v_cmp_3559_, v_k_3560_, v_k_3562_);
v___x_3566_ = lean_unbox(v___x_3565_);
switch(v___x_3566_)
{
case 0:
{
lean_dec(v_r_3564_);
v_t_3561_ = v_l_3563_;
goto _start;
}
case 1:
{
uint8_t v___x_3568_; 
lean_dec(v_r_3564_);
lean_dec(v_l_3563_);
lean_dec(v_k_3560_);
lean_dec_ref(v_cmp_3559_);
v___x_3568_ = 1;
return v___x_3568_;
}
default: 
{
lean_dec(v_l_3563_);
v_t_3561_ = v_r_3564_;
goto _start;
}
}
}
else
{
uint8_t v___x_3570_; 
lean_dec(v_k_3560_);
lean_dec_ref(v_cmp_3559_);
v___x_3570_ = 0;
return v___x_3570_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_3571_, lean_object* v_k_3572_, lean_object* v_t_3573_){
_start:
{
uint8_t v_res_3574_; lean_object* v_r_3575_; 
v_res_3574_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3571_, v_k_3572_, v_t_3573_);
v_r_3575_ = lean_box(v_res_3574_);
return v_r_3575_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(lean_object* v_cmp_3576_, lean_object* v_init_3577_, lean_object* v_x_3578_){
_start:
{
if (lean_obj_tag(v_x_3578_) == 0)
{
lean_object* v_k_3579_; lean_object* v_v_3580_; lean_object* v_l_3581_; lean_object* v_r_3582_; lean_object* v___x_3583_; lean_object* v_a_3584_; uint8_t v___x_3585_; 
v_k_3579_ = lean_ctor_get(v_x_3578_, 1);
lean_inc_n(v_k_3579_, 2);
v_v_3580_ = lean_ctor_get(v_x_3578_, 2);
lean_inc(v_v_3580_);
v_l_3581_ = lean_ctor_get(v_x_3578_, 3);
lean_inc(v_l_3581_);
v_r_3582_ = lean_ctor_get(v_x_3578_, 4);
lean_inc(v_r_3582_);
lean_dec_ref(v_x_3578_);
lean_inc_ref_n(v_cmp_3576_, 2);
v___x_3583_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3576_, v_init_3577_, v_l_3581_);
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
lean_inc_n(v_a_3584_, 2);
lean_dec_ref(v___x_3583_);
v___x_3585_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3576_, v_k_3579_, v_a_3584_);
if (v___x_3585_ == 0)
{
lean_object* v___x_3586_; 
lean_inc_ref(v_cmp_3576_);
v___x_3586_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3576_, v_k_3579_, v_v_3580_, v_a_3584_);
v_init_3577_ = v___x_3586_;
v_x_3578_ = v_r_3582_;
goto _start;
}
else
{
lean_dec(v_v_3580_);
lean_dec(v_k_3579_);
v_init_3577_ = v_a_3584_;
v_x_3578_ = v_r_3582_;
goto _start;
}
}
else
{
lean_object* v___x_3589_; 
lean_dec_ref(v_cmp_3576_);
v___x_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3589_, 0, v_init_3577_);
return v___x_3589_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object* v_cmp_3590_, lean_object* v_t_u2081_3591_, lean_object* v_t_u2082_3592_){
_start:
{
lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3602_; 
if (lean_obj_tag(v_t_u2081_3591_) == 0)
{
lean_object* v_size_3605_; 
v_size_3605_ = lean_ctor_get(v_t_u2081_3591_, 0);
lean_inc(v_size_3605_);
v___y_3602_ = v_size_3605_;
goto v___jp_3601_;
}
else
{
lean_object* v___x_3606_; 
v___x_3606_ = lean_unsigned_to_nat(0u);
v___y_3602_ = v___x_3606_;
goto v___jp_3601_;
}
v___jp_3593_:
{
uint8_t v___x_3596_; 
v___x_3596_ = lean_nat_dec_le(v___y_3594_, v___y_3595_);
lean_dec(v___y_3595_);
lean_dec(v___y_3594_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; lean_object* v_a_3598_; 
v___x_3597_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3590_, v_t_u2081_3591_, v_t_u2082_3592_);
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref(v___x_3597_);
return v_a_3598_;
}
else
{
lean_object* v___x_3599_; lean_object* v_a_3600_; 
v___x_3599_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3590_, v_t_u2082_3592_, v_t_u2081_3591_);
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref(v___x_3599_);
return v_a_3600_;
}
}
v___jp_3601_:
{
if (lean_obj_tag(v_t_u2082_3592_) == 0)
{
lean_object* v_size_3603_; 
v_size_3603_ = lean_ctor_get(v_t_u2082_3592_, 0);
lean_inc(v_size_3603_);
v___y_3594_ = v___y_3602_;
v___y_3595_ = v_size_3603_;
goto v___jp_3593_;
}
else
{
lean_object* v___x_3604_; 
v___x_3604_ = lean_unsigned_to_nat(0u);
v___y_3594_ = v___y_3602_;
v___y_3595_ = v___x_3604_;
goto v___jp_3593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_union___redArg(lean_object* v_cmp_3607_, lean_object* v_t_u2081_3608_, lean_object* v_t_u2082_3609_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3607_, v_t_u2081_3608_, v_t_u2082_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_union(lean_object* v_00_u03b1_3611_, lean_object* v_00_u03b2_3612_, lean_object* v_cmp_3613_, lean_object* v_t_u2081_3614_, lean_object* v_t_u2082_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3613_, v_t_u2081_3614_, v_t_u2082_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0(lean_object* v_00_u03b1_3617_, lean_object* v_cmp_3618_, lean_object* v_00_u03b2_3619_, lean_object* v_t_u2081_3620_, lean_object* v_t_u2082_3621_, lean_object* v_h_u2081_3622_, lean_object* v_h_u2082_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3618_, v_t_u2081_3620_, v_t_u2082_3621_);
return v___x_3624_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0(lean_object* v_00_u03b1_3625_, lean_object* v_cmp_3626_, lean_object* v_00_u03b2_3627_, lean_object* v_k_3628_, lean_object* v_t_3629_){
_start:
{
uint8_t v___x_3630_; 
v___x_3630_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3626_, v_k_3628_, v_t_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3631_, lean_object* v_cmp_3632_, lean_object* v_00_u03b2_3633_, lean_object* v_k_3634_, lean_object* v_t_3635_){
_start:
{
uint8_t v_res_3636_; lean_object* v_r_3637_; 
v_res_3636_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0(v_00_u03b1_3631_, v_cmp_3632_, v_00_u03b2_3633_, v_k_3634_, v_t_3635_);
v_r_3637_ = lean_box(v_res_3636_);
return v_r_3637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1(lean_object* v_00_u03b1_3638_, lean_object* v_cmp_3639_, lean_object* v_00_u03b2_3640_, lean_object* v_k_3641_, lean_object* v_v_3642_, lean_object* v_t_3643_, lean_object* v_hl_3644_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3639_, v_k_3641_, v_v_3642_, v_t_3643_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2(lean_object* v_00_u03b1_3646_, lean_object* v_00_u03b2_3647_, lean_object* v_cmp_3648_, lean_object* v_init_3649_, lean_object* v_x_3650_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3648_, v_init_3649_, v_x_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3(lean_object* v_00_u03b1_3652_, lean_object* v_00_u03b2_3653_, lean_object* v_cmp_3654_, lean_object* v_init_3655_, lean_object* v_x_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3654_, v_init_3655_, v_x_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instUnion___redArg(lean_object* v_cmp_3658_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_alloc_closure((void*)(l_Std_DTreeMap_union), 5, 3);
lean_closure_set(v___x_3659_, 0, lean_box(0));
lean_closure_set(v___x_3659_, 1, lean_box(0));
lean_closure_set(v___x_3659_, 2, v_cmp_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instUnion(lean_object* v_00_u03b1_3660_, lean_object* v_00_u03b2_3661_, lean_object* v_cmp_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_alloc_closure((void*)(l_Std_DTreeMap_union), 5, 3);
lean_closure_set(v___x_3663_, 0, lean_box(0));
lean_closure_set(v___x_3663_, 1, lean_box(0));
lean_closure_set(v___x_3663_, 2, v_cmp_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(lean_object* v_cmp_3664_, lean_object* v_m_u2082_3665_, lean_object* v_t_3666_){
_start:
{
if (lean_obj_tag(v_t_3666_) == 0)
{
lean_object* v_k_3667_; lean_object* v_v_3668_; lean_object* v_l_3669_; lean_object* v_r_3670_; uint8_t v___x_3671_; 
v_k_3667_ = lean_ctor_get(v_t_3666_, 1);
lean_inc_n(v_k_3667_, 2);
v_v_3668_ = lean_ctor_get(v_t_3666_, 2);
lean_inc(v_v_3668_);
v_l_3669_ = lean_ctor_get(v_t_3666_, 3);
lean_inc(v_l_3669_);
v_r_3670_ = lean_ctor_get(v_t_3666_, 4);
lean_inc(v_r_3670_);
lean_dec_ref(v_t_3666_);
lean_inc(v_m_u2082_3665_);
lean_inc_ref(v_cmp_3664_);
v___x_3671_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3664_, v_k_3667_, v_m_u2082_3665_);
if (v___x_3671_ == 0)
{
lean_object* v_impl_3672_; lean_object* v_impl_3673_; lean_object* v___x_3674_; 
lean_dec(v_v_3668_);
lean_dec(v_k_3667_);
lean_inc(v_m_u2082_3665_);
lean_inc_ref(v_cmp_3664_);
v_impl_3672_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3664_, v_m_u2082_3665_, v_l_3669_);
v_impl_3673_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3664_, v_m_u2082_3665_, v_r_3670_);
v___x_3674_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_3672_, v_impl_3673_);
return v___x_3674_;
}
else
{
lean_object* v_impl_3675_; lean_object* v_impl_3676_; lean_object* v___x_3677_; 
lean_inc(v_m_u2082_3665_);
lean_inc_ref(v_cmp_3664_);
v_impl_3675_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3664_, v_m_u2082_3665_, v_l_3669_);
v_impl_3676_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3664_, v_m_u2082_3665_, v_r_3670_);
v___x_3677_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_3667_, v_v_3668_, v_impl_3675_, v_impl_3676_);
return v___x_3677_;
}
}
else
{
lean_dec(v_m_u2082_3665_);
lean_dec_ref(v_cmp_3664_);
return v_t_3666_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_3678_, lean_object* v_t_3679_, lean_object* v_k_3680_){
_start:
{
if (lean_obj_tag(v_t_3679_) == 0)
{
lean_object* v_k_3681_; lean_object* v_v_3682_; lean_object* v_l_3683_; lean_object* v_r_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; 
v_k_3681_ = lean_ctor_get(v_t_3679_, 1);
lean_inc_n(v_k_3681_, 2);
v_v_3682_ = lean_ctor_get(v_t_3679_, 2);
lean_inc(v_v_3682_);
v_l_3683_ = lean_ctor_get(v_t_3679_, 3);
lean_inc(v_l_3683_);
v_r_3684_ = lean_ctor_get(v_t_3679_, 4);
lean_inc(v_r_3684_);
lean_dec_ref(v_t_3679_);
lean_inc_ref(v_cmp_3678_);
lean_inc(v_k_3680_);
v___x_3685_ = lean_apply_2(v_cmp_3678_, v_k_3680_, v_k_3681_);
v___x_3686_ = lean_unbox(v___x_3685_);
switch(v___x_3686_)
{
case 0:
{
lean_dec(v_r_3684_);
lean_dec(v_v_3682_);
lean_dec(v_k_3681_);
v_t_3679_ = v_l_3683_;
goto _start;
}
case 1:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
lean_dec(v_r_3684_);
lean_dec(v_l_3683_);
lean_dec(v_k_3680_);
lean_dec_ref(v_cmp_3678_);
v___x_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3688_, 0, v_k_3681_);
lean_ctor_set(v___x_3688_, 1, v_v_3682_);
v___x_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
return v___x_3689_;
}
default: 
{
lean_dec(v_l_3683_);
lean_dec(v_v_3682_);
lean_dec(v_k_3681_);
v_t_3679_ = v_r_3684_;
goto _start;
}
}
}
else
{
lean_object* v___x_3691_; 
lean_dec(v_k_3680_);
lean_dec_ref(v_cmp_3678_);
v___x_3691_ = lean_box(0);
return v___x_3691_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_cmp_3692_, lean_object* v_m_u2081_3693_, lean_object* v_init_3694_, lean_object* v_x_3695_){
_start:
{
if (lean_obj_tag(v_x_3695_) == 0)
{
lean_object* v_k_3696_; lean_object* v_l_3697_; lean_object* v_r_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v_k_3696_ = lean_ctor_get(v_x_3695_, 1);
lean_inc(v_k_3696_);
v_l_3697_ = lean_ctor_get(v_x_3695_, 3);
lean_inc(v_l_3697_);
v_r_3698_ = lean_ctor_get(v_x_3695_, 4);
lean_inc(v_r_3698_);
lean_dec_ref(v_x_3695_);
lean_inc_n(v_m_u2081_3693_, 2);
lean_inc_ref_n(v_cmp_3692_, 2);
v___x_3699_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3692_, v_m_u2081_3693_, v_init_3694_, v_l_3697_);
v___x_3700_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3692_, v_m_u2081_3693_, v_k_3696_);
if (lean_obj_tag(v___x_3700_) == 0)
{
v_init_3694_ = v___x_3699_;
v_x_3695_ = v_r_3698_;
goto _start;
}
else
{
lean_object* v_val_3702_; lean_object* v_fst_3703_; lean_object* v_snd_3704_; lean_object* v_impl_3705_; 
v_val_3702_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_val_3702_);
lean_dec_ref(v___x_3700_);
v_fst_3703_ = lean_ctor_get(v_val_3702_, 0);
lean_inc(v_fst_3703_);
v_snd_3704_ = lean_ctor_get(v_val_3702_, 1);
lean_inc(v_snd_3704_);
lean_dec(v_val_3702_);
lean_inc_ref(v_cmp_3692_);
v_impl_3705_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3692_, v_fst_3703_, v_snd_3704_, v___x_3699_);
v_init_3694_ = v_impl_3705_;
v_x_3695_ = v_r_3698_;
goto _start;
}
}
else
{
lean_dec(v_m_u2081_3693_);
lean_dec_ref(v_cmp_3692_);
return v_init_3694_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(lean_object* v_cmp_3707_, lean_object* v_m_u2081_3708_, lean_object* v_m_u2082_3709_){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = lean_box(1);
v___x_3711_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3707_, v_m_u2081_3708_, v___x_3710_, v_m_u2082_3709_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(lean_object* v_cmp_3712_, lean_object* v_m_u2081_3713_, lean_object* v_m_u2082_3714_){
_start:
{
lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3722_; 
if (lean_obj_tag(v_m_u2081_3713_) == 0)
{
lean_object* v_size_3725_; 
v_size_3725_ = lean_ctor_get(v_m_u2081_3713_, 0);
lean_inc(v_size_3725_);
v___y_3722_ = v_size_3725_;
goto v___jp_3721_;
}
else
{
lean_object* v___x_3726_; 
v___x_3726_ = lean_unsigned_to_nat(0u);
v___y_3722_ = v___x_3726_;
goto v___jp_3721_;
}
v___jp_3715_:
{
uint8_t v___x_3718_; 
v___x_3718_ = lean_nat_dec_le(v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec(v___y_3716_);
if (v___x_3718_ == 0)
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(v_cmp_3712_, v_m_u2081_3713_, v_m_u2082_3714_);
return v___x_3719_;
}
else
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3712_, v_m_u2082_3714_, v_m_u2081_3713_);
return v___x_3720_;
}
}
v___jp_3721_:
{
if (lean_obj_tag(v_m_u2082_3714_) == 0)
{
lean_object* v_size_3723_; 
v_size_3723_ = lean_ctor_get(v_m_u2082_3714_, 0);
lean_inc(v_size_3723_);
v___y_3716_ = v___y_3722_;
v___y_3717_ = v_size_3723_;
goto v___jp_3715_;
}
else
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_unsigned_to_nat(0u);
v___y_3716_ = v___y_3722_;
v___y_3717_ = v___x_3724_;
goto v___jp_3715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_inter___redArg(lean_object* v_cmp_3727_, lean_object* v_t_u2081_3728_, lean_object* v_t_u2082_3729_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3727_, v_t_u2081_3728_, v_t_u2082_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_inter(lean_object* v_00_u03b1_3731_, lean_object* v_00_u03b2_3732_, lean_object* v_cmp_3733_, lean_object* v_t_u2081_3734_, lean_object* v_t_u2082_3735_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3733_, v_t_u2081_3734_, v_t_u2082_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0(lean_object* v_00_u03b1_3737_, lean_object* v_cmp_3738_, lean_object* v_00_u03b2_3739_, lean_object* v_m_u2081_3740_, lean_object* v_m_u2082_3741_, lean_object* v_h_u2081_3742_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3738_, v_m_u2081_3740_, v_m_u2082_3741_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0(lean_object* v_00_u03b1_3744_, lean_object* v_cmp_3745_, lean_object* v_00_u03b2_3746_, lean_object* v_m_u2081_3747_, lean_object* v_m_u2082_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(v_cmp_3745_, v_m_u2081_3747_, v_m_u2082_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1(lean_object* v_00_u03b1_3750_, lean_object* v_00_u03b2_3751_, lean_object* v_cmp_3752_, lean_object* v_m_u2082_3753_, lean_object* v_t_3754_, lean_object* v_hl_3755_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3752_, v_m_u2082_3753_, v_t_3754_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3757_, lean_object* v_cmp_3758_, lean_object* v_00_u03b2_3759_, lean_object* v_t_3760_, lean_object* v_k_3761_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3758_, v_t_3760_, v_k_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2___redArg(lean_object* v_cmp_3763_, lean_object* v_m_u2081_3764_, lean_object* v_init_3765_, lean_object* v_t_3766_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3763_, v_m_u2081_3764_, v_init_3765_, v_t_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3768_, lean_object* v_00_u03b2_3769_, lean_object* v_cmp_3770_, lean_object* v_m_u2081_3771_, lean_object* v_init_3772_, lean_object* v_t_3773_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3770_, v_m_u2081_3771_, v_init_3772_, v_t_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_3775_, lean_object* v_00_u03b2_3776_, lean_object* v_cmp_3777_, lean_object* v_m_u2081_3778_, lean_object* v_init_3779_, lean_object* v_x_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3777_, v_m_u2081_3778_, v_init_3779_, v_x_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInter___redArg(lean_object* v_cmp_3782_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_alloc_closure((void*)(l_Std_DTreeMap_inter), 5, 3);
lean_closure_set(v___x_3783_, 0, lean_box(0));
lean_closure_set(v___x_3783_, 1, lean_box(0));
lean_closure_set(v___x_3783_, 2, v_cmp_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInter(lean_object* v_00_u03b1_3784_, lean_object* v_00_u03b2_3785_, lean_object* v_cmp_3786_){
_start:
{
lean_object* v___x_3787_; 
v___x_3787_ = lean_alloc_closure((void*)(l_Std_DTreeMap_inter), 5, 3);
lean_closure_set(v___x_3787_, 0, lean_box(0));
lean_closure_set(v___x_3787_, 1, lean_box(0));
lean_closure_set(v___x_3787_, 2, v_cmp_3786_);
return v___x_3787_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_beq___redArg(lean_object* v_cmp_3788_, lean_object* v_inst_3789_, lean_object* v_t_u2081_3790_, lean_object* v_t_u2082_3791_){
_start:
{
uint8_t v___x_3792_; 
v___x_3792_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3788_, v_inst_3789_, v_t_u2081_3790_, v_t_u2082_3791_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_beq___redArg___boxed(lean_object* v_cmp_3793_, lean_object* v_inst_3794_, lean_object* v_t_u2081_3795_, lean_object* v_t_u2082_3796_){
_start:
{
uint8_t v_res_3797_; lean_object* v_r_3798_; 
v_res_3797_ = l_Std_DTreeMap_beq___redArg(v_cmp_3793_, v_inst_3794_, v_t_u2081_3795_, v_t_u2082_3796_);
v_r_3798_ = lean_box(v_res_3797_);
return v_r_3798_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_beq(lean_object* v_00_u03b1_3799_, lean_object* v_00_u03b2_3800_, lean_object* v_cmp_3801_, lean_object* v_inst_3802_, lean_object* v_inst_3803_, lean_object* v_t_u2081_3804_, lean_object* v_t_u2082_3805_){
_start:
{
uint8_t v___x_3806_; 
v___x_3806_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3801_, v_inst_3803_, v_t_u2081_3804_, v_t_u2082_3805_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_beq___boxed(lean_object* v_00_u03b1_3807_, lean_object* v_00_u03b2_3808_, lean_object* v_cmp_3809_, lean_object* v_inst_3810_, lean_object* v_inst_3811_, lean_object* v_t_u2081_3812_, lean_object* v_t_u2082_3813_){
_start:
{
uint8_t v_res_3814_; lean_object* v_r_3815_; 
v_res_3814_ = l_Std_DTreeMap_beq(v_00_u03b1_3807_, v_00_u03b2_3808_, v_cmp_3809_, v_inst_3810_, v_inst_3811_, v_t_u2081_3812_, v_t_u2082_3813_);
v_r_3815_ = lean_box(v_res_3814_);
return v_r_3815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instBEqOfLawfulEqCmp___redArg(lean_object* v_cmp_3816_, lean_object* v_inst_3817_){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = lean_alloc_closure((void*)(l_Std_DTreeMap_beq___boxed), 7, 5);
lean_closure_set(v___x_3818_, 0, lean_box(0));
lean_closure_set(v___x_3818_, 1, lean_box(0));
lean_closure_set(v___x_3818_, 2, v_cmp_3816_);
lean_closure_set(v___x_3818_, 3, lean_box(0));
lean_closure_set(v___x_3818_, 4, v_inst_3817_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instBEqOfLawfulEqCmp(lean_object* v_00_u03b1_3819_, lean_object* v_00_u03b2_3820_, lean_object* v_cmp_3821_, lean_object* v_inst_3822_, lean_object* v_inst_3823_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_alloc_closure((void*)(l_Std_DTreeMap_beq___boxed), 7, 5);
lean_closure_set(v___x_3824_, 0, lean_box(0));
lean_closure_set(v___x_3824_, 1, lean_box(0));
lean_closure_set(v___x_3824_, 2, v_cmp_3821_);
lean_closure_set(v___x_3824_, 3, lean_box(0));
lean_closure_set(v___x_3824_, 4, v_inst_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___redArg(lean_object* v_cmp_3825_, lean_object* v_inst_3826_, lean_object* v_t_u2081_3827_, lean_object* v_t_u2082_3828_){
_start:
{
uint8_t v___x_3829_; 
v___x_3829_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3825_, v_inst_3826_, v_t_u2081_3827_, v_t_u2082_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___redArg___boxed(lean_object* v_cmp_3830_, lean_object* v_inst_3831_, lean_object* v_t_u2081_3832_, lean_object* v_t_u2082_3833_){
_start:
{
uint8_t v_res_3834_; lean_object* v_r_3835_; 
v_res_3834_ = l_Std_DTreeMap_Const_beq___redArg(v_cmp_3830_, v_inst_3831_, v_t_u2081_3832_, v_t_u2082_3833_);
v_r_3835_ = lean_box(v_res_3834_);
return v_r_3835_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq(lean_object* v_00_u03b1_3836_, lean_object* v_cmp_3837_, lean_object* v_00_u03b2_3838_, lean_object* v_inst_3839_, lean_object* v_t_u2081_3840_, lean_object* v_t_u2082_3841_){
_start:
{
uint8_t v___x_3842_; 
v___x_3842_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3837_, v_inst_3839_, v_t_u2081_3840_, v_t_u2082_3841_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___boxed(lean_object* v_00_u03b1_3843_, lean_object* v_cmp_3844_, lean_object* v_00_u03b2_3845_, lean_object* v_inst_3846_, lean_object* v_t_u2081_3847_, lean_object* v_t_u2082_3848_){
_start:
{
uint8_t v_res_3849_; lean_object* v_r_3850_; 
v_res_3849_ = l_Std_DTreeMap_Const_beq(v_00_u03b1_3843_, v_cmp_3844_, v_00_u03b2_3845_, v_inst_3846_, v_t_u2081_3847_, v_t_u2082_3848_);
v_r_3850_ = lean_box(v_res_3849_);
return v_r_3850_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(lean_object* v_cmp_3851_, lean_object* v_k_3852_, lean_object* v_t_3853_){
_start:
{
if (lean_obj_tag(v_t_3853_) == 0)
{
lean_object* v_k_3854_; lean_object* v_v_3855_; lean_object* v_l_3856_; lean_object* v_r_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_4512_; 
v_k_3854_ = lean_ctor_get(v_t_3853_, 1);
v_v_3855_ = lean_ctor_get(v_t_3853_, 2);
v_l_3856_ = lean_ctor_get(v_t_3853_, 3);
v_r_3857_ = lean_ctor_get(v_t_3853_, 4);
v_isSharedCheck_4512_ = !lean_is_exclusive(v_t_3853_);
if (v_isSharedCheck_4512_ == 0)
{
lean_object* v_unused_4513_; 
v_unused_4513_ = lean_ctor_get(v_t_3853_, 0);
lean_dec(v_unused_4513_);
v___x_3859_ = v_t_3853_;
v_isShared_3860_ = v_isSharedCheck_4512_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_r_3857_);
lean_inc(v_l_3856_);
lean_inc(v_v_3855_);
lean_inc(v_k_3854_);
lean_dec(v_t_3853_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_4512_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3861_; uint8_t v___x_3862_; 
lean_inc_ref(v_cmp_3851_);
lean_inc(v_k_3854_);
lean_inc(v_k_3852_);
v___x_3861_ = lean_apply_2(v_cmp_3851_, v_k_3852_, v_k_3854_);
v___x_3862_ = lean_unbox(v___x_3861_);
switch(v___x_3862_)
{
case 0:
{
lean_object* v_impl_3863_; lean_object* v___x_3864_; 
v_impl_3863_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_3851_, v_k_3852_, v_l_3856_);
v___x_3864_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3863_) == 0)
{
if (lean_obj_tag(v_r_3857_) == 0)
{
lean_object* v_size_3865_; lean_object* v_size_3866_; lean_object* v_k_3867_; lean_object* v_v_3868_; lean_object* v_l_3869_; lean_object* v_r_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; 
v_size_3865_ = lean_ctor_get(v_impl_3863_, 0);
lean_inc(v_size_3865_);
v_size_3866_ = lean_ctor_get(v_r_3857_, 0);
v_k_3867_ = lean_ctor_get(v_r_3857_, 1);
v_v_3868_ = lean_ctor_get(v_r_3857_, 2);
v_l_3869_ = lean_ctor_get(v_r_3857_, 3);
lean_inc(v_l_3869_);
v_r_3870_ = lean_ctor_get(v_r_3857_, 4);
v___x_3871_ = lean_unsigned_to_nat(3u);
v___x_3872_ = lean_nat_mul(v___x_3871_, v_size_3865_);
v___x_3873_ = lean_nat_dec_lt(v___x_3872_, v_size_3866_);
lean_dec(v___x_3872_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
lean_dec(v_l_3869_);
v___x_3874_ = lean_nat_add(v___x_3864_, v_size_3865_);
lean_dec(v_size_3865_);
v___x_3875_ = lean_nat_add(v___x_3874_, v_size_3866_);
lean_dec(v___x_3874_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 3, v_impl_3863_);
lean_ctor_set(v___x_3859_, 0, v___x_3875_);
v___x_3877_ = v___x_3859_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3875_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_3878_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_3878_, 3, v_impl_3863_);
lean_ctor_set(v_reuseFailAlloc_3878_, 4, v_r_3857_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
else
{
lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3942_; 
lean_inc(v_r_3870_);
lean_inc(v_v_3868_);
lean_inc(v_k_3867_);
lean_inc(v_size_3866_);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_r_3857_);
if (v_isSharedCheck_3942_ == 0)
{
lean_object* v_unused_3943_; lean_object* v_unused_3944_; lean_object* v_unused_3945_; lean_object* v_unused_3946_; lean_object* v_unused_3947_; 
v_unused_3943_ = lean_ctor_get(v_r_3857_, 4);
lean_dec(v_unused_3943_);
v_unused_3944_ = lean_ctor_get(v_r_3857_, 3);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v_r_3857_, 2);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v_r_3857_, 1);
lean_dec(v_unused_3946_);
v_unused_3947_ = lean_ctor_get(v_r_3857_, 0);
lean_dec(v_unused_3947_);
v___x_3880_ = v_r_3857_;
v_isShared_3881_ = v_isSharedCheck_3942_;
goto v_resetjp_3879_;
}
else
{
lean_dec(v_r_3857_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3942_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v_size_3882_; lean_object* v_k_3883_; lean_object* v_v_3884_; lean_object* v_l_3885_; lean_object* v_r_3886_; lean_object* v_size_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; uint8_t v___x_3890_; 
v_size_3882_ = lean_ctor_get(v_l_3869_, 0);
v_k_3883_ = lean_ctor_get(v_l_3869_, 1);
v_v_3884_ = lean_ctor_get(v_l_3869_, 2);
v_l_3885_ = lean_ctor_get(v_l_3869_, 3);
v_r_3886_ = lean_ctor_get(v_l_3869_, 4);
v_size_3887_ = lean_ctor_get(v_r_3870_, 0);
v___x_3888_ = lean_unsigned_to_nat(2u);
v___x_3889_ = lean_nat_mul(v___x_3888_, v_size_3887_);
v___x_3890_ = lean_nat_dec_lt(v_size_3882_, v___x_3889_);
lean_dec(v___x_3889_);
if (v___x_3890_ == 0)
{
lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3918_; 
lean_inc(v_r_3886_);
lean_inc(v_l_3885_);
lean_inc(v_v_3884_);
lean_inc(v_k_3883_);
v_isSharedCheck_3918_ = !lean_is_exclusive(v_l_3869_);
if (v_isSharedCheck_3918_ == 0)
{
lean_object* v_unused_3919_; lean_object* v_unused_3920_; lean_object* v_unused_3921_; lean_object* v_unused_3922_; lean_object* v_unused_3923_; 
v_unused_3919_ = lean_ctor_get(v_l_3869_, 4);
lean_dec(v_unused_3919_);
v_unused_3920_ = lean_ctor_get(v_l_3869_, 3);
lean_dec(v_unused_3920_);
v_unused_3921_ = lean_ctor_get(v_l_3869_, 2);
lean_dec(v_unused_3921_);
v_unused_3922_ = lean_ctor_get(v_l_3869_, 1);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_l_3869_, 0);
lean_dec(v_unused_3923_);
v___x_3892_ = v_l_3869_;
v_isShared_3893_ = v_isSharedCheck_3918_;
goto v_resetjp_3891_;
}
else
{
lean_dec(v_l_3869_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3918_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3908_; 
v___x_3894_ = lean_nat_add(v___x_3864_, v_size_3865_);
lean_dec(v_size_3865_);
v___x_3895_ = lean_nat_add(v___x_3894_, v_size_3866_);
lean_dec(v_size_3866_);
if (lean_obj_tag(v_l_3885_) == 0)
{
lean_object* v_size_3916_; 
v_size_3916_ = lean_ctor_get(v_l_3885_, 0);
lean_inc(v_size_3916_);
v___y_3908_ = v_size_3916_;
goto v___jp_3907_;
}
else
{
lean_object* v___x_3917_; 
v___x_3917_ = lean_unsigned_to_nat(0u);
v___y_3908_ = v___x_3917_;
goto v___jp_3907_;
}
v___jp_3896_:
{
lean_object* v___x_3900_; lean_object* v___x_3902_; 
v___x_3900_ = lean_nat_add(v___y_3898_, v___y_3899_);
lean_dec(v___y_3899_);
lean_dec(v___y_3898_);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 4, v_r_3870_);
lean_ctor_set(v___x_3892_, 3, v_r_3886_);
lean_ctor_set(v___x_3892_, 2, v_v_3868_);
lean_ctor_set(v___x_3892_, 1, v_k_3867_);
lean_ctor_set(v___x_3892_, 0, v___x_3900_);
v___x_3902_ = v___x_3892_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3900_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v_k_3867_);
lean_ctor_set(v_reuseFailAlloc_3906_, 2, v_v_3868_);
lean_ctor_set(v_reuseFailAlloc_3906_, 3, v_r_3886_);
lean_ctor_set(v_reuseFailAlloc_3906_, 4, v_r_3870_);
v___x_3902_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3904_; 
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 4, v___x_3902_);
lean_ctor_set(v___x_3880_, 3, v___y_3897_);
lean_ctor_set(v___x_3880_, 2, v_v_3884_);
lean_ctor_set(v___x_3880_, 1, v_k_3883_);
lean_ctor_set(v___x_3880_, 0, v___x_3895_);
v___x_3904_ = v___x_3880_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3895_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_k_3883_);
lean_ctor_set(v_reuseFailAlloc_3905_, 2, v_v_3884_);
lean_ctor_set(v_reuseFailAlloc_3905_, 3, v___y_3897_);
lean_ctor_set(v_reuseFailAlloc_3905_, 4, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
v___jp_3907_:
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3909_ = lean_nat_add(v___x_3894_, v___y_3908_);
lean_dec(v___y_3908_);
lean_dec(v___x_3894_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_l_3885_);
lean_ctor_set(v___x_3859_, 3, v_impl_3863_);
lean_ctor_set(v___x_3859_, 0, v___x_3909_);
v___x_3911_ = v___x_3859_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_3915_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_3915_, 3, v_impl_3863_);
lean_ctor_set(v_reuseFailAlloc_3915_, 4, v_l_3885_);
v___x_3911_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3912_; 
v___x_3912_ = lean_nat_add(v___x_3864_, v_size_3887_);
if (lean_obj_tag(v_r_3886_) == 0)
{
lean_object* v_size_3913_; 
v_size_3913_ = lean_ctor_get(v_r_3886_, 0);
lean_inc(v_size_3913_);
v___y_3897_ = v___x_3911_;
v___y_3898_ = v___x_3912_;
v___y_3899_ = v_size_3913_;
goto v___jp_3896_;
}
else
{
lean_object* v___x_3914_; 
v___x_3914_ = lean_unsigned_to_nat(0u);
v___y_3897_ = v___x_3911_;
v___y_3898_ = v___x_3912_;
v___y_3899_ = v___x_3914_;
goto v___jp_3896_;
}
}
}
}
}
else
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
lean_del_object(v___x_3859_);
v___x_3924_ = lean_nat_add(v___x_3864_, v_size_3865_);
lean_dec(v_size_3865_);
v___x_3925_ = lean_nat_add(v___x_3924_, v_size_3866_);
lean_dec(v_size_3866_);
v___x_3926_ = lean_nat_add(v___x_3924_, v_size_3882_);
lean_dec(v___x_3924_);
lean_inc_ref(v_impl_3863_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 4, v_l_3869_);
lean_ctor_set(v___x_3880_, 3, v_impl_3863_);
lean_ctor_set(v___x_3880_, 2, v_v_3855_);
lean_ctor_set(v___x_3880_, 1, v_k_3854_);
lean_ctor_set(v___x_3880_, 0, v___x_3926_);
v___x_3928_ = v___x_3880_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3941_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_3941_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_3941_, 3, v_impl_3863_);
lean_ctor_set(v_reuseFailAlloc_3941_, 4, v_l_3869_);
v___x_3928_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
v_isSharedCheck_3935_ = !lean_is_exclusive(v_impl_3863_);
if (v_isSharedCheck_3935_ == 0)
{
lean_object* v_unused_3936_; lean_object* v_unused_3937_; lean_object* v_unused_3938_; lean_object* v_unused_3939_; lean_object* v_unused_3940_; 
v_unused_3936_ = lean_ctor_get(v_impl_3863_, 4);
lean_dec(v_unused_3936_);
v_unused_3937_ = lean_ctor_get(v_impl_3863_, 3);
lean_dec(v_unused_3937_);
v_unused_3938_ = lean_ctor_get(v_impl_3863_, 2);
lean_dec(v_unused_3938_);
v_unused_3939_ = lean_ctor_get(v_impl_3863_, 1);
lean_dec(v_unused_3939_);
v_unused_3940_ = lean_ctor_get(v_impl_3863_, 0);
lean_dec(v_unused_3940_);
v___x_3930_ = v_impl_3863_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_dec(v_impl_3863_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 4, v_r_3870_);
lean_ctor_set(v___x_3930_, 3, v___x_3928_);
lean_ctor_set(v___x_3930_, 2, v_v_3868_);
lean_ctor_set(v___x_3930_, 1, v_k_3867_);
lean_ctor_set(v___x_3930_, 0, v___x_3925_);
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3925_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_k_3867_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v_v_3868_);
lean_ctor_set(v_reuseFailAlloc_3934_, 3, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_3934_, 4, v_r_3870_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3948_; lean_object* v___x_3949_; lean_object* v___x_3951_; 
v_size_3948_ = lean_ctor_get(v_impl_3863_, 0);
lean_inc(v_size_3948_);
v___x_3949_ = lean_nat_add(v___x_3864_, v_size_3948_);
lean_dec(v_size_3948_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 3, v_impl_3863_);
lean_ctor_set(v___x_3859_, 0, v___x_3949_);
v___x_3951_ = v___x_3859_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3949_);
lean_ctor_set(v_reuseFailAlloc_3952_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_3952_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_3952_, 3, v_impl_3863_);
lean_ctor_set(v_reuseFailAlloc_3952_, 4, v_r_3857_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
else
{
if (lean_obj_tag(v_r_3857_) == 0)
{
lean_object* v_l_3953_; 
v_l_3953_ = lean_ctor_get(v_r_3857_, 3);
lean_inc(v_l_3953_);
if (lean_obj_tag(v_l_3953_) == 0)
{
lean_object* v_r_3954_; 
v_r_3954_ = lean_ctor_get(v_r_3857_, 4);
lean_inc(v_r_3954_);
if (lean_obj_tag(v_r_3954_) == 0)
{
lean_object* v_size_3955_; lean_object* v_k_3956_; lean_object* v_v_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3970_; 
v_size_3955_ = lean_ctor_get(v_r_3857_, 0);
v_k_3956_ = lean_ctor_get(v_r_3857_, 1);
v_v_3957_ = lean_ctor_get(v_r_3857_, 2);
v_isSharedCheck_3970_ = !lean_is_exclusive(v_r_3857_);
if (v_isSharedCheck_3970_ == 0)
{
lean_object* v_unused_3971_; lean_object* v_unused_3972_; 
v_unused_3971_ = lean_ctor_get(v_r_3857_, 4);
lean_dec(v_unused_3971_);
v_unused_3972_ = lean_ctor_get(v_r_3857_, 3);
lean_dec(v_unused_3972_);
v___x_3959_ = v_r_3857_;
v_isShared_3960_ = v_isSharedCheck_3970_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_v_3957_);
lean_inc(v_k_3956_);
lean_inc(v_size_3955_);
lean_dec(v_r_3857_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3970_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v_size_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3965_; 
v_size_3961_ = lean_ctor_get(v_l_3953_, 0);
v___x_3962_ = lean_nat_add(v___x_3864_, v_size_3955_);
lean_dec(v_size_3955_);
v___x_3963_ = lean_nat_add(v___x_3864_, v_size_3961_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 4, v_l_3953_);
lean_ctor_set(v___x_3959_, 3, v_impl_3863_);
lean_ctor_set(v___x_3959_, 2, v_v_3855_);
lean_ctor_set(v___x_3959_, 1, v_k_3854_);
lean_ctor_set(v___x_3959_, 0, v___x_3963_);
v___x_3965_ = v___x_3959_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3963_);
lean_ctor_set(v_reuseFailAlloc_3969_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_3969_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_3969_, 3, v_impl_3863_);
lean_ctor_set(v_reuseFailAlloc_3969_, 4, v_l_3953_);
v___x_3965_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
lean_object* v___x_3967_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_r_3954_);
lean_ctor_set(v___x_3859_, 3, v___x_3965_);
lean_ctor_set(v___x_3859_, 2, v_v_3957_);
lean_ctor_set(v___x_3859_, 1, v_k_3956_);
lean_ctor_set(v___x_3859_, 0, v___x_3962_);
v___x_3967_ = v___x_3859_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3962_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_k_3956_);
lean_ctor_set(v_reuseFailAlloc_3968_, 2, v_v_3957_);
lean_ctor_set(v_reuseFailAlloc_3968_, 3, v___x_3965_);
lean_ctor_set(v_reuseFailAlloc_3968_, 4, v_r_3954_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
else
{
lean_object* v_k_3973_; lean_object* v_v_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3997_; 
v_k_3973_ = lean_ctor_get(v_r_3857_, 1);
v_v_3974_ = lean_ctor_get(v_r_3857_, 2);
v_isSharedCheck_3997_ = !lean_is_exclusive(v_r_3857_);
if (v_isSharedCheck_3997_ == 0)
{
lean_object* v_unused_3998_; lean_object* v_unused_3999_; lean_object* v_unused_4000_; 
v_unused_3998_ = lean_ctor_get(v_r_3857_, 4);
lean_dec(v_unused_3998_);
v_unused_3999_ = lean_ctor_get(v_r_3857_, 3);
lean_dec(v_unused_3999_);
v_unused_4000_ = lean_ctor_get(v_r_3857_, 0);
lean_dec(v_unused_4000_);
v___x_3976_ = v_r_3857_;
v_isShared_3977_ = v_isSharedCheck_3997_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_v_3974_);
lean_inc(v_k_3973_);
lean_dec(v_r_3857_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3997_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v_k_3978_; lean_object* v_v_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3993_; 
v_k_3978_ = lean_ctor_get(v_l_3953_, 1);
v_v_3979_ = lean_ctor_get(v_l_3953_, 2);
v_isSharedCheck_3993_ = !lean_is_exclusive(v_l_3953_);
if (v_isSharedCheck_3993_ == 0)
{
lean_object* v_unused_3994_; lean_object* v_unused_3995_; lean_object* v_unused_3996_; 
v_unused_3994_ = lean_ctor_get(v_l_3953_, 4);
lean_dec(v_unused_3994_);
v_unused_3995_ = lean_ctor_get(v_l_3953_, 3);
lean_dec(v_unused_3995_);
v_unused_3996_ = lean_ctor_get(v_l_3953_, 0);
lean_dec(v_unused_3996_);
v___x_3981_ = v_l_3953_;
v_isShared_3982_ = v_isSharedCheck_3993_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_v_3979_);
lean_inc(v_k_3978_);
lean_dec(v_l_3953_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3993_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3983_; lean_object* v___x_3985_; 
v___x_3983_ = lean_unsigned_to_nat(3u);
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 4, v_r_3954_);
lean_ctor_set(v___x_3981_, 3, v_r_3954_);
lean_ctor_set(v___x_3981_, 2, v_v_3855_);
lean_ctor_set(v___x_3981_, 1, v_k_3854_);
lean_ctor_set(v___x_3981_, 0, v___x_3864_);
v___x_3985_ = v___x_3981_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_3992_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_3992_, 3, v_r_3954_);
lean_ctor_set(v_reuseFailAlloc_3992_, 4, v_r_3954_);
v___x_3985_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3987_; 
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 3, v_r_3954_);
lean_ctor_set(v___x_3976_, 0, v___x_3864_);
v___x_3987_ = v___x_3976_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3991_, 1, v_k_3973_);
lean_ctor_set(v_reuseFailAlloc_3991_, 2, v_v_3974_);
lean_ctor_set(v_reuseFailAlloc_3991_, 3, v_r_3954_);
lean_ctor_set(v_reuseFailAlloc_3991_, 4, v_r_3954_);
v___x_3987_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3989_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_3987_);
lean_ctor_set(v___x_3859_, 3, v___x_3985_);
lean_ctor_set(v___x_3859_, 2, v_v_3979_);
lean_ctor_set(v___x_3859_, 1, v_k_3978_);
lean_ctor_set(v___x_3859_, 0, v___x_3983_);
v___x_3989_ = v___x_3859_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3983_);
lean_ctor_set(v_reuseFailAlloc_3990_, 1, v_k_3978_);
lean_ctor_set(v_reuseFailAlloc_3990_, 2, v_v_3979_);
lean_ctor_set(v_reuseFailAlloc_3990_, 3, v___x_3985_);
lean_ctor_set(v_reuseFailAlloc_3990_, 4, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_4001_; 
v_r_4001_ = lean_ctor_get(v_r_3857_, 4);
lean_inc(v_r_4001_);
if (lean_obj_tag(v_r_4001_) == 0)
{
lean_object* v_k_4002_; lean_object* v_v_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4014_; 
v_k_4002_ = lean_ctor_get(v_r_3857_, 1);
v_v_4003_ = lean_ctor_get(v_r_3857_, 2);
v_isSharedCheck_4014_ = !lean_is_exclusive(v_r_3857_);
if (v_isSharedCheck_4014_ == 0)
{
lean_object* v_unused_4015_; lean_object* v_unused_4016_; lean_object* v_unused_4017_; 
v_unused_4015_ = lean_ctor_get(v_r_3857_, 4);
lean_dec(v_unused_4015_);
v_unused_4016_ = lean_ctor_get(v_r_3857_, 3);
lean_dec(v_unused_4016_);
v_unused_4017_ = lean_ctor_get(v_r_3857_, 0);
lean_dec(v_unused_4017_);
v___x_4005_ = v_r_3857_;
v_isShared_4006_ = v_isSharedCheck_4014_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_v_4003_);
lean_inc(v_k_4002_);
lean_dec(v_r_3857_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4014_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4007_; lean_object* v___x_4009_; 
v___x_4007_ = lean_unsigned_to_nat(3u);
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 4, v_l_3953_);
lean_ctor_set(v___x_4005_, 2, v_v_3855_);
lean_ctor_set(v___x_4005_, 1, v_k_3854_);
lean_ctor_set(v___x_4005_, 0, v___x_3864_);
v___x_4009_ = v___x_4005_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_4013_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4013_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4013_, 3, v_l_3953_);
lean_ctor_set(v_reuseFailAlloc_4013_, 4, v_l_3953_);
v___x_4009_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4011_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_r_4001_);
lean_ctor_set(v___x_3859_, 3, v___x_4009_);
lean_ctor_set(v___x_3859_, 2, v_v_4003_);
lean_ctor_set(v___x_3859_, 1, v_k_4002_);
lean_ctor_set(v___x_3859_, 0, v___x_4007_);
v___x_4011_ = v___x_3859_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4007_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_k_4002_);
lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_v_4003_);
lean_ctor_set(v_reuseFailAlloc_4012_, 3, v___x_4009_);
lean_ctor_set(v_reuseFailAlloc_4012_, 4, v_r_4001_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
else
{
lean_object* v_size_4018_; lean_object* v_k_4019_; lean_object* v_v_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4031_; 
v_size_4018_ = lean_ctor_get(v_r_3857_, 0);
v_k_4019_ = lean_ctor_get(v_r_3857_, 1);
v_v_4020_ = lean_ctor_get(v_r_3857_, 2);
v_isSharedCheck_4031_ = !lean_is_exclusive(v_r_3857_);
if (v_isSharedCheck_4031_ == 0)
{
lean_object* v_unused_4032_; lean_object* v_unused_4033_; 
v_unused_4032_ = lean_ctor_get(v_r_3857_, 4);
lean_dec(v_unused_4032_);
v_unused_4033_ = lean_ctor_get(v_r_3857_, 3);
lean_dec(v_unused_4033_);
v___x_4022_ = v_r_3857_;
v_isShared_4023_ = v_isSharedCheck_4031_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_v_4020_);
lean_inc(v_k_4019_);
lean_inc(v_size_4018_);
lean_dec(v_r_3857_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4031_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 3, v_r_4001_);
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_size_4018_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v_k_4019_);
lean_ctor_set(v_reuseFailAlloc_4030_, 2, v_v_4020_);
lean_ctor_set(v_reuseFailAlloc_4030_, 3, v_r_4001_);
lean_ctor_set(v_reuseFailAlloc_4030_, 4, v_r_4001_);
v___x_4025_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
lean_object* v___x_4026_; lean_object* v___x_4028_; 
v___x_4026_ = lean_unsigned_to_nat(2u);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_4025_);
lean_ctor_set(v___x_3859_, 3, v_r_4001_);
lean_ctor_set(v___x_3859_, 0, v___x_4026_);
v___x_4028_ = v___x_3859_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4026_);
lean_ctor_set(v_reuseFailAlloc_4029_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4029_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4029_, 3, v_r_4001_);
lean_ctor_set(v_reuseFailAlloc_4029_, 4, v___x_4025_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
}
}
else
{
lean_object* v___x_4035_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 3, v_r_3857_);
lean_ctor_set(v___x_3859_, 0, v___x_3864_);
v___x_4035_ = v___x_3859_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4036_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4036_, 3, v_r_3857_);
lean_ctor_set(v_reuseFailAlloc_4036_, 4, v_r_3857_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3859_);
lean_dec(v_v_3855_);
lean_dec(v_k_3854_);
lean_dec(v_k_3852_);
lean_dec_ref(v_cmp_3851_);
if (lean_obj_tag(v_l_3856_) == 0)
{
if (lean_obj_tag(v_r_3857_) == 0)
{
lean_object* v_size_4037_; lean_object* v_k_4038_; lean_object* v_v_4039_; lean_object* v_l_4040_; lean_object* v_r_4041_; lean_object* v_size_4042_; lean_object* v_k_4043_; lean_object* v_v_4044_; lean_object* v_l_4045_; lean_object* v_r_4046_; lean_object* v___x_4047_; uint8_t v___x_4048_; 
v_size_4037_ = lean_ctor_get(v_l_3856_, 0);
v_k_4038_ = lean_ctor_get(v_l_3856_, 1);
v_v_4039_ = lean_ctor_get(v_l_3856_, 2);
v_l_4040_ = lean_ctor_get(v_l_3856_, 3);
v_r_4041_ = lean_ctor_get(v_l_3856_, 4);
lean_inc(v_r_4041_);
v_size_4042_ = lean_ctor_get(v_r_3857_, 0);
v_k_4043_ = lean_ctor_get(v_r_3857_, 1);
v_v_4044_ = lean_ctor_get(v_r_3857_, 2);
v_l_4045_ = lean_ctor_get(v_r_3857_, 3);
lean_inc(v_l_4045_);
v_r_4046_ = lean_ctor_get(v_r_3857_, 4);
v___x_4047_ = lean_unsigned_to_nat(1u);
v___x_4048_ = lean_nat_dec_lt(v_size_4037_, v_size_4042_);
if (v___x_4048_ == 0)
{
lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4184_; 
lean_inc(v_l_4040_);
lean_inc(v_v_4039_);
lean_inc(v_k_4038_);
v_isSharedCheck_4184_ = !lean_is_exclusive(v_l_3856_);
if (v_isSharedCheck_4184_ == 0)
{
lean_object* v_unused_4185_; lean_object* v_unused_4186_; lean_object* v_unused_4187_; lean_object* v_unused_4188_; lean_object* v_unused_4189_; 
v_unused_4185_ = lean_ctor_get(v_l_3856_, 4);
lean_dec(v_unused_4185_);
v_unused_4186_ = lean_ctor_get(v_l_3856_, 3);
lean_dec(v_unused_4186_);
v_unused_4187_ = lean_ctor_get(v_l_3856_, 2);
lean_dec(v_unused_4187_);
v_unused_4188_ = lean_ctor_get(v_l_3856_, 1);
lean_dec(v_unused_4188_);
v_unused_4189_ = lean_ctor_get(v_l_3856_, 0);
lean_dec(v_unused_4189_);
v___x_4050_ = v_l_3856_;
v_isShared_4051_ = v_isSharedCheck_4184_;
goto v_resetjp_4049_;
}
else
{
lean_dec(v_l_3856_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4184_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4052_; lean_object* v_tree_4053_; 
v___x_4052_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_4038_, v_v_4039_, v_l_4040_, v_r_4041_);
v_tree_4053_ = lean_ctor_get(v___x_4052_, 2);
lean_inc(v_tree_4053_);
if (lean_obj_tag(v_tree_4053_) == 0)
{
lean_object* v_k_4054_; lean_object* v_v_4055_; lean_object* v_size_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; uint8_t v___x_4059_; 
v_k_4054_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_k_4054_);
v_v_4055_ = lean_ctor_get(v___x_4052_, 1);
lean_inc(v_v_4055_);
lean_dec_ref(v___x_4052_);
v_size_4056_ = lean_ctor_get(v_tree_4053_, 0);
v___x_4057_ = lean_unsigned_to_nat(3u);
v___x_4058_ = lean_nat_mul(v___x_4057_, v_size_4056_);
v___x_4059_ = lean_nat_dec_lt(v___x_4058_, v_size_4042_);
lean_dec(v___x_4058_);
if (v___x_4059_ == 0)
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4063_; 
lean_dec(v_l_4045_);
v___x_4060_ = lean_nat_add(v___x_4047_, v_size_4056_);
v___x_4061_ = lean_nat_add(v___x_4060_, v_size_4042_);
lean_dec(v___x_4060_);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 4, v_r_3857_);
lean_ctor_set(v___x_4050_, 3, v_tree_4053_);
lean_ctor_set(v___x_4050_, 2, v_v_4055_);
lean_ctor_set(v___x_4050_, 1, v_k_4054_);
lean_ctor_set(v___x_4050_, 0, v___x_4061_);
v___x_4063_ = v___x_4050_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4061_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v_k_4054_);
lean_ctor_set(v_reuseFailAlloc_4064_, 2, v_v_4055_);
lean_ctor_set(v_reuseFailAlloc_4064_, 3, v_tree_4053_);
lean_ctor_set(v_reuseFailAlloc_4064_, 4, v_r_3857_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
else
{
lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4119_; 
lean_inc(v_r_4046_);
lean_inc(v_v_4044_);
lean_inc(v_k_4043_);
lean_inc(v_size_4042_);
v_isSharedCheck_4119_ = !lean_is_exclusive(v_r_3857_);
if (v_isSharedCheck_4119_ == 0)
{
lean_object* v_unused_4120_; lean_object* v_unused_4121_; lean_object* v_unused_4122_; lean_object* v_unused_4123_; lean_object* v_unused_4124_; 
v_unused_4120_ = lean_ctor_get(v_r_3857_, 4);
lean_dec(v_unused_4120_);
v_unused_4121_ = lean_ctor_get(v_r_3857_, 3);
lean_dec(v_unused_4121_);
v_unused_4122_ = lean_ctor_get(v_r_3857_, 2);
lean_dec(v_unused_4122_);
v_unused_4123_ = lean_ctor_get(v_r_3857_, 1);
lean_dec(v_unused_4123_);
v_unused_4124_ = lean_ctor_get(v_r_3857_, 0);
lean_dec(v_unused_4124_);
v___x_4066_ = v_r_3857_;
v_isShared_4067_ = v_isSharedCheck_4119_;
goto v_resetjp_4065_;
}
else
{
lean_dec(v_r_3857_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4119_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v_size_4068_; lean_object* v_k_4069_; lean_object* v_v_4070_; lean_object* v_l_4071_; lean_object* v_r_4072_; lean_object* v_size_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; uint8_t v___x_4076_; 
v_size_4068_ = lean_ctor_get(v_l_4045_, 0);
v_k_4069_ = lean_ctor_get(v_l_4045_, 1);
v_v_4070_ = lean_ctor_get(v_l_4045_, 2);
v_l_4071_ = lean_ctor_get(v_l_4045_, 3);
v_r_4072_ = lean_ctor_get(v_l_4045_, 4);
v_size_4073_ = lean_ctor_get(v_r_4046_, 0);
v___x_4074_ = lean_unsigned_to_nat(2u);
v___x_4075_ = lean_nat_mul(v___x_4074_, v_size_4073_);
v___x_4076_ = lean_nat_dec_lt(v_size_4068_, v___x_4075_);
lean_dec(v___x_4075_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4104_; 
lean_inc(v_r_4072_);
lean_inc(v_l_4071_);
lean_inc(v_v_4070_);
lean_inc(v_k_4069_);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_l_4045_);
if (v_isSharedCheck_4104_ == 0)
{
lean_object* v_unused_4105_; lean_object* v_unused_4106_; lean_object* v_unused_4107_; lean_object* v_unused_4108_; lean_object* v_unused_4109_; 
v_unused_4105_ = lean_ctor_get(v_l_4045_, 4);
lean_dec(v_unused_4105_);
v_unused_4106_ = lean_ctor_get(v_l_4045_, 3);
lean_dec(v_unused_4106_);
v_unused_4107_ = lean_ctor_get(v_l_4045_, 2);
lean_dec(v_unused_4107_);
v_unused_4108_ = lean_ctor_get(v_l_4045_, 1);
lean_dec(v_unused_4108_);
v_unused_4109_ = lean_ctor_get(v_l_4045_, 0);
lean_dec(v_unused_4109_);
v___x_4078_ = v_l_4045_;
v_isShared_4079_ = v_isSharedCheck_4104_;
goto v_resetjp_4077_;
}
else
{
lean_dec(v_l_4045_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4104_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4094_; 
v___x_4080_ = lean_nat_add(v___x_4047_, v_size_4056_);
v___x_4081_ = lean_nat_add(v___x_4080_, v_size_4042_);
lean_dec(v_size_4042_);
if (lean_obj_tag(v_l_4071_) == 0)
{
lean_object* v_size_4102_; 
v_size_4102_ = lean_ctor_get(v_l_4071_, 0);
lean_inc(v_size_4102_);
v___y_4094_ = v_size_4102_;
goto v___jp_4093_;
}
else
{
lean_object* v___x_4103_; 
v___x_4103_ = lean_unsigned_to_nat(0u);
v___y_4094_ = v___x_4103_;
goto v___jp_4093_;
}
v___jp_4082_:
{
lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4086_ = lean_nat_add(v___y_4083_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec(v___y_4083_);
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 4, v_r_4046_);
lean_ctor_set(v___x_4078_, 3, v_r_4072_);
lean_ctor_set(v___x_4078_, 2, v_v_4044_);
lean_ctor_set(v___x_4078_, 1, v_k_4043_);
lean_ctor_set(v___x_4078_, 0, v___x_4086_);
v___x_4088_ = v___x_4078_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4086_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v_k_4043_);
lean_ctor_set(v_reuseFailAlloc_4092_, 2, v_v_4044_);
lean_ctor_set(v_reuseFailAlloc_4092_, 3, v_r_4072_);
lean_ctor_set(v_reuseFailAlloc_4092_, 4, v_r_4046_);
v___x_4088_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4090_; 
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 4, v___x_4088_);
lean_ctor_set(v___x_4066_, 3, v___y_4084_);
lean_ctor_set(v___x_4066_, 2, v_v_4070_);
lean_ctor_set(v___x_4066_, 1, v_k_4069_);
lean_ctor_set(v___x_4066_, 0, v___x_4081_);
v___x_4090_ = v___x_4066_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4081_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_k_4069_);
lean_ctor_set(v_reuseFailAlloc_4091_, 2, v_v_4070_);
lean_ctor_set(v_reuseFailAlloc_4091_, 3, v___y_4084_);
lean_ctor_set(v_reuseFailAlloc_4091_, 4, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
v___jp_4093_:
{
lean_object* v___x_4095_; lean_object* v___x_4097_; 
v___x_4095_ = lean_nat_add(v___x_4080_, v___y_4094_);
lean_dec(v___y_4094_);
lean_dec(v___x_4080_);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 4, v_l_4071_);
lean_ctor_set(v___x_4050_, 3, v_tree_4053_);
lean_ctor_set(v___x_4050_, 2, v_v_4055_);
lean_ctor_set(v___x_4050_, 1, v_k_4054_);
lean_ctor_set(v___x_4050_, 0, v___x_4095_);
v___x_4097_ = v___x_4050_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v___x_4095_);
lean_ctor_set(v_reuseFailAlloc_4101_, 1, v_k_4054_);
lean_ctor_set(v_reuseFailAlloc_4101_, 2, v_v_4055_);
lean_ctor_set(v_reuseFailAlloc_4101_, 3, v_tree_4053_);
lean_ctor_set(v_reuseFailAlloc_4101_, 4, v_l_4071_);
v___x_4097_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
lean_object* v___x_4098_; 
v___x_4098_ = lean_nat_add(v___x_4047_, v_size_4073_);
if (lean_obj_tag(v_r_4072_) == 0)
{
lean_object* v_size_4099_; 
v_size_4099_ = lean_ctor_get(v_r_4072_, 0);
lean_inc(v_size_4099_);
v___y_4083_ = v___x_4098_;
v___y_4084_ = v___x_4097_;
v___y_4085_ = v_size_4099_;
goto v___jp_4082_;
}
else
{
lean_object* v___x_4100_; 
v___x_4100_ = lean_unsigned_to_nat(0u);
v___y_4083_ = v___x_4098_;
v___y_4084_ = v___x_4097_;
v___y_4085_ = v___x_4100_;
goto v___jp_4082_;
}
}
}
}
}
else
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
v___x_4110_ = lean_nat_add(v___x_4047_, v_size_4056_);
v___x_4111_ = lean_nat_add(v___x_4110_, v_size_4042_);
lean_dec(v_size_4042_);
v___x_4112_ = lean_nat_add(v___x_4110_, v_size_4068_);
lean_dec(v___x_4110_);
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 4, v_l_4045_);
lean_ctor_set(v___x_4066_, 3, v_tree_4053_);
lean_ctor_set(v___x_4066_, 2, v_v_4055_);
lean_ctor_set(v___x_4066_, 1, v_k_4054_);
lean_ctor_set(v___x_4066_, 0, v___x_4112_);
v___x_4114_ = v___x_4066_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4112_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_k_4054_);
lean_ctor_set(v_reuseFailAlloc_4118_, 2, v_v_4055_);
lean_ctor_set(v_reuseFailAlloc_4118_, 3, v_tree_4053_);
lean_ctor_set(v_reuseFailAlloc_4118_, 4, v_l_4045_);
v___x_4114_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4116_; 
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 4, v_r_4046_);
lean_ctor_set(v___x_4050_, 3, v___x_4114_);
lean_ctor_set(v___x_4050_, 2, v_v_4044_);
lean_ctor_set(v___x_4050_, 1, v_k_4043_);
lean_ctor_set(v___x_4050_, 0, v___x_4111_);
v___x_4116_ = v___x_4050_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4111_);
lean_ctor_set(v_reuseFailAlloc_4117_, 1, v_k_4043_);
lean_ctor_set(v_reuseFailAlloc_4117_, 2, v_v_4044_);
lean_ctor_set(v_reuseFailAlloc_4117_, 3, v___x_4114_);
lean_ctor_set(v_reuseFailAlloc_4117_, 4, v_r_4046_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
}
}
else
{
lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4178_; 
lean_inc(v_r_4046_);
lean_inc(v_v_4044_);
lean_inc(v_k_4043_);
lean_inc(v_size_4042_);
v_isSharedCheck_4178_ = !lean_is_exclusive(v_r_3857_);
if (v_isSharedCheck_4178_ == 0)
{
lean_object* v_unused_4179_; lean_object* v_unused_4180_; lean_object* v_unused_4181_; lean_object* v_unused_4182_; lean_object* v_unused_4183_; 
v_unused_4179_ = lean_ctor_get(v_r_3857_, 4);
lean_dec(v_unused_4179_);
v_unused_4180_ = lean_ctor_get(v_r_3857_, 3);
lean_dec(v_unused_4180_);
v_unused_4181_ = lean_ctor_get(v_r_3857_, 2);
lean_dec(v_unused_4181_);
v_unused_4182_ = lean_ctor_get(v_r_3857_, 1);
lean_dec(v_unused_4182_);
v_unused_4183_ = lean_ctor_get(v_r_3857_, 0);
lean_dec(v_unused_4183_);
v___x_4126_ = v_r_3857_;
v_isShared_4127_ = v_isSharedCheck_4178_;
goto v_resetjp_4125_;
}
else
{
lean_dec(v_r_3857_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4178_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
if (lean_obj_tag(v_l_4045_) == 0)
{
if (lean_obj_tag(v_r_4046_) == 0)
{
lean_object* v_k_4128_; lean_object* v_v_4129_; lean_object* v_size_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4134_; 
v_k_4128_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_k_4128_);
v_v_4129_ = lean_ctor_get(v___x_4052_, 1);
lean_inc(v_v_4129_);
lean_dec_ref(v___x_4052_);
v_size_4130_ = lean_ctor_get(v_l_4045_, 0);
v___x_4131_ = lean_nat_add(v___x_4047_, v_size_4042_);
lean_dec(v_size_4042_);
v___x_4132_ = lean_nat_add(v___x_4047_, v_size_4130_);
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 4, v_l_4045_);
lean_ctor_set(v___x_4126_, 3, v_tree_4053_);
lean_ctor_set(v___x_4126_, 2, v_v_4129_);
lean_ctor_set(v___x_4126_, 1, v_k_4128_);
lean_ctor_set(v___x_4126_, 0, v___x_4132_);
v___x_4134_ = v___x_4126_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4132_);
lean_ctor_set(v_reuseFailAlloc_4138_, 1, v_k_4128_);
lean_ctor_set(v_reuseFailAlloc_4138_, 2, v_v_4129_);
lean_ctor_set(v_reuseFailAlloc_4138_, 3, v_tree_4053_);
lean_ctor_set(v_reuseFailAlloc_4138_, 4, v_l_4045_);
v___x_4134_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
lean_object* v___x_4136_; 
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 4, v_r_4046_);
lean_ctor_set(v___x_4050_, 3, v___x_4134_);
lean_ctor_set(v___x_4050_, 2, v_v_4044_);
lean_ctor_set(v___x_4050_, 1, v_k_4043_);
lean_ctor_set(v___x_4050_, 0, v___x_4131_);
v___x_4136_ = v___x_4050_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4131_);
lean_ctor_set(v_reuseFailAlloc_4137_, 1, v_k_4043_);
lean_ctor_set(v_reuseFailAlloc_4137_, 2, v_v_4044_);
lean_ctor_set(v_reuseFailAlloc_4137_, 3, v___x_4134_);
lean_ctor_set(v_reuseFailAlloc_4137_, 4, v_r_4046_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
else
{
lean_object* v_k_4139_; lean_object* v_v_4140_; lean_object* v_k_4141_; lean_object* v_v_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4156_; 
lean_dec(v_size_4042_);
v_k_4139_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_k_4139_);
v_v_4140_ = lean_ctor_get(v___x_4052_, 1);
lean_inc(v_v_4140_);
lean_dec_ref(v___x_4052_);
v_k_4141_ = lean_ctor_get(v_l_4045_, 1);
v_v_4142_ = lean_ctor_get(v_l_4045_, 2);
v_isSharedCheck_4156_ = !lean_is_exclusive(v_l_4045_);
if (v_isSharedCheck_4156_ == 0)
{
lean_object* v_unused_4157_; lean_object* v_unused_4158_; lean_object* v_unused_4159_; 
v_unused_4157_ = lean_ctor_get(v_l_4045_, 4);
lean_dec(v_unused_4157_);
v_unused_4158_ = lean_ctor_get(v_l_4045_, 3);
lean_dec(v_unused_4158_);
v_unused_4159_ = lean_ctor_get(v_l_4045_, 0);
lean_dec(v_unused_4159_);
v___x_4144_ = v_l_4045_;
v_isShared_4145_ = v_isSharedCheck_4156_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_v_4142_);
lean_inc(v_k_4141_);
lean_dec(v_l_4045_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4156_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4146_; lean_object* v___x_4148_; 
v___x_4146_ = lean_unsigned_to_nat(3u);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 4, v_r_4046_);
lean_ctor_set(v___x_4144_, 3, v_r_4046_);
lean_ctor_set(v___x_4144_, 2, v_v_4140_);
lean_ctor_set(v___x_4144_, 1, v_k_4139_);
lean_ctor_set(v___x_4144_, 0, v___x_4047_);
v___x_4148_ = v___x_4144_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4155_, 1, v_k_4139_);
lean_ctor_set(v_reuseFailAlloc_4155_, 2, v_v_4140_);
lean_ctor_set(v_reuseFailAlloc_4155_, 3, v_r_4046_);
lean_ctor_set(v_reuseFailAlloc_4155_, 4, v_r_4046_);
v___x_4148_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
lean_object* v___x_4150_; 
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 3, v_r_4046_);
lean_ctor_set(v___x_4126_, 0, v___x_4047_);
v___x_4150_ = v___x_4126_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4154_, 1, v_k_4043_);
lean_ctor_set(v_reuseFailAlloc_4154_, 2, v_v_4044_);
lean_ctor_set(v_reuseFailAlloc_4154_, 3, v_r_4046_);
lean_ctor_set(v_reuseFailAlloc_4154_, 4, v_r_4046_);
v___x_4150_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
lean_object* v___x_4152_; 
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 4, v___x_4150_);
lean_ctor_set(v___x_4050_, 3, v___x_4148_);
lean_ctor_set(v___x_4050_, 2, v_v_4142_);
lean_ctor_set(v___x_4050_, 1, v_k_4141_);
lean_ctor_set(v___x_4050_, 0, v___x_4146_);
v___x_4152_ = v___x_4050_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4146_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_k_4141_);
lean_ctor_set(v_reuseFailAlloc_4153_, 2, v_v_4142_);
lean_ctor_set(v_reuseFailAlloc_4153_, 3, v___x_4148_);
lean_ctor_set(v_reuseFailAlloc_4153_, 4, v___x_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4046_) == 0)
{
lean_object* v_k_4160_; lean_object* v_v_4161_; lean_object* v___x_4162_; lean_object* v___x_4164_; 
lean_dec(v_size_4042_);
v_k_4160_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_k_4160_);
v_v_4161_ = lean_ctor_get(v___x_4052_, 1);
lean_inc(v_v_4161_);
lean_dec_ref(v___x_4052_);
v___x_4162_ = lean_unsigned_to_nat(3u);
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 4, v_l_4045_);
lean_ctor_set(v___x_4126_, 2, v_v_4161_);
lean_ctor_set(v___x_4126_, 1, v_k_4160_);
lean_ctor_set(v___x_4126_, 0, v___x_4047_);
v___x_4164_ = v___x_4126_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4168_, 1, v_k_4160_);
lean_ctor_set(v_reuseFailAlloc_4168_, 2, v_v_4161_);
lean_ctor_set(v_reuseFailAlloc_4168_, 3, v_l_4045_);
lean_ctor_set(v_reuseFailAlloc_4168_, 4, v_l_4045_);
v___x_4164_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
lean_object* v___x_4166_; 
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 4, v_r_4046_);
lean_ctor_set(v___x_4050_, 3, v___x_4164_);
lean_ctor_set(v___x_4050_, 2, v_v_4044_);
lean_ctor_set(v___x_4050_, 1, v_k_4043_);
lean_ctor_set(v___x_4050_, 0, v___x_4162_);
v___x_4166_ = v___x_4050_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4162_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v_k_4043_);
lean_ctor_set(v_reuseFailAlloc_4167_, 2, v_v_4044_);
lean_ctor_set(v_reuseFailAlloc_4167_, 3, v___x_4164_);
lean_ctor_set(v_reuseFailAlloc_4167_, 4, v_r_4046_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
else
{
lean_object* v_k_4169_; lean_object* v_v_4170_; lean_object* v___x_4172_; 
v_k_4169_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_k_4169_);
v_v_4170_ = lean_ctor_get(v___x_4052_, 1);
lean_inc(v_v_4170_);
lean_dec_ref(v___x_4052_);
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 3, v_r_4046_);
v___x_4172_ = v___x_4126_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_size_4042_);
lean_ctor_set(v_reuseFailAlloc_4177_, 1, v_k_4043_);
lean_ctor_set(v_reuseFailAlloc_4177_, 2, v_v_4044_);
lean_ctor_set(v_reuseFailAlloc_4177_, 3, v_r_4046_);
lean_ctor_set(v_reuseFailAlloc_4177_, 4, v_r_4046_);
v___x_4172_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4173_; lean_object* v___x_4175_; 
v___x_4173_ = lean_unsigned_to_nat(2u);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 4, v___x_4172_);
lean_ctor_set(v___x_4050_, 3, v_r_4046_);
lean_ctor_set(v___x_4050_, 2, v_v_4170_);
lean_ctor_set(v___x_4050_, 1, v_k_4169_);
lean_ctor_set(v___x_4050_, 0, v___x_4173_);
v___x_4175_ = v___x_4050_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
lean_ctor_set(v_reuseFailAlloc_4176_, 1, v_k_4169_);
lean_ctor_set(v_reuseFailAlloc_4176_, 2, v_v_4170_);
lean_ctor_set(v_reuseFailAlloc_4176_, 3, v_r_4046_);
lean_ctor_set(v_reuseFailAlloc_4176_, 4, v___x_4172_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
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
lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4342_; 
lean_inc(v_r_4046_);
lean_inc(v_v_4044_);
lean_inc(v_k_4043_);
v_isSharedCheck_4342_ = !lean_is_exclusive(v_r_3857_);
if (v_isSharedCheck_4342_ == 0)
{
lean_object* v_unused_4343_; lean_object* v_unused_4344_; lean_object* v_unused_4345_; lean_object* v_unused_4346_; lean_object* v_unused_4347_; 
v_unused_4343_ = lean_ctor_get(v_r_3857_, 4);
lean_dec(v_unused_4343_);
v_unused_4344_ = lean_ctor_get(v_r_3857_, 3);
lean_dec(v_unused_4344_);
v_unused_4345_ = lean_ctor_get(v_r_3857_, 2);
lean_dec(v_unused_4345_);
v_unused_4346_ = lean_ctor_get(v_r_3857_, 1);
lean_dec(v_unused_4346_);
v_unused_4347_ = lean_ctor_get(v_r_3857_, 0);
lean_dec(v_unused_4347_);
v___x_4191_ = v_r_3857_;
v_isShared_4192_ = v_isSharedCheck_4342_;
goto v_resetjp_4190_;
}
else
{
lean_dec(v_r_3857_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4342_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4193_; lean_object* v_tree_4194_; 
v___x_4193_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_4043_, v_v_4044_, v_l_4045_, v_r_4046_);
v_tree_4194_ = lean_ctor_get(v___x_4193_, 2);
lean_inc(v_tree_4194_);
if (lean_obj_tag(v_tree_4194_) == 0)
{
lean_object* v_k_4195_; lean_object* v_v_4196_; lean_object* v_size_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; 
v_k_4195_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_k_4195_);
v_v_4196_ = lean_ctor_get(v___x_4193_, 1);
lean_inc(v_v_4196_);
lean_dec_ref(v___x_4193_);
v_size_4197_ = lean_ctor_get(v_tree_4194_, 0);
v___x_4198_ = lean_unsigned_to_nat(3u);
v___x_4199_ = lean_nat_mul(v___x_4198_, v_size_4197_);
v___x_4200_ = lean_nat_dec_lt(v___x_4199_, v_size_4037_);
lean_dec(v___x_4199_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4204_; 
lean_dec(v_r_4041_);
v___x_4201_ = lean_nat_add(v___x_4047_, v_size_4037_);
v___x_4202_ = lean_nat_add(v___x_4201_, v_size_4197_);
lean_dec(v___x_4201_);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 4, v_tree_4194_);
lean_ctor_set(v___x_4191_, 3, v_l_3856_);
lean_ctor_set(v___x_4191_, 2, v_v_4196_);
lean_ctor_set(v___x_4191_, 1, v_k_4195_);
lean_ctor_set(v___x_4191_, 0, v___x_4202_);
v___x_4204_ = v___x_4191_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v___x_4202_);
lean_ctor_set(v_reuseFailAlloc_4205_, 1, v_k_4195_);
lean_ctor_set(v_reuseFailAlloc_4205_, 2, v_v_4196_);
lean_ctor_set(v_reuseFailAlloc_4205_, 3, v_l_3856_);
lean_ctor_set(v_reuseFailAlloc_4205_, 4, v_tree_4194_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
else
{
lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4271_; 
lean_inc(v_l_4040_);
lean_inc(v_v_4039_);
lean_inc(v_k_4038_);
lean_inc(v_size_4037_);
v_isSharedCheck_4271_ = !lean_is_exclusive(v_l_3856_);
if (v_isSharedCheck_4271_ == 0)
{
lean_object* v_unused_4272_; lean_object* v_unused_4273_; lean_object* v_unused_4274_; lean_object* v_unused_4275_; lean_object* v_unused_4276_; 
v_unused_4272_ = lean_ctor_get(v_l_3856_, 4);
lean_dec(v_unused_4272_);
v_unused_4273_ = lean_ctor_get(v_l_3856_, 3);
lean_dec(v_unused_4273_);
v_unused_4274_ = lean_ctor_get(v_l_3856_, 2);
lean_dec(v_unused_4274_);
v_unused_4275_ = lean_ctor_get(v_l_3856_, 1);
lean_dec(v_unused_4275_);
v_unused_4276_ = lean_ctor_get(v_l_3856_, 0);
lean_dec(v_unused_4276_);
v___x_4207_ = v_l_3856_;
v_isShared_4208_ = v_isSharedCheck_4271_;
goto v_resetjp_4206_;
}
else
{
lean_dec(v_l_3856_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4271_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v_size_4209_; lean_object* v_size_4210_; lean_object* v_k_4211_; lean_object* v_v_4212_; lean_object* v_l_4213_; lean_object* v_r_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; uint8_t v___x_4217_; 
v_size_4209_ = lean_ctor_get(v_l_4040_, 0);
v_size_4210_ = lean_ctor_get(v_r_4041_, 0);
v_k_4211_ = lean_ctor_get(v_r_4041_, 1);
v_v_4212_ = lean_ctor_get(v_r_4041_, 2);
v_l_4213_ = lean_ctor_get(v_r_4041_, 3);
v_r_4214_ = lean_ctor_get(v_r_4041_, 4);
v___x_4215_ = lean_unsigned_to_nat(2u);
v___x_4216_ = lean_nat_mul(v___x_4215_, v_size_4209_);
v___x_4217_ = lean_nat_dec_lt(v_size_4210_, v___x_4216_);
lean_dec(v___x_4216_);
if (v___x_4217_ == 0)
{
lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4255_; 
lean_inc(v_r_4214_);
lean_inc(v_l_4213_);
lean_inc(v_v_4212_);
lean_inc(v_k_4211_);
lean_del_object(v___x_4207_);
v_isSharedCheck_4255_ = !lean_is_exclusive(v_r_4041_);
if (v_isSharedCheck_4255_ == 0)
{
lean_object* v_unused_4256_; lean_object* v_unused_4257_; lean_object* v_unused_4258_; lean_object* v_unused_4259_; lean_object* v_unused_4260_; 
v_unused_4256_ = lean_ctor_get(v_r_4041_, 4);
lean_dec(v_unused_4256_);
v_unused_4257_ = lean_ctor_get(v_r_4041_, 3);
lean_dec(v_unused_4257_);
v_unused_4258_ = lean_ctor_get(v_r_4041_, 2);
lean_dec(v_unused_4258_);
v_unused_4259_ = lean_ctor_get(v_r_4041_, 1);
lean_dec(v_unused_4259_);
v_unused_4260_ = lean_ctor_get(v_r_4041_, 0);
lean_dec(v_unused_4260_);
v___x_4219_ = v_r_4041_;
v_isShared_4220_ = v_isSharedCheck_4255_;
goto v_resetjp_4218_;
}
else
{
lean_dec(v_r_4041_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4255_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___x_4243_; lean_object* v___y_4245_; 
v___x_4221_ = lean_nat_add(v___x_4047_, v_size_4037_);
lean_dec(v_size_4037_);
v___x_4222_ = lean_nat_add(v___x_4221_, v_size_4197_);
lean_dec(v___x_4221_);
v___x_4243_ = lean_nat_add(v___x_4047_, v_size_4209_);
if (lean_obj_tag(v_l_4213_) == 0)
{
lean_object* v_size_4253_; 
v_size_4253_ = lean_ctor_get(v_l_4213_, 0);
lean_inc(v_size_4253_);
v___y_4245_ = v_size_4253_;
goto v___jp_4244_;
}
else
{
lean_object* v___x_4254_; 
v___x_4254_ = lean_unsigned_to_nat(0u);
v___y_4245_ = v___x_4254_;
goto v___jp_4244_;
}
v___jp_4223_:
{
lean_object* v___x_4227_; lean_object* v___x_4229_; 
v___x_4227_ = lean_nat_add(v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec(v___y_4225_);
lean_inc_ref(v_tree_4194_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 4, v_tree_4194_);
lean_ctor_set(v___x_4219_, 3, v_r_4214_);
lean_ctor_set(v___x_4219_, 2, v_v_4196_);
lean_ctor_set(v___x_4219_, 1, v_k_4195_);
lean_ctor_set(v___x_4219_, 0, v___x_4227_);
v___x_4229_ = v___x_4219_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4227_);
lean_ctor_set(v_reuseFailAlloc_4242_, 1, v_k_4195_);
lean_ctor_set(v_reuseFailAlloc_4242_, 2, v_v_4196_);
lean_ctor_set(v_reuseFailAlloc_4242_, 3, v_r_4214_);
lean_ctor_set(v_reuseFailAlloc_4242_, 4, v_tree_4194_);
v___x_4229_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
v_isSharedCheck_4236_ = !lean_is_exclusive(v_tree_4194_);
if (v_isSharedCheck_4236_ == 0)
{
lean_object* v_unused_4237_; lean_object* v_unused_4238_; lean_object* v_unused_4239_; lean_object* v_unused_4240_; lean_object* v_unused_4241_; 
v_unused_4237_ = lean_ctor_get(v_tree_4194_, 4);
lean_dec(v_unused_4237_);
v_unused_4238_ = lean_ctor_get(v_tree_4194_, 3);
lean_dec(v_unused_4238_);
v_unused_4239_ = lean_ctor_get(v_tree_4194_, 2);
lean_dec(v_unused_4239_);
v_unused_4240_ = lean_ctor_get(v_tree_4194_, 1);
lean_dec(v_unused_4240_);
v_unused_4241_ = lean_ctor_get(v_tree_4194_, 0);
lean_dec(v_unused_4241_);
v___x_4231_ = v_tree_4194_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_dec(v_tree_4194_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 4, v___x_4229_);
lean_ctor_set(v___x_4231_, 3, v___y_4224_);
lean_ctor_set(v___x_4231_, 2, v_v_4212_);
lean_ctor_set(v___x_4231_, 1, v_k_4211_);
lean_ctor_set(v___x_4231_, 0, v___x_4222_);
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4222_);
lean_ctor_set(v_reuseFailAlloc_4235_, 1, v_k_4211_);
lean_ctor_set(v_reuseFailAlloc_4235_, 2, v_v_4212_);
lean_ctor_set(v_reuseFailAlloc_4235_, 3, v___y_4224_);
lean_ctor_set(v_reuseFailAlloc_4235_, 4, v___x_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
v___jp_4244_:
{
lean_object* v___x_4246_; lean_object* v___x_4248_; 
v___x_4246_ = lean_nat_add(v___x_4243_, v___y_4245_);
lean_dec(v___y_4245_);
lean_dec(v___x_4243_);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 4, v_l_4213_);
lean_ctor_set(v___x_4191_, 3, v_l_4040_);
lean_ctor_set(v___x_4191_, 2, v_v_4039_);
lean_ctor_set(v___x_4191_, 1, v_k_4038_);
lean_ctor_set(v___x_4191_, 0, v___x_4246_);
v___x_4248_ = v___x_4191_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4246_);
lean_ctor_set(v_reuseFailAlloc_4252_, 1, v_k_4038_);
lean_ctor_set(v_reuseFailAlloc_4252_, 2, v_v_4039_);
lean_ctor_set(v_reuseFailAlloc_4252_, 3, v_l_4040_);
lean_ctor_set(v_reuseFailAlloc_4252_, 4, v_l_4213_);
v___x_4248_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
lean_object* v___x_4249_; 
v___x_4249_ = lean_nat_add(v___x_4047_, v_size_4197_);
if (lean_obj_tag(v_r_4214_) == 0)
{
lean_object* v_size_4250_; 
v_size_4250_ = lean_ctor_get(v_r_4214_, 0);
lean_inc(v_size_4250_);
v___y_4224_ = v___x_4248_;
v___y_4225_ = v___x_4249_;
v___y_4226_ = v_size_4250_;
goto v___jp_4223_;
}
else
{
lean_object* v___x_4251_; 
v___x_4251_ = lean_unsigned_to_nat(0u);
v___y_4224_ = v___x_4248_;
v___y_4225_ = v___x_4249_;
v___y_4226_ = v___x_4251_;
goto v___jp_4223_;
}
}
}
}
}
else
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4266_; 
v___x_4261_ = lean_nat_add(v___x_4047_, v_size_4037_);
lean_dec(v_size_4037_);
v___x_4262_ = lean_nat_add(v___x_4261_, v_size_4197_);
lean_dec(v___x_4261_);
v___x_4263_ = lean_nat_add(v___x_4047_, v_size_4197_);
v___x_4264_ = lean_nat_add(v___x_4263_, v_size_4210_);
lean_dec(v___x_4263_);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 4, v_tree_4194_);
lean_ctor_set(v___x_4191_, 3, v_r_4041_);
lean_ctor_set(v___x_4191_, 2, v_v_4196_);
lean_ctor_set(v___x_4191_, 1, v_k_4195_);
lean_ctor_set(v___x_4191_, 0, v___x_4264_);
v___x_4266_ = v___x_4191_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v___x_4264_);
lean_ctor_set(v_reuseFailAlloc_4270_, 1, v_k_4195_);
lean_ctor_set(v_reuseFailAlloc_4270_, 2, v_v_4196_);
lean_ctor_set(v_reuseFailAlloc_4270_, 3, v_r_4041_);
lean_ctor_set(v_reuseFailAlloc_4270_, 4, v_tree_4194_);
v___x_4266_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
lean_object* v___x_4268_; 
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 4, v___x_4266_);
lean_ctor_set(v___x_4207_, 0, v___x_4262_);
v___x_4268_ = v___x_4207_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4262_);
lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_k_4038_);
lean_ctor_set(v_reuseFailAlloc_4269_, 2, v_v_4039_);
lean_ctor_set(v_reuseFailAlloc_4269_, 3, v_l_4040_);
lean_ctor_set(v_reuseFailAlloc_4269_, 4, v___x_4266_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_4040_) == 0)
{
lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4300_; 
lean_inc_ref(v_l_4040_);
lean_inc(v_v_4039_);
lean_inc(v_k_4038_);
lean_inc(v_size_4037_);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_l_3856_);
if (v_isSharedCheck_4300_ == 0)
{
lean_object* v_unused_4301_; lean_object* v_unused_4302_; lean_object* v_unused_4303_; lean_object* v_unused_4304_; lean_object* v_unused_4305_; 
v_unused_4301_ = lean_ctor_get(v_l_3856_, 4);
lean_dec(v_unused_4301_);
v_unused_4302_ = lean_ctor_get(v_l_3856_, 3);
lean_dec(v_unused_4302_);
v_unused_4303_ = lean_ctor_get(v_l_3856_, 2);
lean_dec(v_unused_4303_);
v_unused_4304_ = lean_ctor_get(v_l_3856_, 1);
lean_dec(v_unused_4304_);
v_unused_4305_ = lean_ctor_get(v_l_3856_, 0);
lean_dec(v_unused_4305_);
v___x_4278_ = v_l_3856_;
v_isShared_4279_ = v_isSharedCheck_4300_;
goto v_resetjp_4277_;
}
else
{
lean_dec(v_l_3856_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4300_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
if (lean_obj_tag(v_r_4041_) == 0)
{
lean_object* v_k_4280_; lean_object* v_v_4281_; lean_object* v_size_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4286_; 
v_k_4280_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_k_4280_);
v_v_4281_ = lean_ctor_get(v___x_4193_, 1);
lean_inc(v_v_4281_);
lean_dec_ref(v___x_4193_);
v_size_4282_ = lean_ctor_get(v_r_4041_, 0);
v___x_4283_ = lean_nat_add(v___x_4047_, v_size_4037_);
lean_dec(v_size_4037_);
v___x_4284_ = lean_nat_add(v___x_4047_, v_size_4282_);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 4, v_tree_4194_);
lean_ctor_set(v___x_4191_, 3, v_r_4041_);
lean_ctor_set(v___x_4191_, 2, v_v_4281_);
lean_ctor_set(v___x_4191_, 1, v_k_4280_);
lean_ctor_set(v___x_4191_, 0, v___x_4284_);
v___x_4286_ = v___x_4191_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4284_);
lean_ctor_set(v_reuseFailAlloc_4290_, 1, v_k_4280_);
lean_ctor_set(v_reuseFailAlloc_4290_, 2, v_v_4281_);
lean_ctor_set(v_reuseFailAlloc_4290_, 3, v_r_4041_);
lean_ctor_set(v_reuseFailAlloc_4290_, 4, v_tree_4194_);
v___x_4286_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
lean_object* v___x_4288_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 4, v___x_4286_);
lean_ctor_set(v___x_4278_, 0, v___x_4283_);
v___x_4288_ = v___x_4278_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v___x_4283_);
lean_ctor_set(v_reuseFailAlloc_4289_, 1, v_k_4038_);
lean_ctor_set(v_reuseFailAlloc_4289_, 2, v_v_4039_);
lean_ctor_set(v_reuseFailAlloc_4289_, 3, v_l_4040_);
lean_ctor_set(v_reuseFailAlloc_4289_, 4, v___x_4286_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
else
{
lean_object* v_k_4291_; lean_object* v_v_4292_; lean_object* v___x_4293_; lean_object* v___x_4295_; 
lean_dec(v_size_4037_);
v_k_4291_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_k_4291_);
v_v_4292_ = lean_ctor_get(v___x_4193_, 1);
lean_inc(v_v_4292_);
lean_dec_ref(v___x_4193_);
v___x_4293_ = lean_unsigned_to_nat(3u);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 4, v_r_4041_);
lean_ctor_set(v___x_4191_, 3, v_r_4041_);
lean_ctor_set(v___x_4191_, 2, v_v_4292_);
lean_ctor_set(v___x_4191_, 1, v_k_4291_);
lean_ctor_set(v___x_4191_, 0, v___x_4047_);
v___x_4295_ = v___x_4191_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4299_, 1, v_k_4291_);
lean_ctor_set(v_reuseFailAlloc_4299_, 2, v_v_4292_);
lean_ctor_set(v_reuseFailAlloc_4299_, 3, v_r_4041_);
lean_ctor_set(v_reuseFailAlloc_4299_, 4, v_r_4041_);
v___x_4295_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
lean_object* v___x_4297_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 4, v___x_4295_);
lean_ctor_set(v___x_4278_, 0, v___x_4293_);
v___x_4297_ = v___x_4278_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4293_);
lean_ctor_set(v_reuseFailAlloc_4298_, 1, v_k_4038_);
lean_ctor_set(v_reuseFailAlloc_4298_, 2, v_v_4039_);
lean_ctor_set(v_reuseFailAlloc_4298_, 3, v_l_4040_);
lean_ctor_set(v_reuseFailAlloc_4298_, 4, v___x_4295_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4041_) == 0)
{
lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4330_; 
lean_inc(v_l_4040_);
lean_inc(v_v_4039_);
lean_inc(v_k_4038_);
v_isSharedCheck_4330_ = !lean_is_exclusive(v_l_3856_);
if (v_isSharedCheck_4330_ == 0)
{
lean_object* v_unused_4331_; lean_object* v_unused_4332_; lean_object* v_unused_4333_; lean_object* v_unused_4334_; lean_object* v_unused_4335_; 
v_unused_4331_ = lean_ctor_get(v_l_3856_, 4);
lean_dec(v_unused_4331_);
v_unused_4332_ = lean_ctor_get(v_l_3856_, 3);
lean_dec(v_unused_4332_);
v_unused_4333_ = lean_ctor_get(v_l_3856_, 2);
lean_dec(v_unused_4333_);
v_unused_4334_ = lean_ctor_get(v_l_3856_, 1);
lean_dec(v_unused_4334_);
v_unused_4335_ = lean_ctor_get(v_l_3856_, 0);
lean_dec(v_unused_4335_);
v___x_4307_ = v_l_3856_;
v_isShared_4308_ = v_isSharedCheck_4330_;
goto v_resetjp_4306_;
}
else
{
lean_dec(v_l_3856_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4330_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v_k_4309_; lean_object* v_v_4310_; lean_object* v_k_4311_; lean_object* v_v_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4326_; 
v_k_4309_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_k_4309_);
v_v_4310_ = lean_ctor_get(v___x_4193_, 1);
lean_inc(v_v_4310_);
lean_dec_ref(v___x_4193_);
v_k_4311_ = lean_ctor_get(v_r_4041_, 1);
v_v_4312_ = lean_ctor_get(v_r_4041_, 2);
v_isSharedCheck_4326_ = !lean_is_exclusive(v_r_4041_);
if (v_isSharedCheck_4326_ == 0)
{
lean_object* v_unused_4327_; lean_object* v_unused_4328_; lean_object* v_unused_4329_; 
v_unused_4327_ = lean_ctor_get(v_r_4041_, 4);
lean_dec(v_unused_4327_);
v_unused_4328_ = lean_ctor_get(v_r_4041_, 3);
lean_dec(v_unused_4328_);
v_unused_4329_ = lean_ctor_get(v_r_4041_, 0);
lean_dec(v_unused_4329_);
v___x_4314_ = v_r_4041_;
v_isShared_4315_ = v_isSharedCheck_4326_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_v_4312_);
lean_inc(v_k_4311_);
lean_dec(v_r_4041_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4326_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4316_; lean_object* v___x_4318_; 
v___x_4316_ = lean_unsigned_to_nat(3u);
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 4, v_l_4040_);
lean_ctor_set(v___x_4314_, 3, v_l_4040_);
lean_ctor_set(v___x_4314_, 2, v_v_4039_);
lean_ctor_set(v___x_4314_, 1, v_k_4038_);
lean_ctor_set(v___x_4314_, 0, v___x_4047_);
v___x_4318_ = v___x_4314_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4325_, 1, v_k_4038_);
lean_ctor_set(v_reuseFailAlloc_4325_, 2, v_v_4039_);
lean_ctor_set(v_reuseFailAlloc_4325_, 3, v_l_4040_);
lean_ctor_set(v_reuseFailAlloc_4325_, 4, v_l_4040_);
v___x_4318_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
lean_object* v___x_4320_; 
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 4, v_l_4040_);
lean_ctor_set(v___x_4191_, 3, v_l_4040_);
lean_ctor_set(v___x_4191_, 2, v_v_4310_);
lean_ctor_set(v___x_4191_, 1, v_k_4309_);
lean_ctor_set(v___x_4191_, 0, v___x_4047_);
v___x_4320_ = v___x_4191_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4324_, 1, v_k_4309_);
lean_ctor_set(v_reuseFailAlloc_4324_, 2, v_v_4310_);
lean_ctor_set(v_reuseFailAlloc_4324_, 3, v_l_4040_);
lean_ctor_set(v_reuseFailAlloc_4324_, 4, v_l_4040_);
v___x_4320_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
lean_object* v___x_4322_; 
if (v_isShared_4308_ == 0)
{
lean_ctor_set(v___x_4307_, 4, v___x_4320_);
lean_ctor_set(v___x_4307_, 3, v___x_4318_);
lean_ctor_set(v___x_4307_, 2, v_v_4312_);
lean_ctor_set(v___x_4307_, 1, v_k_4311_);
lean_ctor_set(v___x_4307_, 0, v___x_4316_);
v___x_4322_ = v___x_4307_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v___x_4316_);
lean_ctor_set(v_reuseFailAlloc_4323_, 1, v_k_4311_);
lean_ctor_set(v_reuseFailAlloc_4323_, 2, v_v_4312_);
lean_ctor_set(v_reuseFailAlloc_4323_, 3, v___x_4318_);
lean_ctor_set(v_reuseFailAlloc_4323_, 4, v___x_4320_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
}
}
}
else
{
lean_object* v_k_4336_; lean_object* v_v_4337_; lean_object* v___x_4338_; lean_object* v___x_4340_; 
v_k_4336_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_k_4336_);
v_v_4337_ = lean_ctor_get(v___x_4193_, 1);
lean_inc(v_v_4337_);
lean_dec_ref(v___x_4193_);
v___x_4338_ = lean_unsigned_to_nat(2u);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 4, v_r_4041_);
lean_ctor_set(v___x_4191_, 3, v_l_3856_);
lean_ctor_set(v___x_4191_, 2, v_v_4337_);
lean_ctor_set(v___x_4191_, 1, v_k_4336_);
lean_ctor_set(v___x_4191_, 0, v___x_4338_);
v___x_4340_ = v___x_4191_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v___x_4338_);
lean_ctor_set(v_reuseFailAlloc_4341_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4341_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4341_, 3, v_l_3856_);
lean_ctor_set(v_reuseFailAlloc_4341_, 4, v_r_4041_);
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
}
}
else
{
return v_l_3856_;
}
}
else
{
return v_r_3857_;
}
}
default: 
{
lean_object* v_impl_4348_; lean_object* v___x_4349_; 
v_impl_4348_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_3851_, v_k_3852_, v_r_3857_);
v___x_4349_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_4348_) == 0)
{
if (lean_obj_tag(v_l_3856_) == 0)
{
lean_object* v_size_4350_; lean_object* v_size_4351_; lean_object* v_k_4352_; lean_object* v_v_4353_; lean_object* v_l_4354_; lean_object* v_r_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v_size_4350_ = lean_ctor_get(v_impl_4348_, 0);
lean_inc(v_size_4350_);
v_size_4351_ = lean_ctor_get(v_l_3856_, 0);
v_k_4352_ = lean_ctor_get(v_l_3856_, 1);
v_v_4353_ = lean_ctor_get(v_l_3856_, 2);
v_l_4354_ = lean_ctor_get(v_l_3856_, 3);
v_r_4355_ = lean_ctor_get(v_l_3856_, 4);
lean_inc(v_r_4355_);
v___x_4356_ = lean_unsigned_to_nat(3u);
v___x_4357_ = lean_nat_mul(v___x_4356_, v_size_4350_);
v___x_4358_ = lean_nat_dec_lt(v___x_4357_, v_size_4351_);
lean_dec(v___x_4357_);
if (v___x_4358_ == 0)
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4362_; 
lean_dec(v_r_4355_);
v___x_4359_ = lean_nat_add(v___x_4349_, v_size_4351_);
v___x_4360_ = lean_nat_add(v___x_4359_, v_size_4350_);
lean_dec(v_size_4350_);
lean_dec(v___x_4359_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_impl_4348_);
lean_ctor_set(v___x_3859_, 0, v___x_4360_);
v___x_4362_ = v___x_3859_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4360_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4363_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4363_, 3, v_l_3856_);
lean_ctor_set(v_reuseFailAlloc_4363_, 4, v_impl_4348_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
else
{
lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4429_; 
lean_inc(v_l_4354_);
lean_inc(v_v_4353_);
lean_inc(v_k_4352_);
lean_inc(v_size_4351_);
v_isSharedCheck_4429_ = !lean_is_exclusive(v_l_3856_);
if (v_isSharedCheck_4429_ == 0)
{
lean_object* v_unused_4430_; lean_object* v_unused_4431_; lean_object* v_unused_4432_; lean_object* v_unused_4433_; lean_object* v_unused_4434_; 
v_unused_4430_ = lean_ctor_get(v_l_3856_, 4);
lean_dec(v_unused_4430_);
v_unused_4431_ = lean_ctor_get(v_l_3856_, 3);
lean_dec(v_unused_4431_);
v_unused_4432_ = lean_ctor_get(v_l_3856_, 2);
lean_dec(v_unused_4432_);
v_unused_4433_ = lean_ctor_get(v_l_3856_, 1);
lean_dec(v_unused_4433_);
v_unused_4434_ = lean_ctor_get(v_l_3856_, 0);
lean_dec(v_unused_4434_);
v___x_4365_ = v_l_3856_;
v_isShared_4366_ = v_isSharedCheck_4429_;
goto v_resetjp_4364_;
}
else
{
lean_dec(v_l_3856_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4429_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v_size_4367_; lean_object* v_size_4368_; lean_object* v_k_4369_; lean_object* v_v_4370_; lean_object* v_l_4371_; lean_object* v_r_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; uint8_t v___x_4375_; 
v_size_4367_ = lean_ctor_get(v_l_4354_, 0);
v_size_4368_ = lean_ctor_get(v_r_4355_, 0);
v_k_4369_ = lean_ctor_get(v_r_4355_, 1);
v_v_4370_ = lean_ctor_get(v_r_4355_, 2);
v_l_4371_ = lean_ctor_get(v_r_4355_, 3);
v_r_4372_ = lean_ctor_get(v_r_4355_, 4);
v___x_4373_ = lean_unsigned_to_nat(2u);
v___x_4374_ = lean_nat_mul(v___x_4373_, v_size_4367_);
v___x_4375_ = lean_nat_dec_lt(v_size_4368_, v___x_4374_);
lean_dec(v___x_4374_);
if (v___x_4375_ == 0)
{
lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4404_; 
lean_inc(v_r_4372_);
lean_inc(v_l_4371_);
lean_inc(v_v_4370_);
lean_inc(v_k_4369_);
v_isSharedCheck_4404_ = !lean_is_exclusive(v_r_4355_);
if (v_isSharedCheck_4404_ == 0)
{
lean_object* v_unused_4405_; lean_object* v_unused_4406_; lean_object* v_unused_4407_; lean_object* v_unused_4408_; lean_object* v_unused_4409_; 
v_unused_4405_ = lean_ctor_get(v_r_4355_, 4);
lean_dec(v_unused_4405_);
v_unused_4406_ = lean_ctor_get(v_r_4355_, 3);
lean_dec(v_unused_4406_);
v_unused_4407_ = lean_ctor_get(v_r_4355_, 2);
lean_dec(v_unused_4407_);
v_unused_4408_ = lean_ctor_get(v_r_4355_, 1);
lean_dec(v_unused_4408_);
v_unused_4409_ = lean_ctor_get(v_r_4355_, 0);
lean_dec(v_unused_4409_);
v___x_4377_ = v_r_4355_;
v_isShared_4378_ = v_isSharedCheck_4404_;
goto v_resetjp_4376_;
}
else
{
lean_dec(v_r_4355_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4404_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___x_4392_; lean_object* v___y_4394_; 
v___x_4379_ = lean_nat_add(v___x_4349_, v_size_4351_);
lean_dec(v_size_4351_);
v___x_4380_ = lean_nat_add(v___x_4379_, v_size_4350_);
lean_dec(v___x_4379_);
v___x_4392_ = lean_nat_add(v___x_4349_, v_size_4367_);
if (lean_obj_tag(v_l_4371_) == 0)
{
lean_object* v_size_4402_; 
v_size_4402_ = lean_ctor_get(v_l_4371_, 0);
lean_inc(v_size_4402_);
v___y_4394_ = v_size_4402_;
goto v___jp_4393_;
}
else
{
lean_object* v___x_4403_; 
v___x_4403_ = lean_unsigned_to_nat(0u);
v___y_4394_ = v___x_4403_;
goto v___jp_4393_;
}
v___jp_4381_:
{
lean_object* v___x_4385_; lean_object* v___x_4387_; 
v___x_4385_ = lean_nat_add(v___y_4382_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec(v___y_4382_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 4, v_impl_4348_);
lean_ctor_set(v___x_4377_, 3, v_r_4372_);
lean_ctor_set(v___x_4377_, 2, v_v_3855_);
lean_ctor_set(v___x_4377_, 1, v_k_3854_);
lean_ctor_set(v___x_4377_, 0, v___x_4385_);
v___x_4387_ = v___x_4377_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4385_);
lean_ctor_set(v_reuseFailAlloc_4391_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4391_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4391_, 3, v_r_4372_);
lean_ctor_set(v_reuseFailAlloc_4391_, 4, v_impl_4348_);
v___x_4387_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
lean_object* v___x_4389_; 
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 4, v___x_4387_);
lean_ctor_set(v___x_4365_, 3, v___y_4383_);
lean_ctor_set(v___x_4365_, 2, v_v_4370_);
lean_ctor_set(v___x_4365_, 1, v_k_4369_);
lean_ctor_set(v___x_4365_, 0, v___x_4380_);
v___x_4389_ = v___x_4365_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4380_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v_k_4369_);
lean_ctor_set(v_reuseFailAlloc_4390_, 2, v_v_4370_);
lean_ctor_set(v_reuseFailAlloc_4390_, 3, v___y_4383_);
lean_ctor_set(v_reuseFailAlloc_4390_, 4, v___x_4387_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
v___jp_4393_:
{
lean_object* v___x_4395_; lean_object* v___x_4397_; 
v___x_4395_ = lean_nat_add(v___x_4392_, v___y_4394_);
lean_dec(v___y_4394_);
lean_dec(v___x_4392_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_l_4371_);
lean_ctor_set(v___x_3859_, 3, v_l_4354_);
lean_ctor_set(v___x_3859_, 2, v_v_4353_);
lean_ctor_set(v___x_3859_, 1, v_k_4352_);
lean_ctor_set(v___x_3859_, 0, v___x_4395_);
v___x_4397_ = v___x_3859_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4395_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v_k_4352_);
lean_ctor_set(v_reuseFailAlloc_4401_, 2, v_v_4353_);
lean_ctor_set(v_reuseFailAlloc_4401_, 3, v_l_4354_);
lean_ctor_set(v_reuseFailAlloc_4401_, 4, v_l_4371_);
v___x_4397_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4398_; 
v___x_4398_ = lean_nat_add(v___x_4349_, v_size_4350_);
lean_dec(v_size_4350_);
if (lean_obj_tag(v_r_4372_) == 0)
{
lean_object* v_size_4399_; 
v_size_4399_ = lean_ctor_get(v_r_4372_, 0);
lean_inc(v_size_4399_);
v___y_4382_ = v___x_4398_;
v___y_4383_ = v___x_4397_;
v___y_4384_ = v_size_4399_;
goto v___jp_4381_;
}
else
{
lean_object* v___x_4400_; 
v___x_4400_ = lean_unsigned_to_nat(0u);
v___y_4382_ = v___x_4398_;
v___y_4383_ = v___x_4397_;
v___y_4384_ = v___x_4400_;
goto v___jp_4381_;
}
}
}
}
}
else
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4415_; 
lean_del_object(v___x_3859_);
v___x_4410_ = lean_nat_add(v___x_4349_, v_size_4351_);
lean_dec(v_size_4351_);
v___x_4411_ = lean_nat_add(v___x_4410_, v_size_4350_);
lean_dec(v___x_4410_);
v___x_4412_ = lean_nat_add(v___x_4349_, v_size_4350_);
lean_dec(v_size_4350_);
v___x_4413_ = lean_nat_add(v___x_4412_, v_size_4368_);
lean_dec(v___x_4412_);
lean_inc_ref(v_impl_4348_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 4, v_impl_4348_);
lean_ctor_set(v___x_4365_, 3, v_r_4355_);
lean_ctor_set(v___x_4365_, 2, v_v_3855_);
lean_ctor_set(v___x_4365_, 1, v_k_3854_);
lean_ctor_set(v___x_4365_, 0, v___x_4413_);
v___x_4415_ = v___x_4365_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v___x_4413_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4428_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4428_, 3, v_r_4355_);
lean_ctor_set(v_reuseFailAlloc_4428_, 4, v_impl_4348_);
v___x_4415_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
v_isSharedCheck_4422_ = !lean_is_exclusive(v_impl_4348_);
if (v_isSharedCheck_4422_ == 0)
{
lean_object* v_unused_4423_; lean_object* v_unused_4424_; lean_object* v_unused_4425_; lean_object* v_unused_4426_; lean_object* v_unused_4427_; 
v_unused_4423_ = lean_ctor_get(v_impl_4348_, 4);
lean_dec(v_unused_4423_);
v_unused_4424_ = lean_ctor_get(v_impl_4348_, 3);
lean_dec(v_unused_4424_);
v_unused_4425_ = lean_ctor_get(v_impl_4348_, 2);
lean_dec(v_unused_4425_);
v_unused_4426_ = lean_ctor_get(v_impl_4348_, 1);
lean_dec(v_unused_4426_);
v_unused_4427_ = lean_ctor_get(v_impl_4348_, 0);
lean_dec(v_unused_4427_);
v___x_4417_ = v_impl_4348_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_dec(v_impl_4348_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 4, v___x_4415_);
lean_ctor_set(v___x_4417_, 3, v_l_4354_);
lean_ctor_set(v___x_4417_, 2, v_v_4353_);
lean_ctor_set(v___x_4417_, 1, v_k_4352_);
lean_ctor_set(v___x_4417_, 0, v___x_4411_);
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v___x_4411_);
lean_ctor_set(v_reuseFailAlloc_4421_, 1, v_k_4352_);
lean_ctor_set(v_reuseFailAlloc_4421_, 2, v_v_4353_);
lean_ctor_set(v_reuseFailAlloc_4421_, 3, v_l_4354_);
lean_ctor_set(v_reuseFailAlloc_4421_, 4, v___x_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_4435_; lean_object* v___x_4436_; lean_object* v___x_4438_; 
v_size_4435_ = lean_ctor_get(v_impl_4348_, 0);
lean_inc(v_size_4435_);
v___x_4436_ = lean_nat_add(v___x_4349_, v_size_4435_);
lean_dec(v_size_4435_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_impl_4348_);
lean_ctor_set(v___x_3859_, 0, v___x_4436_);
v___x_4438_ = v___x_3859_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
lean_ctor_set(v_reuseFailAlloc_4439_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4439_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4439_, 3, v_l_3856_);
lean_ctor_set(v_reuseFailAlloc_4439_, 4, v_impl_4348_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
else
{
if (lean_obj_tag(v_l_3856_) == 0)
{
lean_object* v_l_4440_; 
v_l_4440_ = lean_ctor_get(v_l_3856_, 3);
if (lean_obj_tag(v_l_4440_) == 0)
{
lean_object* v_r_4441_; 
lean_inc_ref(v_l_4440_);
v_r_4441_ = lean_ctor_get(v_l_3856_, 4);
lean_inc(v_r_4441_);
if (lean_obj_tag(v_r_4441_) == 0)
{
lean_object* v_size_4442_; lean_object* v_k_4443_; lean_object* v_v_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4457_; 
v_size_4442_ = lean_ctor_get(v_l_3856_, 0);
v_k_4443_ = lean_ctor_get(v_l_3856_, 1);
v_v_4444_ = lean_ctor_get(v_l_3856_, 2);
v_isSharedCheck_4457_ = !lean_is_exclusive(v_l_3856_);
if (v_isSharedCheck_4457_ == 0)
{
lean_object* v_unused_4458_; lean_object* v_unused_4459_; 
v_unused_4458_ = lean_ctor_get(v_l_3856_, 4);
lean_dec(v_unused_4458_);
v_unused_4459_ = lean_ctor_get(v_l_3856_, 3);
lean_dec(v_unused_4459_);
v___x_4446_ = v_l_3856_;
v_isShared_4447_ = v_isSharedCheck_4457_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_v_4444_);
lean_inc(v_k_4443_);
lean_inc(v_size_4442_);
lean_dec(v_l_3856_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4457_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v_size_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4452_; 
v_size_4448_ = lean_ctor_get(v_r_4441_, 0);
v___x_4449_ = lean_nat_add(v___x_4349_, v_size_4442_);
lean_dec(v_size_4442_);
v___x_4450_ = lean_nat_add(v___x_4349_, v_size_4448_);
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 4, v_impl_4348_);
lean_ctor_set(v___x_4446_, 3, v_r_4441_);
lean_ctor_set(v___x_4446_, 2, v_v_3855_);
lean_ctor_set(v___x_4446_, 1, v_k_3854_);
lean_ctor_set(v___x_4446_, 0, v___x_4450_);
v___x_4452_ = v___x_4446_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v___x_4450_);
lean_ctor_set(v_reuseFailAlloc_4456_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4456_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4456_, 3, v_r_4441_);
lean_ctor_set(v_reuseFailAlloc_4456_, 4, v_impl_4348_);
v___x_4452_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
lean_object* v___x_4454_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_4452_);
lean_ctor_set(v___x_3859_, 3, v_l_4440_);
lean_ctor_set(v___x_3859_, 2, v_v_4444_);
lean_ctor_set(v___x_3859_, 1, v_k_4443_);
lean_ctor_set(v___x_3859_, 0, v___x_4449_);
v___x_4454_ = v___x_3859_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___x_4449_);
lean_ctor_set(v_reuseFailAlloc_4455_, 1, v_k_4443_);
lean_ctor_set(v_reuseFailAlloc_4455_, 2, v_v_4444_);
lean_ctor_set(v_reuseFailAlloc_4455_, 3, v_l_4440_);
lean_ctor_set(v_reuseFailAlloc_4455_, 4, v___x_4452_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
else
{
lean_object* v_k_4460_; lean_object* v_v_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4472_; 
v_k_4460_ = lean_ctor_get(v_l_3856_, 1);
v_v_4461_ = lean_ctor_get(v_l_3856_, 2);
v_isSharedCheck_4472_ = !lean_is_exclusive(v_l_3856_);
if (v_isSharedCheck_4472_ == 0)
{
lean_object* v_unused_4473_; lean_object* v_unused_4474_; lean_object* v_unused_4475_; 
v_unused_4473_ = lean_ctor_get(v_l_3856_, 4);
lean_dec(v_unused_4473_);
v_unused_4474_ = lean_ctor_get(v_l_3856_, 3);
lean_dec(v_unused_4474_);
v_unused_4475_ = lean_ctor_get(v_l_3856_, 0);
lean_dec(v_unused_4475_);
v___x_4463_ = v_l_3856_;
v_isShared_4464_ = v_isSharedCheck_4472_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_v_4461_);
lean_inc(v_k_4460_);
lean_dec(v_l_3856_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4472_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; lean_object* v___x_4467_; 
v___x_4465_ = lean_unsigned_to_nat(3u);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 3, v_r_4441_);
lean_ctor_set(v___x_4463_, 2, v_v_3855_);
lean_ctor_set(v___x_4463_, 1, v_k_3854_);
lean_ctor_set(v___x_4463_, 0, v___x_4349_);
v___x_4467_ = v___x_4463_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4349_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4471_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4471_, 3, v_r_4441_);
lean_ctor_set(v_reuseFailAlloc_4471_, 4, v_r_4441_);
v___x_4467_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
lean_object* v___x_4469_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_4467_);
lean_ctor_set(v___x_3859_, 3, v_l_4440_);
lean_ctor_set(v___x_3859_, 2, v_v_4461_);
lean_ctor_set(v___x_3859_, 1, v_k_4460_);
lean_ctor_set(v___x_3859_, 0, v___x_4465_);
v___x_4469_ = v___x_3859_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4470_, 1, v_k_4460_);
lean_ctor_set(v_reuseFailAlloc_4470_, 2, v_v_4461_);
lean_ctor_set(v_reuseFailAlloc_4470_, 3, v_l_4440_);
lean_ctor_set(v_reuseFailAlloc_4470_, 4, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
}
else
{
lean_object* v_r_4476_; 
v_r_4476_ = lean_ctor_get(v_l_3856_, 4);
lean_inc(v_r_4476_);
if (lean_obj_tag(v_r_4476_) == 0)
{
lean_object* v_k_4477_; lean_object* v_v_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4501_; 
lean_inc(v_l_4440_);
v_k_4477_ = lean_ctor_get(v_l_3856_, 1);
v_v_4478_ = lean_ctor_get(v_l_3856_, 2);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_l_3856_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; lean_object* v_unused_4503_; lean_object* v_unused_4504_; 
v_unused_4502_ = lean_ctor_get(v_l_3856_, 4);
lean_dec(v_unused_4502_);
v_unused_4503_ = lean_ctor_get(v_l_3856_, 3);
lean_dec(v_unused_4503_);
v_unused_4504_ = lean_ctor_get(v_l_3856_, 0);
lean_dec(v_unused_4504_);
v___x_4480_ = v_l_3856_;
v_isShared_4481_ = v_isSharedCheck_4501_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_v_4478_);
lean_inc(v_k_4477_);
lean_dec(v_l_3856_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4501_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v_k_4482_; lean_object* v_v_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4497_; 
v_k_4482_ = lean_ctor_get(v_r_4476_, 1);
v_v_4483_ = lean_ctor_get(v_r_4476_, 2);
v_isSharedCheck_4497_ = !lean_is_exclusive(v_r_4476_);
if (v_isSharedCheck_4497_ == 0)
{
lean_object* v_unused_4498_; lean_object* v_unused_4499_; lean_object* v_unused_4500_; 
v_unused_4498_ = lean_ctor_get(v_r_4476_, 4);
lean_dec(v_unused_4498_);
v_unused_4499_ = lean_ctor_get(v_r_4476_, 3);
lean_dec(v_unused_4499_);
v_unused_4500_ = lean_ctor_get(v_r_4476_, 0);
lean_dec(v_unused_4500_);
v___x_4485_ = v_r_4476_;
v_isShared_4486_ = v_isSharedCheck_4497_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_v_4483_);
lean_inc(v_k_4482_);
lean_dec(v_r_4476_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4497_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4487_ = lean_unsigned_to_nat(3u);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 4, v_l_4440_);
lean_ctor_set(v___x_4485_, 3, v_l_4440_);
lean_ctor_set(v___x_4485_, 2, v_v_4478_);
lean_ctor_set(v___x_4485_, 1, v_k_4477_);
lean_ctor_set(v___x_4485_, 0, v___x_4349_);
v___x_4489_ = v___x_4485_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4349_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v_k_4477_);
lean_ctor_set(v_reuseFailAlloc_4496_, 2, v_v_4478_);
lean_ctor_set(v_reuseFailAlloc_4496_, 3, v_l_4440_);
lean_ctor_set(v_reuseFailAlloc_4496_, 4, v_l_4440_);
v___x_4489_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
lean_object* v___x_4491_; 
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 4, v_l_4440_);
lean_ctor_set(v___x_4480_, 2, v_v_3855_);
lean_ctor_set(v___x_4480_, 1, v_k_3854_);
lean_ctor_set(v___x_4480_, 0, v___x_4349_);
v___x_4491_ = v___x_4480_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4349_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4495_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4495_, 3, v_l_4440_);
lean_ctor_set(v_reuseFailAlloc_4495_, 4, v_l_4440_);
v___x_4491_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
lean_object* v___x_4493_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_4491_);
lean_ctor_set(v___x_3859_, 3, v___x_4489_);
lean_ctor_set(v___x_3859_, 2, v_v_4483_);
lean_ctor_set(v___x_3859_, 1, v_k_4482_);
lean_ctor_set(v___x_3859_, 0, v___x_4487_);
v___x_4493_ = v___x_3859_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4487_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v_k_4482_);
lean_ctor_set(v_reuseFailAlloc_4494_, 2, v_v_4483_);
lean_ctor_set(v_reuseFailAlloc_4494_, 3, v___x_4489_);
lean_ctor_set(v_reuseFailAlloc_4494_, 4, v___x_4491_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
}
}
else
{
lean_object* v___x_4505_; lean_object* v___x_4507_; 
v___x_4505_ = lean_unsigned_to_nat(2u);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_r_4476_);
lean_ctor_set(v___x_3859_, 0, v___x_4505_);
v___x_4507_ = v___x_3859_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4505_);
lean_ctor_set(v_reuseFailAlloc_4508_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4508_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4508_, 3, v_l_3856_);
lean_ctor_set(v_reuseFailAlloc_4508_, 4, v_r_4476_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
else
{
lean_object* v___x_4510_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_l_3856_);
lean_ctor_set(v___x_3859_, 0, v___x_4349_);
v___x_4510_ = v___x_3859_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4349_);
lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4511_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4511_, 3, v_l_3856_);
lean_ctor_set(v_reuseFailAlloc_4511_, 4, v_l_3856_);
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
}
}
else
{
lean_dec(v_k_3852_);
lean_dec_ref(v_cmp_3851_);
return v_t_3853_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(lean_object* v_cmp_4514_, lean_object* v_init_4515_, lean_object* v_x_4516_){
_start:
{
if (lean_obj_tag(v_x_4516_) == 0)
{
lean_object* v_k_4517_; lean_object* v_l_4518_; lean_object* v_r_4519_; lean_object* v___x_4520_; lean_object* v_a_4521_; lean_object* v_r_4522_; 
v_k_4517_ = lean_ctor_get(v_x_4516_, 1);
lean_inc(v_k_4517_);
v_l_4518_ = lean_ctor_get(v_x_4516_, 3);
lean_inc(v_l_4518_);
v_r_4519_ = lean_ctor_get(v_x_4516_, 4);
lean_inc(v_r_4519_);
lean_dec_ref(v_x_4516_);
lean_inc_ref_n(v_cmp_4514_, 2);
v___x_4520_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4514_, v_init_4515_, v_l_4518_);
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
lean_inc(v_a_4521_);
lean_dec_ref(v___x_4520_);
v_r_4522_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_4514_, v_k_4517_, v_a_4521_);
v_init_4515_ = v_r_4522_;
v_x_4516_ = v_r_4519_;
goto _start;
}
else
{
lean_object* v___x_4524_; 
lean_dec_ref(v_cmp_4514_);
v___x_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4524_, 0, v_init_4515_);
return v___x_4524_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(lean_object* v_cmp_4525_, lean_object* v_t_u2082_4526_, lean_object* v_t_4527_){
_start:
{
if (lean_obj_tag(v_t_4527_) == 0)
{
lean_object* v_k_4528_; lean_object* v_v_4529_; lean_object* v_l_4530_; lean_object* v_r_4531_; uint8_t v___x_4532_; 
v_k_4528_ = lean_ctor_get(v_t_4527_, 1);
lean_inc_n(v_k_4528_, 2);
v_v_4529_ = lean_ctor_get(v_t_4527_, 2);
lean_inc(v_v_4529_);
v_l_4530_ = lean_ctor_get(v_t_4527_, 3);
lean_inc(v_l_4530_);
v_r_4531_ = lean_ctor_get(v_t_4527_, 4);
lean_inc(v_r_4531_);
lean_dec_ref(v_t_4527_);
lean_inc(v_t_u2082_4526_);
lean_inc_ref(v_cmp_4525_);
v___x_4532_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_4525_, v_k_4528_, v_t_u2082_4526_);
if (v___x_4532_ == 0)
{
lean_object* v_impl_4533_; lean_object* v_impl_4534_; lean_object* v___x_4535_; 
lean_inc(v_t_u2082_4526_);
lean_inc_ref(v_cmp_4525_);
v_impl_4533_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4525_, v_t_u2082_4526_, v_l_4530_);
v_impl_4534_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4525_, v_t_u2082_4526_, v_r_4531_);
v___x_4535_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_4528_, v_v_4529_, v_impl_4533_, v_impl_4534_);
return v___x_4535_;
}
else
{
lean_object* v_impl_4536_; lean_object* v_impl_4537_; lean_object* v___x_4538_; 
lean_dec(v_v_4529_);
lean_dec(v_k_4528_);
lean_inc(v_t_u2082_4526_);
lean_inc_ref(v_cmp_4525_);
v_impl_4536_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4525_, v_t_u2082_4526_, v_l_4530_);
v_impl_4537_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4525_, v_t_u2082_4526_, v_r_4531_);
v___x_4538_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_4536_, v_impl_4537_);
return v___x_4538_;
}
}
else
{
lean_dec(v_t_u2082_4526_);
lean_dec_ref(v_cmp_4525_);
return v_t_4527_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object* v_cmp_4539_, lean_object* v_t_u2081_4540_, lean_object* v_t_u2082_4541_){
_start:
{
lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4550_; 
if (lean_obj_tag(v_t_u2081_4540_) == 0)
{
lean_object* v_size_4553_; 
v_size_4553_ = lean_ctor_get(v_t_u2081_4540_, 0);
lean_inc(v_size_4553_);
v___y_4550_ = v_size_4553_;
goto v___jp_4549_;
}
else
{
lean_object* v___x_4554_; 
v___x_4554_ = lean_unsigned_to_nat(0u);
v___y_4550_ = v___x_4554_;
goto v___jp_4549_;
}
v___jp_4542_:
{
uint8_t v___x_4545_; 
v___x_4545_ = lean_nat_dec_le(v___y_4543_, v___y_4544_);
lean_dec(v___y_4544_);
lean_dec(v___y_4543_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4546_; lean_object* v_a_4547_; 
v___x_4546_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4539_, v_t_u2081_4540_, v_t_u2082_4541_);
v_a_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc(v_a_4547_);
lean_dec_ref(v___x_4546_);
return v_a_4547_;
}
else
{
lean_object* v___x_4548_; 
v___x_4548_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4539_, v_t_u2082_4541_, v_t_u2081_4540_);
return v___x_4548_;
}
}
v___jp_4549_:
{
if (lean_obj_tag(v_t_u2082_4541_) == 0)
{
lean_object* v_size_4551_; 
v_size_4551_ = lean_ctor_get(v_t_u2082_4541_, 0);
lean_inc(v_size_4551_);
v___y_4543_ = v___y_4550_;
v___y_4544_ = v_size_4551_;
goto v___jp_4542_;
}
else
{
lean_object* v___x_4552_; 
v___x_4552_ = lean_unsigned_to_nat(0u);
v___y_4543_ = v___y_4550_;
v___y_4544_ = v___x_4552_;
goto v___jp_4542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff___redArg(lean_object* v_cmp_4555_, lean_object* v_t_u2081_4556_, lean_object* v_t_u2082_4557_){
_start:
{
lean_object* v___x_4558_; 
v___x_4558_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4555_, v_t_u2081_4556_, v_t_u2082_4557_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff(lean_object* v_00_u03b1_4559_, lean_object* v_00_u03b2_4560_, lean_object* v_cmp_4561_, lean_object* v_t_u2081_4562_, lean_object* v_t_u2082_4563_){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4561_, v_t_u2081_4562_, v_t_u2082_4563_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0(lean_object* v_00_u03b1_4565_, lean_object* v_cmp_4566_, lean_object* v_00_u03b2_4567_, lean_object* v_t_u2081_4568_, lean_object* v_t_u2082_4569_, lean_object* v_h_u2081_4570_){
_start:
{
lean_object* v___x_4571_; 
v___x_4571_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4566_, v_t_u2081_4568_, v_t_u2082_4569_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0(lean_object* v_00_u03b1_4572_, lean_object* v_cmp_4573_, lean_object* v_00_u03b2_4574_, lean_object* v_k_4575_, lean_object* v_t_4576_, lean_object* v_h_4577_){
_start:
{
lean_object* v___x_4578_; 
v___x_4578_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_4573_, v_k_4575_, v_t_4576_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1(lean_object* v_00_u03b1_4579_, lean_object* v_00_u03b2_4580_, lean_object* v_cmp_4581_, lean_object* v_init_4582_, lean_object* v_x_4583_){
_start:
{
lean_object* v___x_4584_; 
v___x_4584_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4581_, v_init_4582_, v_x_4583_);
return v___x_4584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2(lean_object* v_00_u03b1_4585_, lean_object* v_00_u03b2_4586_, lean_object* v_cmp_4587_, lean_object* v_t_u2082_4588_, lean_object* v_t_4589_, lean_object* v_hl_4590_){
_start:
{
lean_object* v___x_4591_; 
v___x_4591_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4587_, v_t_u2082_4588_, v_t_4589_);
return v___x_4591_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSDiff___redArg(lean_object* v_cmp_4592_){
_start:
{
lean_object* v___x_4593_; 
v___x_4593_ = lean_alloc_closure((void*)(l_Std_DTreeMap_diff), 5, 3);
lean_closure_set(v___x_4593_, 0, lean_box(0));
lean_closure_set(v___x_4593_, 1, lean_box(0));
lean_closure_set(v___x_4593_, 2, v_cmp_4592_);
return v___x_4593_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSDiff(lean_object* v_00_u03b1_4594_, lean_object* v_00_u03b2_4595_, lean_object* v_cmp_4596_){
_start:
{
lean_object* v___x_4597_; 
v___x_4597_ = lean_alloc_closure((void*)(l_Std_DTreeMap_diff), 5, 3);
lean_closure_set(v___x_4597_, 0, lean_box(0));
lean_closure_set(v___x_4597_, 1, lean_box(0));
lean_closure_set(v___x_4597_, 2, v_cmp_4596_);
return v___x_4597_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_4598_, lean_object* v_a_4599_, lean_object* v_____s_4600_){
_start:
{
lean_object* v_r_4601_; lean_object* v___x_4602_; 
v_r_4601_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_4598_, v_a_4599_, v_____s_4600_);
v___x_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4602_, 0, v_r_4601_);
return v___x_4602_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany___redArg(lean_object* v_cmp_4603_, lean_object* v_inst_4604_, lean_object* v_t_4605_, lean_object* v_l_4606_){
_start:
{
lean_object* v___f_4607_; lean_object* v___x_4608_; 
v___f_4607_ = lean_alloc_closure((void*)(l_Std_DTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4607_, 0, v_cmp_4603_);
v___x_4608_ = lean_apply_4(v_inst_4604_, lean_box(0), v_l_4606_, v_t_4605_, v___f_4607_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany(lean_object* v_00_u03b1_4609_, lean_object* v_00_u03b2_4610_, lean_object* v_cmp_4611_, lean_object* v_00_u03c1_4612_, lean_object* v_inst_4613_, lean_object* v_t_4614_, lean_object* v_l_4615_){
_start:
{
lean_object* v___f_4616_; lean_object* v___x_4617_; 
v___f_4616_ = lean_alloc_closure((void*)(l_Std_DTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4616_, 0, v_cmp_4611_);
v___x_4617_ = lean_apply_4(v_inst_4613_, lean_box(0), v_l_4615_, v_t_4614_, v___f_4616_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany___redArg___lam__0(lean_object* v_cmp_4618_, lean_object* v_x_4619_, lean_object* v_____s_4620_){
_start:
{
lean_object* v_fst_4621_; lean_object* v_snd_4622_; lean_object* v_r_4623_; lean_object* v___x_4624_; 
v_fst_4621_ = lean_ctor_get(v_x_4619_, 0);
lean_inc(v_fst_4621_);
v_snd_4622_ = lean_ctor_get(v_x_4619_, 1);
lean_inc(v_snd_4622_);
lean_dec_ref(v_x_4619_);
v_r_4623_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4618_, v_fst_4621_, v_snd_4622_, v_____s_4620_);
v___x_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4624_, 0, v_r_4623_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany___redArg(lean_object* v_cmp_4625_, lean_object* v_inst_4626_, lean_object* v_t_4627_, lean_object* v_l_4628_){
_start:
{
lean_object* v___f_4629_; lean_object* v___x_4630_; 
v___f_4629_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4629_, 0, v_cmp_4625_);
v___x_4630_ = lean_apply_4(v_inst_4626_, lean_box(0), v_l_4628_, v_t_4627_, v___f_4629_);
return v___x_4630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany(lean_object* v_00_u03b1_4631_, lean_object* v_cmp_4632_, lean_object* v_00_u03b2_4633_, lean_object* v_00_u03c1_4634_, lean_object* v_inst_4635_, lean_object* v_t_4636_, lean_object* v_l_4637_){
_start:
{
lean_object* v___f_4638_; lean_object* v___x_4639_; 
v___f_4638_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4638_, 0, v_cmp_4632_);
v___x_4639_ = lean_apply_4(v_inst_4635_, lean_box(0), v_l_4637_, v_t_4636_, v___f_4638_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_4640_, lean_object* v_a_4641_, lean_object* v_____s_4642_){
_start:
{
uint8_t v___x_4643_; 
lean_inc(v_____s_4642_);
lean_inc(v_a_4641_);
lean_inc_ref(v_cmp_4640_);
v___x_4643_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4640_, v_a_4641_, v_____s_4642_);
if (v___x_4643_ == 0)
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4644_ = lean_box(0);
v___x_4645_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4640_, v_a_4641_, v___x_4644_, v_____s_4642_);
v___x_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4645_);
return v___x_4646_;
}
else
{
lean_object* v___x_4647_; 
lean_dec(v_a_4641_);
lean_dec_ref(v_cmp_4640_);
v___x_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4647_, 0, v_____s_4642_);
return v___x_4647_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_4648_, lean_object* v_inst_4649_, lean_object* v_t_4650_, lean_object* v_l_4651_){
_start:
{
lean_object* v___f_4652_; lean_object* v___x_4653_; 
v___f_4652_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4652_, 0, v_cmp_4648_);
v___x_4653_ = lean_apply_4(v_inst_4649_, lean_box(0), v_l_4651_, v_t_4650_, v___f_4652_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_4654_, lean_object* v_cmp_4655_, lean_object* v_00_u03c1_4656_, lean_object* v_inst_4657_, lean_object* v_t_4658_, lean_object* v_l_4659_){
_start:
{
lean_object* v___f_4660_; lean_object* v___x_4661_; 
v___f_4660_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4660_, 0, v_cmp_4655_);
v___x_4661_ = lean_apply_4(v_inst_4657_, lean_box(0), v_l_4659_, v_t_4658_, v___f_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1(lean_object* v___f_4665_, lean_object* v___x_4666_, lean_object* v_m_4667_, lean_object* v_prec_4668_){
_start:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4669_ = ((lean_object*)(l_Std_DTreeMap_instRepr___redArg___lam__1___closed__1));
v___x_4670_ = lean_box(0);
v___x_4671_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_4672_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_4671_, v___f_4665_, v___x_4670_, v_m_4667_);
v___x_4673_ = l_List_repr___redArg(v___x_4666_, v___x_4672_);
v___x_4674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4669_);
lean_ctor_set(v___x_4674_, 1, v___x_4673_);
v___x_4675_ = l_Repr_addAppParen(v___x_4674_, v_prec_4668_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1___boxed(lean_object* v___f_4676_, lean_object* v___x_4677_, lean_object* v_m_4678_, lean_object* v_prec_4679_){
_start:
{
lean_object* v_res_4680_; 
v_res_4680_ = l_Std_DTreeMap_instRepr___redArg___lam__1(v___f_4676_, v___x_4677_, v_m_4678_, v_prec_4679_);
lean_dec(v_prec_4679_);
return v_res_4680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg(lean_object* v_inst_4681_, lean_object* v_inst_4682_){
_start:
{
lean_object* v___f_4683_; lean_object* v___x_4684_; lean_object* v___f_4685_; 
v___f_4683_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_4684_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_4684_, 0, lean_box(0));
lean_closure_set(v___x_4684_, 1, lean_box(0));
lean_closure_set(v___x_4684_, 2, v_inst_4681_);
lean_closure_set(v___x_4684_, 3, v_inst_4682_);
v___f_4685_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4685_, 0, v___f_4683_);
lean_closure_set(v___f_4685_, 1, v___x_4684_);
return v___f_4685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr(lean_object* v_00_u03b1_4686_, lean_object* v_00_u03b2_4687_, lean_object* v_cmp_4688_, lean_object* v_inst_4689_, lean_object* v_inst_4690_){
_start:
{
lean_object* v___x_4691_; 
v___x_4691_ = l_Std_DTreeMap_instRepr___redArg(v_inst_4689_, v_inst_4690_);
return v___x_4691_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___boxed(lean_object* v_00_u03b1_4692_, lean_object* v_00_u03b2_4693_, lean_object* v_cmp_4694_, lean_object* v_inst_4695_, lean_object* v_inst_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Std_DTreeMap_instRepr(v_00_u03b1_4692_, v_00_u03b2_4693_, v_cmp_4694_, v_inst_4695_, v_inst_4696_);
lean_dec_ref(v_cmp_4694_);
return v_res_4697_;
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
