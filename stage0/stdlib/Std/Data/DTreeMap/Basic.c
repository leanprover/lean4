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
lean_object* l_Std_DTreeMap_instCoeTypeForall___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_instCoeTypeForall___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_75_;
v_res_75_ = l_Std_DTreeMap_instCoeTypeForall___redArg();
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall___redArg___boxed(lean_object* v___dummy_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_DTreeMap_instCoeTypeForall___redArg();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall(lean_object* v_00_u03b1_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_box(0);
return v___x_79_;
}
}
lean_object* l_Std_DTreeMap_empty___redArg(){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(1);
return v___x_81_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_82_;
v_res_82_ = l_Std_DTreeMap_empty___redArg();
stack->m_obj
 = v_res_82_;
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
lean_object* l_Std_DTreeMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(1);
return v___x_94_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_95_;
v_res_95_ = l_Std_DTreeMap_instEmptyCollection___redArg();
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_DTreeMap_instEmptyCollection___redArg();
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_cmp_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_box(1);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_102_, lean_object* v_00_u03b2_103_, lean_object* v_cmp_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_DTreeMap_instEmptyCollection(v_00_u03b1_102_, v_00_u03b2_103_, v_cmp_104_);
lean_dec_ref(v_cmp_104_);
return v_res_105_;
}
}
lean_object* l_Std_DTreeMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_box(1);
return v___x_107_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_108_;
v_res_108_ = l_Std_DTreeMap_instInhabited___redArg();
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited___redArg___boxed(lean_object* v___dummy_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_DTreeMap_instInhabited___redArg();
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_cmp_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(1);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInhabited___boxed(lean_object* v_00_u03b1_115_, lean_object* v_00_u03b2_116_, lean_object* v_cmp_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_DTreeMap_instInhabited(v_00_u03b1_115_, v_00_u03b2_116_, v_cmp_117_);
lean_dec_ref(v_cmp_117_);
return v_res_118_;
}
}
static lean_object* _init_l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3));
v___x_157_ = l_String_toRawSubstring_x27(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1(lean_object* v_x_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__3));
lean_inc(v_x_175_);
v___x_179_ = l_Lean_Syntax_isOfKind(v_x_175_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_x_175_);
v___x_180_ = lean_box(1);
v___x_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v_a_177_);
return v___x_181_;
}
else
{
lean_object* v_quotContext_182_; lean_object* v_currMacroScope_183_; lean_object* v_ref_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_quotContext_182_ = lean_ctor_get(v_a_176_, 1);
v_currMacroScope_183_ = lean_ctor_get(v_a_176_, 2);
v_ref_184_ = lean_ctor_get(v_a_176_, 5);
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = l_Lean_Syntax_getArg(v_x_175_, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(2u);
v___x_188_ = l_Lean_Syntax_getArg(v_x_175_, v___x_187_);
lean_dec(v_x_175_);
v___x_189_ = 0;
v___x_190_ = l_Lean_SourceInfo_fromRef(v_ref_184_, v___x_189_);
v___x_191_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2));
v___x_192_ = lean_obj_once(&l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4, &l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4_once, _init_l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4);
v___x_193_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_183_);
lean_inc(v_quotContext_182_);
v___x_194_ = l_Lean_addMacroScope(v_quotContext_182_, v___x_193_, v_currMacroScope_183_);
v___x_195_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__10));
lean_inc_n(v___x_190_, 2);
v___x_196_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_196_, 0, v___x_190_);
lean_ctor_set(v___x_196_, 1, v___x_192_);
lean_ctor_set(v___x_196_, 2, v___x_194_);
lean_ctor_set(v___x_196_, 3, v___x_195_);
v___x_197_ = ((lean_object*)(l_Std_DTreeMap___auto__1___closed__9));
v___x_198_ = l_Lean_Syntax_node2(v___x_190_, v___x_197_, v___x_186_, v___x_188_);
v___x_199_ = l_Lean_Syntax_node2(v___x_190_, v___x_191_, v___x_196_, v___x_198_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v_a_177_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___boxed(lean_object* v_x_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1(v_x_201_, v_a_202_, v_a_203_);
lean_dec_ref(v_a_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(lean_object* v_x_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2));
lean_inc(v_x_208_);
v___x_212_ = l_Lean_Syntax_isOfKind(v_x_208_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v_x_208_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v_a_210_);
return v___x_214_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = l_Lean_Syntax_getArg(v_x_208_, v___x_215_);
v___x_217_ = ((lean_object*)(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__1));
lean_inc(v___x_216_);
v___x_218_ = l_Lean_Syntax_isOfKind(v___x_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v___x_216_);
lean_dec(v_x_208_);
v___x_219_ = lean_box(0);
v___x_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v_a_210_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = l_Lean_Syntax_getArg(v_x_208_, v___x_221_);
lean_dec(v_x_208_);
v___x_223_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_222_);
v___x_224_ = l_Lean_Syntax_matchesNull(v___x_222_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec(v___x_222_);
lean_dec(v___x_216_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v_a_210_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v_ref_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_227_ = l_Lean_Syntax_getArg(v___x_222_, v___x_215_);
v___x_228_ = l_Lean_Syntax_getArg(v___x_222_, v___x_221_);
lean_dec(v___x_222_);
v_ref_229_ = l_Lean_replaceRef(v___x_216_, v_a_209_);
lean_dec(v___x_216_);
v___x_230_ = 0;
v___x_231_ = l_Lean_SourceInfo_fromRef(v_ref_229_, v___x_230_);
lean_dec(v_ref_229_);
v___x_232_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__3));
v___x_233_ = ((lean_object*)(l_Std_DTreeMap_term___x7em___00__closed__6));
lean_inc(v___x_231_);
v___x_234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_231_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = l_Lean_Syntax_node3(v___x_231_, v___x_232_, v___x_227_, v___x_234_, v___x_228_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v_a_210_);
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___boxed(lean_object* v_x_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(v_x_237_, v_a_238_, v_a_239_);
lean_dec(v_a_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insert___redArg(lean_object* v_cmp_241_, lean_object* v_t_242_, lean_object* v_a_243_, lean_object* v_b_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_241_, v_a_243_, v_b_244_, v_t_242_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insert(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_cmp_248_, lean_object* v_t_249_, lean_object* v_a_250_, lean_object* v_b_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_248_, v_a_250_, v_b_251_, v_t_249_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma___redArg___lam__0(lean_object* v_cmp_253_, lean_object* v_e_254_){
_start:
{
lean_object* v_fst_255_; lean_object* v_snd_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_fst_255_ = lean_ctor_get(v_e_254_, 0);
lean_inc(v_fst_255_);
v_snd_256_ = lean_ctor_get(v_e_254_, 1);
lean_inc(v_snd_256_);
lean_dec_ref(v_e_254_);
v___x_257_ = lean_box(1);
v___x_258_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_253_, v_fst_255_, v_snd_256_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma___redArg(lean_object* v_cmp_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_260_, 0, v_cmp_259_);
return v___f_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSingletonSigma(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_cmp_263_){
_start:
{
lean_object* v___f_264_; 
v___f_264_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_264_, 0, v_cmp_263_);
return v___f_264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma___redArg___lam__0(lean_object* v_cmp_265_, lean_object* v_e_266_, lean_object* v_s_267_){
_start:
{
lean_object* v_fst_268_; lean_object* v_snd_269_; lean_object* v___x_270_; 
v_fst_268_ = lean_ctor_get(v_e_266_, 0);
lean_inc(v_fst_268_);
v_snd_269_ = lean_ctor_get(v_e_266_, 1);
lean_inc(v_snd_269_);
lean_dec_ref(v_e_266_);
v___x_270_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_265_, v_fst_268_, v_snd_269_, v_s_267_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma___redArg(lean_object* v_cmp_271_){
_start:
{
lean_object* v___f_272_; 
v___f_272_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_272_, 0, v_cmp_271_);
return v___f_272_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInsertSigma(lean_object* v_00_u03b1_273_, lean_object* v_00_u03b2_274_, lean_object* v_cmp_275_){
_start:
{
lean_object* v___f_276_; 
v___f_276_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_276_, 0, v_cmp_275_);
return v___f_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertIfNew___redArg(lean_object* v_cmp_277_, lean_object* v_t_278_, lean_object* v_a_279_, lean_object* v_b_280_){
_start:
{
uint8_t v___x_281_; 
lean_inc(v_t_278_);
lean_inc(v_a_279_);
lean_inc_ref(v_cmp_277_);
v___x_281_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_277_, v_a_279_, v_t_278_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_277_, v_a_279_, v_b_280_, v_t_278_);
return v___x_282_;
}
else
{
lean_dec(v_b_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_cmp_277_);
return v_t_278_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertIfNew(lean_object* v_00_u03b1_283_, lean_object* v_00_u03b2_284_, lean_object* v_cmp_285_, lean_object* v_t_286_, lean_object* v_a_287_, lean_object* v_b_288_){
_start:
{
uint8_t v___x_289_; 
lean_inc(v_t_286_);
lean_inc(v_a_287_);
lean_inc_ref(v_cmp_285_);
v___x_289_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_285_, v_a_287_, v_t_286_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
v___x_290_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_285_, v_a_287_, v_b_288_, v_t_286_);
return v___x_290_;
}
else
{
lean_dec(v_b_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_cmp_285_);
return v_t_286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsert___redArg(lean_object* v_cmp_291_, lean_object* v_t_292_, lean_object* v_a_293_, lean_object* v_b_294_){
_start:
{
lean_object* v_sz_295_; lean_object* v_m_296_; lean_object* v___y_298_; 
v_sz_295_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_292_);
v_m_296_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_291_, v_a_293_, v_b_294_, v_t_292_);
if (lean_obj_tag(v_m_296_) == 0)
{
lean_object* v_size_302_; 
v_size_302_ = lean_ctor_get(v_m_296_, 0);
lean_inc(v_size_302_);
v___y_298_ = v_size_302_;
goto v___jp_297_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_unsigned_to_nat(0u);
v___y_298_ = v___x_303_;
goto v___jp_297_;
}
v___jp_297_:
{
uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_nat_dec_eq(v_sz_295_, v___y_298_);
lean_dec(v___y_298_);
lean_dec(v_sz_295_);
v___x_300_ = lean_box(v___x_299_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_m_296_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsert(lean_object* v_00_u03b1_304_, lean_object* v_00_u03b2_305_, lean_object* v_cmp_306_, lean_object* v_t_307_, lean_object* v_a_308_, lean_object* v_b_309_){
_start:
{
lean_object* v_sz_310_; lean_object* v_m_311_; lean_object* v___y_313_; 
v_sz_310_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_307_);
v_m_311_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_306_, v_a_308_, v_b_309_, v_t_307_);
if (lean_obj_tag(v_m_311_) == 0)
{
lean_object* v_size_317_; 
v_size_317_ = lean_ctor_get(v_m_311_, 0);
lean_inc(v_size_317_);
v___y_313_ = v_size_317_;
goto v___jp_312_;
}
else
{
lean_object* v___x_318_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___y_313_ = v___x_318_;
goto v___jp_312_;
}
v___jp_312_:
{
uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_nat_dec_eq(v_sz_310_, v___y_313_);
lean_dec(v___y_313_);
lean_dec(v_sz_310_);
v___x_315_ = lean_box(v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v_m_311_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_319_, lean_object* v_t_320_, lean_object* v_a_321_, lean_object* v_b_322_){
_start:
{
uint8_t v___x_323_; 
lean_inc(v_t_320_);
lean_inc(v_a_321_);
lean_inc_ref(v_cmp_319_);
v___x_323_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_319_, v_a_321_, v_t_320_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_319_, v_a_321_, v_b_322_, v_t_320_);
v___x_325_ = lean_box(v___x_323_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
return v___x_326_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_b_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_cmp_319_);
v___x_327_ = lean_box(v___x_323_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v_t_320_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_cmp_331_, lean_object* v_t_332_, lean_object* v_a_333_, lean_object* v_b_334_){
_start:
{
uint8_t v___x_335_; 
lean_inc(v_t_332_);
lean_inc(v_a_333_);
lean_inc_ref(v_cmp_331_);
v___x_335_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_331_, v_a_333_, v_t_332_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_331_, v_a_333_, v_b_334_, v_t_332_);
v___x_337_ = lean_box(v___x_335_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_336_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec(v_b_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_cmp_331_);
v___x_339_ = lean_box(v___x_335_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_t_332_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_341_, lean_object* v_t_342_, lean_object* v_a_343_, lean_object* v_b_344_){
_start:
{
lean_object* v___x_345_; 
lean_inc(v_a_343_);
lean_inc(v_t_342_);
lean_inc_ref(v_cmp_341_);
v___x_345_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_341_, v_t_342_, v_a_343_);
if (lean_obj_tag(v___x_345_) == 0)
{
uint8_t v___x_346_; 
lean_inc(v_t_342_);
lean_inc(v_a_343_);
lean_inc_ref(v_cmp_341_);
v___x_346_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_341_, v_a_343_, v_t_342_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_341_, v_a_343_, v_b_344_, v_t_342_);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_345_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; 
lean_dec(v_b_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_cmp_341_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_345_);
lean_ctor_set(v___x_349_, 1, v_t_342_);
return v___x_349_;
}
}
else
{
lean_object* v___x_350_; 
lean_dec(v_b_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_cmp_341_);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_345_);
lean_ctor_set(v___x_350_, 1, v_t_342_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_351_, lean_object* v_00_u03b2_352_, lean_object* v_cmp_353_, lean_object* v_inst_354_, lean_object* v_t_355_, lean_object* v_a_356_, lean_object* v_b_357_){
_start:
{
lean_object* v___x_358_; 
lean_inc(v_a_356_);
lean_inc(v_t_355_);
lean_inc_ref(v_cmp_353_);
v___x_358_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_353_, v_t_355_, v_a_356_);
if (lean_obj_tag(v___x_358_) == 0)
{
uint8_t v___x_359_; 
lean_inc(v_t_355_);
lean_inc(v_a_356_);
lean_inc_ref(v_cmp_353_);
v___x_359_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_353_, v_a_356_, v_t_355_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_353_, v_a_356_, v_b_357_, v_t_355_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_358_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; 
lean_dec(v_b_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_cmp_353_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_358_);
lean_ctor_set(v___x_362_, 1, v_t_355_);
return v___x_362_;
}
}
else
{
lean_object* v___x_363_; 
lean_dec(v_b_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_cmp_353_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_358_);
lean_ctor_set(v___x_363_, 1, v_t_355_);
return v___x_363_;
}
}
}
uint8_t l_Std_DTreeMap_contains___redArg(lean_object* v_cmp_364_, lean_object* v_t_365_, lean_object* v_a_366_){
_start:
{
uint8_t v___x_367_; 
v___x_367_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_364_, v_a_366_, v_t_365_);
return v___x_367_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_364_ = stack[0].m_obj;
lean_object* v_t_365_ = stack[1].m_obj;
lean_object* v_a_366_ = stack[2].m_obj;
uint8_t v_res_368_;
v_res_368_ = l_Std_DTreeMap_contains___redArg(v_cmp_364_, v_t_365_, v_a_366_);
stack->m_num = v_res_368_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_contains___redArg___boxed(lean_object* v_cmp_369_, lean_object* v_t_370_, lean_object* v_a_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Std_DTreeMap_contains___redArg(v_cmp_369_, v_t_370_, v_a_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
uint8_t l_Std_DTreeMap_contains(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_cmp_376_, lean_object* v_t_377_, lean_object* v_a_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_376_, v_a_378_, v_t_377_);
return v___x_379_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_376_ = stack[2].m_obj;
lean_object* v_t_377_ = stack[3].m_obj;
lean_object* v_a_378_ = stack[4].m_obj;
uint8_t v_res_380_;
v_res_380_ = l_Std_DTreeMap_contains(lean_box(0), lean_box(0), v_cmp_376_, v_t_377_, v_a_378_);
stack->m_num = v_res_380_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_contains___boxed(lean_object* v_00_u03b1_381_, lean_object* v_00_u03b2_382_, lean_object* v_cmp_383_, lean_object* v_t_384_, lean_object* v_a_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_Std_DTreeMap_contains(v_00_u03b1_381_, v_00_u03b2_382_, v_cmp_383_, v_t_384_, v_a_385_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
lean_object* l_Std_DTreeMap_instMembership___redArg(){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_box(0);
return v___x_389_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_390_;
v_res_390_ = l_Std_DTreeMap_instMembership___redArg();
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___redArg___boxed(lean_object* v___dummy_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_DTreeMap_instMembership___redArg();
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership(lean_object* v_00_u03b1_393_, lean_object* v_00_u03b2_394_, lean_object* v_cmp_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = lean_box(0);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instMembership___boxed(lean_object* v_00_u03b1_397_, lean_object* v_00_u03b2_398_, lean_object* v_cmp_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Std_DTreeMap_instMembership(v_00_u03b1_397_, v_00_u03b2_398_, v_cmp_399_);
lean_dec_ref(v_cmp_399_);
return v_res_400_;
}
}
uint8_t l_Std_DTreeMap_instDecidableMem___redArg(lean_object* v_cmp_401_, lean_object* v_m_402_, lean_object* v_a_403_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_401_, v_a_403_, v_m_402_);
return v___x_404_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_401_ = stack[0].m_obj;
lean_object* v_m_402_ = stack[1].m_obj;
lean_object* v_a_403_ = stack[2].m_obj;
uint8_t v_res_405_;
v_res_405_ = l_Std_DTreeMap_instDecidableMem___redArg(v_cmp_401_, v_m_402_, v_a_403_);
stack->m_num = v_res_405_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_406_, lean_object* v_m_407_, lean_object* v_a_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l_Std_DTreeMap_instDecidableMem___redArg(v_cmp_406_, v_m_407_, v_a_408_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
uint8_t l_Std_DTreeMap_instDecidableMem(lean_object* v_00_u03b1_411_, lean_object* v_00_u03b2_412_, lean_object* v_cmp_413_, lean_object* v_m_414_, lean_object* v_a_415_){
_start:
{
uint8_t v___x_416_; 
v___x_416_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_413_, v_a_415_, v_m_414_);
return v___x_416_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_413_ = stack[2].m_obj;
lean_object* v_m_414_ = stack[3].m_obj;
lean_object* v_a_415_ = stack[4].m_obj;
uint8_t v_res_417_;
v_res_417_ = l_Std_DTreeMap_instDecidableMem(lean_box(0), lean_box(0), v_cmp_413_, v_m_414_, v_a_415_);
stack->m_num = v_res_417_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_cmp_420_, lean_object* v_m_421_, lean_object* v_a_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Std_DTreeMap_instDecidableMem(v_00_u03b1_418_, v_00_u03b2_419_, v_cmp_420_, v_m_421_, v_a_422_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___redArg(lean_object* v_t_425_){
_start:
{
if (lean_obj_tag(v_t_425_) == 0)
{
lean_object* v_size_426_; 
v_size_426_ = lean_ctor_get(v_t_425_, 0);
lean_inc(v_size_426_);
return v_size_426_;
}
else
{
lean_object* v___x_427_; 
v___x_427_ = lean_unsigned_to_nat(0u);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___redArg___boxed(lean_object* v_t_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_DTreeMap_size___redArg(v_t_428_);
lean_dec(v_t_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size(lean_object* v_00_u03b1_430_, lean_object* v_00_u03b2_431_, lean_object* v_cmp_432_, lean_object* v_t_433_){
_start:
{
if (lean_obj_tag(v_t_433_) == 0)
{
lean_object* v_size_434_; 
v_size_434_ = lean_ctor_get(v_t_433_, 0);
lean_inc(v_size_434_);
return v_size_434_;
}
else
{
lean_object* v___x_435_; 
v___x_435_ = lean_unsigned_to_nat(0u);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_size___boxed(lean_object* v_00_u03b1_436_, lean_object* v_00_u03b2_437_, lean_object* v_cmp_438_, lean_object* v_t_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_DTreeMap_size(v_00_u03b1_436_, v_00_u03b2_437_, v_cmp_438_, v_t_439_);
lean_dec(v_t_439_);
lean_dec_ref(v_cmp_438_);
return v_res_440_;
}
}
uint8_t l_Std_DTreeMap_isEmpty___redArg(lean_object* v_t_441_){
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
LEAN_EXPORT void l_Std_DTreeMap_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_441_ = stack[0].m_obj;
uint8_t v_res_444_;
v_res_444_ = l_Std_DTreeMap_isEmpty___redArg(v_t_441_);
stack->m_num = v_res_444_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isEmpty___redArg___boxed(lean_object* v_t_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Std_DTreeMap_isEmpty___redArg(v_t_445_);
lean_dec(v_t_445_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
uint8_t l_Std_DTreeMap_isEmpty(lean_object* v_00_u03b1_448_, lean_object* v_00_u03b2_449_, lean_object* v_cmp_450_, lean_object* v_t_451_){
_start:
{
if (lean_obj_tag(v_t_451_) == 0)
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
}
else
{
uint8_t v___x_453_; 
v___x_453_ = 1;
return v___x_453_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_450_ = stack[2].m_obj;
lean_object* v_t_451_ = stack[3].m_obj;
uint8_t v_res_454_;
v_res_454_ = l_Std_DTreeMap_isEmpty(lean_box(0), lean_box(0), v_cmp_450_, v_t_451_);
stack->m_num = v_res_454_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_455_, lean_object* v_00_u03b2_456_, lean_object* v_cmp_457_, lean_object* v_t_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_Std_DTreeMap_isEmpty(v_00_u03b1_455_, v_00_u03b2_456_, v_cmp_457_, v_t_458_);
lean_dec(v_t_458_);
lean_dec_ref(v_cmp_457_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_erase___redArg(lean_object* v_cmp_461_, lean_object* v_t_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_461_, v_a_463_, v_t_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_erase(lean_object* v_00_u03b1_465_, lean_object* v_00_u03b2_466_, lean_object* v_cmp_467_, lean_object* v_t_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_467_, v_a_469_, v_t_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x3f___redArg(lean_object* v_cmp_471_, lean_object* v_t_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_471_, v_t_472_, v_a_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x3f(lean_object* v_00_u03b1_475_, lean_object* v_00_u03b2_476_, lean_object* v_cmp_477_, lean_object* v_inst_478_, lean_object* v_t_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_477_, v_t_479_, v_a_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get___redArg(lean_object* v_cmp_482_, lean_object* v_t_483_, lean_object* v_a_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_482_, v_t_483_, v_a_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get(lean_object* v_00_u03b1_486_, lean_object* v_00_u03b2_487_, lean_object* v_cmp_488_, lean_object* v_inst_489_, lean_object* v_t_490_, lean_object* v_a_491_, lean_object* v_h_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_488_, v_t_490_, v_a_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___redArg(lean_object* v_cmp_494_, lean_object* v_t_495_, lean_object* v_a_496_, lean_object* v_inst_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_494_, v_t_495_, v_a_496_, v_inst_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___redArg___boxed(lean_object* v_cmp_499_, lean_object* v_t_500_, lean_object* v_a_501_, lean_object* v_inst_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_DTreeMap_get_x21___redArg(v_cmp_499_, v_t_500_, v_a_501_, v_inst_502_);
lean_dec(v_inst_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21(lean_object* v_00_u03b1_504_, lean_object* v_00_u03b2_505_, lean_object* v_cmp_506_, lean_object* v_inst_507_, lean_object* v_t_508_, lean_object* v_a_509_, lean_object* v_inst_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_506_, v_t_508_, v_a_509_, v_inst_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_get_x21___boxed(lean_object* v_00_u03b1_512_, lean_object* v_00_u03b2_513_, lean_object* v_cmp_514_, lean_object* v_inst_515_, lean_object* v_t_516_, lean_object* v_a_517_, lean_object* v_inst_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_DTreeMap_get_x21(v_00_u03b1_512_, v_00_u03b2_513_, v_cmp_514_, v_inst_515_, v_t_516_, v_a_517_, v_inst_518_);
lean_dec(v_inst_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg(lean_object* v_cmp_520_, lean_object* v_t_521_, lean_object* v_a_522_, lean_object* v_fallback_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_520_, v_t_521_, v_a_522_, v_fallback_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___redArg___boxed(lean_object* v_cmp_525_, lean_object* v_t_526_, lean_object* v_a_527_, lean_object* v_fallback_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_DTreeMap_getD___redArg(v_cmp_525_, v_t_526_, v_a_527_, v_fallback_528_);
lean_dec(v_fallback_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_cmp_532_, lean_object* v_inst_533_, lean_object* v_t_534_, lean_object* v_a_535_, lean_object* v_fallback_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_532_, v_t_534_, v_a_535_, v_fallback_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getD___boxed(lean_object* v_00_u03b1_538_, lean_object* v_00_u03b2_539_, lean_object* v_cmp_540_, lean_object* v_inst_541_, lean_object* v_t_542_, lean_object* v_a_543_, lean_object* v_fallback_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Std_DTreeMap_getD(v_00_u03b1_538_, v_00_u03b2_539_, v_cmp_540_, v_inst_541_, v_t_542_, v_a_543_, v_fallback_544_);
lean_dec(v_fallback_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f___redArg(lean_object* v_cmp_546_, lean_object* v_t_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_546_, v_t_547_, v_a_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x3f(lean_object* v_00_u03b1_550_, lean_object* v_00_u03b2_551_, lean_object* v_cmp_552_, lean_object* v_t_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_552_, v_t_553_, v_a_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey___redArg(lean_object* v_cmp_556_, lean_object* v_t_557_, lean_object* v_a_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_556_, v_t_557_, v_a_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey(lean_object* v_00_u03b1_560_, lean_object* v_00_u03b2_561_, lean_object* v_cmp_562_, lean_object* v_t_563_, lean_object* v_a_564_, lean_object* v_h_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_562_, v_t_563_, v_a_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___redArg(lean_object* v_cmp_567_, lean_object* v_inst_568_, lean_object* v_t_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_567_, v_t_569_, v_a_570_, v_inst_568_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___redArg___boxed(lean_object* v_cmp_572_, lean_object* v_inst_573_, lean_object* v_t_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_DTreeMap_getKey_x21___redArg(v_cmp_572_, v_inst_573_, v_t_574_, v_a_575_);
lean_dec(v_inst_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21(lean_object* v_00_u03b1_577_, lean_object* v_00_u03b2_578_, lean_object* v_cmp_579_, lean_object* v_inst_580_, lean_object* v_t_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_579_, v_t_581_, v_a_582_, v_inst_580_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKey_x21___boxed(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_cmp_586_, lean_object* v_inst_587_, lean_object* v_t_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_DTreeMap_getKey_x21(v_00_u03b1_584_, v_00_u03b2_585_, v_cmp_586_, v_inst_587_, v_t_588_, v_a_589_);
lean_dec(v_inst_587_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___redArg(lean_object* v_cmp_591_, lean_object* v_t_592_, lean_object* v_a_593_, lean_object* v_fallback_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_591_, v_t_592_, v_a_593_, v_fallback_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_596_, lean_object* v_t_597_, lean_object* v_a_598_, lean_object* v_fallback_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_DTreeMap_getKeyD___redArg(v_cmp_596_, v_t_597_, v_a_598_, v_fallback_599_);
lean_dec(v_fallback_599_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD(lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v_cmp_603_, lean_object* v_t_604_, lean_object* v_a_605_, lean_object* v_fallback_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_603_, v_t_604_, v_a_605_, v_fallback_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_cmp_610_, lean_object* v_t_611_, lean_object* v_a_612_, lean_object* v_fallback_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_DTreeMap_getKeyD(v_00_u03b1_608_, v_00_u03b2_609_, v_cmp_610_, v_t_611_, v_a_612_, v_fallback_613_);
lean_dec(v_fallback_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x3f___redArg(lean_object* v_cmp_615_, lean_object* v_t_616_, lean_object* v_a_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_615_, v_t_616_, v_a_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x3f(lean_object* v_00_u03b1_619_, lean_object* v_00_u03b2_620_, lean_object* v_cmp_621_, lean_object* v_t_622_, lean_object* v_a_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_621_, v_t_622_, v_a_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry___redArg(lean_object* v_cmp_625_, lean_object* v_t_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_625_, v_t_626_, v_a_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry(lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_cmp_631_, lean_object* v_t_632_, lean_object* v_a_633_, lean_object* v_h_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_631_, v_t_632_, v_a_633_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___redArg(lean_object* v_cmp_636_, lean_object* v_t_637_, lean_object* v_a_638_, lean_object* v_fallback_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_636_, v_t_637_, v_a_638_, v_fallback_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___redArg___boxed(lean_object* v_cmp_641_, lean_object* v_t_642_, lean_object* v_a_643_, lean_object* v_fallback_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_DTreeMap_getEntryD___redArg(v_cmp_641_, v_t_642_, v_a_643_, v_fallback_644_);
lean_dec_ref(v_fallback_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD(lean_object* v_00_u03b1_646_, lean_object* v_00_u03b2_647_, lean_object* v_cmp_648_, lean_object* v_t_649_, lean_object* v_a_650_, lean_object* v_fallback_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_648_, v_t_649_, v_a_650_, v_fallback_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryD___boxed(lean_object* v_00_u03b1_653_, lean_object* v_00_u03b2_654_, lean_object* v_cmp_655_, lean_object* v_t_656_, lean_object* v_a_657_, lean_object* v_fallback_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_DTreeMap_getEntryD(v_00_u03b1_653_, v_00_u03b2_654_, v_cmp_655_, v_t_656_, v_a_657_, v_fallback_658_);
lean_dec_ref(v_fallback_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___redArg(lean_object* v_cmp_660_, lean_object* v_inst_661_, lean_object* v_t_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_660_, v_inst_661_, v_t_662_, v_a_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___redArg___boxed(lean_object* v_cmp_665_, lean_object* v_inst_666_, lean_object* v_t_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Std_DTreeMap_getEntry_x21___redArg(v_cmp_665_, v_inst_666_, v_t_667_, v_a_668_);
lean_dec_ref(v_inst_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21(lean_object* v_00_u03b1_670_, lean_object* v_00_u03b2_671_, lean_object* v_cmp_672_, lean_object* v_inst_673_, lean_object* v_t_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_672_, v_inst_673_, v_t_674_, v_a_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntry_x21___boxed(lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_cmp_679_, lean_object* v_inst_680_, lean_object* v_t_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_DTreeMap_getEntry_x21(v_00_u03b1_677_, v_00_u03b2_678_, v_cmp_679_, v_inst_680_, v_t_681_, v_a_682_);
lean_dec_ref(v_inst_680_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___redArg(lean_object* v_t_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_DTreeMap_minEntry_x3f___redArg(v_t_686_);
lean_dec(v_t_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_cmp_690_, lean_object* v_t_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_693_, lean_object* v_00_u03b2_694_, lean_object* v_cmp_695_, lean_object* v_t_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_DTreeMap_minEntry_x3f(v_00_u03b1_693_, v_00_u03b2_694_, v_cmp_695_, v_t_696_);
lean_dec(v_t_696_);
lean_dec_ref(v_cmp_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___redArg(lean_object* v_t_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___redArg___boxed(lean_object* v_t_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Std_DTreeMap_minEntry___redArg(v_t_700_);
lean_dec(v_t_700_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry(lean_object* v_00_u03b1_702_, lean_object* v_00_u03b2_703_, lean_object* v_cmp_704_, lean_object* v_t_705_, lean_object* v_h_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_705_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry___boxed(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_cmp_710_, lean_object* v_t_711_, lean_object* v_h_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Std_DTreeMap_minEntry(v_00_u03b1_708_, v_00_u03b2_709_, v_cmp_710_, v_t_711_, v_h_712_);
lean_dec(v_t_711_);
lean_dec_ref(v_cmp_710_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___redArg(lean_object* v_inst_714_, lean_object* v_t_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_714_, v_t_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_717_, lean_object* v_t_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_DTreeMap_minEntry_x21___redArg(v_inst_717_, v_t_718_);
lean_dec(v_t_718_);
lean_dec_ref(v_inst_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21(lean_object* v_00_u03b1_720_, lean_object* v_00_u03b2_721_, lean_object* v_cmp_722_, lean_object* v_inst_723_, lean_object* v_t_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_723_, v_t_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_726_, lean_object* v_00_u03b2_727_, lean_object* v_cmp_728_, lean_object* v_inst_729_, lean_object* v_t_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_DTreeMap_minEntry_x21(v_00_u03b1_726_, v_00_u03b2_727_, v_cmp_728_, v_inst_729_, v_t_730_);
lean_dec(v_t_730_);
lean_dec_ref(v_inst_729_);
lean_dec_ref(v_cmp_728_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___redArg(lean_object* v_t_732_, lean_object* v_fallback_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_732_, v_fallback_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___redArg___boxed(lean_object* v_t_735_, lean_object* v_fallback_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Std_DTreeMap_minEntryD___redArg(v_t_735_, v_fallback_736_);
lean_dec_ref(v_fallback_736_);
lean_dec(v_t_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD(lean_object* v_00_u03b1_738_, lean_object* v_00_u03b2_739_, lean_object* v_cmp_740_, lean_object* v_t_741_, lean_object* v_fallback_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_741_, v_fallback_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_744_, lean_object* v_00_u03b2_745_, lean_object* v_cmp_746_, lean_object* v_t_747_, lean_object* v_fallback_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_DTreeMap_minEntryD(v_00_u03b1_744_, v_00_u03b2_745_, v_cmp_746_, v_t_747_, v_fallback_748_);
lean_dec_ref(v_fallback_748_);
lean_dec(v_t_747_);
lean_dec_ref(v_cmp_746_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___redArg(lean_object* v_t_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_DTreeMap_maxEntry_x3f___redArg(v_t_752_);
lean_dec(v_t_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_754_, lean_object* v_00_u03b2_755_, lean_object* v_cmp_756_, lean_object* v_t_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_cmp_761_, lean_object* v_t_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_DTreeMap_maxEntry_x3f(v_00_u03b1_759_, v_00_u03b2_760_, v_cmp_761_, v_t_762_);
lean_dec(v_t_762_);
lean_dec_ref(v_cmp_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___redArg(lean_object* v_t_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___redArg___boxed(lean_object* v_t_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_DTreeMap_maxEntry___redArg(v_t_766_);
lean_dec(v_t_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry(lean_object* v_00_u03b1_768_, lean_object* v_00_u03b2_769_, lean_object* v_cmp_770_, lean_object* v_t_771_, lean_object* v_h_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_774_, lean_object* v_00_u03b2_775_, lean_object* v_cmp_776_, lean_object* v_t_777_, lean_object* v_h_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_DTreeMap_maxEntry(v_00_u03b1_774_, v_00_u03b2_775_, v_cmp_776_, v_t_777_, v_h_778_);
lean_dec(v_t_777_);
lean_dec_ref(v_cmp_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___redArg(lean_object* v_inst_780_, lean_object* v_t_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_780_, v_t_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_783_, lean_object* v_t_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_DTreeMap_maxEntry_x21___redArg(v_inst_783_, v_t_784_);
lean_dec(v_t_784_);
lean_dec_ref(v_inst_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21(lean_object* v_00_u03b1_786_, lean_object* v_00_u03b2_787_, lean_object* v_cmp_788_, lean_object* v_inst_789_, lean_object* v_t_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_789_, v_t_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_cmp_794_, lean_object* v_inst_795_, lean_object* v_t_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_DTreeMap_maxEntry_x21(v_00_u03b1_792_, v_00_u03b2_793_, v_cmp_794_, v_inst_795_, v_t_796_);
lean_dec(v_t_796_);
lean_dec_ref(v_inst_795_);
lean_dec_ref(v_cmp_794_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___redArg(lean_object* v_t_798_, lean_object* v_fallback_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_798_, v_fallback_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_801_, lean_object* v_fallback_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_DTreeMap_maxEntryD___redArg(v_t_801_, v_fallback_802_);
lean_dec_ref(v_fallback_802_);
lean_dec(v_t_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD(lean_object* v_00_u03b1_804_, lean_object* v_00_u03b2_805_, lean_object* v_cmp_806_, lean_object* v_t_807_, lean_object* v_fallback_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_807_, v_fallback_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_810_, lean_object* v_00_u03b2_811_, lean_object* v_cmp_812_, lean_object* v_t_813_, lean_object* v_fallback_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_DTreeMap_maxEntryD(v_00_u03b1_810_, v_00_u03b2_811_, v_cmp_812_, v_t_813_, v_fallback_814_);
lean_dec_ref(v_fallback_814_);
lean_dec(v_t_813_);
lean_dec_ref(v_cmp_812_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___redArg(lean_object* v_t_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_DTreeMap_minKey_x3f___redArg(v_t_818_);
lean_dec(v_t_818_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f(lean_object* v_00_u03b1_820_, lean_object* v_00_u03b2_821_, lean_object* v_cmp_822_, lean_object* v_t_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_cmp_827_, lean_object* v_t_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_DTreeMap_minKey_x3f(v_00_u03b1_825_, v_00_u03b2_826_, v_cmp_827_, v_t_828_);
lean_dec(v_t_828_);
lean_dec_ref(v_cmp_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___redArg(lean_object* v_t_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___redArg___boxed(lean_object* v_t_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_DTreeMap_minKey___redArg(v_t_832_);
lean_dec(v_t_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey(lean_object* v_00_u03b1_834_, lean_object* v_00_u03b2_835_, lean_object* v_cmp_836_, lean_object* v_t_837_, lean_object* v_h_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey___boxed(lean_object* v_00_u03b1_840_, lean_object* v_00_u03b2_841_, lean_object* v_cmp_842_, lean_object* v_t_843_, lean_object* v_h_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_DTreeMap_minKey(v_00_u03b1_840_, v_00_u03b2_841_, v_cmp_842_, v_t_843_, v_h_844_);
lean_dec(v_t_843_);
lean_dec_ref(v_cmp_842_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___redArg(lean_object* v_inst_846_, lean_object* v_t_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_846_, v_t_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_849_, lean_object* v_t_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Std_DTreeMap_minKey_x21___redArg(v_inst_849_, v_t_850_);
lean_dec(v_t_850_);
lean_dec(v_inst_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21(lean_object* v_00_u03b1_852_, lean_object* v_00_u03b2_853_, lean_object* v_cmp_854_, lean_object* v_inst_855_, lean_object* v_t_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_855_, v_t_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_858_, lean_object* v_00_u03b2_859_, lean_object* v_cmp_860_, lean_object* v_inst_861_, lean_object* v_t_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_DTreeMap_minKey_x21(v_00_u03b1_858_, v_00_u03b2_859_, v_cmp_860_, v_inst_861_, v_t_862_);
lean_dec(v_t_862_);
lean_dec(v_inst_861_);
lean_dec_ref(v_cmp_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___redArg(lean_object* v_t_864_, lean_object* v_fallback_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_864_, v_fallback_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___redArg___boxed(lean_object* v_t_867_, lean_object* v_fallback_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_DTreeMap_minKeyD___redArg(v_t_867_, v_fallback_868_);
lean_dec(v_fallback_868_);
lean_dec(v_t_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD(lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_cmp_872_, lean_object* v_t_873_, lean_object* v_fallback_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_873_, v_fallback_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_876_, lean_object* v_00_u03b2_877_, lean_object* v_cmp_878_, lean_object* v_t_879_, lean_object* v_fallback_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_DTreeMap_minKeyD(v_00_u03b1_876_, v_00_u03b2_877_, v_cmp_878_, v_t_879_, v_fallback_880_);
lean_dec(v_fallback_880_);
lean_dec(v_t_879_);
lean_dec_ref(v_cmp_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___redArg(lean_object* v_t_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_DTreeMap_maxKey_x3f___redArg(v_t_884_);
lean_dec(v_t_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f(lean_object* v_00_u03b1_886_, lean_object* v_00_u03b2_887_, lean_object* v_cmp_888_, lean_object* v_t_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_cmp_893_, lean_object* v_t_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_DTreeMap_maxKey_x3f(v_00_u03b1_891_, v_00_u03b2_892_, v_cmp_893_, v_t_894_);
lean_dec(v_t_894_);
lean_dec_ref(v_cmp_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___redArg(lean_object* v_t_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___redArg___boxed(lean_object* v_t_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_DTreeMap_maxKey___redArg(v_t_898_);
lean_dec(v_t_898_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey(lean_object* v_00_u03b1_900_, lean_object* v_00_u03b2_901_, lean_object* v_cmp_902_, lean_object* v_t_903_, lean_object* v_h_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey___boxed(lean_object* v_00_u03b1_906_, lean_object* v_00_u03b2_907_, lean_object* v_cmp_908_, lean_object* v_t_909_, lean_object* v_h_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Std_DTreeMap_maxKey(v_00_u03b1_906_, v_00_u03b2_907_, v_cmp_908_, v_t_909_, v_h_910_);
lean_dec(v_t_909_);
lean_dec_ref(v_cmp_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___redArg(lean_object* v_inst_912_, lean_object* v_t_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_912_, v_t_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_915_, lean_object* v_t_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Std_DTreeMap_maxKey_x21___redArg(v_inst_915_, v_t_916_);
lean_dec(v_t_916_);
lean_dec(v_inst_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21(lean_object* v_00_u03b1_918_, lean_object* v_00_u03b2_919_, lean_object* v_cmp_920_, lean_object* v_inst_921_, lean_object* v_t_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_921_, v_t_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_cmp_926_, lean_object* v_inst_927_, lean_object* v_t_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_DTreeMap_maxKey_x21(v_00_u03b1_924_, v_00_u03b2_925_, v_cmp_926_, v_inst_927_, v_t_928_);
lean_dec(v_t_928_);
lean_dec(v_inst_927_);
lean_dec_ref(v_cmp_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___redArg(lean_object* v_t_930_, lean_object* v_fallback_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_930_, v_fallback_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_933_, lean_object* v_fallback_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_DTreeMap_maxKeyD___redArg(v_t_933_, v_fallback_934_);
lean_dec(v_fallback_934_);
lean_dec(v_t_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD(lean_object* v_00_u03b1_936_, lean_object* v_00_u03b2_937_, lean_object* v_cmp_938_, lean_object* v_t_939_, lean_object* v_fallback_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_939_, v_fallback_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_942_, lean_object* v_00_u03b2_943_, lean_object* v_cmp_944_, lean_object* v_t_945_, lean_object* v_fallback_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Std_DTreeMap_maxKeyD(v_00_u03b1_942_, v_00_u03b2_943_, v_cmp_944_, v_t_945_, v_fallback_946_);
lean_dec(v_fallback_946_);
lean_dec(v_t_945_);
lean_dec_ref(v_cmp_944_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_948_, lean_object* v_n_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_948_, v_n_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_951_, lean_object* v_n_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_DTreeMap_entryAtIdx_x3f___redArg(v_t_951_, v_n_952_);
lean_dec(v_t_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_954_, lean_object* v_00_u03b2_955_, lean_object* v_cmp_956_, lean_object* v_t_957_, lean_object* v_n_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_957_, v_n_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_960_, lean_object* v_00_u03b2_961_, lean_object* v_cmp_962_, lean_object* v_t_963_, lean_object* v_n_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_DTreeMap_entryAtIdx_x3f(v_00_u03b1_960_, v_00_u03b2_961_, v_cmp_962_, v_t_963_, v_n_964_);
lean_dec(v_t_963_);
lean_dec_ref(v_cmp_962_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___redArg(lean_object* v_t_966_, lean_object* v_n_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_966_, v_n_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_969_, lean_object* v_n_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Std_DTreeMap_entryAtIdx___redArg(v_t_969_, v_n_970_);
lean_dec(v_t_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx(lean_object* v_00_u03b1_972_, lean_object* v_00_u03b2_973_, lean_object* v_cmp_974_, lean_object* v_t_975_, lean_object* v_n_976_, lean_object* v_h_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_975_, v_n_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_979_, lean_object* v_00_u03b2_980_, lean_object* v_cmp_981_, lean_object* v_t_982_, lean_object* v_n_983_, lean_object* v_h_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_DTreeMap_entryAtIdx(v_00_u03b1_979_, v_00_u03b2_980_, v_cmp_981_, v_t_982_, v_n_983_, v_h_984_);
lean_dec(v_t_982_);
lean_dec_ref(v_cmp_981_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_986_, lean_object* v_t_987_, lean_object* v_n_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_986_, v_t_987_, v_n_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_990_, lean_object* v_t_991_, lean_object* v_n_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_DTreeMap_entryAtIdx_x21___redArg(v_inst_990_, v_t_991_, v_n_992_);
lean_dec(v_t_991_);
lean_dec_ref(v_inst_990_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_994_, lean_object* v_00_u03b2_995_, lean_object* v_cmp_996_, lean_object* v_inst_997_, lean_object* v_t_998_, lean_object* v_n_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_997_, v_t_998_, v_n_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_1001_, lean_object* v_00_u03b2_1002_, lean_object* v_cmp_1003_, lean_object* v_inst_1004_, lean_object* v_t_1005_, lean_object* v_n_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_DTreeMap_entryAtIdx_x21(v_00_u03b1_1001_, v_00_u03b2_1002_, v_cmp_1003_, v_inst_1004_, v_t_1005_, v_n_1006_);
lean_dec(v_t_1005_);
lean_dec_ref(v_inst_1004_);
lean_dec_ref(v_cmp_1003_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___redArg(lean_object* v_t_1008_, lean_object* v_n_1009_, lean_object* v_fallback_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_1008_, v_n_1009_, v_fallback_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_1012_, lean_object* v_n_1013_, lean_object* v_fallback_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Std_DTreeMap_entryAtIdxD___redArg(v_t_1012_, v_n_1013_, v_fallback_1014_);
lean_dec_ref(v_fallback_1014_);
lean_dec(v_t_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03b2_1017_, lean_object* v_cmp_1018_, lean_object* v_t_1019_, lean_object* v_n_1020_, lean_object* v_fallback_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_1019_, v_n_1020_, v_fallback_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_1023_, lean_object* v_00_u03b2_1024_, lean_object* v_cmp_1025_, lean_object* v_t_1026_, lean_object* v_n_1027_, lean_object* v_fallback_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Std_DTreeMap_entryAtIdxD(v_00_u03b1_1023_, v_00_u03b2_1024_, v_cmp_1025_, v_t_1026_, v_n_1027_, v_fallback_1028_);
lean_dec_ref(v_fallback_1028_);
lean_dec(v_t_1026_);
lean_dec_ref(v_cmp_1025_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_1030_, lean_object* v_n_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_1030_, v_n_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_1033_, lean_object* v_n_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Std_DTreeMap_keyAtIdx_x3f___redArg(v_t_1033_, v_n_1034_);
lean_dec(v_t_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_1036_, lean_object* v_00_u03b2_1037_, lean_object* v_cmp_1038_, lean_object* v_t_1039_, lean_object* v_n_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_1039_, v_n_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_cmp_1044_, lean_object* v_t_1045_, lean_object* v_n_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Std_DTreeMap_keyAtIdx_x3f(v_00_u03b1_1042_, v_00_u03b2_1043_, v_cmp_1044_, v_t_1045_, v_n_1046_);
lean_dec(v_t_1045_);
lean_dec_ref(v_cmp_1044_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___redArg(lean_object* v_t_1048_, lean_object* v_n_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1048_, v_n_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_1051_, lean_object* v_n_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Std_DTreeMap_keyAtIdx___redArg(v_t_1051_, v_n_1052_);
lean_dec(v_t_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx(lean_object* v_00_u03b1_1054_, lean_object* v_00_u03b2_1055_, lean_object* v_cmp_1056_, lean_object* v_t_1057_, lean_object* v_n_1058_, lean_object* v_h_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_1057_, v_n_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_00_u03b2_1062_, lean_object* v_cmp_1063_, lean_object* v_t_1064_, lean_object* v_n_1065_, lean_object* v_h_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Std_DTreeMap_keyAtIdx(v_00_u03b1_1061_, v_00_u03b2_1062_, v_cmp_1063_, v_t_1064_, v_n_1065_, v_h_1066_);
lean_dec(v_t_1064_);
lean_dec_ref(v_cmp_1063_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_1068_, lean_object* v_t_1069_, lean_object* v_n_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1068_, v_t_1069_, v_n_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_1072_, lean_object* v_t_1073_, lean_object* v_n_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Std_DTreeMap_keyAtIdx_x21___redArg(v_inst_1072_, v_t_1073_, v_n_1074_);
lean_dec(v_t_1073_);
lean_dec(v_inst_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_1076_, lean_object* v_00_u03b2_1077_, lean_object* v_cmp_1078_, lean_object* v_inst_1079_, lean_object* v_t_1080_, lean_object* v_n_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_1079_, v_t_1080_, v_n_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_1083_, lean_object* v_00_u03b2_1084_, lean_object* v_cmp_1085_, lean_object* v_inst_1086_, lean_object* v_t_1087_, lean_object* v_n_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Std_DTreeMap_keyAtIdx_x21(v_00_u03b1_1083_, v_00_u03b2_1084_, v_cmp_1085_, v_inst_1086_, v_t_1087_, v_n_1088_);
lean_dec(v_t_1087_);
lean_dec(v_inst_1086_);
lean_dec_ref(v_cmp_1085_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___redArg(lean_object* v_t_1090_, lean_object* v_n_1091_, lean_object* v_fallback_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1090_, v_n_1091_, v_fallback_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_1094_, lean_object* v_n_1095_, lean_object* v_fallback_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_DTreeMap_keyAtIdxD___redArg(v_t_1094_, v_n_1095_, v_fallback_1096_);
lean_dec(v_fallback_1096_);
lean_dec(v_t_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD(lean_object* v_00_u03b1_1098_, lean_object* v_00_u03b2_1099_, lean_object* v_cmp_1100_, lean_object* v_t_1101_, lean_object* v_n_1102_, lean_object* v_fallback_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1101_, v_n_1102_, v_fallback_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_1105_, lean_object* v_00_u03b2_1106_, lean_object* v_cmp_1107_, lean_object* v_t_1108_, lean_object* v_n_1109_, lean_object* v_fallback_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Std_DTreeMap_keyAtIdxD(v_00_u03b1_1105_, v_00_u03b2_1106_, v_cmp_1107_, v_t_1108_, v_n_1109_, v_fallback_1110_);
lean_dec(v_fallback_1110_);
lean_dec(v_t_1108_);
lean_dec_ref(v_cmp_1107_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_1112_, lean_object* v_t_1113_, lean_object* v_k_1114_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_box(0);
v___x_1116_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1112_, v_k_1114_, v___x_1115_, v_t_1113_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_1117_, lean_object* v_00_u03b2_1118_, lean_object* v_cmp_1119_, lean_object* v_t_1120_, lean_object* v_k_1121_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_box(0);
v___x_1123_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1119_, v_k_1121_, v___x_1122_, v_t_1120_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_1124_, lean_object* v_t_1125_, lean_object* v_k_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_box(0);
v___x_1128_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1124_, v_k_1126_, v___x_1127_, v_t_1125_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_cmp_1131_, lean_object* v_t_1132_, lean_object* v_k_1133_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_box(0);
v___x_1135_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1131_, v_k_1133_, v___x_1134_, v_t_1132_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1136_, lean_object* v_t_1137_, lean_object* v_k_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_box(0);
v___x_1140_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1136_, v_k_1138_, v___x_1139_, v_t_1137_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1141_, lean_object* v_00_u03b2_1142_, lean_object* v_cmp_1143_, lean_object* v_t_1144_, lean_object* v_k_1145_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_box(0);
v___x_1147_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1143_, v_k_1145_, v___x_1146_, v_t_1144_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1148_, lean_object* v_t_1149_, lean_object* v_k_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_box(0);
v___x_1152_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1148_, v_k_1150_, v___x_1151_, v_t_1149_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1153_, lean_object* v_00_u03b2_1154_, lean_object* v_cmp_1155_, lean_object* v_t_1156_, lean_object* v_k_1157_){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_box(0);
v___x_1159_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1155_, v_k_1157_, v___x_1158_, v_t_1156_);
return v___x_1159_;
}
}
static lean_object* _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1163_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1164_ = lean_unsigned_to_nat(14u);
v___x_1165_ = lean_unsigned_to_nat(22u);
v___x_1166_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1167_ = ((lean_object*)(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1168_ = l_mkPanicMessageWithDecl(v___x_1167_, v___x_1166_, v___x_1165_, v___x_1164_, v___x_1163_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1169_, lean_object* v_inst_1170_, lean_object* v_t_1171_, lean_object* v_k_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_box(0);
v___x_1174_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1169_, v_k_1172_, v___x_1173_, v_t_1171_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1176_ = l_panic___redArg(v_inst_1170_, v___x_1175_);
return v___x_1176_;
}
else
{
lean_object* v_val_1177_; 
v_val_1177_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_val_1177_);
lean_dec_ref_known(v___x_1174_, 1);
return v_val_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1178_, lean_object* v_inst_1179_, lean_object* v_t_1180_, lean_object* v_k_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Std_DTreeMap_getEntryGE_x21___redArg(v_cmp_1178_, v_inst_1179_, v_t_1180_, v_k_1181_);
lean_dec_ref(v_inst_1179_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_cmp_1185_, lean_object* v_inst_1186_, lean_object* v_t_1187_, lean_object* v_k_1188_){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_box(0);
v___x_1190_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1185_, v_k_1188_, v___x_1189_, v_t_1187_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1192_ = l_panic___redArg(v_inst_1186_, v___x_1191_);
return v___x_1192_;
}
else
{
lean_object* v_val_1193_; 
v_val_1193_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_val_1193_);
lean_dec_ref_known(v___x_1190_, 1);
return v_val_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_cmp_1196_, lean_object* v_inst_1197_, lean_object* v_t_1198_, lean_object* v_k_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_DTreeMap_getEntryGE_x21(v_00_u03b1_1194_, v_00_u03b2_1195_, v_cmp_1196_, v_inst_1197_, v_t_1198_, v_k_1199_);
lean_dec_ref(v_inst_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1201_, lean_object* v_inst_1202_, lean_object* v_t_1203_, lean_object* v_k_1204_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_box(0);
v___x_1206_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1201_, v_k_1204_, v___x_1205_, v_t_1203_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1208_ = l_panic___redArg(v_inst_1202_, v___x_1207_);
return v___x_1208_;
}
else
{
lean_object* v_val_1209_; 
v_val_1209_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_val_1209_);
lean_dec_ref_known(v___x_1206_, 1);
return v_val_1209_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1210_, lean_object* v_inst_1211_, lean_object* v_t_1212_, lean_object* v_k_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Std_DTreeMap_getEntryGT_x21___redArg(v_cmp_1210_, v_inst_1211_, v_t_1212_, v_k_1213_);
lean_dec_ref(v_inst_1211_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1215_, lean_object* v_00_u03b2_1216_, lean_object* v_cmp_1217_, lean_object* v_inst_1218_, lean_object* v_t_1219_, lean_object* v_k_1220_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1217_, v_k_1220_, v___x_1221_, v_t_1219_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1224_ = l_panic___redArg(v_inst_1218_, v___x_1223_);
return v___x_1224_;
}
else
{
lean_object* v_val_1225_; 
v_val_1225_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v___x_1222_, 1);
return v_val_1225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1226_, lean_object* v_00_u03b2_1227_, lean_object* v_cmp_1228_, lean_object* v_inst_1229_, lean_object* v_t_1230_, lean_object* v_k_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Std_DTreeMap_getEntryGT_x21(v_00_u03b1_1226_, v_00_u03b2_1227_, v_cmp_1228_, v_inst_1229_, v_t_1230_, v_k_1231_);
lean_dec_ref(v_inst_1229_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1233_, lean_object* v_inst_1234_, lean_object* v_t_1235_, lean_object* v_k_1236_){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_box(0);
v___x_1238_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1233_, v_k_1236_, v___x_1237_, v_t_1235_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1240_ = l_panic___redArg(v_inst_1234_, v___x_1239_);
return v___x_1240_;
}
else
{
lean_object* v_val_1241_; 
v_val_1241_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_val_1241_);
lean_dec_ref_known(v___x_1238_, 1);
return v_val_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1242_, lean_object* v_inst_1243_, lean_object* v_t_1244_, lean_object* v_k_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Std_DTreeMap_getEntryLE_x21___redArg(v_cmp_1242_, v_inst_1243_, v_t_1244_, v_k_1245_);
lean_dec_ref(v_inst_1243_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1247_, lean_object* v_00_u03b2_1248_, lean_object* v_cmp_1249_, lean_object* v_inst_1250_, lean_object* v_t_1251_, lean_object* v_k_1252_){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_box(0);
v___x_1254_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1249_, v_k_1252_, v___x_1253_, v_t_1251_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1258_, lean_object* v_00_u03b2_1259_, lean_object* v_cmp_1260_, lean_object* v_inst_1261_, lean_object* v_t_1262_, lean_object* v_k_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Std_DTreeMap_getEntryLE_x21(v_00_u03b1_1258_, v_00_u03b2_1259_, v_cmp_1260_, v_inst_1261_, v_t_1262_, v_k_1263_);
lean_dec_ref(v_inst_1261_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1265_, lean_object* v_inst_1266_, lean_object* v_t_1267_, lean_object* v_k_1268_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_box(0);
v___x_1270_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1265_, v_k_1268_, v___x_1269_, v_t_1267_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1272_ = l_panic___redArg(v_inst_1266_, v___x_1271_);
return v___x_1272_;
}
else
{
lean_object* v_val_1273_; 
v_val_1273_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v___x_1270_, 1);
return v_val_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1274_, lean_object* v_inst_1275_, lean_object* v_t_1276_, lean_object* v_k_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Std_DTreeMap_getEntryLT_x21___redArg(v_cmp_1274_, v_inst_1275_, v_t_1276_, v_k_1277_);
lean_dec_ref(v_inst_1275_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1279_, lean_object* v_00_u03b2_1280_, lean_object* v_cmp_1281_, lean_object* v_inst_1282_, lean_object* v_t_1283_, lean_object* v_k_1284_){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_box(0);
v___x_1286_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1281_, v_k_1284_, v___x_1285_, v_t_1283_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1288_ = l_panic___redArg(v_inst_1282_, v___x_1287_);
return v___x_1288_;
}
else
{
lean_object* v_val_1289_; 
v_val_1289_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_val_1289_);
lean_dec_ref_known(v___x_1286_, 1);
return v_val_1289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1290_, lean_object* v_00_u03b2_1291_, lean_object* v_cmp_1292_, lean_object* v_inst_1293_, lean_object* v_t_1294_, lean_object* v_k_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Std_DTreeMap_getEntryLT_x21(v_00_u03b1_1290_, v_00_u03b2_1291_, v_cmp_1292_, v_inst_1293_, v_t_1294_, v_k_1295_);
lean_dec_ref(v_inst_1293_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___redArg(lean_object* v_cmp_1297_, lean_object* v_t_1298_, lean_object* v_k_1299_, lean_object* v_fallback_1300_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_box(0);
v___x_1302_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1297_, v_k_1299_, v___x_1301_, v_t_1298_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_inc_ref(v_fallback_1300_);
return v_fallback_1300_;
}
else
{
lean_object* v_val_1303_; 
v_val_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v___x_1302_, 1);
return v_val_1303_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1304_, lean_object* v_t_1305_, lean_object* v_k_1306_, lean_object* v_fallback_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_DTreeMap_getEntryGED___redArg(v_cmp_1304_, v_t_1305_, v_k_1306_, v_fallback_1307_);
lean_dec_ref(v_fallback_1307_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED(lean_object* v_00_u03b1_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_cmp_1311_, lean_object* v_t_1312_, lean_object* v_k_1313_, lean_object* v_fallback_1314_){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_box(0);
v___x_1316_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1311_, v_k_1313_, v___x_1315_, v_t_1312_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_inc_ref(v_fallback_1314_);
return v_fallback_1314_;
}
else
{
lean_object* v_val_1317_; 
v_val_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_val_1317_);
lean_dec_ref_known(v___x_1316_, 1);
return v_val_1317_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1318_, lean_object* v_00_u03b2_1319_, lean_object* v_cmp_1320_, lean_object* v_t_1321_, lean_object* v_k_1322_, lean_object* v_fallback_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Std_DTreeMap_getEntryGED(v_00_u03b1_1318_, v_00_u03b2_1319_, v_cmp_1320_, v_t_1321_, v_k_1322_, v_fallback_1323_);
lean_dec_ref(v_fallback_1323_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1325_, lean_object* v_t_1326_, lean_object* v_k_1327_, lean_object* v_fallback_1328_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_box(0);
v___x_1330_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1325_, v_k_1327_, v___x_1329_, v_t_1326_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1332_, lean_object* v_t_1333_, lean_object* v_k_1334_, lean_object* v_fallback_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_DTreeMap_getEntryGTD___redArg(v_cmp_1332_, v_t_1333_, v_k_1334_, v_fallback_1335_);
lean_dec_ref(v_fallback_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD(lean_object* v_00_u03b1_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_cmp_1339_, lean_object* v_t_1340_, lean_object* v_k_1341_, lean_object* v_fallback_1342_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_box(0);
v___x_1344_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1339_, v_k_1341_, v___x_1343_, v_t_1340_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_inc_ref(v_fallback_1342_);
return v_fallback_1342_;
}
else
{
lean_object* v_val_1345_; 
v_val_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_val_1345_);
lean_dec_ref_known(v___x_1344_, 1);
return v_val_1345_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1346_, lean_object* v_00_u03b2_1347_, lean_object* v_cmp_1348_, lean_object* v_t_1349_, lean_object* v_k_1350_, lean_object* v_fallback_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Std_DTreeMap_getEntryGTD(v_00_u03b1_1346_, v_00_u03b2_1347_, v_cmp_1348_, v_t_1349_, v_k_1350_, v_fallback_1351_);
lean_dec_ref(v_fallback_1351_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___redArg(lean_object* v_cmp_1353_, lean_object* v_t_1354_, lean_object* v_k_1355_, lean_object* v_fallback_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_box(0);
v___x_1358_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1353_, v_k_1355_, v___x_1357_, v_t_1354_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1360_, lean_object* v_t_1361_, lean_object* v_k_1362_, lean_object* v_fallback_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Std_DTreeMap_getEntryLED___redArg(v_cmp_1360_, v_t_1361_, v_k_1362_, v_fallback_1363_);
lean_dec_ref(v_fallback_1363_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED(lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_cmp_1367_, lean_object* v_t_1368_, lean_object* v_k_1369_, lean_object* v_fallback_1370_){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_box(0);
v___x_1372_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1367_, v_k_1369_, v___x_1371_, v_t_1368_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_inc_ref(v_fallback_1370_);
return v_fallback_1370_;
}
else
{
lean_object* v_val_1373_; 
v_val_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_val_1373_);
lean_dec_ref_known(v___x_1372_, 1);
return v_val_1373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1374_, lean_object* v_00_u03b2_1375_, lean_object* v_cmp_1376_, lean_object* v_t_1377_, lean_object* v_k_1378_, lean_object* v_fallback_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Std_DTreeMap_getEntryLED(v_00_u03b1_1374_, v_00_u03b2_1375_, v_cmp_1376_, v_t_1377_, v_k_1378_, v_fallback_1379_);
lean_dec_ref(v_fallback_1379_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1381_, lean_object* v_t_1382_, lean_object* v_k_1383_, lean_object* v_fallback_1384_){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_box(0);
v___x_1386_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1381_, v_k_1383_, v___x_1385_, v_t_1382_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_inc_ref(v_fallback_1384_);
return v_fallback_1384_;
}
else
{
lean_object* v_val_1387_; 
v_val_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_val_1387_);
lean_dec_ref_known(v___x_1386_, 1);
return v_val_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1388_, lean_object* v_t_1389_, lean_object* v_k_1390_, lean_object* v_fallback_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Std_DTreeMap_getEntryLTD___redArg(v_cmp_1388_, v_t_1389_, v_k_1390_, v_fallback_1391_);
lean_dec_ref(v_fallback_1391_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD(lean_object* v_00_u03b1_1393_, lean_object* v_00_u03b2_1394_, lean_object* v_cmp_1395_, lean_object* v_t_1396_, lean_object* v_k_1397_, lean_object* v_fallback_1398_){
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
lean_dec_ref_known(v___x_1400_, 1);
return v_val_1401_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1402_, lean_object* v_00_u03b2_1403_, lean_object* v_cmp_1404_, lean_object* v_t_1405_, lean_object* v_k_1406_, lean_object* v_fallback_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Std_DTreeMap_getEntryLTD(v_00_u03b1_1402_, v_00_u03b2_1403_, v_cmp_1404_, v_t_1405_, v_k_1406_, v_fallback_1407_);
lean_dec_ref(v_fallback_1407_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1409_, lean_object* v_t_1410_, lean_object* v_k_1411_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_box(0);
v___x_1413_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1409_, v_k_1411_, v___x_1412_, v_t_1410_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1414_, lean_object* v_00_u03b2_1415_, lean_object* v_cmp_1416_, lean_object* v_t_1417_, lean_object* v_k_1418_){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_box(0);
v___x_1420_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1416_, v_k_1418_, v___x_1419_, v_t_1417_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1421_, lean_object* v_t_1422_, lean_object* v_k_1423_){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_box(0);
v___x_1425_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1421_, v_k_1423_, v___x_1424_, v_t_1422_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1426_, lean_object* v_00_u03b2_1427_, lean_object* v_cmp_1428_, lean_object* v_t_1429_, lean_object* v_k_1430_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_box(0);
v___x_1432_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1428_, v_k_1430_, v___x_1431_, v_t_1429_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1433_, lean_object* v_t_1434_, lean_object* v_k_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = lean_box(0);
v___x_1437_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1433_, v_k_1435_, v___x_1436_, v_t_1434_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1438_, lean_object* v_00_u03b2_1439_, lean_object* v_cmp_1440_, lean_object* v_t_1441_, lean_object* v_k_1442_){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_box(0);
v___x_1444_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1440_, v_k_1442_, v___x_1443_, v_t_1441_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1445_, lean_object* v_t_1446_, lean_object* v_k_1447_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1445_, v_k_1447_, v___x_1448_, v_t_1446_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_cmp_1452_, lean_object* v_t_1453_, lean_object* v_k_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_box(0);
v___x_1456_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1452_, v_k_1454_, v___x_1455_, v_t_1453_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1457_, lean_object* v_inst_1458_, lean_object* v_t_1459_, lean_object* v_k_1460_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_box(0);
v___x_1462_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1457_, v_k_1460_, v___x_1461_, v_t_1459_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1464_ = l_panic___redArg(v_inst_1458_, v___x_1463_);
return v___x_1464_;
}
else
{
lean_object* v_val_1465_; 
v_val_1465_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_val_1465_);
lean_dec_ref_known(v___x_1462_, 1);
return v_val_1465_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1466_, lean_object* v_inst_1467_, lean_object* v_t_1468_, lean_object* v_k_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Std_DTreeMap_getKeyGE_x21___redArg(v_cmp_1466_, v_inst_1467_, v_t_1468_, v_k_1469_);
lean_dec(v_inst_1467_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1471_, lean_object* v_00_u03b2_1472_, lean_object* v_cmp_1473_, lean_object* v_inst_1474_, lean_object* v_t_1475_, lean_object* v_k_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_box(0);
v___x_1478_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1473_, v_k_1476_, v___x_1477_, v_t_1475_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1480_ = l_panic___redArg(v_inst_1474_, v___x_1479_);
return v___x_1480_;
}
else
{
lean_object* v_val_1481_; 
v_val_1481_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_val_1481_);
lean_dec_ref_known(v___x_1478_, 1);
return v_val_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1482_, lean_object* v_00_u03b2_1483_, lean_object* v_cmp_1484_, lean_object* v_inst_1485_, lean_object* v_t_1486_, lean_object* v_k_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Std_DTreeMap_getKeyGE_x21(v_00_u03b1_1482_, v_00_u03b2_1483_, v_cmp_1484_, v_inst_1485_, v_t_1486_, v_k_1487_);
lean_dec(v_inst_1485_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1489_, lean_object* v_inst_1490_, lean_object* v_t_1491_, lean_object* v_k_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1489_, v_k_1492_, v___x_1493_, v_t_1491_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1496_ = l_panic___redArg(v_inst_1490_, v___x_1495_);
return v___x_1496_;
}
else
{
lean_object* v_val_1497_; 
v_val_1497_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_val_1497_);
lean_dec_ref_known(v___x_1494_, 1);
return v_val_1497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1498_, lean_object* v_inst_1499_, lean_object* v_t_1500_, lean_object* v_k_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Std_DTreeMap_getKeyGT_x21___redArg(v_cmp_1498_, v_inst_1499_, v_t_1500_, v_k_1501_);
lean_dec(v_inst_1499_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1503_, lean_object* v_00_u03b2_1504_, lean_object* v_cmp_1505_, lean_object* v_inst_1506_, lean_object* v_t_1507_, lean_object* v_k_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_box(0);
v___x_1510_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1505_, v_k_1508_, v___x_1509_, v_t_1507_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1512_ = l_panic___redArg(v_inst_1506_, v___x_1511_);
return v___x_1512_;
}
else
{
lean_object* v_val_1513_; 
v_val_1513_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_val_1513_);
lean_dec_ref_known(v___x_1510_, 1);
return v_val_1513_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1514_, lean_object* v_00_u03b2_1515_, lean_object* v_cmp_1516_, lean_object* v_inst_1517_, lean_object* v_t_1518_, lean_object* v_k_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Std_DTreeMap_getKeyGT_x21(v_00_u03b1_1514_, v_00_u03b2_1515_, v_cmp_1516_, v_inst_1517_, v_t_1518_, v_k_1519_);
lean_dec(v_inst_1517_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1521_, lean_object* v_inst_1522_, lean_object* v_t_1523_, lean_object* v_k_1524_){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_box(0);
v___x_1526_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1521_, v_k_1524_, v___x_1525_, v_t_1523_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1528_ = l_panic___redArg(v_inst_1522_, v___x_1527_);
return v___x_1528_;
}
else
{
lean_object* v_val_1529_; 
v_val_1529_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_val_1529_);
lean_dec_ref_known(v___x_1526_, 1);
return v_val_1529_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1530_, lean_object* v_inst_1531_, lean_object* v_t_1532_, lean_object* v_k_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Std_DTreeMap_getKeyLE_x21___redArg(v_cmp_1530_, v_inst_1531_, v_t_1532_, v_k_1533_);
lean_dec(v_inst_1531_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1535_, lean_object* v_00_u03b2_1536_, lean_object* v_cmp_1537_, lean_object* v_inst_1538_, lean_object* v_t_1539_, lean_object* v_k_1540_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_box(0);
v___x_1542_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1537_, v_k_1540_, v___x_1541_, v_t_1539_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1544_ = l_panic___redArg(v_inst_1538_, v___x_1543_);
return v___x_1544_;
}
else
{
lean_object* v_val_1545_; 
v_val_1545_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_val_1545_);
lean_dec_ref_known(v___x_1542_, 1);
return v_val_1545_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1546_, lean_object* v_00_u03b2_1547_, lean_object* v_cmp_1548_, lean_object* v_inst_1549_, lean_object* v_t_1550_, lean_object* v_k_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Std_DTreeMap_getKeyLE_x21(v_00_u03b1_1546_, v_00_u03b2_1547_, v_cmp_1548_, v_inst_1549_, v_t_1550_, v_k_1551_);
lean_dec(v_inst_1549_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1553_, lean_object* v_inst_1554_, lean_object* v_t_1555_, lean_object* v_k_1556_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_box(0);
v___x_1558_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1553_, v_k_1556_, v___x_1557_, v_t_1555_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1560_ = l_panic___redArg(v_inst_1554_, v___x_1559_);
return v___x_1560_;
}
else
{
lean_object* v_val_1561_; 
v_val_1561_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_val_1561_);
lean_dec_ref_known(v___x_1558_, 1);
return v_val_1561_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1562_, lean_object* v_inst_1563_, lean_object* v_t_1564_, lean_object* v_k_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Std_DTreeMap_getKeyLT_x21___redArg(v_cmp_1562_, v_inst_1563_, v_t_1564_, v_k_1565_);
lean_dec(v_inst_1563_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1567_, lean_object* v_00_u03b2_1568_, lean_object* v_cmp_1569_, lean_object* v_inst_1570_, lean_object* v_t_1571_, lean_object* v_k_1572_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1569_, v_k_1572_, v___x_1573_, v_t_1571_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1576_ = l_panic___redArg(v_inst_1570_, v___x_1575_);
return v___x_1576_;
}
else
{
lean_object* v_val_1577_; 
v_val_1577_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v___x_1574_, 1);
return v_val_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1578_, lean_object* v_00_u03b2_1579_, lean_object* v_cmp_1580_, lean_object* v_inst_1581_, lean_object* v_t_1582_, lean_object* v_k_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Std_DTreeMap_getKeyLT_x21(v_00_u03b1_1578_, v_00_u03b2_1579_, v_cmp_1580_, v_inst_1581_, v_t_1582_, v_k_1583_);
lean_dec(v_inst_1581_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___redArg(lean_object* v_cmp_1585_, lean_object* v_t_1586_, lean_object* v_k_1587_, lean_object* v_fallback_1588_){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_box(0);
v___x_1590_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1585_, v_k_1587_, v___x_1589_, v_t_1586_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_inc(v_fallback_1588_);
return v_fallback_1588_;
}
else
{
lean_object* v_val_1591_; 
v_val_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_val_1591_);
lean_dec_ref_known(v___x_1590_, 1);
return v_val_1591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1592_, lean_object* v_t_1593_, lean_object* v_k_1594_, lean_object* v_fallback_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Std_DTreeMap_getKeyGED___redArg(v_cmp_1592_, v_t_1593_, v_k_1594_, v_fallback_1595_);
lean_dec(v_fallback_1595_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED(lean_object* v_00_u03b1_1597_, lean_object* v_00_u03b2_1598_, lean_object* v_cmp_1599_, lean_object* v_t_1600_, lean_object* v_k_1601_, lean_object* v_fallback_1602_){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_box(0);
v___x_1604_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1599_, v_k_1601_, v___x_1603_, v_t_1600_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_inc(v_fallback_1602_);
return v_fallback_1602_;
}
else
{
lean_object* v_val_1605_; 
v_val_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_val_1605_);
lean_dec_ref_known(v___x_1604_, 1);
return v_val_1605_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1606_, lean_object* v_00_u03b2_1607_, lean_object* v_cmp_1608_, lean_object* v_t_1609_, lean_object* v_k_1610_, lean_object* v_fallback_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Std_DTreeMap_getKeyGED(v_00_u03b1_1606_, v_00_u03b2_1607_, v_cmp_1608_, v_t_1609_, v_k_1610_, v_fallback_1611_);
lean_dec(v_fallback_1611_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1613_, lean_object* v_t_1614_, lean_object* v_k_1615_, lean_object* v_fallback_1616_){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_box(0);
v___x_1618_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1613_, v_k_1615_, v___x_1617_, v_t_1614_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_inc(v_fallback_1616_);
return v_fallback_1616_;
}
else
{
lean_object* v_val_1619_; 
v_val_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_val_1619_);
lean_dec_ref_known(v___x_1618_, 1);
return v_val_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1620_, lean_object* v_t_1621_, lean_object* v_k_1622_, lean_object* v_fallback_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Std_DTreeMap_getKeyGTD___redArg(v_cmp_1620_, v_t_1621_, v_k_1622_, v_fallback_1623_);
lean_dec(v_fallback_1623_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD(lean_object* v_00_u03b1_1625_, lean_object* v_00_u03b2_1626_, lean_object* v_cmp_1627_, lean_object* v_t_1628_, lean_object* v_k_1629_, lean_object* v_fallback_1630_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_box(0);
v___x_1632_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1627_, v_k_1629_, v___x_1631_, v_t_1628_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_inc(v_fallback_1630_);
return v_fallback_1630_;
}
else
{
lean_object* v_val_1633_; 
v_val_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_val_1633_);
lean_dec_ref_known(v___x_1632_, 1);
return v_val_1633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1634_, lean_object* v_00_u03b2_1635_, lean_object* v_cmp_1636_, lean_object* v_t_1637_, lean_object* v_k_1638_, lean_object* v_fallback_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Std_DTreeMap_getKeyGTD(v_00_u03b1_1634_, v_00_u03b2_1635_, v_cmp_1636_, v_t_1637_, v_k_1638_, v_fallback_1639_);
lean_dec(v_fallback_1639_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___redArg(lean_object* v_cmp_1641_, lean_object* v_t_1642_, lean_object* v_k_1643_, lean_object* v_fallback_1644_){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_box(0);
v___x_1646_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1641_, v_k_1643_, v___x_1645_, v_t_1642_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1648_, lean_object* v_t_1649_, lean_object* v_k_1650_, lean_object* v_fallback_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Std_DTreeMap_getKeyLED___redArg(v_cmp_1648_, v_t_1649_, v_k_1650_, v_fallback_1651_);
lean_dec(v_fallback_1651_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED(lean_object* v_00_u03b1_1653_, lean_object* v_00_u03b2_1654_, lean_object* v_cmp_1655_, lean_object* v_t_1656_, lean_object* v_k_1657_, lean_object* v_fallback_1658_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = lean_box(0);
v___x_1660_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1655_, v_k_1657_, v___x_1659_, v_t_1656_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_inc(v_fallback_1658_);
return v_fallback_1658_;
}
else
{
lean_object* v_val_1661_; 
v_val_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_val_1661_);
lean_dec_ref_known(v___x_1660_, 1);
return v_val_1661_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1662_, lean_object* v_00_u03b2_1663_, lean_object* v_cmp_1664_, lean_object* v_t_1665_, lean_object* v_k_1666_, lean_object* v_fallback_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Std_DTreeMap_getKeyLED(v_00_u03b1_1662_, v_00_u03b2_1663_, v_cmp_1664_, v_t_1665_, v_k_1666_, v_fallback_1667_);
lean_dec(v_fallback_1667_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1669_, lean_object* v_t_1670_, lean_object* v_k_1671_, lean_object* v_fallback_1672_){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_box(0);
v___x_1674_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1669_, v_k_1671_, v___x_1673_, v_t_1670_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_inc(v_fallback_1672_);
return v_fallback_1672_;
}
else
{
lean_object* v_val_1675_; 
v_val_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_val_1675_);
lean_dec_ref_known(v___x_1674_, 1);
return v_val_1675_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1676_, lean_object* v_t_1677_, lean_object* v_k_1678_, lean_object* v_fallback_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Std_DTreeMap_getKeyLTD___redArg(v_cmp_1676_, v_t_1677_, v_k_1678_, v_fallback_1679_);
lean_dec(v_fallback_1679_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD(lean_object* v_00_u03b1_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_cmp_1683_, lean_object* v_t_1684_, lean_object* v_k_1685_, lean_object* v_fallback_1686_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_box(0);
v___x_1688_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1683_, v_k_1685_, v___x_1687_, v_t_1684_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_inc(v_fallback_1686_);
return v_fallback_1686_;
}
else
{
lean_object* v_val_1689_; 
v_val_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_val_1689_);
lean_dec_ref_known(v___x_1688_, 1);
return v_val_1689_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1690_, lean_object* v_00_u03b2_1691_, lean_object* v_cmp_1692_, lean_object* v_t_1693_, lean_object* v_k_1694_, lean_object* v_fallback_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Std_DTreeMap_getKeyLTD(v_00_u03b1_1690_, v_00_u03b2_1691_, v_cmp_1692_, v_t_1693_, v_k_1694_, v_fallback_1695_);
lean_dec(v_fallback_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1697_, lean_object* v_t_1698_, lean_object* v_a_1699_, lean_object* v_b_1700_){
_start:
{
lean_object* v___x_1701_; 
lean_inc(v_a_1699_);
lean_inc(v_t_1698_);
lean_inc_ref(v_cmp_1697_);
v___x_1701_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1697_, v_t_1698_, v_a_1699_);
if (lean_obj_tag(v___x_1701_) == 0)
{
uint8_t v___x_1702_; 
lean_inc(v_t_1698_);
lean_inc(v_a_1699_);
lean_inc_ref(v_cmp_1697_);
v___x_1702_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1697_, v_a_1699_, v_t_1698_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1697_, v_a_1699_, v_b_1700_, v_t_1698_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1701_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
return v___x_1704_;
}
else
{
lean_object* v___x_1705_; 
lean_dec(v_b_1700_);
lean_dec(v_a_1699_);
lean_dec_ref(v_cmp_1697_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1701_);
lean_ctor_set(v___x_1705_, 1, v_t_1698_);
return v___x_1705_;
}
}
else
{
lean_object* v___x_1706_; 
lean_dec(v_b_1700_);
lean_dec(v_a_1699_);
lean_dec_ref(v_cmp_1697_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1701_);
lean_ctor_set(v___x_1706_, 1, v_t_1698_);
return v___x_1706_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1707_, lean_object* v_cmp_1708_, lean_object* v_00_u03b2_1709_, lean_object* v_t_1710_, lean_object* v_a_1711_, lean_object* v_b_1712_){
_start:
{
lean_object* v___x_1713_; 
lean_inc(v_a_1711_);
lean_inc(v_t_1710_);
lean_inc_ref(v_cmp_1708_);
v___x_1713_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1708_, v_t_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1713_) == 0)
{
uint8_t v___x_1714_; 
lean_inc(v_t_1710_);
lean_inc(v_a_1711_);
lean_inc_ref(v_cmp_1708_);
v___x_1714_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1708_, v_a_1711_, v_t_1710_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1708_, v_a_1711_, v_b_1712_, v_t_1710_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1713_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
return v___x_1716_;
}
else
{
lean_object* v___x_1717_; 
lean_dec(v_b_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_cmp_1708_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1713_);
lean_ctor_set(v___x_1717_, 1, v_t_1710_);
return v___x_1717_;
}
}
else
{
lean_object* v___x_1718_; 
lean_dec(v_b_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_cmp_1708_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1713_);
lean_ctor_set(v___x_1718_, 1, v_t_1710_);
return v___x_1718_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x3f___redArg(lean_object* v_cmp_1719_, lean_object* v_t_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1719_, v_t_1720_, v_a_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x3f(lean_object* v_00_u03b1_1723_, lean_object* v_cmp_1724_, lean_object* v_00_u03b2_1725_, lean_object* v_t_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1724_, v_t_1726_, v_a_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get___redArg(lean_object* v_cmp_1729_, lean_object* v_t_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1729_, v_t_1730_, v_a_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get(lean_object* v_00_u03b1_1733_, lean_object* v_cmp_1734_, lean_object* v_00_u03b2_1735_, lean_object* v_t_1736_, lean_object* v_a_1737_, lean_object* v_h_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1734_, v_t_1736_, v_a_1737_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___redArg(lean_object* v_cmp_1740_, lean_object* v_inst_1741_, lean_object* v_t_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1740_, v_inst_1741_, v_t_1742_, v_a_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___redArg___boxed(lean_object* v_cmp_1745_, lean_object* v_inst_1746_, lean_object* v_t_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Std_DTreeMap_Const_get_x21___redArg(v_cmp_1745_, v_inst_1746_, v_t_1747_, v_a_1748_);
lean_dec(v_inst_1746_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21(lean_object* v_00_u03b1_1750_, lean_object* v_cmp_1751_, lean_object* v_00_u03b2_1752_, lean_object* v_inst_1753_, lean_object* v_t_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1751_, v_inst_1753_, v_t_1754_, v_a_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_get_x21___boxed(lean_object* v_00_u03b1_1757_, lean_object* v_cmp_1758_, lean_object* v_00_u03b2_1759_, lean_object* v_inst_1760_, lean_object* v_t_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Std_DTreeMap_Const_get_x21(v_00_u03b1_1757_, v_cmp_1758_, v_00_u03b2_1759_, v_inst_1760_, v_t_1761_, v_a_1762_);
lean_dec(v_inst_1760_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___redArg(lean_object* v_cmp_1764_, lean_object* v_t_1765_, lean_object* v_a_1766_, lean_object* v_fallback_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1764_, v_t_1765_, v_a_1766_, v_fallback_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___redArg___boxed(lean_object* v_cmp_1769_, lean_object* v_t_1770_, lean_object* v_a_1771_, lean_object* v_fallback_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Std_DTreeMap_Const_getD___redArg(v_cmp_1769_, v_t_1770_, v_a_1771_, v_fallback_1772_);
lean_dec(v_fallback_1772_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD(lean_object* v_00_u03b1_1774_, lean_object* v_cmp_1775_, lean_object* v_00_u03b2_1776_, lean_object* v_t_1777_, lean_object* v_a_1778_, lean_object* v_fallback_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1775_, v_t_1777_, v_a_1778_, v_fallback_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getD___boxed(lean_object* v_00_u03b1_1781_, lean_object* v_cmp_1782_, lean_object* v_00_u03b2_1783_, lean_object* v_t_1784_, lean_object* v_a_1785_, lean_object* v_fallback_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Std_DTreeMap_Const_getD(v_00_u03b1_1781_, v_cmp_1782_, v_00_u03b2_1783_, v_t_1784_, v_a_1785_, v_fallback_1786_);
lean_dec(v_fallback_1786_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___redArg(lean_object* v_t_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Std_DTreeMap_Const_minEntry_x3f___redArg(v_t_1790_);
lean_dec(v_t_1790_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f(lean_object* v_00_u03b1_1792_, lean_object* v_cmp_1793_, lean_object* v_00_u03b2_1794_, lean_object* v_t_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1797_, lean_object* v_cmp_1798_, lean_object* v_00_u03b2_1799_, lean_object* v_t_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Std_DTreeMap_Const_minEntry_x3f(v_00_u03b1_1797_, v_cmp_1798_, v_00_u03b2_1799_, v_t_1800_);
lean_dec(v_t_1800_);
lean_dec_ref(v_cmp_1798_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___redArg(lean_object* v_t_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___redArg___boxed(lean_object* v_t_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Std_DTreeMap_Const_minEntry___redArg(v_t_1804_);
lean_dec(v_t_1804_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry(lean_object* v_00_u03b1_1806_, lean_object* v_cmp_1807_, lean_object* v_00_u03b2_1808_, lean_object* v_t_1809_, lean_object* v_h_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry___boxed(lean_object* v_00_u03b1_1812_, lean_object* v_cmp_1813_, lean_object* v_00_u03b2_1814_, lean_object* v_t_1815_, lean_object* v_h_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Std_DTreeMap_Const_minEntry(v_00_u03b1_1812_, v_cmp_1813_, v_00_u03b2_1814_, v_t_1815_, v_h_1816_);
lean_dec(v_t_1815_);
lean_dec_ref(v_cmp_1813_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___redArg(lean_object* v_inst_1818_, lean_object* v_t_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1818_, v_t_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1821_, lean_object* v_t_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Std_DTreeMap_Const_minEntry_x21___redArg(v_inst_1821_, v_t_1822_);
lean_dec(v_t_1822_);
lean_dec_ref(v_inst_1821_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21(lean_object* v_00_u03b1_1824_, lean_object* v_cmp_1825_, lean_object* v_00_u03b2_1826_, lean_object* v_inst_1827_, lean_object* v_t_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1827_, v_t_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1830_, lean_object* v_cmp_1831_, lean_object* v_00_u03b2_1832_, lean_object* v_inst_1833_, lean_object* v_t_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Std_DTreeMap_Const_minEntry_x21(v_00_u03b1_1830_, v_cmp_1831_, v_00_u03b2_1832_, v_inst_1833_, v_t_1834_);
lean_dec(v_t_1834_);
lean_dec_ref(v_inst_1833_);
lean_dec_ref(v_cmp_1831_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___redArg(lean_object* v_t_1836_, lean_object* v_fallback_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1836_, v_fallback_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___redArg___boxed(lean_object* v_t_1839_, lean_object* v_fallback_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Std_DTreeMap_Const_minEntryD___redArg(v_t_1839_, v_fallback_1840_);
lean_dec_ref(v_fallback_1840_);
lean_dec(v_t_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD(lean_object* v_00_u03b1_1842_, lean_object* v_cmp_1843_, lean_object* v_00_u03b2_1844_, lean_object* v_t_1845_, lean_object* v_fallback_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1845_, v_fallback_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_minEntryD___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_cmp_1849_, lean_object* v_00_u03b2_1850_, lean_object* v_t_1851_, lean_object* v_fallback_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Std_DTreeMap_Const_minEntryD(v_00_u03b1_1848_, v_cmp_1849_, v_00_u03b2_1850_, v_t_1851_, v_fallback_1852_);
lean_dec_ref(v_fallback_1852_);
lean_dec(v_t_1851_);
lean_dec_ref(v_cmp_1849_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___redArg(lean_object* v_t_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Std_DTreeMap_Const_maxEntry_x3f___redArg(v_t_1856_);
lean_dec(v_t_1856_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f(lean_object* v_00_u03b1_1858_, lean_object* v_cmp_1859_, lean_object* v_00_u03b2_1860_, lean_object* v_t_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1863_, lean_object* v_cmp_1864_, lean_object* v_00_u03b2_1865_, lean_object* v_t_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Std_DTreeMap_Const_maxEntry_x3f(v_00_u03b1_1863_, v_cmp_1864_, v_00_u03b2_1865_, v_t_1866_);
lean_dec(v_t_1866_);
lean_dec_ref(v_cmp_1864_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___redArg(lean_object* v_t_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___redArg___boxed(lean_object* v_t_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Std_DTreeMap_Const_maxEntry___redArg(v_t_1870_);
lean_dec(v_t_1870_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry(lean_object* v_00_u03b1_1872_, lean_object* v_cmp_1873_, lean_object* v_00_u03b2_1874_, lean_object* v_t_1875_, lean_object* v_h_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_1875_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry___boxed(lean_object* v_00_u03b1_1878_, lean_object* v_cmp_1879_, lean_object* v_00_u03b2_1880_, lean_object* v_t_1881_, lean_object* v_h_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Std_DTreeMap_Const_maxEntry(v_00_u03b1_1878_, v_cmp_1879_, v_00_u03b2_1880_, v_t_1881_, v_h_1882_);
lean_dec(v_t_1881_);
lean_dec_ref(v_cmp_1879_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___redArg(lean_object* v_inst_1884_, lean_object* v_t_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1884_, v_t_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_1887_, lean_object* v_t_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Std_DTreeMap_Const_maxEntry_x21___redArg(v_inst_1887_, v_t_1888_);
lean_dec(v_t_1888_);
lean_dec_ref(v_inst_1887_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21(lean_object* v_00_u03b1_1890_, lean_object* v_cmp_1891_, lean_object* v_00_u03b2_1892_, lean_object* v_inst_1893_, lean_object* v_t_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1893_, v_t_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_1896_, lean_object* v_cmp_1897_, lean_object* v_00_u03b2_1898_, lean_object* v_inst_1899_, lean_object* v_t_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Std_DTreeMap_Const_maxEntry_x21(v_00_u03b1_1896_, v_cmp_1897_, v_00_u03b2_1898_, v_inst_1899_, v_t_1900_);
lean_dec(v_t_1900_);
lean_dec_ref(v_inst_1899_);
lean_dec_ref(v_cmp_1897_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___redArg(lean_object* v_t_1902_, lean_object* v_fallback_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1902_, v_fallback_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___redArg___boxed(lean_object* v_t_1905_, lean_object* v_fallback_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Std_DTreeMap_Const_maxEntryD___redArg(v_t_1905_, v_fallback_1906_);
lean_dec_ref(v_fallback_1906_);
lean_dec(v_t_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD(lean_object* v_00_u03b1_1908_, lean_object* v_cmp_1909_, lean_object* v_00_u03b2_1910_, lean_object* v_t_1911_, lean_object* v_fallback_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1911_, v_fallback_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_maxEntryD___boxed(lean_object* v_00_u03b1_1914_, lean_object* v_cmp_1915_, lean_object* v_00_u03b2_1916_, lean_object* v_t_1917_, lean_object* v_fallback_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Std_DTreeMap_Const_maxEntryD(v_00_u03b1_1914_, v_cmp_1915_, v_00_u03b2_1916_, v_t_1917_, v_fallback_1918_);
lean_dec_ref(v_fallback_1918_);
lean_dec(v_t_1917_);
lean_dec_ref(v_cmp_1915_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(lean_object* v_t_1920_, lean_object* v_n_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1920_, v_n_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_1923_, lean_object* v_n_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(v_t_1923_, v_n_1924_);
lean_dec(v_t_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_1926_, lean_object* v_cmp_1927_, lean_object* v_00_u03b2_1928_, lean_object* v_t_1929_, lean_object* v_n_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1929_, v_n_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1932_, lean_object* v_cmp_1933_, lean_object* v_00_u03b2_1934_, lean_object* v_t_1935_, lean_object* v_n_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Std_DTreeMap_Const_entryAtIdx_x3f(v_00_u03b1_1932_, v_cmp_1933_, v_00_u03b2_1934_, v_t_1935_, v_n_1936_);
lean_dec(v_t_1935_);
lean_dec_ref(v_cmp_1933_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___redArg(lean_object* v_t_1938_, lean_object* v_n_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_1938_, v_n_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___redArg___boxed(lean_object* v_t_1941_, lean_object* v_n_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Std_DTreeMap_Const_entryAtIdx___redArg(v_t_1941_, v_n_1942_);
lean_dec(v_t_1941_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx(lean_object* v_00_u03b1_1944_, lean_object* v_cmp_1945_, lean_object* v_00_u03b2_1946_, lean_object* v_t_1947_, lean_object* v_n_1948_, lean_object* v_h_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_1947_, v_n_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_1951_, lean_object* v_cmp_1952_, lean_object* v_00_u03b2_1953_, lean_object* v_t_1954_, lean_object* v_n_1955_, lean_object* v_h_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Std_DTreeMap_Const_entryAtIdx(v_00_u03b1_1951_, v_cmp_1952_, v_00_u03b2_1953_, v_t_1954_, v_n_1955_, v_h_1956_);
lean_dec(v_t_1954_);
lean_dec_ref(v_cmp_1952_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(lean_object* v_inst_1958_, lean_object* v_t_1959_, lean_object* v_n_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1958_, v_t_1959_, v_n_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_1962_, lean_object* v_t_1963_, lean_object* v_n_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(v_inst_1962_, v_t_1963_, v_n_1964_);
lean_dec(v_t_1963_);
lean_dec_ref(v_inst_1962_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21(lean_object* v_00_u03b1_1966_, lean_object* v_cmp_1967_, lean_object* v_00_u03b2_1968_, lean_object* v_inst_1969_, lean_object* v_t_1970_, lean_object* v_n_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1969_, v_t_1970_, v_n_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_1973_, lean_object* v_cmp_1974_, lean_object* v_00_u03b2_1975_, lean_object* v_inst_1976_, lean_object* v_t_1977_, lean_object* v_n_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Std_DTreeMap_Const_entryAtIdx_x21(v_00_u03b1_1973_, v_cmp_1974_, v_00_u03b2_1975_, v_inst_1976_, v_t_1977_, v_n_1978_);
lean_dec(v_t_1977_);
lean_dec_ref(v_inst_1976_);
lean_dec_ref(v_cmp_1974_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___redArg(lean_object* v_t_1980_, lean_object* v_n_1981_, lean_object* v_fallback_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1980_, v_n_1981_, v_fallback_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_1984_, lean_object* v_n_1985_, lean_object* v_fallback_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Std_DTreeMap_Const_entryAtIdxD___redArg(v_t_1984_, v_n_1985_, v_fallback_1986_);
lean_dec_ref(v_fallback_1986_);
lean_dec(v_t_1984_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD(lean_object* v_00_u03b1_1988_, lean_object* v_cmp_1989_, lean_object* v_00_u03b2_1990_, lean_object* v_t_1991_, lean_object* v_n_1992_, lean_object* v_fallback_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1991_, v_n_1992_, v_fallback_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_1995_, lean_object* v_cmp_1996_, lean_object* v_00_u03b2_1997_, lean_object* v_t_1998_, lean_object* v_n_1999_, lean_object* v_fallback_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Std_DTreeMap_Const_entryAtIdxD(v_00_u03b1_1995_, v_cmp_1996_, v_00_u03b2_1997_, v_t_1998_, v_n_1999_, v_fallback_2000_);
lean_dec_ref(v_fallback_2000_);
lean_dec(v_t_1998_);
lean_dec_ref(v_cmp_1996_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_2002_, lean_object* v_t_2003_, lean_object* v_k_2004_){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = lean_box(0);
v___x_2006_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2002_, v_k_2004_, v___x_2005_, v_t_2003_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x3f(lean_object* v_00_u03b1_2007_, lean_object* v_cmp_2008_, lean_object* v_00_u03b2_2009_, lean_object* v_t_2010_, lean_object* v_k_2011_){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_box(0);
v___x_2013_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2008_, v_k_2011_, v___x_2012_, v_t_2010_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_2014_, lean_object* v_t_2015_, lean_object* v_k_2016_){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = lean_box(0);
v___x_2018_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2014_, v_k_2016_, v___x_2017_, v_t_2015_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x3f(lean_object* v_00_u03b1_2019_, lean_object* v_cmp_2020_, lean_object* v_00_u03b2_2021_, lean_object* v_t_2022_, lean_object* v_k_2023_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_box(0);
v___x_2025_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2020_, v_k_2023_, v___x_2024_, v_t_2022_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_2026_, lean_object* v_t_2027_, lean_object* v_k_2028_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_box(0);
v___x_2030_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2026_, v_k_2028_, v___x_2029_, v_t_2027_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x3f(lean_object* v_00_u03b1_2031_, lean_object* v_cmp_2032_, lean_object* v_00_u03b2_2033_, lean_object* v_t_2034_, lean_object* v_k_2035_){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = lean_box(0);
v___x_2037_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2032_, v_k_2035_, v___x_2036_, v_t_2034_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_2038_, lean_object* v_t_2039_, lean_object* v_k_2040_){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_box(0);
v___x_2042_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2038_, v_k_2040_, v___x_2041_, v_t_2039_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x3f(lean_object* v_00_u03b1_2043_, lean_object* v_cmp_2044_, lean_object* v_00_u03b2_2045_, lean_object* v_t_2046_, lean_object* v_k_2047_){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_box(0);
v___x_2049_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2044_, v_k_2047_, v___x_2048_, v_t_2046_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___redArg(lean_object* v_cmp_2050_, lean_object* v_inst_2051_, lean_object* v_t_2052_, lean_object* v_k_2053_){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_box(0);
v___x_2055_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2050_, v_k_2053_, v___x_2054_, v_t_2052_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2057_ = l_panic___redArg(v_inst_2051_, v___x_2056_);
return v___x_2057_;
}
else
{
lean_object* v_val_2058_; 
v_val_2058_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_val_2058_);
lean_dec_ref_known(v___x_2055_, 1);
return v_val_2058_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_2059_, lean_object* v_inst_2060_, lean_object* v_t_2061_, lean_object* v_k_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Std_DTreeMap_Const_getEntryGE_x21___redArg(v_cmp_2059_, v_inst_2060_, v_t_2061_, v_k_2062_);
lean_dec_ref(v_inst_2060_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21(lean_object* v_00_u03b1_2064_, lean_object* v_cmp_2065_, lean_object* v_00_u03b2_2066_, lean_object* v_inst_2067_, lean_object* v_t_2068_, lean_object* v_k_2069_){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = lean_box(0);
v___x_2071_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2065_, v_k_2069_, v___x_2070_, v_t_2068_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2073_ = l_panic___redArg(v_inst_2067_, v___x_2072_);
return v___x_2073_;
}
else
{
lean_object* v_val_2074_; 
v_val_2074_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_val_2074_);
lean_dec_ref_known(v___x_2071_, 1);
return v_val_2074_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_2075_, lean_object* v_cmp_2076_, lean_object* v_00_u03b2_2077_, lean_object* v_inst_2078_, lean_object* v_t_2079_, lean_object* v_k_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Std_DTreeMap_Const_getEntryGE_x21(v_00_u03b1_2075_, v_cmp_2076_, v_00_u03b2_2077_, v_inst_2078_, v_t_2079_, v_k_2080_);
lean_dec_ref(v_inst_2078_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___redArg(lean_object* v_cmp_2082_, lean_object* v_inst_2083_, lean_object* v_t_2084_, lean_object* v_k_2085_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_box(0);
v___x_2087_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2082_, v_k_2085_, v___x_2086_, v_t_2084_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2089_ = l_panic___redArg(v_inst_2083_, v___x_2088_);
return v___x_2089_;
}
else
{
lean_object* v_val_2090_; 
v_val_2090_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v___x_2087_, 1);
return v_val_2090_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_2091_, lean_object* v_inst_2092_, lean_object* v_t_2093_, lean_object* v_k_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Std_DTreeMap_Const_getEntryGT_x21___redArg(v_cmp_2091_, v_inst_2092_, v_t_2093_, v_k_2094_);
lean_dec_ref(v_inst_2092_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21(lean_object* v_00_u03b1_2096_, lean_object* v_cmp_2097_, lean_object* v_00_u03b2_2098_, lean_object* v_inst_2099_, lean_object* v_t_2100_, lean_object* v_k_2101_){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_box(0);
v___x_2103_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2097_, v_k_2101_, v___x_2102_, v_t_2100_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2105_ = l_panic___redArg(v_inst_2099_, v___x_2104_);
return v___x_2105_;
}
else
{
lean_object* v_val_2106_; 
v_val_2106_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_val_2106_);
lean_dec_ref_known(v___x_2103_, 1);
return v_val_2106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_2107_, lean_object* v_cmp_2108_, lean_object* v_00_u03b2_2109_, lean_object* v_inst_2110_, lean_object* v_t_2111_, lean_object* v_k_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Std_DTreeMap_Const_getEntryGT_x21(v_00_u03b1_2107_, v_cmp_2108_, v_00_u03b2_2109_, v_inst_2110_, v_t_2111_, v_k_2112_);
lean_dec_ref(v_inst_2110_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___redArg(lean_object* v_cmp_2114_, lean_object* v_inst_2115_, lean_object* v_t_2116_, lean_object* v_k_2117_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_box(0);
v___x_2119_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2114_, v_k_2117_, v___x_2118_, v_t_2116_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2121_ = l_panic___redArg(v_inst_2115_, v___x_2120_);
return v___x_2121_;
}
else
{
lean_object* v_val_2122_; 
v_val_2122_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_val_2122_);
lean_dec_ref_known(v___x_2119_, 1);
return v_val_2122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_2123_, lean_object* v_inst_2124_, lean_object* v_t_2125_, lean_object* v_k_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Std_DTreeMap_Const_getEntryLE_x21___redArg(v_cmp_2123_, v_inst_2124_, v_t_2125_, v_k_2126_);
lean_dec_ref(v_inst_2124_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21(lean_object* v_00_u03b1_2128_, lean_object* v_cmp_2129_, lean_object* v_00_u03b2_2130_, lean_object* v_inst_2131_, lean_object* v_t_2132_, lean_object* v_k_2133_){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_box(0);
v___x_2135_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2129_, v_k_2133_, v___x_2134_, v_t_2132_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2137_ = l_panic___redArg(v_inst_2131_, v___x_2136_);
return v___x_2137_;
}
else
{
lean_object* v_val_2138_; 
v_val_2138_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_val_2138_);
lean_dec_ref_known(v___x_2135_, 1);
return v_val_2138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2139_, lean_object* v_cmp_2140_, lean_object* v_00_u03b2_2141_, lean_object* v_inst_2142_, lean_object* v_t_2143_, lean_object* v_k_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Std_DTreeMap_Const_getEntryLE_x21(v_00_u03b1_2139_, v_cmp_2140_, v_00_u03b2_2141_, v_inst_2142_, v_t_2143_, v_k_2144_);
lean_dec_ref(v_inst_2142_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___redArg(lean_object* v_cmp_2146_, lean_object* v_inst_2147_, lean_object* v_t_2148_, lean_object* v_k_2149_){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2146_, v_k_2149_, v___x_2150_, v_t_2148_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2153_ = l_panic___redArg(v_inst_2147_, v___x_2152_);
return v___x_2153_;
}
else
{
lean_object* v_val_2154_; 
v_val_2154_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_val_2154_);
lean_dec_ref_known(v___x_2151_, 1);
return v_val_2154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_2155_, lean_object* v_inst_2156_, lean_object* v_t_2157_, lean_object* v_k_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Std_DTreeMap_Const_getEntryLT_x21___redArg(v_cmp_2155_, v_inst_2156_, v_t_2157_, v_k_2158_);
lean_dec_ref(v_inst_2156_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21(lean_object* v_00_u03b1_2160_, lean_object* v_cmp_2161_, lean_object* v_00_u03b2_2162_, lean_object* v_inst_2163_, lean_object* v_t_2164_, lean_object* v_k_2165_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_box(0);
v___x_2167_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2161_, v_k_2165_, v___x_2166_, v_t_2164_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = lean_obj_once(&l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_2169_ = l_panic___redArg(v_inst_2163_, v___x_2168_);
return v___x_2169_;
}
else
{
lean_object* v_val_2170_; 
v_val_2170_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_val_2170_);
lean_dec_ref_known(v___x_2167_, 1);
return v_val_2170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2171_, lean_object* v_cmp_2172_, lean_object* v_00_u03b2_2173_, lean_object* v_inst_2174_, lean_object* v_t_2175_, lean_object* v_k_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Std_DTreeMap_Const_getEntryLT_x21(v_00_u03b1_2171_, v_cmp_2172_, v_00_u03b2_2173_, v_inst_2174_, v_t_2175_, v_k_2176_);
lean_dec_ref(v_inst_2174_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___redArg(lean_object* v_cmp_2178_, lean_object* v_t_2179_, lean_object* v_k_2180_, lean_object* v_fallback_2181_){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = lean_box(0);
v___x_2183_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2178_, v_k_2180_, v___x_2182_, v_t_2179_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_inc_ref(v_fallback_2181_);
return v_fallback_2181_;
}
else
{
lean_object* v_val_2184_; 
v_val_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v___x_2183_, 1);
return v_val_2184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2185_, lean_object* v_t_2186_, lean_object* v_k_2187_, lean_object* v_fallback_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Std_DTreeMap_Const_getEntryGED___redArg(v_cmp_2185_, v_t_2186_, v_k_2187_, v_fallback_2188_);
lean_dec_ref(v_fallback_2188_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED(lean_object* v_00_u03b1_2190_, lean_object* v_cmp_2191_, lean_object* v_00_u03b2_2192_, lean_object* v_t_2193_, lean_object* v_k_2194_, lean_object* v_fallback_2195_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_box(0);
v___x_2197_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2191_, v_k_2194_, v___x_2196_, v_t_2193_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_inc_ref(v_fallback_2195_);
return v_fallback_2195_;
}
else
{
lean_object* v_val_2198_; 
v_val_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v___x_2197_, 1);
return v_val_2198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2199_, lean_object* v_cmp_2200_, lean_object* v_00_u03b2_2201_, lean_object* v_t_2202_, lean_object* v_k_2203_, lean_object* v_fallback_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Std_DTreeMap_Const_getEntryGED(v_00_u03b1_2199_, v_cmp_2200_, v_00_u03b2_2201_, v_t_2202_, v_k_2203_, v_fallback_2204_);
lean_dec_ref(v_fallback_2204_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___redArg(lean_object* v_cmp_2206_, lean_object* v_t_2207_, lean_object* v_k_2208_, lean_object* v_fallback_2209_){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = lean_box(0);
v___x_2211_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2206_, v_k_2208_, v___x_2210_, v_t_2207_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_inc_ref(v_fallback_2209_);
return v_fallback_2209_;
}
else
{
lean_object* v_val_2212_; 
v_val_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_val_2212_);
lean_dec_ref_known(v___x_2211_, 1);
return v_val_2212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2213_, lean_object* v_t_2214_, lean_object* v_k_2215_, lean_object* v_fallback_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Std_DTreeMap_Const_getEntryGTD___redArg(v_cmp_2213_, v_t_2214_, v_k_2215_, v_fallback_2216_);
lean_dec_ref(v_fallback_2216_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD(lean_object* v_00_u03b1_2218_, lean_object* v_cmp_2219_, lean_object* v_00_u03b2_2220_, lean_object* v_t_2221_, lean_object* v_k_2222_, lean_object* v_fallback_2223_){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_box(0);
v___x_2225_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2219_, v_k_2222_, v___x_2224_, v_t_2221_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_inc_ref(v_fallback_2223_);
return v_fallback_2223_;
}
else
{
lean_object* v_val_2226_; 
v_val_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_val_2226_);
lean_dec_ref_known(v___x_2225_, 1);
return v_val_2226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2227_, lean_object* v_cmp_2228_, lean_object* v_00_u03b2_2229_, lean_object* v_t_2230_, lean_object* v_k_2231_, lean_object* v_fallback_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Std_DTreeMap_Const_getEntryGTD(v_00_u03b1_2227_, v_cmp_2228_, v_00_u03b2_2229_, v_t_2230_, v_k_2231_, v_fallback_2232_);
lean_dec_ref(v_fallback_2232_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___redArg(lean_object* v_cmp_2234_, lean_object* v_t_2235_, lean_object* v_k_2236_, lean_object* v_fallback_2237_){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_box(0);
v___x_2239_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2234_, v_k_2236_, v___x_2238_, v_t_2235_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_inc_ref(v_fallback_2237_);
return v_fallback_2237_;
}
else
{
lean_object* v_val_2240_; 
v_val_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_val_2240_);
lean_dec_ref_known(v___x_2239_, 1);
return v_val_2240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2241_, lean_object* v_t_2242_, lean_object* v_k_2243_, lean_object* v_fallback_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Std_DTreeMap_Const_getEntryLED___redArg(v_cmp_2241_, v_t_2242_, v_k_2243_, v_fallback_2244_);
lean_dec_ref(v_fallback_2244_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED(lean_object* v_00_u03b1_2246_, lean_object* v_cmp_2247_, lean_object* v_00_u03b2_2248_, lean_object* v_t_2249_, lean_object* v_k_2250_, lean_object* v_fallback_2251_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_box(0);
v___x_2253_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2247_, v_k_2250_, v___x_2252_, v_t_2249_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_inc_ref(v_fallback_2251_);
return v_fallback_2251_;
}
else
{
lean_object* v_val_2254_; 
v_val_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_val_2254_);
lean_dec_ref_known(v___x_2253_, 1);
return v_val_2254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2255_, lean_object* v_cmp_2256_, lean_object* v_00_u03b2_2257_, lean_object* v_t_2258_, lean_object* v_k_2259_, lean_object* v_fallback_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Std_DTreeMap_Const_getEntryLED(v_00_u03b1_2255_, v_cmp_2256_, v_00_u03b2_2257_, v_t_2258_, v_k_2259_, v_fallback_2260_);
lean_dec_ref(v_fallback_2260_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___redArg(lean_object* v_cmp_2262_, lean_object* v_t_2263_, lean_object* v_k_2264_, lean_object* v_fallback_2265_){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2262_, v_k_2264_, v___x_2266_, v_t_2263_);
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
lean_dec_ref_known(v___x_2267_, 1);
return v_val_2268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2269_, lean_object* v_t_2270_, lean_object* v_k_2271_, lean_object* v_fallback_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Std_DTreeMap_Const_getEntryLTD___redArg(v_cmp_2269_, v_t_2270_, v_k_2271_, v_fallback_2272_);
lean_dec_ref(v_fallback_2272_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD(lean_object* v_00_u03b1_2274_, lean_object* v_cmp_2275_, lean_object* v_00_u03b2_2276_, lean_object* v_t_2277_, lean_object* v_k_2278_, lean_object* v_fallback_2279_){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_box(0);
v___x_2281_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2275_, v_k_2278_, v___x_2280_, v_t_2277_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_inc_ref(v_fallback_2279_);
return v_fallback_2279_;
}
else
{
lean_object* v_val_2282_; 
v_val_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_val_2282_);
lean_dec_ref_known(v___x_2281_, 1);
return v_val_2282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2283_, lean_object* v_cmp_2284_, lean_object* v_00_u03b2_2285_, lean_object* v_t_2286_, lean_object* v_k_2287_, lean_object* v_fallback_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Std_DTreeMap_Const_getEntryLTD(v_00_u03b1_2283_, v_cmp_2284_, v_00_u03b2_2285_, v_t_2286_, v_k_2287_, v_fallback_2288_);
lean_dec_ref(v_fallback_2288_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter___redArg(lean_object* v_f_2290_, lean_object* v_t_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2290_, v_t_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter(lean_object* v_00_u03b1_2293_, lean_object* v_00_u03b2_2294_, lean_object* v_cmp_2295_, lean_object* v_f_2296_, lean_object* v_t_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_2296_, v_t_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filter___boxed(lean_object* v_00_u03b1_2299_, lean_object* v_00_u03b2_2300_, lean_object* v_cmp_2301_, lean_object* v_f_2302_, lean_object* v_t_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Std_DTreeMap_filter(v_00_u03b1_2299_, v_00_u03b2_2300_, v_cmp_2301_, v_f_2302_, v_t_2303_);
lean_dec_ref(v_cmp_2301_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM___redArg(lean_object* v_inst_2305_, lean_object* v_f_2306_, lean_object* v_init_2307_, lean_object* v_t_2308_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2305_, v_f_2306_, v_init_2307_, v_t_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM(lean_object* v_00_u03b1_2310_, lean_object* v_00_u03b2_2311_, lean_object* v_cmp_2312_, lean_object* v_00_u03b4_2313_, lean_object* v_m_2314_, lean_object* v_inst_2315_, lean_object* v_f_2316_, lean_object* v_init_2317_, lean_object* v_t_2318_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2315_, v_f_2316_, v_init_2317_, v_t_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldlM___boxed(lean_object* v_00_u03b1_2320_, lean_object* v_00_u03b2_2321_, lean_object* v_cmp_2322_, lean_object* v_00_u03b4_2323_, lean_object* v_m_2324_, lean_object* v_inst_2325_, lean_object* v_f_2326_, lean_object* v_init_2327_, lean_object* v_t_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Std_DTreeMap_foldlM(v_00_u03b1_2320_, v_00_u03b2_2321_, v_cmp_2322_, v_00_u03b4_2323_, v_m_2324_, v_inst_2325_, v_f_2326_, v_init_2327_, v_t_2328_);
lean_dec_ref(v_cmp_2322_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl___redArg(lean_object* v_f_2330_, lean_object* v_init_2331_, lean_object* v_t_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2330_, v_init_2331_, v_t_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl(lean_object* v_00_u03b1_2334_, lean_object* v_00_u03b2_2335_, lean_object* v_cmp_2336_, lean_object* v_00_u03b4_2337_, lean_object* v_f_2338_, lean_object* v_init_2339_, lean_object* v_t_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2338_, v_init_2339_, v_t_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldl___boxed(lean_object* v_00_u03b1_2342_, lean_object* v_00_u03b2_2343_, lean_object* v_cmp_2344_, lean_object* v_00_u03b4_2345_, lean_object* v_f_2346_, lean_object* v_init_2347_, lean_object* v_t_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Std_DTreeMap_foldl(v_00_u03b1_2342_, v_00_u03b2_2343_, v_cmp_2344_, v_00_u03b4_2345_, v_f_2346_, v_init_2347_, v_t_2348_);
lean_dec_ref(v_cmp_2344_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM___redArg(lean_object* v_inst_2350_, lean_object* v_f_2351_, lean_object* v_init_2352_, lean_object* v_t_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2350_, v_f_2351_, v_init_2352_, v_t_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM(lean_object* v_00_u03b1_2355_, lean_object* v_00_u03b2_2356_, lean_object* v_cmp_2357_, lean_object* v_00_u03b4_2358_, lean_object* v_m_2359_, lean_object* v_inst_2360_, lean_object* v_f_2361_, lean_object* v_init_2362_, lean_object* v_t_2363_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2360_, v_f_2361_, v_init_2362_, v_t_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldrM___boxed(lean_object* v_00_u03b1_2365_, lean_object* v_00_u03b2_2366_, lean_object* v_cmp_2367_, lean_object* v_00_u03b4_2368_, lean_object* v_m_2369_, lean_object* v_inst_2370_, lean_object* v_f_2371_, lean_object* v_init_2372_, lean_object* v_t_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Std_DTreeMap_foldrM(v_00_u03b1_2365_, v_00_u03b2_2366_, v_cmp_2367_, v_00_u03b4_2368_, v_m_2369_, v_inst_2370_, v_f_2371_, v_init_2372_, v_t_2373_);
lean_dec_ref(v_cmp_2367_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___redArg___lam__0(lean_object* v_f_2375_, lean_object* v_x1_2376_, lean_object* v_x2_2377_, lean_object* v_x3_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_apply_3(v_f_2375_, v_x1_2376_, v_x2_2377_, v_x3_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___redArg(lean_object* v_f_2399_, lean_object* v_init_2400_, lean_object* v_t_2401_){
_start:
{
lean_object* v___f_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___f_2402_ = lean_alloc_closure((void*)(l_Std_DTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2402_, 0, v_f_2399_);
v___x_2403_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2404_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2403_, v___f_2402_, v_init_2400_, v_t_2401_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr(lean_object* v_00_u03b1_2405_, lean_object* v_00_u03b2_2406_, lean_object* v_cmp_2407_, lean_object* v_00_u03b4_2408_, lean_object* v_f_2409_, lean_object* v_init_2410_, lean_object* v_t_2411_){
_start:
{
lean_object* v___f_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___f_2412_ = lean_alloc_closure((void*)(l_Std_DTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2412_, 0, v_f_2409_);
v___x_2413_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2414_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2413_, v___f_2412_, v_init_2410_, v_t_2411_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_foldr___boxed(lean_object* v_00_u03b1_2415_, lean_object* v_00_u03b2_2416_, lean_object* v_cmp_2417_, lean_object* v_00_u03b4_2418_, lean_object* v_f_2419_, lean_object* v_init_2420_, lean_object* v_t_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Std_DTreeMap_foldr(v_00_u03b1_2415_, v_00_u03b2_2416_, v_cmp_2417_, v_00_u03b4_2418_, v_f_2419_, v_init_2420_, v_t_2421_);
lean_dec_ref(v_cmp_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition___redArg___lam__0(lean_object* v_f_2423_, lean_object* v_cmp_2424_, lean_object* v_x_2425_, lean_object* v_a_2426_, lean_object* v_b_2427_){
_start:
{
lean_object* v_fst_2428_; lean_object* v_snd_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2443_; 
v_fst_2428_ = lean_ctor_get(v_x_2425_, 0);
v_snd_2429_ = lean_ctor_get(v_x_2425_, 1);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_x_2425_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2431_ = v_x_2425_;
v_isShared_2432_ = v_isSharedCheck_2443_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_snd_2429_);
lean_inc(v_fst_2428_);
lean_dec(v_x_2425_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2443_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; uint8_t v___x_2434_; 
lean_inc(v_b_2427_);
lean_inc(v_a_2426_);
v___x_2433_ = lean_apply_2(v_f_2423_, v_a_2426_, v_b_2427_);
v___x_2434_ = lean_unbox(v___x_2433_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2435_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2424_, v_a_2426_, v_b_2427_, v_snd_2429_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 1, v___x_2435_);
v___x_2437_ = v___x_2431_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_fst_2428_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
else
{
lean_object* v___x_2439_; lean_object* v___x_2441_; 
v___x_2439_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2424_, v_a_2426_, v_b_2427_, v_fst_2428_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v___x_2439_);
v___x_2441_ = v___x_2431_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_snd_2429_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition___redArg(lean_object* v_cmp_2446_, lean_object* v_f_2447_, lean_object* v_t_2448_){
_start:
{
lean_object* v___f_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___f_2449_ = lean_alloc_closure((void*)(l_Std_DTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2449_, 0, v_f_2447_);
lean_closure_set(v___f_2449_, 1, v_cmp_2446_);
v___x_2450_ = ((lean_object*)(l_Std_DTreeMap_partition___redArg___closed__0));
v___x_2451_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2449_, v___x_2450_, v_t_2448_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_partition(lean_object* v_00_u03b1_2452_, lean_object* v_00_u03b2_2453_, lean_object* v_cmp_2454_, lean_object* v_f_2455_, lean_object* v_t_2456_){
_start:
{
lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___f_2457_ = lean_alloc_closure((void*)(l_Std_DTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2457_, 0, v_f_2455_);
lean_closure_set(v___f_2457_, 1, v_cmp_2454_);
v___x_2458_ = ((lean_object*)(l_Std_DTreeMap_partition___redArg___closed__0));
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2457_, v___x_2458_, v_t_2456_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___redArg___lam__0(lean_object* v_f_2460_, lean_object* v_x_2461_, lean_object* v_k_2462_, lean_object* v_v_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_apply_2(v_f_2460_, v_k_2462_, v_v_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___redArg(lean_object* v_inst_2465_, lean_object* v_f_2466_, lean_object* v_t_2467_){
_start:
{
lean_object* v___f_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___f_2468_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2468_, 0, v_f_2466_);
v___x_2469_ = lean_box(0);
v___x_2470_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2465_, v___f_2468_, v___x_2469_, v_t_2467_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM(lean_object* v_00_u03b1_2471_, lean_object* v_00_u03b2_2472_, lean_object* v_cmp_2473_, lean_object* v_m_2474_, lean_object* v_inst_2475_, lean_object* v_f_2476_, lean_object* v_t_2477_){
_start:
{
lean_object* v___f_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___f_2478_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2478_, 0, v_f_2476_);
v___x_2479_ = lean_box(0);
v___x_2480_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2475_, v___f_2478_, v___x_2479_, v_t_2477_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forM___boxed(lean_object* v_00_u03b1_2481_, lean_object* v_00_u03b2_2482_, lean_object* v_cmp_2483_, lean_object* v_m_2484_, lean_object* v_inst_2485_, lean_object* v_f_2486_, lean_object* v_t_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Std_DTreeMap_forM(v_00_u03b1_2481_, v_00_u03b2_2482_, v_cmp_2483_, v_m_2484_, v_inst_2485_, v_f_2486_, v_t_2487_);
lean_dec_ref(v_cmp_2483_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___redArg___lam__0(lean_object* v_toPure_2489_, lean_object* v_____do__lift_2490_){
_start:
{
lean_object* v_a_2491_; lean_object* v___x_2492_; 
v_a_2491_ = lean_ctor_get(v_____do__lift_2490_, 0);
lean_inc(v_a_2491_);
lean_dec_ref(v_____do__lift_2490_);
v___x_2492_ = lean_apply_2(v_toPure_2489_, lean_box(0), v_a_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___redArg(lean_object* v_inst_2493_, lean_object* v_f_2494_, lean_object* v_init_2495_, lean_object* v_t_2496_){
_start:
{
lean_object* v_toApplicative_2497_; lean_object* v_toBind_2498_; lean_object* v_toPure_2499_; lean_object* v___x_2500_; lean_object* v___f_2501_; lean_object* v___x_2502_; 
v_toApplicative_2497_ = lean_ctor_get(v_inst_2493_, 0);
v_toBind_2498_ = lean_ctor_get(v_inst_2493_, 1);
lean_inc(v_toBind_2498_);
v_toPure_2499_ = lean_ctor_get(v_toApplicative_2497_, 1);
lean_inc(v_toPure_2499_);
v___x_2500_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2493_, v_f_2494_, v_init_2495_, v_t_2496_);
v___f_2501_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2501_, 0, v_toPure_2499_);
v___x_2502_ = lean_apply_4(v_toBind_2498_, lean_box(0), lean_box(0), v___x_2500_, v___f_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn(lean_object* v_00_u03b1_2503_, lean_object* v_00_u03b2_2504_, lean_object* v_cmp_2505_, lean_object* v_00_u03b4_2506_, lean_object* v_m_2507_, lean_object* v_inst_2508_, lean_object* v_f_2509_, lean_object* v_init_2510_, lean_object* v_t_2511_){
_start:
{
lean_object* v_toApplicative_2512_; lean_object* v_toBind_2513_; lean_object* v_toPure_2514_; lean_object* v___x_2515_; lean_object* v___f_2516_; lean_object* v___x_2517_; 
v_toApplicative_2512_ = lean_ctor_get(v_inst_2508_, 0);
v_toBind_2513_ = lean_ctor_get(v_inst_2508_, 1);
lean_inc(v_toBind_2513_);
v_toPure_2514_ = lean_ctor_get(v_toApplicative_2512_, 1);
lean_inc(v_toPure_2514_);
v___x_2515_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2508_, v_f_2509_, v_init_2510_, v_t_2511_);
v___f_2516_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2516_, 0, v_toPure_2514_);
v___x_2517_ = lean_apply_4(v_toBind_2513_, lean_box(0), lean_box(0), v___x_2515_, v___f_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_forIn___boxed(lean_object* v_00_u03b1_2518_, lean_object* v_00_u03b2_2519_, lean_object* v_cmp_2520_, lean_object* v_00_u03b4_2521_, lean_object* v_m_2522_, lean_object* v_inst_2523_, lean_object* v_f_2524_, lean_object* v_init_2525_, lean_object* v_t_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Std_DTreeMap_forIn(v_00_u03b1_2518_, v_00_u03b2_2519_, v_cmp_2520_, v_00_u03b4_2521_, v_m_2522_, v_inst_2523_, v_f_2524_, v_init_2525_, v_t_2526_);
lean_dec_ref(v_cmp_2520_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_2528_, lean_object* v_x_2529_, lean_object* v_k_2530_, lean_object* v_v_2531_){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v_k_2530_);
lean_ctor_set(v___x_2532_, 1, v_v_2531_);
v___x_2533_ = lean_apply_1(v_f_2528_, v___x_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1(lean_object* v_inst_2534_, lean_object* v_t_2535_, lean_object* v_f_2536_){
_start:
{
lean_object* v___f_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___f_2537_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2537_, 0, v_f_2536_);
v___x_2538_ = lean_box(0);
v___x_2539_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2534_, v___f_2537_, v___x_2538_, v_t_2535_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___redArg(lean_object* v_inst_2540_){
_start:
{
lean_object* v___f_2541_; 
v___f_2541_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2541_, 0, v_inst_2540_);
return v___f_2541_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad(lean_object* v_00_u03b1_2542_, lean_object* v_00_u03b2_2543_, lean_object* v_cmp_2544_, lean_object* v_m_2545_, lean_object* v_inst_2546_){
_start:
{
lean_object* v___f_2547_; 
v___f_2547_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2547_, 0, v_inst_2546_);
return v___f_2547_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForMSigmaOfMonad___boxed(lean_object* v_00_u03b1_2548_, lean_object* v_00_u03b2_2549_, lean_object* v_cmp_2550_, lean_object* v_m_2551_, lean_object* v_inst_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Std_DTreeMap_instForMSigmaOfMonad(v_00_u03b1_2548_, v_00_u03b2_2549_, v_cmp_2550_, v_m_2551_, v_inst_2552_);
lean_dec_ref(v_cmp_2550_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_2554_, lean_object* v_a_2555_, lean_object* v_b_2556_, lean_object* v_acc_2557_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_a_2555_);
lean_ctor_set(v___x_2558_, 1, v_b_2556_);
v___x_2559_ = lean_apply_2(v_f_2554_, v___x_2558_, v_acc_2557_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_2560_, lean_object* v_00_u03b2_2561_, lean_object* v_m_2562_, lean_object* v_init_2563_, lean_object* v_f_2564_){
_start:
{
lean_object* v_toApplicative_2565_; lean_object* v_toBind_2566_; lean_object* v_toPure_2567_; lean_object* v___f_2568_; lean_object* v___x_2569_; lean_object* v___f_2570_; lean_object* v___x_2571_; 
v_toApplicative_2565_ = lean_ctor_get(v_inst_2560_, 0);
v_toBind_2566_ = lean_ctor_get(v_inst_2560_, 1);
lean_inc(v_toBind_2566_);
v_toPure_2567_ = lean_ctor_get(v_toApplicative_2565_, 1);
lean_inc(v_toPure_2567_);
v___f_2568_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2568_, 0, v_f_2564_);
v___x_2569_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2560_, v___f_2568_, v_init_2563_, v_m_2562_);
v___f_2570_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2570_, 0, v_toPure_2567_);
v___x_2571_ = lean_apply_4(v_toBind_2566_, lean_box(0), lean_box(0), v___x_2569_, v___f_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___redArg(lean_object* v_inst_2572_){
_start:
{
lean_object* v___f_2573_; 
v___f_2573_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2573_, 0, v_inst_2572_);
return v___f_2573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad(lean_object* v_00_u03b1_2574_, lean_object* v_00_u03b2_2575_, lean_object* v_cmp_2576_, lean_object* v_m_2577_, lean_object* v_inst_2578_){
_start:
{
lean_object* v___f_2579_; 
v___f_2579_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2579_, 0, v_inst_2578_);
return v___f_2579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instForInSigmaOfMonad___boxed(lean_object* v_00_u03b1_2580_, lean_object* v_00_u03b2_2581_, lean_object* v_cmp_2582_, lean_object* v_m_2583_, lean_object* v_inst_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Std_DTreeMap_instForInSigmaOfMonad(v_00_u03b1_2580_, v_00_u03b2_2581_, v_cmp_2582_, v_m_2583_, v_inst_2584_);
lean_dec_ref(v_cmp_2582_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2586_, lean_object* v_x_2587_, lean_object* v_k_2588_, lean_object* v_v_2589_){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v_k_2588_);
lean_ctor_set(v___x_2590_, 1, v_v_2589_);
v___x_2591_ = lean_apply_1(v_f_2586_, v___x_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___redArg(lean_object* v_inst_2592_, lean_object* v_f_2593_, lean_object* v_t_2594_){
_start:
{
lean_object* v___f_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___f_2595_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2595_, 0, v_f_2593_);
v___x_2596_ = lean_box(0);
v___x_2597_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2592_, v___f_2595_, v___x_2596_, v_t_2594_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried(lean_object* v_00_u03b1_2598_, lean_object* v_cmp_2599_, lean_object* v_m_2600_, lean_object* v_inst_2601_, lean_object* v_00_u03b2_2602_, lean_object* v_f_2603_, lean_object* v_t_2604_){
_start:
{
lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___f_2605_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2605_, 0, v_f_2603_);
v___x_2606_ = lean_box(0);
v___x_2607_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2601_, v___f_2605_, v___x_2606_, v_t_2604_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2608_, lean_object* v_cmp_2609_, lean_object* v_m_2610_, lean_object* v_inst_2611_, lean_object* v_00_u03b2_2612_, lean_object* v_f_2613_, lean_object* v_t_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Std_DTreeMap_Const_forMUncurried(v_00_u03b1_2608_, v_cmp_2609_, v_m_2610_, v_inst_2611_, v_00_u03b2_2612_, v_f_2613_, v_t_2614_);
lean_dec_ref(v_cmp_2609_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2616_, lean_object* v_a_2617_, lean_object* v_b_2618_, lean_object* v_acc_2619_){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v_a_2617_);
lean_ctor_set(v___x_2620_, 1, v_b_2618_);
v___x_2621_ = lean_apply_2(v_f_2616_, v___x_2620_, v_acc_2619_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___redArg(lean_object* v_inst_2622_, lean_object* v_f_2623_, lean_object* v_init_2624_, lean_object* v_t_2625_){
_start:
{
lean_object* v_toApplicative_2626_; lean_object* v_toBind_2627_; lean_object* v_toPure_2628_; lean_object* v___f_2629_; lean_object* v___x_2630_; lean_object* v___f_2631_; lean_object* v___x_2632_; 
v_toApplicative_2626_ = lean_ctor_get(v_inst_2622_, 0);
v_toBind_2627_ = lean_ctor_get(v_inst_2622_, 1);
lean_inc(v_toBind_2627_);
v_toPure_2628_ = lean_ctor_get(v_toApplicative_2626_, 1);
lean_inc(v_toPure_2628_);
v___f_2629_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2629_, 0, v_f_2623_);
v___x_2630_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2622_, v___f_2629_, v_init_2624_, v_t_2625_);
v___f_2631_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2631_, 0, v_toPure_2628_);
v___x_2632_ = lean_apply_4(v_toBind_2627_, lean_box(0), lean_box(0), v___x_2630_, v___f_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried(lean_object* v_00_u03b1_2633_, lean_object* v_cmp_2634_, lean_object* v_00_u03b4_2635_, lean_object* v_m_2636_, lean_object* v_inst_2637_, lean_object* v_00_u03b2_2638_, lean_object* v_f_2639_, lean_object* v_init_2640_, lean_object* v_t_2641_){
_start:
{
lean_object* v_toApplicative_2642_; lean_object* v_toBind_2643_; lean_object* v_toPure_2644_; lean_object* v___f_2645_; lean_object* v___x_2646_; lean_object* v___f_2647_; lean_object* v___x_2648_; 
v_toApplicative_2642_ = lean_ctor_get(v_inst_2637_, 0);
v_toBind_2643_ = lean_ctor_get(v_inst_2637_, 1);
lean_inc(v_toBind_2643_);
v_toPure_2644_ = lean_ctor_get(v_toApplicative_2642_, 1);
lean_inc(v_toPure_2644_);
v___f_2645_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2645_, 0, v_f_2639_);
v___x_2646_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2637_, v___f_2645_, v_init_2640_, v_t_2641_);
v___f_2647_ = lean_alloc_closure((void*)(l_Std_DTreeMap_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2647_, 0, v_toPure_2644_);
v___x_2648_ = lean_apply_4(v_toBind_2643_, lean_box(0), lean_box(0), v___x_2646_, v___f_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2649_, lean_object* v_cmp_2650_, lean_object* v_00_u03b4_2651_, lean_object* v_m_2652_, lean_object* v_inst_2653_, lean_object* v_00_u03b2_2654_, lean_object* v_f_2655_, lean_object* v_init_2656_, lean_object* v_t_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Std_DTreeMap_Const_forInUncurried(v_00_u03b1_2649_, v_cmp_2650_, v_00_u03b4_2651_, v_m_2652_, v_inst_2653_, v_00_u03b2_2654_, v_f_2655_, v_init_2656_, v_t_2657_);
lean_dec_ref(v_cmp_2650_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___lam__0(lean_object* v_p_2659_, lean_object* v___x_2660_, lean_object* v___x_2661_, lean_object* v_a_2662_, lean_object* v_b_2663_, lean_object* v_acc_2664_){
_start:
{
lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2665_ = lean_apply_2(v_p_2659_, v_a_2662_, v_b_2663_);
v___x_2666_ = lean_unbox(v___x_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
v___x_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2660_);
return v___x_2667_;
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
lean_dec_ref(v___x_2660_);
v___x_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2665_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
lean_ctor_set(v___x_2669_, 1, v___x_2661_);
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
return v___x_2670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2671_, lean_object* v___x_2672_, lean_object* v___x_2673_, lean_object* v_a_2674_, lean_object* v_b_2675_, lean_object* v_acc_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Std_DTreeMap_any___redArg___lam__0(v_p_2671_, v___x_2672_, v___x_2673_, v_a_2674_, v_b_2675_, v_acc_2676_);
lean_dec_ref(v_acc_2676_);
return v_res_2677_;
}
}
uint8_t l_Std_DTreeMap_any___redArg(lean_object* v_t_2681_, lean_object* v_p_2682_){
_start:
{
lean_object* v___y_2684_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___f_2692_; lean_object* v___x_2693_; lean_object* v_a_2694_; 
v___x_2689_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2690_ = lean_box(0);
v___x_2691_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2692_ = lean_alloc_closure((void*)(l_Std_DTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2692_, 0, v_p_2682_);
lean_closure_set(v___f_2692_, 1, v___x_2691_);
lean_closure_set(v___f_2692_, 2, v___x_2690_);
v___x_2693_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2689_, v___f_2692_, v___x_2691_, v_t_2681_);
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___y_2684_ = v_a_2694_;
goto v___jp_2683_;
v___jp_2683_:
{
lean_object* v_fst_2685_; 
v_fst_2685_ = lean_ctor_get(v___y_2684_, 0);
lean_inc(v_fst_2685_);
lean_dec_ref(v___y_2684_);
if (lean_obj_tag(v_fst_2685_) == 0)
{
uint8_t v___x_2686_; 
v___x_2686_ = 0;
return v___x_2686_;
}
else
{
lean_object* v_val_2687_; uint8_t v___x_2688_; 
v_val_2687_ = lean_ctor_get(v_fst_2685_, 0);
lean_inc(v_val_2687_);
lean_dec_ref_known(v_fst_2685_, 1);
v___x_2688_ = lean_unbox(v_val_2687_);
lean_dec(v_val_2687_);
return v___x_2688_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2681_ = stack[0].m_obj;
lean_object* v_p_2682_ = stack[1].m_obj;
uint8_t v_res_2695_;
v_res_2695_ = l_Std_DTreeMap_any___redArg(v_t_2681_, v_p_2682_);
stack->m_num = v_res_2695_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___redArg___boxed(lean_object* v_t_2696_, lean_object* v_p_2697_){
_start:
{
uint8_t v_res_2698_; lean_object* v_r_2699_; 
v_res_2698_ = l_Std_DTreeMap_any___redArg(v_t_2696_, v_p_2697_);
v_r_2699_ = lean_box(v_res_2698_);
return v_r_2699_;
}
}
uint8_t l_Std_DTreeMap_any(lean_object* v_00_u03b1_2700_, lean_object* v_00_u03b2_2701_, lean_object* v_cmp_2702_, lean_object* v_t_2703_, lean_object* v_p_2704_){
_start:
{
lean_object* v___y_2706_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___f_2714_; lean_object* v___x_2715_; lean_object* v_a_2716_; 
v___x_2711_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2712_ = lean_box(0);
v___x_2713_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2714_ = lean_alloc_closure((void*)(l_Std_DTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2714_, 0, v_p_2704_);
lean_closure_set(v___f_2714_, 1, v___x_2713_);
lean_closure_set(v___f_2714_, 2, v___x_2712_);
v___x_2715_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2711_, v___f_2714_, v___x_2713_, v_t_2703_);
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___y_2706_ = v_a_2716_;
goto v___jp_2705_;
v___jp_2705_:
{
lean_object* v_fst_2707_; 
v_fst_2707_ = lean_ctor_get(v___y_2706_, 0);
lean_inc(v_fst_2707_);
lean_dec_ref(v___y_2706_);
if (lean_obj_tag(v_fst_2707_) == 0)
{
uint8_t v___x_2708_; 
v___x_2708_ = 0;
return v___x_2708_;
}
else
{
lean_object* v_val_2709_; uint8_t v___x_2710_; 
v_val_2709_ = lean_ctor_get(v_fst_2707_, 0);
lean_inc(v_val_2709_);
lean_dec_ref_known(v_fst_2707_, 1);
v___x_2710_ = lean_unbox(v_val_2709_);
lean_dec(v_val_2709_);
return v___x_2710_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2702_ = stack[2].m_obj;
lean_object* v_t_2703_ = stack[3].m_obj;
lean_object* v_p_2704_ = stack[4].m_obj;
uint8_t v_res_2717_;
v_res_2717_ = l_Std_DTreeMap_any(lean_box(0), lean_box(0), v_cmp_2702_, v_t_2703_, v_p_2704_);
stack->m_num = v_res_2717_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_any___boxed(lean_object* v_00_u03b1_2718_, lean_object* v_00_u03b2_2719_, lean_object* v_cmp_2720_, lean_object* v_t_2721_, lean_object* v_p_2722_){
_start:
{
uint8_t v_res_2723_; lean_object* v_r_2724_; 
v_res_2723_ = l_Std_DTreeMap_any(v_00_u03b1_2718_, v_00_u03b2_2719_, v_cmp_2720_, v_t_2721_, v_p_2722_);
lean_dec_ref(v_cmp_2720_);
v_r_2724_ = lean_box(v_res_2723_);
return v_r_2724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___lam__0(lean_object* v_p_2725_, lean_object* v___x_2726_, lean_object* v___x_2727_, lean_object* v_a_2728_, lean_object* v_b_2729_, lean_object* v_acc_2730_){
_start:
{
lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = lean_apply_2(v_p_2725_, v_a_2728_, v_b_2729_);
v___x_2732_ = lean_unbox(v___x_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
lean_dec_ref(v___x_2727_);
v___x_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2731_);
v___x_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
lean_ctor_set(v___x_2734_, 1, v___x_2726_);
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
return v___x_2735_;
}
else
{
lean_object* v___x_2736_; 
v___x_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2727_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_2737_, lean_object* v___x_2738_, lean_object* v___x_2739_, lean_object* v_a_2740_, lean_object* v_b_2741_, lean_object* v_acc_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Std_DTreeMap_all___redArg___lam__0(v_p_2737_, v___x_2738_, v___x_2739_, v_a_2740_, v_b_2741_, v_acc_2742_);
lean_dec_ref(v_acc_2742_);
return v_res_2743_;
}
}
uint8_t l_Std_DTreeMap_all___redArg(lean_object* v_t_2744_, lean_object* v_p_2745_){
_start:
{
lean_object* v___y_2747_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___f_2755_; lean_object* v___x_2756_; lean_object* v_a_2757_; 
v___x_2752_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2753_ = lean_box(0);
v___x_2754_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2755_ = lean_alloc_closure((void*)(l_Std_DTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2755_, 0, v_p_2745_);
lean_closure_set(v___f_2755_, 1, v___x_2753_);
lean_closure_set(v___f_2755_, 2, v___x_2754_);
v___x_2756_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2752_, v___f_2755_, v___x_2754_, v_t_2744_);
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___y_2747_ = v_a_2757_;
goto v___jp_2746_;
v___jp_2746_:
{
lean_object* v_fst_2748_; 
v_fst_2748_ = lean_ctor_get(v___y_2747_, 0);
lean_inc(v_fst_2748_);
lean_dec_ref(v___y_2747_);
if (lean_obj_tag(v_fst_2748_) == 0)
{
uint8_t v___x_2749_; 
v___x_2749_ = 1;
return v___x_2749_;
}
else
{
lean_object* v_val_2750_; uint8_t v___x_2751_; 
v_val_2750_ = lean_ctor_get(v_fst_2748_, 0);
lean_inc(v_val_2750_);
lean_dec_ref_known(v_fst_2748_, 1);
v___x_2751_ = lean_unbox(v_val_2750_);
lean_dec(v_val_2750_);
return v___x_2751_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2744_ = stack[0].m_obj;
lean_object* v_p_2745_ = stack[1].m_obj;
uint8_t v_res_2758_;
v_res_2758_ = l_Std_DTreeMap_all___redArg(v_t_2744_, v_p_2745_);
stack->m_num = v_res_2758_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___redArg___boxed(lean_object* v_t_2759_, lean_object* v_p_2760_){
_start:
{
uint8_t v_res_2761_; lean_object* v_r_2762_; 
v_res_2761_ = l_Std_DTreeMap_all___redArg(v_t_2759_, v_p_2760_);
v_r_2762_ = lean_box(v_res_2761_);
return v_r_2762_;
}
}
uint8_t l_Std_DTreeMap_all(lean_object* v_00_u03b1_2763_, lean_object* v_00_u03b2_2764_, lean_object* v_cmp_2765_, lean_object* v_t_2766_, lean_object* v_p_2767_){
_start:
{
lean_object* v___y_2769_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___f_2777_; lean_object* v___x_2778_; lean_object* v_a_2779_; 
v___x_2774_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2775_ = lean_box(0);
v___x_2776_ = ((lean_object*)(l_Std_DTreeMap_any___redArg___closed__0));
v___f_2777_ = lean_alloc_closure((void*)(l_Std_DTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2777_, 0, v_p_2767_);
lean_closure_set(v___f_2777_, 1, v___x_2775_);
lean_closure_set(v___f_2777_, 2, v___x_2776_);
v___x_2778_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2774_, v___f_2777_, v___x_2776_, v_t_2766_);
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___y_2769_ = v_a_2779_;
goto v___jp_2768_;
v___jp_2768_:
{
lean_object* v_fst_2770_; 
v_fst_2770_ = lean_ctor_get(v___y_2769_, 0);
lean_inc(v_fst_2770_);
lean_dec_ref(v___y_2769_);
if (lean_obj_tag(v_fst_2770_) == 0)
{
uint8_t v___x_2771_; 
v___x_2771_ = 1;
return v___x_2771_;
}
else
{
lean_object* v_val_2772_; uint8_t v___x_2773_; 
v_val_2772_ = lean_ctor_get(v_fst_2770_, 0);
lean_inc(v_val_2772_);
lean_dec_ref_known(v_fst_2770_, 1);
v___x_2773_ = lean_unbox(v_val_2772_);
lean_dec(v_val_2772_);
return v___x_2773_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2765_ = stack[2].m_obj;
lean_object* v_t_2766_ = stack[3].m_obj;
lean_object* v_p_2767_ = stack[4].m_obj;
uint8_t v_res_2780_;
v_res_2780_ = l_Std_DTreeMap_all(lean_box(0), lean_box(0), v_cmp_2765_, v_t_2766_, v_p_2767_);
stack->m_num = v_res_2780_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_all___boxed(lean_object* v_00_u03b1_2781_, lean_object* v_00_u03b2_2782_, lean_object* v_cmp_2783_, lean_object* v_t_2784_, lean_object* v_p_2785_){
_start:
{
uint8_t v_res_2786_; lean_object* v_r_2787_; 
v_res_2786_ = l_Std_DTreeMap_all(v_00_u03b1_2781_, v_00_u03b2_2782_, v_cmp_2783_, v_t_2784_, v_p_2785_);
lean_dec_ref(v_cmp_2783_);
v_r_2787_ = lean_box(v_res_2786_);
return v_r_2787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg___lam__0(lean_object* v_x1_2788_, lean_object* v_x2_2789_, lean_object* v_x3_2790_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2791_, 0, v_x1_2788_);
lean_ctor_set(v___x_2791_, 1, v_x3_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_2792_, lean_object* v_x2_2793_, lean_object* v_x3_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Std_DTreeMap_keys___redArg___lam__0(v_x1_2792_, v_x2_2793_, v_x3_2794_);
lean_dec(v_x2_2793_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___redArg(lean_object* v_t_2797_){
_start:
{
lean_object* v___f_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___f_2798_ = ((lean_object*)(l_Std_DTreeMap_keys___redArg___closed__0));
v___x_2799_ = lean_box(0);
v___x_2800_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2801_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2800_, v___f_2798_, v___x_2799_, v_t_2797_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys(lean_object* v_00_u03b1_2802_, lean_object* v_00_u03b2_2803_, lean_object* v_cmp_2804_, lean_object* v_t_2805_){
_start:
{
lean_object* v___f_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___f_2806_ = ((lean_object*)(l_Std_DTreeMap_keys___redArg___closed__0));
v___x_2807_ = lean_box(0);
v___x_2808_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2809_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2808_, v___f_2806_, v___x_2807_, v_t_2805_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keys___boxed(lean_object* v_00_u03b1_2810_, lean_object* v_00_u03b2_2811_, lean_object* v_cmp_2812_, lean_object* v_t_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Std_DTreeMap_keys(v_00_u03b1_2810_, v_00_u03b2_2811_, v_cmp_2812_, v_t_2813_);
lean_dec_ref(v_cmp_2812_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg___lam__0(lean_object* v_l_2815_, lean_object* v_k_2816_, lean_object* v_x_2817_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_array_push(v_l_2815_, v_k_2816_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_2819_, lean_object* v_k_2820_, lean_object* v_x_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Std_DTreeMap_keysArray___redArg___lam__0(v_l_2819_, v_k_2820_, v_x_2821_);
lean_dec(v_x_2821_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___redArg(lean_object* v_t_2824_){
_start:
{
lean_object* v___f_2825_; lean_object* v___y_2827_; 
v___f_2825_ = ((lean_object*)(l_Std_DTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2824_) == 0)
{
lean_object* v_size_2830_; 
v_size_2830_ = lean_ctor_get(v_t_2824_, 0);
lean_inc(v_size_2830_);
v___y_2827_ = v_size_2830_;
goto v___jp_2826_;
}
else
{
lean_object* v___x_2831_; 
v___x_2831_ = lean_unsigned_to_nat(0u);
v___y_2827_ = v___x_2831_;
goto v___jp_2826_;
}
v___jp_2826_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_mk_empty_array_with_capacity(v___y_2827_);
lean_dec(v___y_2827_);
v___x_2829_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2825_, v___x_2828_, v_t_2824_);
return v___x_2829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray(lean_object* v_00_u03b1_2832_, lean_object* v_00_u03b2_2833_, lean_object* v_cmp_2834_, lean_object* v_t_2835_){
_start:
{
lean_object* v___f_2836_; lean_object* v___y_2838_; 
v___f_2836_ = ((lean_object*)(l_Std_DTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2835_) == 0)
{
lean_object* v_size_2841_; 
v_size_2841_ = lean_ctor_get(v_t_2835_, 0);
lean_inc(v_size_2841_);
v___y_2838_ = v_size_2841_;
goto v___jp_2837_;
}
else
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_unsigned_to_nat(0u);
v___y_2838_ = v___x_2842_;
goto v___jp_2837_;
}
v___jp_2837_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_mk_empty_array_with_capacity(v___y_2838_);
lean_dec(v___y_2838_);
v___x_2840_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2836_, v___x_2839_, v_t_2835_);
return v___x_2840_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_keysArray___boxed(lean_object* v_00_u03b1_2843_, lean_object* v_00_u03b2_2844_, lean_object* v_cmp_2845_, lean_object* v_t_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Std_DTreeMap_keysArray(v_00_u03b1_2843_, v_00_u03b2_2844_, v_cmp_2845_, v_t_2846_);
lean_dec_ref(v_cmp_2845_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg___lam__0(lean_object* v_x1_2848_, lean_object* v_x2_2849_, lean_object* v_x3_2850_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2851_, 0, v_x2_2849_);
lean_ctor_set(v___x_2851_, 1, v_x3_2850_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_2852_, lean_object* v_x2_2853_, lean_object* v_x3_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Std_DTreeMap_values___redArg___lam__0(v_x1_2852_, v_x2_2853_, v_x3_2854_);
lean_dec(v_x1_2852_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___redArg(lean_object* v_t_2857_){
_start:
{
lean_object* v___f_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___f_2858_ = ((lean_object*)(l_Std_DTreeMap_values___redArg___closed__0));
v___x_2859_ = lean_box(0);
v___x_2860_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2861_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2860_, v___f_2858_, v___x_2859_, v_t_2857_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values(lean_object* v_00_u03b1_2862_, lean_object* v_cmp_2863_, lean_object* v_00_u03b2_2864_, lean_object* v_t_2865_){
_start:
{
lean_object* v___f_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___f_2866_ = ((lean_object*)(l_Std_DTreeMap_values___redArg___closed__0));
v___x_2867_ = lean_box(0);
v___x_2868_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2869_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2868_, v___f_2866_, v___x_2867_, v_t_2865_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_values___boxed(lean_object* v_00_u03b1_2870_, lean_object* v_cmp_2871_, lean_object* v_00_u03b2_2872_, lean_object* v_t_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Std_DTreeMap_values(v_00_u03b1_2870_, v_cmp_2871_, v_00_u03b2_2872_, v_t_2873_);
lean_dec_ref(v_cmp_2871_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_2875_, lean_object* v_x_2876_, lean_object* v_v_2877_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = lean_array_push(v_l_2875_, v_v_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2879_, lean_object* v_x_2880_, lean_object* v_v_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Std_DTreeMap_valuesArray___redArg___lam__0(v_l_2879_, v_x_2880_, v_v_2881_);
lean_dec(v_x_2880_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___redArg(lean_object* v_t_2884_){
_start:
{
lean_object* v___f_2885_; lean_object* v___y_2887_; 
v___f_2885_ = ((lean_object*)(l_Std_DTreeMap_valuesArray___redArg___closed__0));
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray(lean_object* v_00_u03b1_2892_, lean_object* v_cmp_2893_, lean_object* v_00_u03b2_2894_, lean_object* v_t_2895_){
_start:
{
lean_object* v___f_2896_; lean_object* v___y_2898_; 
v___f_2896_ = ((lean_object*)(l_Std_DTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2895_) == 0)
{
lean_object* v_size_2901_; 
v_size_2901_ = lean_ctor_get(v_t_2895_, 0);
lean_inc(v_size_2901_);
v___y_2898_ = v_size_2901_;
goto v___jp_2897_;
}
else
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_unsigned_to_nat(0u);
v___y_2898_ = v___x_2902_;
goto v___jp_2897_;
}
v___jp_2897_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = lean_mk_empty_array_with_capacity(v___y_2898_);
lean_dec(v___y_2898_);
v___x_2900_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2896_, v___x_2899_, v_t_2895_);
return v___x_2900_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_2903_, lean_object* v_cmp_2904_, lean_object* v_00_u03b2_2905_, lean_object* v_t_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Std_DTreeMap_valuesArray(v_00_u03b1_2903_, v_cmp_2904_, v_00_u03b2_2905_, v_t_2906_);
lean_dec_ref(v_cmp_2904_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___redArg___lam__0(lean_object* v_x1_2908_, lean_object* v_x2_2909_, lean_object* v_x3_2910_){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v_x1_2908_);
lean_ctor_set(v___x_2911_, 1, v_x2_2909_);
v___x_2912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v_x3_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___redArg(lean_object* v_t_2914_){
_start:
{
lean_object* v___f_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___f_2915_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_2916_ = lean_box(0);
v___x_2917_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2918_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2917_, v___f_2915_, v___x_2916_, v_t_2914_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList(lean_object* v_00_u03b1_2919_, lean_object* v_00_u03b2_2920_, lean_object* v_cmp_2921_, lean_object* v_t_2922_){
_start:
{
lean_object* v___f_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___f_2923_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_2924_ = lean_box(0);
v___x_2925_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_2926_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2925_, v___f_2923_, v___x_2924_, v_t_2922_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toList___boxed(lean_object* v_00_u03b1_2927_, lean_object* v_00_u03b2_2928_, lean_object* v_cmp_2929_, lean_object* v_t_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Std_DTreeMap_toList(v_00_u03b1_2927_, v_00_u03b2_2928_, v_cmp_2929_, v_t_2930_);
lean_dec_ref(v_cmp_2929_);
return v_res_2931_;
}
}
static lean_object* _init_l_Std_DTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_2933_, lean_object* v_a_2934_, lean_object* v_x_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_fst_2937_; lean_object* v_snd_2938_; lean_object* v_r_2939_; lean_object* v___x_2940_; 
v_fst_2937_ = lean_ctor_get(v_a_2934_, 0);
lean_inc(v_fst_2937_);
v_snd_2938_ = lean_ctor_get(v_a_2934_, 1);
lean_inc(v_snd_2938_);
lean_dec_ref(v_a_2934_);
v_r_2939_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2933_, v_fst_2937_, v_snd_2938_, v___y_2936_);
v___x_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2940_, 0, v_r_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg(lean_object* v_l_2941_, lean_object* v_cmp_2942_){
_start:
{
lean_object* v___f_2943_; lean_object* v___x_2944_; lean_object* v_r_2945_; lean_object* v___x_2946_; 
v___f_2943_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2943_, 0, v_cmp_2942_);
v___x_2944_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2945_ = lean_box(1);
v___x_2946_ = l_List_forIn_x27_loop___redArg(v___x_2944_, v___f_2943_, v_l_2941_, v_r_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___redArg___boxed(lean_object* v_l_2947_, lean_object* v_cmp_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Std_DTreeMap_ofList___redArg(v_l_2947_, v_cmp_2948_);
lean_dec(v_l_2947_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList(lean_object* v_00_u03b1_2950_, lean_object* v_00_u03b2_2951_, lean_object* v_l_2952_, lean_object* v_cmp_2953_){
_start:
{
lean_object* v___f_2954_; lean_object* v___x_2955_; lean_object* v_r_2956_; lean_object* v___x_2957_; 
v___f_2954_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2954_, 0, v_cmp_2953_);
v___x_2955_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2956_ = lean_box(1);
v___x_2957_ = l_List_forIn_x27_loop___redArg(v___x_2955_, v___f_2954_, v_l_2952_, v_r_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofList___boxed(lean_object* v_00_u03b1_2958_, lean_object* v_00_u03b2_2959_, lean_object* v_l_2960_, lean_object* v_cmp_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Std_DTreeMap_ofList(v_00_u03b1_2958_, v_00_u03b2_2959_, v_l_2960_, v_cmp_2961_);
lean_dec(v_l_2960_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___redArg___lam__0(lean_object* v_l_2963_, lean_object* v_k_2964_, lean_object* v_v_2965_){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v_k_2964_);
lean_ctor_set(v___x_2966_, 1, v_v_2965_);
v___x_2967_ = lean_array_push(v_l_2963_, v___x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___redArg(lean_object* v_t_2969_){
_start:
{
lean_object* v___f_2970_; lean_object* v___y_2972_; 
v___f_2970_ = ((lean_object*)(l_Std_DTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2969_) == 0)
{
lean_object* v_size_2975_; 
v_size_2975_ = lean_ctor_get(v_t_2969_, 0);
lean_inc(v_size_2975_);
v___y_2972_ = v_size_2975_;
goto v___jp_2971_;
}
else
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_unsigned_to_nat(0u);
v___y_2972_ = v___x_2976_;
goto v___jp_2971_;
}
v___jp_2971_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_mk_empty_array_with_capacity(v___y_2972_);
lean_dec(v___y_2972_);
v___x_2974_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2970_, v___x_2973_, v_t_2969_);
return v___x_2974_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray(lean_object* v_00_u03b1_2977_, lean_object* v_00_u03b2_2978_, lean_object* v_cmp_2979_, lean_object* v_t_2980_){
_start:
{
lean_object* v___f_2981_; lean_object* v___y_2983_; 
v___f_2981_ = ((lean_object*)(l_Std_DTreeMap_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2980_) == 0)
{
lean_object* v_size_2986_; 
v_size_2986_ = lean_ctor_get(v_t_2980_, 0);
lean_inc(v_size_2986_);
v___y_2983_ = v_size_2986_;
goto v___jp_2982_;
}
else
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_unsigned_to_nat(0u);
v___y_2983_ = v___x_2987_;
goto v___jp_2982_;
}
v___jp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_mk_empty_array_with_capacity(v___y_2983_);
lean_dec(v___y_2983_);
v___x_2985_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2981_, v___x_2984_, v_t_2980_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_toArray___boxed(lean_object* v_00_u03b1_2988_, lean_object* v_00_u03b2_2989_, lean_object* v_cmp_2990_, lean_object* v_t_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Std_DTreeMap_toArray(v_00_u03b1_2988_, v_00_u03b2_2989_, v_cmp_2990_, v_t_2991_);
lean_dec_ref(v_cmp_2990_);
return v_res_2992_;
}
}
static lean_object* _init_l_Std_DTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray___redArg(lean_object* v_a_2994_, lean_object* v_cmp_2995_){
_start:
{
lean_object* v___f_2996_; lean_object* v___x_2997_; lean_object* v_r_2998_; size_t v_sz_2999_; size_t v___x_3000_; lean_object* v___x_3001_; 
v___f_2996_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2996_, 0, v_cmp_2995_);
v___x_2997_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_2998_ = lean_box(1);
v_sz_2999_ = lean_array_size(v_a_2994_);
v___x_3000_ = ((size_t)0ULL);
v___x_3001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2997_, v_a_2994_, v___f_2996_, v_sz_2999_, v___x_3000_, v_r_2998_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_ofArray(lean_object* v_00_u03b1_3002_, lean_object* v_00_u03b2_3003_, lean_object* v_a_3004_, lean_object* v_cmp_3005_){
_start:
{
lean_object* v___f_3006_; lean_object* v___x_3007_; lean_object* v_r_3008_; size_t v_sz_3009_; size_t v___x_3010_; lean_object* v___x_3011_; 
v___f_3006_ = lean_alloc_closure((void*)(l_Std_DTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3006_, 0, v_cmp_3005_);
v___x_3007_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3008_ = lean_box(1);
v_sz_3009_ = lean_array_size(v_a_3004_);
v___x_3010_ = ((size_t)0ULL);
v___x_3011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3007_, v_a_3004_, v___f_3006_, v_sz_3009_, v___x_3010_, v_r_3008_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_modify___redArg(lean_object* v_cmp_3012_, lean_object* v_t_3013_, lean_object* v_a_3014_, lean_object* v_f_3015_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3012_, v_a_3014_, v_f_3015_, v_t_3013_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_modify(lean_object* v_00_u03b1_3017_, lean_object* v_00_u03b2_3018_, lean_object* v_cmp_3019_, lean_object* v_inst_3020_, lean_object* v_t_3021_, lean_object* v_a_3022_, lean_object* v_f_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_3019_, v_a_3022_, v_f_3023_, v_t_3021_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_alter___redArg(lean_object* v_cmp_3025_, lean_object* v_t_3026_, lean_object* v_a_3027_, lean_object* v_f_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3025_, v_a_3027_, v_f_3028_, v_t_3026_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_alter(lean_object* v_00_u03b1_3030_, lean_object* v_00_u03b2_3031_, lean_object* v_cmp_3032_, lean_object* v_inst_3033_, lean_object* v_t_3034_, lean_object* v_a_3035_, lean_object* v_f_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3032_, v_a_3035_, v_f_3036_, v_t_3034_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_3038_, lean_object* v_mergeFn_3039_, lean_object* v_a_3040_, lean_object* v_x_3041_){
_start:
{
if (lean_obj_tag(v_x_3041_) == 0)
{
lean_object* v___x_3042_; 
lean_dec(v_a_3040_);
lean_dec(v_mergeFn_3039_);
v___x_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3042_, 0, v_b_u2082_3038_);
return v___x_3042_;
}
else
{
lean_object* v_val_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3051_; 
v_val_3043_ = lean_ctor_get(v_x_3041_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_x_3041_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3045_ = v_x_3041_;
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_val_3043_);
lean_dec(v_x_3041_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = lean_apply_3(v_mergeFn_3039_, v_a_3040_, v_val_3043_, v_b_u2082_3038_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3052_, lean_object* v_cmp_3053_, lean_object* v_t_3054_, lean_object* v_a_3055_, lean_object* v_b_u2082_3056_){
_start:
{
lean_object* v___f_3057_; lean_object* v___x_3058_; 
lean_inc(v_a_3055_);
v___f_3057_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3057_, 0, v_b_u2082_3056_);
lean_closure_set(v___f_3057_, 1, v_mergeFn_3052_);
lean_closure_set(v___f_3057_, 2, v_a_3055_);
v___x_3058_ = l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_3053_, v_a_3055_, v___f_3057_, v_t_3054_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith___redArg(lean_object* v_cmp_3059_, lean_object* v_mergeFn_3060_, lean_object* v_t_u2081_3061_, lean_object* v_t_u2082_3062_){
_start:
{
lean_object* v___f_3063_; lean_object* v___x_3064_; 
v___f_3063_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3063_, 0, v_mergeFn_3060_);
lean_closure_set(v___f_3063_, 1, v_cmp_3059_);
v___x_3064_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3063_, v_t_u2081_3061_, v_t_u2082_3062_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_mergeWith(lean_object* v_00_u03b1_3065_, lean_object* v_00_u03b2_3066_, lean_object* v_cmp_3067_, lean_object* v_inst_3068_, lean_object* v_mergeFn_3069_, lean_object* v_t_u2081_3070_, lean_object* v_t_u2082_3071_){
_start:
{
lean_object* v___f_3072_; lean_object* v___x_3073_; 
v___f_3072_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3072_, 0, v_mergeFn_3069_);
lean_closure_set(v___f_3072_, 1, v_cmp_3067_);
v___x_3073_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3072_, v_t_u2081_3070_, v_t_u2082_3071_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___redArg___lam__0(lean_object* v_x1_3074_, lean_object* v_x2_3075_, lean_object* v_x3_3076_){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3077_, 0, v_x1_3074_);
lean_ctor_set(v___x_3077_, 1, v_x2_3075_);
v___x_3078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set(v___x_3078_, 1, v_x3_3076_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___redArg(lean_object* v_t_3080_){
_start:
{
lean_object* v___f_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___f_3081_ = ((lean_object*)(l_Std_DTreeMap_Const_toList___redArg___closed__0));
v___x_3082_ = lean_box(0);
v___x_3083_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_3084_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3083_, v___f_3081_, v___x_3082_, v_t_3080_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList(lean_object* v_00_u03b1_3085_, lean_object* v_cmp_3086_, lean_object* v_00_u03b2_3087_, lean_object* v_t_3088_){
_start:
{
lean_object* v___f_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___f_3089_ = ((lean_object*)(l_Std_DTreeMap_Const_toList___redArg___closed__0));
v___x_3090_ = lean_box(0);
v___x_3091_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_3092_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_3091_, v___f_3089_, v___x_3090_, v_t_3088_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toList___boxed(lean_object* v_00_u03b1_3093_, lean_object* v_cmp_3094_, lean_object* v_00_u03b2_3095_, lean_object* v_t_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Std_DTreeMap_Const_toList(v_00_u03b1_3093_, v_cmp_3094_, v_00_u03b2_3095_, v_t_3096_);
lean_dec_ref(v_cmp_3094_);
return v_res_3097_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_3098_; 
v___x_3098_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg___lam__0(lean_object* v_cmp_3099_, lean_object* v_a_3100_, lean_object* v_x_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v_fst_3103_; lean_object* v_snd_3104_; lean_object* v_r_3105_; lean_object* v___x_3106_; 
v_fst_3103_ = lean_ctor_get(v_a_3100_, 0);
lean_inc(v_fst_3103_);
v_snd_3104_ = lean_ctor_get(v_a_3100_, 1);
lean_inc(v_snd_3104_);
lean_dec_ref(v_a_3100_);
v_r_3105_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3099_, v_fst_3103_, v_snd_3104_, v___y_3102_);
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v_r_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg(lean_object* v_l_3107_, lean_object* v_cmp_3108_){
_start:
{
lean_object* v___f_3109_; lean_object* v___x_3110_; lean_object* v_r_3111_; lean_object* v___x_3112_; 
v___f_3109_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3109_, 0, v_cmp_3108_);
v___x_3110_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3111_ = lean_box(1);
v___x_3112_ = l_List_forIn_x27_loop___redArg(v___x_3110_, v___f_3109_, v_l_3107_, v_r_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___redArg___boxed(lean_object* v_l_3113_, lean_object* v_cmp_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Std_DTreeMap_Const_ofList___redArg(v_l_3113_, v_cmp_3114_);
lean_dec(v_l_3113_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList(lean_object* v_00_u03b1_3116_, lean_object* v_00_u03b2_3117_, lean_object* v_l_3118_, lean_object* v_cmp_3119_){
_start:
{
lean_object* v___f_3120_; lean_object* v___x_3121_; lean_object* v_r_3122_; lean_object* v___x_3123_; 
v___f_3120_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3120_, 0, v_cmp_3119_);
v___x_3121_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3122_ = lean_box(1);
v___x_3123_ = l_List_forIn_x27_loop___redArg(v___x_3121_, v___f_3120_, v_l_3118_, v_r_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofList___boxed(lean_object* v_00_u03b1_3124_, lean_object* v_00_u03b2_3125_, lean_object* v_l_3126_, lean_object* v_cmp_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Std_DTreeMap_Const_ofList(v_00_u03b1_3124_, v_00_u03b2_3125_, v_l_3126_, v_cmp_3127_);
lean_dec(v_l_3126_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___redArg___lam__0(lean_object* v_acc_3129_, lean_object* v_k_3130_, lean_object* v_v_3131_){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v_k_3130_);
lean_ctor_set(v___x_3132_, 1, v_v_3131_);
v___x_3133_ = lean_array_push(v_acc_3129_, v___x_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___redArg(lean_object* v_t_3137_){
_start:
{
lean_object* v___f_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___f_3138_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__0));
v___x_3139_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__1));
v___x_3140_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3138_, v___x_3139_, v_t_3137_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray(lean_object* v_00_u03b1_3141_, lean_object* v_cmp_3142_, lean_object* v_00_u03b2_3143_, lean_object* v_t_3144_){
_start:
{
lean_object* v___f_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___f_3145_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__0));
v___x_3146_ = ((lean_object*)(l_Std_DTreeMap_Const_toArray___redArg___closed__1));
v___x_3147_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3145_, v___x_3146_, v_t_3144_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_toArray___boxed(lean_object* v_00_u03b1_3148_, lean_object* v_cmp_3149_, lean_object* v_00_u03b2_3150_, lean_object* v_t_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Std_DTreeMap_Const_toArray(v_00_u03b1_3148_, v_cmp_3149_, v_00_u03b2_3150_, v_t_3151_);
lean_dec_ref(v_cmp_3149_);
return v_res_3152_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray___redArg(lean_object* v_a_3154_, lean_object* v_cmp_3155_){
_start:
{
lean_object* v___f_3156_; lean_object* v___x_3157_; lean_object* v_r_3158_; size_t v_sz_3159_; size_t v___x_3160_; lean_object* v___x_3161_; 
v___f_3156_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3156_, 0, v_cmp_3155_);
v___x_3157_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3158_ = lean_box(1);
v_sz_3159_ = lean_array_size(v_a_3154_);
v___x_3160_ = ((size_t)0ULL);
v___x_3161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3157_, v_a_3154_, v___f_3156_, v_sz_3159_, v___x_3160_, v_r_3158_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_ofArray(lean_object* v_00_u03b1_3162_, lean_object* v_00_u03b2_3163_, lean_object* v_a_3164_, lean_object* v_cmp_3165_){
_start:
{
lean_object* v___f_3166_; lean_object* v___x_3167_; lean_object* v_r_3168_; size_t v_sz_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v___f_3166_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3166_, 0, v_cmp_3165_);
v___x_3167_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3168_ = lean_box(1);
v_sz_3169_ = lean_array_size(v_a_3164_);
v___x_3170_ = ((size_t)0ULL);
v___x_3171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3167_, v_a_3164_, v___f_3166_, v_sz_3169_, v___x_3170_, v_r_3168_);
return v___x_3171_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_3173_, lean_object* v_a_3174_, lean_object* v_x_3175_, lean_object* v___y_3176_){
_start:
{
uint8_t v___x_3177_; 
lean_inc(v___y_3176_);
lean_inc(v_a_3174_);
lean_inc_ref(v_cmp_3173_);
v___x_3177_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3173_, v_a_3174_, v___y_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = lean_box(0);
v___x_3179_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3173_, v_a_3174_, v___x_3178_, v___y_3176_);
v___x_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
return v___x_3180_;
}
else
{
lean_object* v___x_3181_; 
lean_dec(v_a_3174_);
lean_dec_ref(v_cmp_3173_);
v___x_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___y_3176_);
return v___x_3181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg(lean_object* v_l_3182_, lean_object* v_cmp_3183_){
_start:
{
lean_object* v___f_3184_; lean_object* v___x_3185_; lean_object* v_r_3186_; lean_object* v___x_3187_; 
v___f_3184_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3184_, 0, v_cmp_3183_);
v___x_3185_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3186_ = lean_box(1);
v___x_3187_ = l_List_forIn_x27_loop___redArg(v___x_3185_, v___f_3184_, v_l_3182_, v_r_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___redArg___boxed(lean_object* v_l_3188_, lean_object* v_cmp_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Std_DTreeMap_Const_unitOfList___redArg(v_l_3188_, v_cmp_3189_);
lean_dec(v_l_3188_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList(lean_object* v_00_u03b1_3191_, lean_object* v_l_3192_, lean_object* v_cmp_3193_){
_start:
{
lean_object* v___f_3194_; lean_object* v___x_3195_; lean_object* v_r_3196_; lean_object* v___x_3197_; 
v___f_3194_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3194_, 0, v_cmp_3193_);
v___x_3195_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3196_ = lean_box(1);
v___x_3197_ = l_List_forIn_x27_loop___redArg(v___x_3195_, v___f_3194_, v_l_3192_, v_r_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfList___boxed(lean_object* v_00_u03b1_3198_, lean_object* v_l_3199_, lean_object* v_cmp_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Std_DTreeMap_Const_unitOfList(v_00_u03b1_3198_, v_l_3199_, v_cmp_3200_);
lean_dec(v_l_3199_);
return v_res_3201_;
}
}
static lean_object* _init_l_Std_DTreeMap_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_obj_once(&l_Std_DTreeMap___auto__1___closed__25, &l_Std_DTreeMap___auto__1___closed__25_once, _init_l_Std_DTreeMap___auto__1___closed__25);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray___redArg(lean_object* v_a_3203_, lean_object* v_cmp_3204_){
_start:
{
lean_object* v___f_3205_; lean_object* v___x_3206_; lean_object* v_r_3207_; size_t v_sz_3208_; size_t v___x_3209_; lean_object* v___x_3210_; 
v___f_3205_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3205_, 0, v_cmp_3204_);
v___x_3206_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3207_ = lean_box(1);
v_sz_3208_ = lean_array_size(v_a_3203_);
v___x_3209_ = ((size_t)0ULL);
v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3206_, v_a_3203_, v___f_3205_, v_sz_3208_, v___x_3209_, v_r_3207_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_unitOfArray(lean_object* v_00_u03b1_3211_, lean_object* v_a_3212_, lean_object* v_cmp_3213_){
_start:
{
lean_object* v___f_3214_; lean_object* v___x_3215_; lean_object* v_r_3216_; size_t v_sz_3217_; size_t v___x_3218_; lean_object* v___x_3219_; 
v___f_3214_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3214_, 0, v_cmp_3213_);
v___x_3215_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v_r_3216_ = lean_box(1);
v_sz_3217_ = lean_array_size(v_a_3212_);
v___x_3218_ = ((size_t)0ULL);
v___x_3219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3215_, v_a_3212_, v___f_3214_, v_sz_3217_, v___x_3218_, v_r_3216_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_modify___redArg(lean_object* v_cmp_3220_, lean_object* v_t_3221_, lean_object* v_a_3222_, lean_object* v_f_3223_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3220_, v_a_3222_, v_f_3223_, v_t_3221_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_modify(lean_object* v_00_u03b1_3225_, lean_object* v_cmp_3226_, lean_object* v_00_u03b2_3227_, lean_object* v_t_3228_, lean_object* v_a_3229_, lean_object* v_f_3230_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3226_, v_a_3229_, v_f_3230_, v_t_3228_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_alter___redArg(lean_object* v_cmp_3232_, lean_object* v_t_3233_, lean_object* v_a_3234_, lean_object* v_f_3235_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3232_, v_a_3234_, v_f_3235_, v_t_3233_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_alter(lean_object* v_00_u03b1_3237_, lean_object* v_cmp_3238_, lean_object* v_00_u03b2_3239_, lean_object* v_t_3240_, lean_object* v_a_3241_, lean_object* v_f_3242_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3238_, v_a_3241_, v_f_3242_, v_t_3240_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3244_, lean_object* v_cmp_3245_, lean_object* v_t_3246_, lean_object* v_a_3247_, lean_object* v_b_u2082_3248_){
_start:
{
lean_object* v___f_3249_; lean_object* v___x_3250_; 
lean_inc(v_a_3247_);
v___f_3249_ = lean_alloc_closure((void*)(l_Std_DTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3249_, 0, v_b_u2082_3248_);
lean_closure_set(v___f_3249_, 1, v_mergeFn_3244_);
lean_closure_set(v___f_3249_, 2, v_a_3247_);
v___x_3250_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_3245_, v_a_3247_, v___f_3249_, v_t_3246_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith___redArg(lean_object* v_cmp_3251_, lean_object* v_mergeFn_3252_, lean_object* v_t_u2081_3253_, lean_object* v_t_u2082_3254_){
_start:
{
lean_object* v___f_3255_; lean_object* v___x_3256_; 
v___f_3255_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3255_, 0, v_mergeFn_3252_);
lean_closure_set(v___f_3255_, 1, v_cmp_3251_);
v___x_3256_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3255_, v_t_u2081_3253_, v_t_u2082_3254_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_mergeWith(lean_object* v_00_u03b1_3257_, lean_object* v_cmp_3258_, lean_object* v_00_u03b2_3259_, lean_object* v_mergeFn_3260_, lean_object* v_t_u2081_3261_, lean_object* v_t_u2082_3262_){
_start:
{
lean_object* v___f_3263_; lean_object* v___x_3264_; 
v___f_3263_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3263_, 0, v_mergeFn_3260_);
lean_closure_set(v___f_3263_, 1, v_cmp_3258_);
v___x_3264_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3263_, v_t_u2081_3261_, v_t_u2082_3262_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_3265_, lean_object* v_x_3266_, lean_object* v_____s_3267_){
_start:
{
lean_object* v_fst_3268_; lean_object* v_snd_3269_; lean_object* v_r_3270_; lean_object* v___x_3271_; 
v_fst_3268_ = lean_ctor_get(v_x_3266_, 0);
lean_inc(v_fst_3268_);
v_snd_3269_ = lean_ctor_get(v_x_3266_, 1);
lean_inc(v_snd_3269_);
lean_dec_ref(v_x_3266_);
v_r_3270_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3265_, v_fst_3268_, v_snd_3269_, v_____s_3267_);
v___x_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_r_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany___redArg(lean_object* v_cmp_3272_, lean_object* v_inst_3273_, lean_object* v_t_3274_, lean_object* v_l_3275_){
_start:
{
lean_object* v___f_3276_; lean_object* v___x_3277_; 
v___f_3276_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3276_, 0, v_cmp_3272_);
v___x_3277_ = lean_apply_4(v_inst_3273_, lean_box(0), v_l_3275_, v_t_3274_, v___f_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertMany(lean_object* v_00_u03b1_3278_, lean_object* v_00_u03b2_3279_, lean_object* v_cmp_3280_, lean_object* v_00_u03c1_3281_, lean_object* v_inst_3282_, lean_object* v_t_3283_, lean_object* v_l_3284_){
_start:
{
lean_object* v___f_3285_; lean_object* v___x_3286_; 
v___f_3285_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3285_, 0, v_cmp_3280_);
v___x_3286_ = lean_apply_4(v_inst_3282_, lean_box(0), v_l_3284_, v_t_3283_, v___f_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew___redArg___lam__0(lean_object* v_cmp_3287_, lean_object* v_x_3288_, lean_object* v_____s_3289_){
_start:
{
lean_object* v_fst_3290_; lean_object* v_snd_3291_; uint8_t v___x_3292_; 
v_fst_3290_ = lean_ctor_get(v_x_3288_, 0);
lean_inc_n(v_fst_3290_, 2);
v_snd_3291_ = lean_ctor_get(v_x_3288_, 1);
lean_inc(v_snd_3291_);
lean_dec_ref(v_x_3288_);
lean_inc(v_____s_3289_);
lean_inc_ref(v_cmp_3287_);
v___x_3292_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3287_, v_fst_3290_, v_____s_3289_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3287_, v_fst_3290_, v_snd_3291_, v_____s_3289_);
v___x_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
return v___x_3294_;
}
else
{
lean_object* v___x_3295_; 
lean_dec(v_snd_3291_);
lean_dec(v_fst_3290_);
lean_dec_ref(v_cmp_3287_);
v___x_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3295_, 0, v_____s_3289_);
return v___x_3295_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew___redArg(lean_object* v_cmp_3296_, lean_object* v_inst_3297_, lean_object* v_t_3298_, lean_object* v_l_3299_){
_start:
{
lean_object* v___f_3300_; lean_object* v___x_3301_; 
v___f_3300_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertManyIfNew___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3300_, 0, v_cmp_3296_);
v___x_3301_ = lean_apply_4(v_inst_3297_, lean_box(0), v_l_3299_, v_t_3298_, v___f_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_insertManyIfNew(lean_object* v_00_u03b1_3302_, lean_object* v_00_u03b2_3303_, lean_object* v_cmp_3304_, lean_object* v_00_u03c1_3305_, lean_object* v_inst_3306_, lean_object* v_t_3307_, lean_object* v_l_3308_){
_start:
{
lean_object* v___f_3309_; lean_object* v___x_3310_; 
v___f_3309_ = lean_alloc_closure((void*)(l_Std_DTreeMap_insertManyIfNew___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3309_, 0, v_cmp_3304_);
v___x_3310_ = lean_apply_4(v_inst_3306_, lean_box(0), v_l_3308_, v_t_3307_, v___f_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(lean_object* v_cmp_3311_, lean_object* v_k_3312_, lean_object* v_v_3313_, lean_object* v_t_3314_){
_start:
{
if (lean_obj_tag(v_t_3314_) == 0)
{
lean_object* v_size_3315_; lean_object* v_k_3316_; lean_object* v_v_3317_; lean_object* v_l_3318_; lean_object* v_r_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3600_; 
v_size_3315_ = lean_ctor_get(v_t_3314_, 0);
v_k_3316_ = lean_ctor_get(v_t_3314_, 1);
v_v_3317_ = lean_ctor_get(v_t_3314_, 2);
v_l_3318_ = lean_ctor_get(v_t_3314_, 3);
v_r_3319_ = lean_ctor_get(v_t_3314_, 4);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_t_3314_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3321_ = v_t_3314_;
v_isShared_3322_ = v_isSharedCheck_3600_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_r_3319_);
lean_inc(v_l_3318_);
lean_inc(v_v_3317_);
lean_inc(v_k_3316_);
lean_inc(v_size_3315_);
lean_dec(v_t_3314_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3600_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; uint8_t v___x_3324_; 
lean_inc_ref(v_cmp_3311_);
lean_inc(v_k_3316_);
lean_inc(v_k_3312_);
v___x_3323_ = lean_apply_2(v_cmp_3311_, v_k_3312_, v_k_3316_);
v___x_3324_ = lean_unbox(v___x_3323_);
switch(v___x_3324_)
{
case 0:
{
lean_object* v_impl_3325_; lean_object* v___x_3326_; 
lean_dec(v_size_3315_);
v_impl_3325_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3311_, v_k_3312_, v_v_3313_, v_l_3318_);
v___x_3326_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3319_) == 0)
{
lean_object* v_size_3327_; lean_object* v_size_3328_; lean_object* v_k_3329_; lean_object* v_v_3330_; lean_object* v_l_3331_; lean_object* v_r_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; 
v_size_3327_ = lean_ctor_get(v_r_3319_, 0);
v_size_3328_ = lean_ctor_get(v_impl_3325_, 0);
v_k_3329_ = lean_ctor_get(v_impl_3325_, 1);
v_v_3330_ = lean_ctor_get(v_impl_3325_, 2);
v_l_3331_ = lean_ctor_get(v_impl_3325_, 3);
v_r_3332_ = lean_ctor_get(v_impl_3325_, 4);
lean_inc(v_r_3332_);
v___x_3333_ = lean_unsigned_to_nat(3u);
v___x_3334_ = lean_nat_mul(v___x_3333_, v_size_3327_);
v___x_3335_ = lean_nat_dec_lt(v___x_3334_, v_size_3328_);
lean_dec(v___x_3334_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
lean_dec(v_r_3332_);
v___x_3336_ = lean_nat_add(v___x_3326_, v_size_3328_);
v___x_3337_ = lean_nat_add(v___x_3336_, v_size_3327_);
lean_dec(v___x_3336_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 3, v_impl_3325_);
lean_ctor_set(v___x_3321_, 0, v___x_3337_);
v___x_3339_ = v___x_3321_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3340_, 3, v_impl_3325_);
lean_ctor_set(v_reuseFailAlloc_3340_, 4, v_r_3319_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
else
{
lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3406_; 
lean_inc(v_l_3331_);
lean_inc(v_v_3330_);
lean_inc(v_k_3329_);
lean_inc(v_size_3328_);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_impl_3325_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; lean_object* v_unused_3408_; lean_object* v_unused_3409_; lean_object* v_unused_3410_; lean_object* v_unused_3411_; 
v_unused_3407_ = lean_ctor_get(v_impl_3325_, 4);
lean_dec(v_unused_3407_);
v_unused_3408_ = lean_ctor_get(v_impl_3325_, 3);
lean_dec(v_unused_3408_);
v_unused_3409_ = lean_ctor_get(v_impl_3325_, 2);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_impl_3325_, 1);
lean_dec(v_unused_3410_);
v_unused_3411_ = lean_ctor_get(v_impl_3325_, 0);
lean_dec(v_unused_3411_);
v___x_3342_ = v_impl_3325_;
v_isShared_3343_ = v_isSharedCheck_3406_;
goto v_resetjp_3341_;
}
else
{
lean_dec(v_impl_3325_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3406_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v_size_3344_; lean_object* v_size_3345_; lean_object* v_k_3346_; lean_object* v_v_3347_; lean_object* v_l_3348_; lean_object* v_r_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; 
v_size_3344_ = lean_ctor_get(v_l_3331_, 0);
v_size_3345_ = lean_ctor_get(v_r_3332_, 0);
v_k_3346_ = lean_ctor_get(v_r_3332_, 1);
v_v_3347_ = lean_ctor_get(v_r_3332_, 2);
v_l_3348_ = lean_ctor_get(v_r_3332_, 3);
v_r_3349_ = lean_ctor_get(v_r_3332_, 4);
v___x_3350_ = lean_unsigned_to_nat(2u);
v___x_3351_ = lean_nat_mul(v___x_3350_, v_size_3344_);
v___x_3352_ = lean_nat_dec_lt(v_size_3345_, v___x_3351_);
lean_dec(v___x_3351_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3381_; 
lean_inc(v_r_3349_);
lean_inc(v_l_3348_);
lean_inc(v_v_3347_);
lean_inc(v_k_3346_);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_r_3332_);
if (v_isSharedCheck_3381_ == 0)
{
lean_object* v_unused_3382_; lean_object* v_unused_3383_; lean_object* v_unused_3384_; lean_object* v_unused_3385_; lean_object* v_unused_3386_; 
v_unused_3382_ = lean_ctor_get(v_r_3332_, 4);
lean_dec(v_unused_3382_);
v_unused_3383_ = lean_ctor_get(v_r_3332_, 3);
lean_dec(v_unused_3383_);
v_unused_3384_ = lean_ctor_get(v_r_3332_, 2);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v_r_3332_, 1);
lean_dec(v_unused_3385_);
v_unused_3386_ = lean_ctor_get(v_r_3332_, 0);
lean_dec(v_unused_3386_);
v___x_3354_ = v_r_3332_;
v_isShared_3355_ = v_isSharedCheck_3381_;
goto v_resetjp_3353_;
}
else
{
lean_dec(v_r_3332_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3381_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___x_3369_; lean_object* v___y_3371_; 
v___x_3356_ = lean_nat_add(v___x_3326_, v_size_3328_);
lean_dec(v_size_3328_);
v___x_3357_ = lean_nat_add(v___x_3356_, v_size_3327_);
lean_dec(v___x_3356_);
v___x_3369_ = lean_nat_add(v___x_3326_, v_size_3344_);
if (lean_obj_tag(v_l_3348_) == 0)
{
lean_object* v_size_3379_; 
v_size_3379_ = lean_ctor_get(v_l_3348_, 0);
lean_inc(v_size_3379_);
v___y_3371_ = v_size_3379_;
goto v___jp_3370_;
}
else
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_unsigned_to_nat(0u);
v___y_3371_ = v___x_3380_;
goto v___jp_3370_;
}
v___jp_3358_:
{
lean_object* v___x_3362_; lean_object* v___x_3364_; 
v___x_3362_ = lean_nat_add(v___y_3359_, v___y_3361_);
lean_dec(v___y_3361_);
lean_dec(v___y_3359_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 4, v_r_3319_);
lean_ctor_set(v___x_3354_, 3, v_r_3349_);
lean_ctor_set(v___x_3354_, 2, v_v_3317_);
lean_ctor_set(v___x_3354_, 1, v_k_3316_);
lean_ctor_set(v___x_3354_, 0, v___x_3362_);
v___x_3364_ = v___x_3354_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3368_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3368_, 3, v_r_3349_);
lean_ctor_set(v_reuseFailAlloc_3368_, 4, v_r_3319_);
v___x_3364_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3366_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 4, v___x_3364_);
lean_ctor_set(v___x_3342_, 3, v___y_3360_);
lean_ctor_set(v___x_3342_, 2, v_v_3347_);
lean_ctor_set(v___x_3342_, 1, v_k_3346_);
lean_ctor_set(v___x_3342_, 0, v___x_3357_);
v___x_3366_ = v___x_3342_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_k_3346_);
lean_ctor_set(v_reuseFailAlloc_3367_, 2, v_v_3347_);
lean_ctor_set(v_reuseFailAlloc_3367_, 3, v___y_3360_);
lean_ctor_set(v_reuseFailAlloc_3367_, 4, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
v___jp_3370_:
{
lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3372_ = lean_nat_add(v___x_3369_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec(v___x_3369_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 4, v_l_3348_);
lean_ctor_set(v___x_3321_, 3, v_l_3331_);
lean_ctor_set(v___x_3321_, 2, v_v_3330_);
lean_ctor_set(v___x_3321_, 1, v_k_3329_);
lean_ctor_set(v___x_3321_, 0, v___x_3372_);
v___x_3374_ = v___x_3321_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_k_3329_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_v_3330_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v_l_3331_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v_l_3348_);
v___x_3374_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; 
v___x_3375_ = lean_nat_add(v___x_3326_, v_size_3327_);
if (lean_obj_tag(v_r_3349_) == 0)
{
lean_object* v_size_3376_; 
v_size_3376_ = lean_ctor_get(v_r_3349_, 0);
lean_inc(v_size_3376_);
v___y_3359_ = v___x_3375_;
v___y_3360_ = v___x_3374_;
v___y_3361_ = v_size_3376_;
goto v___jp_3358_;
}
else
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_unsigned_to_nat(0u);
v___y_3359_ = v___x_3375_;
v___y_3360_ = v___x_3374_;
v___y_3361_ = v___x_3377_;
goto v___jp_3358_;
}
}
}
}
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
lean_del_object(v___x_3321_);
v___x_3387_ = lean_nat_add(v___x_3326_, v_size_3328_);
lean_dec(v_size_3328_);
v___x_3388_ = lean_nat_add(v___x_3387_, v_size_3327_);
lean_dec(v___x_3387_);
v___x_3389_ = lean_nat_add(v___x_3326_, v_size_3327_);
v___x_3390_ = lean_nat_add(v___x_3389_, v_size_3345_);
lean_dec(v___x_3389_);
lean_inc_ref(v_r_3319_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 4, v_r_3319_);
lean_ctor_set(v___x_3342_, 3, v_r_3332_);
lean_ctor_set(v___x_3342_, 2, v_v_3317_);
lean_ctor_set(v___x_3342_, 1, v_k_3316_);
lean_ctor_set(v___x_3342_, 0, v___x_3390_);
v___x_3392_ = v___x_3342_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3405_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3405_, 3, v_r_3332_);
lean_ctor_set(v_reuseFailAlloc_3405_, 4, v_r_3319_);
v___x_3392_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
v_isSharedCheck_3399_ = !lean_is_exclusive(v_r_3319_);
if (v_isSharedCheck_3399_ == 0)
{
lean_object* v_unused_3400_; lean_object* v_unused_3401_; lean_object* v_unused_3402_; lean_object* v_unused_3403_; lean_object* v_unused_3404_; 
v_unused_3400_ = lean_ctor_get(v_r_3319_, 4);
lean_dec(v_unused_3400_);
v_unused_3401_ = lean_ctor_get(v_r_3319_, 3);
lean_dec(v_unused_3401_);
v_unused_3402_ = lean_ctor_get(v_r_3319_, 2);
lean_dec(v_unused_3402_);
v_unused_3403_ = lean_ctor_get(v_r_3319_, 1);
lean_dec(v_unused_3403_);
v_unused_3404_ = lean_ctor_get(v_r_3319_, 0);
lean_dec(v_unused_3404_);
v___x_3394_ = v_r_3319_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_dec(v_r_3319_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 4, v___x_3392_);
lean_ctor_set(v___x_3394_, 3, v_l_3331_);
lean_ctor_set(v___x_3394_, 2, v_v_3330_);
lean_ctor_set(v___x_3394_, 1, v_k_3329_);
lean_ctor_set(v___x_3394_, 0, v___x_3388_);
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_k_3329_);
lean_ctor_set(v_reuseFailAlloc_3398_, 2, v_v_3330_);
lean_ctor_set(v_reuseFailAlloc_3398_, 3, v_l_3331_);
lean_ctor_set(v_reuseFailAlloc_3398_, 4, v___x_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3412_; 
v_l_3412_ = lean_ctor_get(v_impl_3325_, 3);
if (lean_obj_tag(v_l_3412_) == 0)
{
lean_object* v_r_3413_; lean_object* v_k_3414_; lean_object* v_v_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3426_; 
lean_inc_ref(v_l_3412_);
v_r_3413_ = lean_ctor_get(v_impl_3325_, 4);
v_k_3414_ = lean_ctor_get(v_impl_3325_, 1);
v_v_3415_ = lean_ctor_get(v_impl_3325_, 2);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_impl_3325_);
if (v_isSharedCheck_3426_ == 0)
{
lean_object* v_unused_3427_; lean_object* v_unused_3428_; 
v_unused_3427_ = lean_ctor_get(v_impl_3325_, 3);
lean_dec(v_unused_3427_);
v_unused_3428_ = lean_ctor_get(v_impl_3325_, 0);
lean_dec(v_unused_3428_);
v___x_3417_ = v_impl_3325_;
v_isShared_3418_ = v_isSharedCheck_3426_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_r_3413_);
lean_inc(v_v_3415_);
lean_inc(v_k_3414_);
lean_dec(v_impl_3325_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3426_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3419_; lean_object* v___x_3421_; 
v___x_3419_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3413_);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 3, v_r_3413_);
lean_ctor_set(v___x_3417_, 2, v_v_3317_);
lean_ctor_set(v___x_3417_, 1, v_k_3316_);
lean_ctor_set(v___x_3417_, 0, v___x_3326_);
v___x_3421_ = v___x_3417_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3425_, 3, v_r_3413_);
lean_ctor_set(v_reuseFailAlloc_3425_, 4, v_r_3413_);
v___x_3421_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3423_; 
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 4, v___x_3421_);
lean_ctor_set(v___x_3321_, 3, v_l_3412_);
lean_ctor_set(v___x_3321_, 2, v_v_3415_);
lean_ctor_set(v___x_3321_, 1, v_k_3414_);
lean_ctor_set(v___x_3321_, 0, v___x_3419_);
v___x_3423_ = v___x_3321_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_k_3414_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_v_3415_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v_l_3412_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
lean_object* v_r_3429_; 
v_r_3429_ = lean_ctor_get(v_impl_3325_, 4);
lean_inc(v_r_3429_);
if (lean_obj_tag(v_r_3429_) == 0)
{
lean_object* v_k_3430_; lean_object* v_v_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3454_; 
lean_inc(v_l_3412_);
v_k_3430_ = lean_ctor_get(v_impl_3325_, 1);
v_v_3431_ = lean_ctor_get(v_impl_3325_, 2);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_impl_3325_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; lean_object* v_unused_3456_; lean_object* v_unused_3457_; 
v_unused_3455_ = lean_ctor_get(v_impl_3325_, 4);
lean_dec(v_unused_3455_);
v_unused_3456_ = lean_ctor_get(v_impl_3325_, 3);
lean_dec(v_unused_3456_);
v_unused_3457_ = lean_ctor_get(v_impl_3325_, 0);
lean_dec(v_unused_3457_);
v___x_3433_ = v_impl_3325_;
v_isShared_3434_ = v_isSharedCheck_3454_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_v_3431_);
lean_inc(v_k_3430_);
lean_dec(v_impl_3325_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3454_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v_k_3435_; lean_object* v_v_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3450_; 
v_k_3435_ = lean_ctor_get(v_r_3429_, 1);
v_v_3436_ = lean_ctor_get(v_r_3429_, 2);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_r_3429_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; lean_object* v_unused_3452_; lean_object* v_unused_3453_; 
v_unused_3451_ = lean_ctor_get(v_r_3429_, 4);
lean_dec(v_unused_3451_);
v_unused_3452_ = lean_ctor_get(v_r_3429_, 3);
lean_dec(v_unused_3452_);
v_unused_3453_ = lean_ctor_get(v_r_3429_, 0);
lean_dec(v_unused_3453_);
v___x_3438_ = v_r_3429_;
v_isShared_3439_ = v_isSharedCheck_3450_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_v_3436_);
lean_inc(v_k_3435_);
lean_dec(v_r_3429_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3450_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3440_ = lean_unsigned_to_nat(3u);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 4, v_l_3412_);
lean_ctor_set(v___x_3438_, 3, v_l_3412_);
lean_ctor_set(v___x_3438_, 2, v_v_3431_);
lean_ctor_set(v___x_3438_, 1, v_k_3430_);
lean_ctor_set(v___x_3438_, 0, v___x_3326_);
v___x_3442_ = v___x_3438_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_k_3430_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_v_3431_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v_l_3412_);
lean_ctor_set(v_reuseFailAlloc_3449_, 4, v_l_3412_);
v___x_3442_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3444_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 4, v_l_3412_);
lean_ctor_set(v___x_3433_, 2, v_v_3317_);
lean_ctor_set(v___x_3433_, 1, v_k_3316_);
lean_ctor_set(v___x_3433_, 0, v___x_3326_);
v___x_3444_ = v___x_3433_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_l_3412_);
lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_l_3412_);
v___x_3444_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 4, v___x_3444_);
lean_ctor_set(v___x_3321_, 3, v___x_3442_);
lean_ctor_set(v___x_3321_, 2, v_v_3436_);
lean_ctor_set(v___x_3321_, 1, v_k_3435_);
lean_ctor_set(v___x_3321_, 0, v___x_3440_);
v___x_3446_ = v___x_3321_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_k_3435_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_v_3436_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3447_, 4, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
}
else
{
lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3458_ = lean_unsigned_to_nat(2u);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 4, v_r_3429_);
lean_ctor_set(v___x_3321_, 3, v_impl_3325_);
lean_ctor_set(v___x_3321_, 0, v___x_3458_);
v___x_3460_ = v___x_3321_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3461_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3461_, 3, v_impl_3325_);
lean_ctor_set(v_reuseFailAlloc_3461_, 4, v_r_3429_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3463_; 
lean_dec(v_v_3317_);
lean_dec(v_k_3316_);
lean_dec_ref(v_cmp_3311_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 2, v_v_3313_);
lean_ctor_set(v___x_3321_, 1, v_k_3312_);
v___x_3463_ = v___x_3321_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_size_3315_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3464_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3464_, 3, v_l_3318_);
lean_ctor_set(v_reuseFailAlloc_3464_, 4, v_r_3319_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
default: 
{
lean_object* v_impl_3465_; lean_object* v___x_3466_; 
lean_dec(v_size_3315_);
v_impl_3465_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3311_, v_k_3312_, v_v_3313_, v_r_3319_);
v___x_3466_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3318_) == 0)
{
lean_object* v_size_3467_; lean_object* v_size_3468_; lean_object* v_k_3469_; lean_object* v_v_3470_; lean_object* v_l_3471_; lean_object* v_r_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
v_size_3467_ = lean_ctor_get(v_l_3318_, 0);
v_size_3468_ = lean_ctor_get(v_impl_3465_, 0);
v_k_3469_ = lean_ctor_get(v_impl_3465_, 1);
v_v_3470_ = lean_ctor_get(v_impl_3465_, 2);
v_l_3471_ = lean_ctor_get(v_impl_3465_, 3);
lean_inc(v_l_3471_);
v_r_3472_ = lean_ctor_get(v_impl_3465_, 4);
v___x_3473_ = lean_unsigned_to_nat(3u);
v___x_3474_ = lean_nat_mul(v___x_3473_, v_size_3467_);
v___x_3475_ = lean_nat_dec_lt(v___x_3474_, v_size_3468_);
lean_dec(v___x_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3479_; 
lean_dec(v_l_3471_);
v___x_3476_ = lean_nat_add(v___x_3466_, v_size_3467_);
v___x_3477_ = lean_nat_add(v___x_3476_, v_size_3468_);
lean_dec(v___x_3476_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 4, v_impl_3465_);
lean_ctor_set(v___x_3321_, 0, v___x_3477_);
v___x_3479_ = v___x_3321_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3480_, 3, v_l_3318_);
lean_ctor_set(v_reuseFailAlloc_3480_, 4, v_impl_3465_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
else
{
lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3544_; 
lean_inc(v_r_3472_);
lean_inc(v_v_3470_);
lean_inc(v_k_3469_);
lean_inc(v_size_3468_);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_impl_3465_);
if (v_isSharedCheck_3544_ == 0)
{
lean_object* v_unused_3545_; lean_object* v_unused_3546_; lean_object* v_unused_3547_; lean_object* v_unused_3548_; lean_object* v_unused_3549_; 
v_unused_3545_ = lean_ctor_get(v_impl_3465_, 4);
lean_dec(v_unused_3545_);
v_unused_3546_ = lean_ctor_get(v_impl_3465_, 3);
lean_dec(v_unused_3546_);
v_unused_3547_ = lean_ctor_get(v_impl_3465_, 2);
lean_dec(v_unused_3547_);
v_unused_3548_ = lean_ctor_get(v_impl_3465_, 1);
lean_dec(v_unused_3548_);
v_unused_3549_ = lean_ctor_get(v_impl_3465_, 0);
lean_dec(v_unused_3549_);
v___x_3482_ = v_impl_3465_;
v_isShared_3483_ = v_isSharedCheck_3544_;
goto v_resetjp_3481_;
}
else
{
lean_dec(v_impl_3465_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3544_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v_size_3484_; lean_object* v_k_3485_; lean_object* v_v_3486_; lean_object* v_l_3487_; lean_object* v_r_3488_; lean_object* v_size_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v_size_3484_ = lean_ctor_get(v_l_3471_, 0);
v_k_3485_ = lean_ctor_get(v_l_3471_, 1);
v_v_3486_ = lean_ctor_get(v_l_3471_, 2);
v_l_3487_ = lean_ctor_get(v_l_3471_, 3);
v_r_3488_ = lean_ctor_get(v_l_3471_, 4);
v_size_3489_ = lean_ctor_get(v_r_3472_, 0);
v___x_3490_ = lean_unsigned_to_nat(2u);
v___x_3491_ = lean_nat_mul(v___x_3490_, v_size_3489_);
v___x_3492_ = lean_nat_dec_lt(v_size_3484_, v___x_3491_);
lean_dec(v___x_3491_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3520_; 
lean_inc(v_r_3488_);
lean_inc(v_l_3487_);
lean_inc(v_v_3486_);
lean_inc(v_k_3485_);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_l_3471_);
if (v_isSharedCheck_3520_ == 0)
{
lean_object* v_unused_3521_; lean_object* v_unused_3522_; lean_object* v_unused_3523_; lean_object* v_unused_3524_; lean_object* v_unused_3525_; 
v_unused_3521_ = lean_ctor_get(v_l_3471_, 4);
lean_dec(v_unused_3521_);
v_unused_3522_ = lean_ctor_get(v_l_3471_, 3);
lean_dec(v_unused_3522_);
v_unused_3523_ = lean_ctor_get(v_l_3471_, 2);
lean_dec(v_unused_3523_);
v_unused_3524_ = lean_ctor_get(v_l_3471_, 1);
lean_dec(v_unused_3524_);
v_unused_3525_ = lean_ctor_get(v_l_3471_, 0);
lean_dec(v_unused_3525_);
v___x_3494_ = v_l_3471_;
v_isShared_3495_ = v_isSharedCheck_3520_;
goto v_resetjp_3493_;
}
else
{
lean_dec(v_l_3471_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3520_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3510_; 
v___x_3496_ = lean_nat_add(v___x_3466_, v_size_3467_);
v___x_3497_ = lean_nat_add(v___x_3496_, v_size_3468_);
lean_dec(v_size_3468_);
if (lean_obj_tag(v_l_3487_) == 0)
{
lean_object* v_size_3518_; 
v_size_3518_ = lean_ctor_get(v_l_3487_, 0);
lean_inc(v_size_3518_);
v___y_3510_ = v_size_3518_;
goto v___jp_3509_;
}
else
{
lean_object* v___x_3519_; 
v___x_3519_ = lean_unsigned_to_nat(0u);
v___y_3510_ = v___x_3519_;
goto v___jp_3509_;
}
v___jp_3498_:
{
lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3502_ = lean_nat_add(v___y_3500_, v___y_3501_);
lean_dec(v___y_3501_);
lean_dec(v___y_3500_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 4, v_r_3472_);
lean_ctor_set(v___x_3494_, 3, v_r_3488_);
lean_ctor_set(v___x_3494_, 2, v_v_3470_);
lean_ctor_set(v___x_3494_, 1, v_k_3469_);
lean_ctor_set(v___x_3494_, 0, v___x_3502_);
v___x_3504_ = v___x_3494_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_k_3469_);
lean_ctor_set(v_reuseFailAlloc_3508_, 2, v_v_3470_);
lean_ctor_set(v_reuseFailAlloc_3508_, 3, v_r_3488_);
lean_ctor_set(v_reuseFailAlloc_3508_, 4, v_r_3472_);
v___x_3504_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 4, v___x_3504_);
lean_ctor_set(v___x_3482_, 3, v___y_3499_);
lean_ctor_set(v___x_3482_, 2, v_v_3486_);
lean_ctor_set(v___x_3482_, 1, v_k_3485_);
lean_ctor_set(v___x_3482_, 0, v___x_3497_);
v___x_3506_ = v___x_3482_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_k_3485_);
lean_ctor_set(v_reuseFailAlloc_3507_, 2, v_v_3486_);
lean_ctor_set(v_reuseFailAlloc_3507_, 3, v___y_3499_);
lean_ctor_set(v_reuseFailAlloc_3507_, 4, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
v___jp_3509_:
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
v___x_3511_ = lean_nat_add(v___x_3496_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec(v___x_3496_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 4, v_l_3487_);
lean_ctor_set(v___x_3321_, 0, v___x_3511_);
v___x_3513_ = v___x_3321_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3511_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3517_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3517_, 3, v_l_3318_);
lean_ctor_set(v_reuseFailAlloc_3517_, 4, v_l_3487_);
v___x_3513_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_object* v___x_3514_; 
v___x_3514_ = lean_nat_add(v___x_3466_, v_size_3489_);
if (lean_obj_tag(v_r_3488_) == 0)
{
lean_object* v_size_3515_; 
v_size_3515_ = lean_ctor_get(v_r_3488_, 0);
lean_inc(v_size_3515_);
v___y_3499_ = v___x_3513_;
v___y_3500_ = v___x_3514_;
v___y_3501_ = v_size_3515_;
goto v___jp_3498_;
}
else
{
lean_object* v___x_3516_; 
v___x_3516_ = lean_unsigned_to_nat(0u);
v___y_3499_ = v___x_3513_;
v___y_3500_ = v___x_3514_;
v___y_3501_ = v___x_3516_;
goto v___jp_3498_;
}
}
}
}
}
else
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3530_; 
lean_del_object(v___x_3321_);
v___x_3526_ = lean_nat_add(v___x_3466_, v_size_3467_);
v___x_3527_ = lean_nat_add(v___x_3526_, v_size_3468_);
lean_dec(v_size_3468_);
v___x_3528_ = lean_nat_add(v___x_3526_, v_size_3484_);
lean_dec(v___x_3526_);
lean_inc_ref(v_l_3318_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 4, v_l_3471_);
lean_ctor_set(v___x_3482_, 3, v_l_3318_);
lean_ctor_set(v___x_3482_, 2, v_v_3317_);
lean_ctor_set(v___x_3482_, 1, v_k_3316_);
lean_ctor_set(v___x_3482_, 0, v___x_3528_);
v___x_3530_ = v___x_3482_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3543_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3543_, 3, v_l_3318_);
lean_ctor_set(v_reuseFailAlloc_3543_, 4, v_l_3471_);
v___x_3530_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
v_isSharedCheck_3537_ = !lean_is_exclusive(v_l_3318_);
if (v_isSharedCheck_3537_ == 0)
{
lean_object* v_unused_3538_; lean_object* v_unused_3539_; lean_object* v_unused_3540_; lean_object* v_unused_3541_; lean_object* v_unused_3542_; 
v_unused_3538_ = lean_ctor_get(v_l_3318_, 4);
lean_dec(v_unused_3538_);
v_unused_3539_ = lean_ctor_get(v_l_3318_, 3);
lean_dec(v_unused_3539_);
v_unused_3540_ = lean_ctor_get(v_l_3318_, 2);
lean_dec(v_unused_3540_);
v_unused_3541_ = lean_ctor_get(v_l_3318_, 1);
lean_dec(v_unused_3541_);
v_unused_3542_ = lean_ctor_get(v_l_3318_, 0);
lean_dec(v_unused_3542_);
v___x_3532_ = v_l_3318_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_dec(v_l_3318_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 4, v_r_3472_);
lean_ctor_set(v___x_3532_, 3, v___x_3530_);
lean_ctor_set(v___x_3532_, 2, v_v_3470_);
lean_ctor_set(v___x_3532_, 1, v_k_3469_);
lean_ctor_set(v___x_3532_, 0, v___x_3527_);
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3527_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_k_3469_);
lean_ctor_set(v_reuseFailAlloc_3536_, 2, v_v_3470_);
lean_ctor_set(v_reuseFailAlloc_3536_, 3, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3536_, 4, v_r_3472_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3550_; 
v_l_3550_ = lean_ctor_get(v_impl_3465_, 3);
lean_inc(v_l_3550_);
if (lean_obj_tag(v_l_3550_) == 0)
{
lean_object* v_r_3551_; lean_object* v_k_3552_; lean_object* v_v_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3576_; 
v_r_3551_ = lean_ctor_get(v_impl_3465_, 4);
v_k_3552_ = lean_ctor_get(v_impl_3465_, 1);
v_v_3553_ = lean_ctor_get(v_impl_3465_, 2);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_impl_3465_);
if (v_isSharedCheck_3576_ == 0)
{
lean_object* v_unused_3577_; lean_object* v_unused_3578_; 
v_unused_3577_ = lean_ctor_get(v_impl_3465_, 3);
lean_dec(v_unused_3577_);
v_unused_3578_ = lean_ctor_get(v_impl_3465_, 0);
lean_dec(v_unused_3578_);
v___x_3555_ = v_impl_3465_;
v_isShared_3556_ = v_isSharedCheck_3576_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_r_3551_);
lean_inc(v_v_3553_);
lean_inc(v_k_3552_);
lean_dec(v_impl_3465_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3576_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v_k_3557_; lean_object* v_v_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3572_; 
v_k_3557_ = lean_ctor_get(v_l_3550_, 1);
v_v_3558_ = lean_ctor_get(v_l_3550_, 2);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_l_3550_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; lean_object* v_unused_3574_; lean_object* v_unused_3575_; 
v_unused_3573_ = lean_ctor_get(v_l_3550_, 4);
lean_dec(v_unused_3573_);
v_unused_3574_ = lean_ctor_get(v_l_3550_, 3);
lean_dec(v_unused_3574_);
v_unused_3575_ = lean_ctor_get(v_l_3550_, 0);
lean_dec(v_unused_3575_);
v___x_3560_ = v_l_3550_;
v_isShared_3561_ = v_isSharedCheck_3572_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_v_3558_);
lean_inc(v_k_3557_);
lean_dec(v_l_3550_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3572_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; lean_object* v___x_3564_; 
v___x_3562_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3551_, 2);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 4, v_r_3551_);
lean_ctor_set(v___x_3560_, 3, v_r_3551_);
lean_ctor_set(v___x_3560_, 2, v_v_3317_);
lean_ctor_set(v___x_3560_, 1, v_k_3316_);
lean_ctor_set(v___x_3560_, 0, v___x_3466_);
v___x_3564_ = v___x_3560_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3571_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3571_, 3, v_r_3551_);
lean_ctor_set(v_reuseFailAlloc_3571_, 4, v_r_3551_);
v___x_3564_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3566_; 
lean_inc(v_r_3551_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 3, v_r_3551_);
lean_ctor_set(v___x_3555_, 0, v___x_3466_);
v___x_3566_ = v___x_3555_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_k_3552_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v_v_3553_);
lean_ctor_set(v_reuseFailAlloc_3570_, 3, v_r_3551_);
lean_ctor_set(v_reuseFailAlloc_3570_, 4, v_r_3551_);
v___x_3566_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3568_; 
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 4, v___x_3566_);
lean_ctor_set(v___x_3321_, 3, v___x_3564_);
lean_ctor_set(v___x_3321_, 2, v_v_3558_);
lean_ctor_set(v___x_3321_, 1, v_k_3557_);
lean_ctor_set(v___x_3321_, 0, v___x_3562_);
v___x_3568_ = v___x_3321_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3562_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_k_3557_);
lean_ctor_set(v_reuseFailAlloc_3569_, 2, v_v_3558_);
lean_ctor_set(v_reuseFailAlloc_3569_, 3, v___x_3564_);
lean_ctor_set(v_reuseFailAlloc_3569_, 4, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
}
else
{
lean_object* v_r_3579_; 
v_r_3579_ = lean_ctor_get(v_impl_3465_, 4);
lean_inc(v_r_3579_);
if (lean_obj_tag(v_r_3579_) == 0)
{
lean_object* v_k_3580_; lean_object* v_v_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3592_; 
v_k_3580_ = lean_ctor_get(v_impl_3465_, 1);
v_v_3581_ = lean_ctor_get(v_impl_3465_, 2);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_impl_3465_);
if (v_isSharedCheck_3592_ == 0)
{
lean_object* v_unused_3593_; lean_object* v_unused_3594_; lean_object* v_unused_3595_; 
v_unused_3593_ = lean_ctor_get(v_impl_3465_, 4);
lean_dec(v_unused_3593_);
v_unused_3594_ = lean_ctor_get(v_impl_3465_, 3);
lean_dec(v_unused_3594_);
v_unused_3595_ = lean_ctor_get(v_impl_3465_, 0);
lean_dec(v_unused_3595_);
v___x_3583_ = v_impl_3465_;
v_isShared_3584_ = v_isSharedCheck_3592_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_v_3581_);
lean_inc(v_k_3580_);
lean_dec(v_impl_3465_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3592_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v___x_3587_; 
v___x_3585_ = lean_unsigned_to_nat(3u);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 4, v_l_3550_);
lean_ctor_set(v___x_3583_, 2, v_v_3317_);
lean_ctor_set(v___x_3583_, 1, v_k_3316_);
lean_ctor_set(v___x_3583_, 0, v___x_3466_);
v___x_3587_ = v___x_3583_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3591_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3591_, 3, v_l_3550_);
lean_ctor_set(v_reuseFailAlloc_3591_, 4, v_l_3550_);
v___x_3587_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3589_; 
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 4, v_r_3579_);
lean_ctor_set(v___x_3321_, 3, v___x_3587_);
lean_ctor_set(v___x_3321_, 2, v_v_3581_);
lean_ctor_set(v___x_3321_, 1, v_k_3580_);
lean_ctor_set(v___x_3321_, 0, v___x_3585_);
v___x_3589_ = v___x_3321_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_k_3580_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_v_3581_);
lean_ctor_set(v_reuseFailAlloc_3590_, 3, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3590_, 4, v_r_3579_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v___x_3596_; lean_object* v___x_3598_; 
v___x_3596_ = lean_unsigned_to_nat(2u);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 4, v_impl_3465_);
lean_ctor_set(v___x_3321_, 3, v_r_3579_);
lean_ctor_set(v___x_3321_, 0, v___x_3596_);
v___x_3598_ = v___x_3321_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3599_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3599_, 3, v_r_3579_);
lean_ctor_set(v_reuseFailAlloc_3599_, 4, v_impl_3465_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
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
lean_object* v___x_3601_; lean_object* v___x_3602_; 
lean_dec_ref(v_cmp_3311_);
v___x_3601_ = lean_unsigned_to_nat(1u);
v___x_3602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
lean_ctor_set(v___x_3602_, 1, v_k_3312_);
lean_ctor_set(v___x_3602_, 2, v_v_3313_);
lean_ctor_set(v___x_3602_, 3, v_t_3314_);
lean_ctor_set(v___x_3602_, 4, v_t_3314_);
return v___x_3602_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(lean_object* v_cmp_3603_, lean_object* v_init_3604_, lean_object* v_x_3605_){
_start:
{
if (lean_obj_tag(v_x_3605_) == 0)
{
lean_object* v_k_3606_; lean_object* v_v_3607_; lean_object* v_l_3608_; lean_object* v_r_3609_; lean_object* v___x_3610_; lean_object* v_a_3611_; lean_object* v_r_3612_; 
v_k_3606_ = lean_ctor_get(v_x_3605_, 1);
lean_inc(v_k_3606_);
v_v_3607_ = lean_ctor_get(v_x_3605_, 2);
lean_inc(v_v_3607_);
v_l_3608_ = lean_ctor_get(v_x_3605_, 3);
lean_inc(v_l_3608_);
v_r_3609_ = lean_ctor_get(v_x_3605_, 4);
lean_inc(v_r_3609_);
lean_dec_ref_known(v_x_3605_, 5);
lean_inc_ref_n(v_cmp_3603_, 2);
v___x_3610_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3603_, v_init_3604_, v_l_3608_);
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref(v___x_3610_);
v_r_3612_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3603_, v_k_3606_, v_v_3607_, v_a_3611_);
v_init_3604_ = v_r_3612_;
v_x_3605_ = v_r_3609_;
goto _start;
}
else
{
lean_object* v___x_3614_; 
lean_dec_ref(v_cmp_3603_);
v___x_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3614_, 0, v_init_3604_);
return v___x_3614_;
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(lean_object* v_cmp_3615_, lean_object* v_k_3616_, lean_object* v_t_3617_){
_start:
{
if (lean_obj_tag(v_t_3617_) == 0)
{
lean_object* v_k_3618_; lean_object* v_l_3619_; lean_object* v_r_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; 
v_k_3618_ = lean_ctor_get(v_t_3617_, 1);
lean_inc(v_k_3618_);
v_l_3619_ = lean_ctor_get(v_t_3617_, 3);
lean_inc(v_l_3619_);
v_r_3620_ = lean_ctor_get(v_t_3617_, 4);
lean_inc(v_r_3620_);
lean_dec_ref_known(v_t_3617_, 5);
lean_inc_ref(v_cmp_3615_);
lean_inc(v_k_3616_);
v___x_3621_ = lean_apply_2(v_cmp_3615_, v_k_3616_, v_k_3618_);
v___x_3622_ = lean_unbox(v___x_3621_);
switch(v___x_3622_)
{
case 0:
{
lean_dec(v_r_3620_);
v_t_3617_ = v_l_3619_;
goto _start;
}
case 1:
{
uint8_t v___x_3624_; 
lean_dec(v_r_3620_);
lean_dec(v_l_3619_);
lean_dec(v_k_3616_);
lean_dec_ref(v_cmp_3615_);
v___x_3624_ = 1;
return v___x_3624_;
}
default: 
{
lean_dec(v_l_3619_);
v_t_3617_ = v_r_3620_;
goto _start;
}
}
}
else
{
uint8_t v___x_3626_; 
lean_dec(v_k_3616_);
lean_dec_ref(v_cmp_3615_);
v___x_3626_ = 0;
return v___x_3626_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3615_ = stack[0].m_obj;
lean_object* v_k_3616_ = stack[1].m_obj;
lean_object* v_t_3617_ = stack[2].m_obj;
uint8_t v_res_3627_;
v_res_3627_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3615_, v_k_3616_, v_t_3617_);
stack->m_num = v_res_3627_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_3628_, lean_object* v_k_3629_, lean_object* v_t_3630_){
_start:
{
uint8_t v_res_3631_; lean_object* v_r_3632_; 
v_res_3631_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3628_, v_k_3629_, v_t_3630_);
v_r_3632_ = lean_box(v_res_3631_);
return v_r_3632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(lean_object* v_cmp_3633_, lean_object* v_init_3634_, lean_object* v_x_3635_){
_start:
{
if (lean_obj_tag(v_x_3635_) == 0)
{
lean_object* v_k_3636_; lean_object* v_v_3637_; lean_object* v_l_3638_; lean_object* v_r_3639_; lean_object* v___x_3640_; lean_object* v_a_3641_; uint8_t v___x_3642_; 
v_k_3636_ = lean_ctor_get(v_x_3635_, 1);
lean_inc_n(v_k_3636_, 2);
v_v_3637_ = lean_ctor_get(v_x_3635_, 2);
lean_inc(v_v_3637_);
v_l_3638_ = lean_ctor_get(v_x_3635_, 3);
lean_inc(v_l_3638_);
v_r_3639_ = lean_ctor_get(v_x_3635_, 4);
lean_inc(v_r_3639_);
lean_dec_ref_known(v_x_3635_, 5);
lean_inc_ref_n(v_cmp_3633_, 2);
v___x_3640_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3633_, v_init_3634_, v_l_3638_);
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc_n(v_a_3641_, 2);
lean_dec_ref(v___x_3640_);
v___x_3642_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3633_, v_k_3636_, v_a_3641_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; 
lean_inc_ref(v_cmp_3633_);
v___x_3643_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3633_, v_k_3636_, v_v_3637_, v_a_3641_);
v_init_3634_ = v___x_3643_;
v_x_3635_ = v_r_3639_;
goto _start;
}
else
{
lean_dec(v_v_3637_);
lean_dec(v_k_3636_);
v_init_3634_ = v_a_3641_;
v_x_3635_ = v_r_3639_;
goto _start;
}
}
else
{
lean_object* v___x_3646_; 
lean_dec_ref(v_cmp_3633_);
v___x_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3646_, 0, v_init_3634_);
return v___x_3646_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object* v_cmp_3647_, lean_object* v_t_u2081_3648_, lean_object* v_t_u2082_3649_){
_start:
{
lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3659_; 
if (lean_obj_tag(v_t_u2081_3648_) == 0)
{
lean_object* v_size_3662_; 
v_size_3662_ = lean_ctor_get(v_t_u2081_3648_, 0);
lean_inc(v_size_3662_);
v___y_3659_ = v_size_3662_;
goto v___jp_3658_;
}
else
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_unsigned_to_nat(0u);
v___y_3659_ = v___x_3663_;
goto v___jp_3658_;
}
v___jp_3650_:
{
uint8_t v___x_3653_; 
v___x_3653_ = lean_nat_dec_le(v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec(v___y_3651_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3654_; lean_object* v_a_3655_; 
v___x_3654_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3647_, v_t_u2081_3648_, v_t_u2082_3649_);
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3655_);
lean_dec_ref(v___x_3654_);
return v_a_3655_;
}
else
{
lean_object* v___x_3656_; lean_object* v_a_3657_; 
v___x_3656_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3647_, v_t_u2082_3649_, v_t_u2081_3648_);
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref(v___x_3656_);
return v_a_3657_;
}
}
v___jp_3658_:
{
if (lean_obj_tag(v_t_u2082_3649_) == 0)
{
lean_object* v_size_3660_; 
v_size_3660_ = lean_ctor_get(v_t_u2082_3649_, 0);
lean_inc(v_size_3660_);
v___y_3651_ = v___y_3659_;
v___y_3652_ = v_size_3660_;
goto v___jp_3650_;
}
else
{
lean_object* v___x_3661_; 
v___x_3661_ = lean_unsigned_to_nat(0u);
v___y_3651_ = v___y_3659_;
v___y_3652_ = v___x_3661_;
goto v___jp_3650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_union___redArg(lean_object* v_cmp_3664_, lean_object* v_t_u2081_3665_, lean_object* v_t_u2082_3666_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3664_, v_t_u2081_3665_, v_t_u2082_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_union(lean_object* v_00_u03b1_3668_, lean_object* v_00_u03b2_3669_, lean_object* v_cmp_3670_, lean_object* v_t_u2081_3671_, lean_object* v_t_u2082_3672_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3670_, v_t_u2081_3671_, v_t_u2082_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0(lean_object* v_00_u03b1_3674_, lean_object* v_cmp_3675_, lean_object* v_00_u03b2_3676_, lean_object* v_t_u2081_3677_, lean_object* v_t_u2082_3678_, lean_object* v_h_u2081_3679_, lean_object* v_h_u2082_3680_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_3675_, v_t_u2081_3677_, v_t_u2082_3678_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0(lean_object* v_00_u03b1_3682_, lean_object* v_cmp_3683_, lean_object* v_00_u03b2_3684_, lean_object* v_k_3685_, lean_object* v_v_3686_, lean_object* v_t_3687_, lean_object* v_hl_3688_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3683_, v_k_3685_, v_v_3686_, v_t_3687_);
return v___x_3689_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1(lean_object* v_00_u03b1_3690_, lean_object* v_cmp_3691_, lean_object* v_00_u03b2_3692_, lean_object* v_k_3693_, lean_object* v_t_3694_){
_start:
{
uint8_t v___x_3695_; 
v___x_3695_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3691_, v_k_3693_, v_t_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3691_ = stack[1].m_obj;
lean_object* v_k_3693_ = stack[3].m_obj;
lean_object* v_t_3694_ = stack[4].m_obj;
uint8_t v_res_3696_;
v_res_3696_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1(lean_box(0), v_cmp_3691_, lean_box(0), v_k_3693_, v_t_3694_);
stack->m_num = v_res_3696_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3697_, lean_object* v_cmp_3698_, lean_object* v_00_u03b2_3699_, lean_object* v_k_3700_, lean_object* v_t_3701_){
_start:
{
uint8_t v_res_3702_; lean_object* v_r_3703_; 
v_res_3702_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1(v_00_u03b1_3697_, v_cmp_3698_, v_00_u03b2_3699_, v_k_3700_, v_t_3701_);
v_r_3703_ = lean_box(v_res_3702_);
return v_r_3703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2(lean_object* v_00_u03b1_3704_, lean_object* v_00_u03b2_3705_, lean_object* v_cmp_3706_, lean_object* v_init_3707_, lean_object* v_x_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_3706_, v_init_3707_, v_x_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3(lean_object* v_00_u03b1_3710_, lean_object* v_00_u03b2_3711_, lean_object* v_cmp_3712_, lean_object* v_init_3713_, lean_object* v_x_3714_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_3712_, v_init_3713_, v_x_3714_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instUnion___redArg(lean_object* v_cmp_3716_){
_start:
{
lean_object* v___x_3717_; 
v___x_3717_ = lean_alloc_closure((void*)(l_Std_DTreeMap_union), 5, 3);
lean_closure_set(v___x_3717_, 0, lean_box(0));
lean_closure_set(v___x_3717_, 1, lean_box(0));
lean_closure_set(v___x_3717_, 2, v_cmp_3716_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instUnion(lean_object* v_00_u03b1_3718_, lean_object* v_00_u03b2_3719_, lean_object* v_cmp_3720_){
_start:
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_alloc_closure((void*)(l_Std_DTreeMap_union), 5, 3);
lean_closure_set(v___x_3721_, 0, lean_box(0));
lean_closure_set(v___x_3721_, 1, lean_box(0));
lean_closure_set(v___x_3721_, 2, v_cmp_3720_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(lean_object* v_cmp_3722_, lean_object* v_m_u2082_3723_, lean_object* v_t_3724_){
_start:
{
if (lean_obj_tag(v_t_3724_) == 0)
{
lean_object* v_k_3725_; lean_object* v_v_3726_; lean_object* v_l_3727_; lean_object* v_r_3728_; uint8_t v___x_3729_; 
v_k_3725_ = lean_ctor_get(v_t_3724_, 1);
lean_inc_n(v_k_3725_, 2);
v_v_3726_ = lean_ctor_get(v_t_3724_, 2);
lean_inc(v_v_3726_);
v_l_3727_ = lean_ctor_get(v_t_3724_, 3);
lean_inc(v_l_3727_);
v_r_3728_ = lean_ctor_get(v_t_3724_, 4);
lean_inc(v_r_3728_);
lean_dec_ref_known(v_t_3724_, 5);
lean_inc(v_m_u2082_3723_);
lean_inc_ref(v_cmp_3722_);
v___x_3729_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_3722_, v_k_3725_, v_m_u2082_3723_);
if (v___x_3729_ == 0)
{
lean_object* v_impl_3730_; lean_object* v_impl_3731_; lean_object* v___x_3732_; 
lean_dec(v_v_3726_);
lean_dec(v_k_3725_);
lean_inc(v_m_u2082_3723_);
lean_inc_ref(v_cmp_3722_);
v_impl_3730_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3722_, v_m_u2082_3723_, v_l_3727_);
v_impl_3731_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3722_, v_m_u2082_3723_, v_r_3728_);
v___x_3732_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_3730_, v_impl_3731_);
return v___x_3732_;
}
else
{
lean_object* v_impl_3733_; lean_object* v_impl_3734_; lean_object* v___x_3735_; 
lean_inc(v_m_u2082_3723_);
lean_inc_ref(v_cmp_3722_);
v_impl_3733_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3722_, v_m_u2082_3723_, v_l_3727_);
v_impl_3734_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3722_, v_m_u2082_3723_, v_r_3728_);
v___x_3735_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_3725_, v_v_3726_, v_impl_3733_, v_impl_3734_);
return v___x_3735_;
}
}
else
{
lean_dec(v_m_u2082_3723_);
lean_dec_ref(v_cmp_3722_);
return v_t_3724_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_3736_, lean_object* v_t_3737_, lean_object* v_k_3738_){
_start:
{
if (lean_obj_tag(v_t_3737_) == 0)
{
lean_object* v_k_3739_; lean_object* v_v_3740_; lean_object* v_l_3741_; lean_object* v_r_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; 
v_k_3739_ = lean_ctor_get(v_t_3737_, 1);
lean_inc_n(v_k_3739_, 2);
v_v_3740_ = lean_ctor_get(v_t_3737_, 2);
lean_inc(v_v_3740_);
v_l_3741_ = lean_ctor_get(v_t_3737_, 3);
lean_inc(v_l_3741_);
v_r_3742_ = lean_ctor_get(v_t_3737_, 4);
lean_inc(v_r_3742_);
lean_dec_ref_known(v_t_3737_, 5);
lean_inc_ref(v_cmp_3736_);
lean_inc(v_k_3738_);
v___x_3743_ = lean_apply_2(v_cmp_3736_, v_k_3738_, v_k_3739_);
v___x_3744_ = lean_unbox(v___x_3743_);
switch(v___x_3744_)
{
case 0:
{
lean_dec(v_r_3742_);
lean_dec(v_v_3740_);
lean_dec(v_k_3739_);
v_t_3737_ = v_l_3741_;
goto _start;
}
case 1:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; 
lean_dec(v_r_3742_);
lean_dec(v_l_3741_);
lean_dec(v_k_3738_);
lean_dec_ref(v_cmp_3736_);
v___x_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3746_, 0, v_k_3739_);
lean_ctor_set(v___x_3746_, 1, v_v_3740_);
v___x_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
return v___x_3747_;
}
default: 
{
lean_dec(v_l_3741_);
lean_dec(v_v_3740_);
lean_dec(v_k_3739_);
v_t_3737_ = v_r_3742_;
goto _start;
}
}
}
else
{
lean_object* v___x_3749_; 
lean_dec(v_k_3738_);
lean_dec_ref(v_cmp_3736_);
v___x_3749_ = lean_box(0);
return v___x_3749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_cmp_3750_, lean_object* v_m_u2081_3751_, lean_object* v_init_3752_, lean_object* v_x_3753_){
_start:
{
if (lean_obj_tag(v_x_3753_) == 0)
{
lean_object* v_k_3754_; lean_object* v_l_3755_; lean_object* v_r_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v_k_3754_ = lean_ctor_get(v_x_3753_, 1);
lean_inc(v_k_3754_);
v_l_3755_ = lean_ctor_get(v_x_3753_, 3);
lean_inc(v_l_3755_);
v_r_3756_ = lean_ctor_get(v_x_3753_, 4);
lean_inc(v_r_3756_);
lean_dec_ref_known(v_x_3753_, 5);
lean_inc_n(v_m_u2081_3751_, 2);
lean_inc_ref_n(v_cmp_3750_, 2);
v___x_3757_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3750_, v_m_u2081_3751_, v_init_3752_, v_l_3755_);
v___x_3758_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3750_, v_m_u2081_3751_, v_k_3754_);
if (lean_obj_tag(v___x_3758_) == 0)
{
v_init_3752_ = v___x_3757_;
v_x_3753_ = v_r_3756_;
goto _start;
}
else
{
lean_object* v_val_3760_; lean_object* v_fst_3761_; lean_object* v_snd_3762_; lean_object* v_impl_3763_; 
v_val_3760_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_val_3760_);
lean_dec_ref_known(v___x_3758_, 1);
v_fst_3761_ = lean_ctor_get(v_val_3760_, 0);
lean_inc(v_fst_3761_);
v_snd_3762_ = lean_ctor_get(v_val_3760_, 1);
lean_inc(v_snd_3762_);
lean_dec(v_val_3760_);
lean_inc_ref(v_cmp_3750_);
v_impl_3763_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_3750_, v_fst_3761_, v_snd_3762_, v___x_3757_);
v_init_3752_ = v_impl_3763_;
v_x_3753_ = v_r_3756_;
goto _start;
}
}
else
{
lean_dec(v_m_u2081_3751_);
lean_dec_ref(v_cmp_3750_);
return v_init_3752_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(lean_object* v_cmp_3765_, lean_object* v_m_u2081_3766_, lean_object* v_m_u2082_3767_){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3768_ = lean_box(1);
v___x_3769_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3765_, v_m_u2081_3766_, v___x_3768_, v_m_u2082_3767_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(lean_object* v_cmp_3770_, lean_object* v_m_u2081_3771_, lean_object* v_m_u2082_3772_){
_start:
{
lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3780_; 
if (lean_obj_tag(v_m_u2081_3771_) == 0)
{
lean_object* v_size_3783_; 
v_size_3783_ = lean_ctor_get(v_m_u2081_3771_, 0);
lean_inc(v_size_3783_);
v___y_3780_ = v_size_3783_;
goto v___jp_3779_;
}
else
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_unsigned_to_nat(0u);
v___y_3780_ = v___x_3784_;
goto v___jp_3779_;
}
v___jp_3773_:
{
uint8_t v___x_3776_; 
v___x_3776_ = lean_nat_dec_le(v___y_3774_, v___y_3775_);
lean_dec(v___y_3775_);
lean_dec(v___y_3774_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(v_cmp_3770_, v_m_u2081_3771_, v_m_u2082_3772_);
return v___x_3777_;
}
else
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3770_, v_m_u2082_3772_, v_m_u2081_3771_);
return v___x_3778_;
}
}
v___jp_3779_:
{
if (lean_obj_tag(v_m_u2082_3772_) == 0)
{
lean_object* v_size_3781_; 
v_size_3781_ = lean_ctor_get(v_m_u2082_3772_, 0);
lean_inc(v_size_3781_);
v___y_3774_ = v___y_3780_;
v___y_3775_ = v_size_3781_;
goto v___jp_3773_;
}
else
{
lean_object* v___x_3782_; 
v___x_3782_ = lean_unsigned_to_nat(0u);
v___y_3774_ = v___y_3780_;
v___y_3775_ = v___x_3782_;
goto v___jp_3773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_inter___redArg(lean_object* v_cmp_3785_, lean_object* v_t_u2081_3786_, lean_object* v_t_u2082_3787_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3785_, v_t_u2081_3786_, v_t_u2082_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_inter(lean_object* v_00_u03b1_3789_, lean_object* v_00_u03b2_3790_, lean_object* v_cmp_3791_, lean_object* v_t_u2081_3792_, lean_object* v_t_u2082_3793_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3791_, v_t_u2081_3792_, v_t_u2082_3793_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0(lean_object* v_00_u03b1_3795_, lean_object* v_cmp_3796_, lean_object* v_00_u03b2_3797_, lean_object* v_m_u2081_3798_, lean_object* v_m_u2082_3799_, lean_object* v_h_u2081_3800_){
_start:
{
lean_object* v___x_3801_; 
v___x_3801_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_3796_, v_m_u2081_3798_, v_m_u2082_3799_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0(lean_object* v_00_u03b1_3802_, lean_object* v_cmp_3803_, lean_object* v_00_u03b2_3804_, lean_object* v_m_u2081_3805_, lean_object* v_m_u2082_3806_){
_start:
{
lean_object* v___x_3807_; 
v___x_3807_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(v_cmp_3803_, v_m_u2081_3805_, v_m_u2082_3806_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1(lean_object* v_00_u03b1_3808_, lean_object* v_00_u03b2_3809_, lean_object* v_cmp_3810_, lean_object* v_m_u2082_3811_, lean_object* v_t_3812_, lean_object* v_hl_3813_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_3810_, v_m_u2082_3811_, v_t_3812_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3815_, lean_object* v_cmp_3816_, lean_object* v_00_u03b2_3817_, lean_object* v_t_3818_, lean_object* v_k_3819_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3816_, v_t_3818_, v_k_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2___redArg(lean_object* v_cmp_3821_, lean_object* v_m_u2081_3822_, lean_object* v_init_3823_, lean_object* v_t_3824_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3821_, v_m_u2081_3822_, v_init_3823_, v_t_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3826_, lean_object* v_00_u03b2_3827_, lean_object* v_cmp_3828_, lean_object* v_m_u2081_3829_, lean_object* v_init_3830_, lean_object* v_t_3831_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3828_, v_m_u2081_3829_, v_init_3830_, v_t_3831_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_3833_, lean_object* v_00_u03b2_3834_, lean_object* v_cmp_3835_, lean_object* v_m_u2081_3836_, lean_object* v_init_3837_, lean_object* v_x_3838_){
_start:
{
lean_object* v___x_3839_; 
v___x_3839_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_3835_, v_m_u2081_3836_, v_init_3837_, v_x_3838_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInter___redArg(lean_object* v_cmp_3840_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_alloc_closure((void*)(l_Std_DTreeMap_inter), 5, 3);
lean_closure_set(v___x_3841_, 0, lean_box(0));
lean_closure_set(v___x_3841_, 1, lean_box(0));
lean_closure_set(v___x_3841_, 2, v_cmp_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instInter(lean_object* v_00_u03b1_3842_, lean_object* v_00_u03b2_3843_, lean_object* v_cmp_3844_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = lean_alloc_closure((void*)(l_Std_DTreeMap_inter), 5, 3);
lean_closure_set(v___x_3845_, 0, lean_box(0));
lean_closure_set(v___x_3845_, 1, lean_box(0));
lean_closure_set(v___x_3845_, 2, v_cmp_3844_);
return v___x_3845_;
}
}
uint8_t l_Std_DTreeMap_beq___redArg(lean_object* v_cmp_3846_, lean_object* v_inst_3847_, lean_object* v_t_u2081_3848_, lean_object* v_t_u2082_3849_){
_start:
{
uint8_t v___x_3850_; 
v___x_3850_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3846_, v_inst_3847_, v_t_u2081_3848_, v_t_u2082_3849_);
return v___x_3850_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3846_ = stack[0].m_obj;
lean_object* v_inst_3847_ = stack[1].m_obj;
lean_object* v_t_u2081_3848_ = stack[2].m_obj;
lean_object* v_t_u2082_3849_ = stack[3].m_obj;
uint8_t v_res_3851_;
v_res_3851_ = l_Std_DTreeMap_beq___redArg(v_cmp_3846_, v_inst_3847_, v_t_u2081_3848_, v_t_u2082_3849_);
stack->m_num = v_res_3851_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_beq___redArg___boxed(lean_object* v_cmp_3852_, lean_object* v_inst_3853_, lean_object* v_t_u2081_3854_, lean_object* v_t_u2082_3855_){
_start:
{
uint8_t v_res_3856_; lean_object* v_r_3857_; 
v_res_3856_ = l_Std_DTreeMap_beq___redArg(v_cmp_3852_, v_inst_3853_, v_t_u2081_3854_, v_t_u2082_3855_);
v_r_3857_ = lean_box(v_res_3856_);
return v_r_3857_;
}
}
uint8_t l_Std_DTreeMap_beq(lean_object* v_00_u03b1_3858_, lean_object* v_00_u03b2_3859_, lean_object* v_cmp_3860_, lean_object* v_inst_3861_, lean_object* v_inst_3862_, lean_object* v_t_u2081_3863_, lean_object* v_t_u2082_3864_){
_start:
{
uint8_t v___x_3865_; 
v___x_3865_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3860_, v_inst_3862_, v_t_u2081_3863_, v_t_u2082_3864_);
return v___x_3865_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3860_ = stack[2].m_obj;
lean_object* v_inst_3862_ = stack[4].m_obj;
lean_object* v_t_u2081_3863_ = stack[5].m_obj;
lean_object* v_t_u2082_3864_ = stack[6].m_obj;
uint8_t v_res_3866_;
v_res_3866_ = l_Std_DTreeMap_beq(lean_box(0), lean_box(0), v_cmp_3860_, lean_box(0), v_inst_3862_, v_t_u2081_3863_, v_t_u2082_3864_);
stack->m_num = v_res_3866_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_beq___boxed(lean_object* v_00_u03b1_3867_, lean_object* v_00_u03b2_3868_, lean_object* v_cmp_3869_, lean_object* v_inst_3870_, lean_object* v_inst_3871_, lean_object* v_t_u2081_3872_, lean_object* v_t_u2082_3873_){
_start:
{
uint8_t v_res_3874_; lean_object* v_r_3875_; 
v_res_3874_ = l_Std_DTreeMap_beq(v_00_u03b1_3867_, v_00_u03b2_3868_, v_cmp_3869_, v_inst_3870_, v_inst_3871_, v_t_u2081_3872_, v_t_u2082_3873_);
v_r_3875_ = lean_box(v_res_3874_);
return v_r_3875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instBEqOfLawfulEqCmp___redArg(lean_object* v_cmp_3876_, lean_object* v_inst_3877_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = lean_alloc_closure((void*)(l_Std_DTreeMap_beq___boxed), 7, 5);
lean_closure_set(v___x_3878_, 0, lean_box(0));
lean_closure_set(v___x_3878_, 1, lean_box(0));
lean_closure_set(v___x_3878_, 2, v_cmp_3876_);
lean_closure_set(v___x_3878_, 3, lean_box(0));
lean_closure_set(v___x_3878_, 4, v_inst_3877_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instBEqOfLawfulEqCmp(lean_object* v_00_u03b1_3879_, lean_object* v_00_u03b2_3880_, lean_object* v_cmp_3881_, lean_object* v_inst_3882_, lean_object* v_inst_3883_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_alloc_closure((void*)(l_Std_DTreeMap_beq___boxed), 7, 5);
lean_closure_set(v___x_3884_, 0, lean_box(0));
lean_closure_set(v___x_3884_, 1, lean_box(0));
lean_closure_set(v___x_3884_, 2, v_cmp_3881_);
lean_closure_set(v___x_3884_, 3, lean_box(0));
lean_closure_set(v___x_3884_, 4, v_inst_3883_);
return v___x_3884_;
}
}
uint8_t l_Std_DTreeMap_Const_beq___redArg(lean_object* v_cmp_3885_, lean_object* v_inst_3886_, lean_object* v_t_u2081_3887_, lean_object* v_t_u2082_3888_){
_start:
{
uint8_t v___x_3889_; 
v___x_3889_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3885_, v_inst_3886_, v_t_u2081_3887_, v_t_u2082_3888_);
return v___x_3889_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Const_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3885_ = stack[0].m_obj;
lean_object* v_inst_3886_ = stack[1].m_obj;
lean_object* v_t_u2081_3887_ = stack[2].m_obj;
lean_object* v_t_u2082_3888_ = stack[3].m_obj;
uint8_t v_res_3890_;
v_res_3890_ = l_Std_DTreeMap_Const_beq___redArg(v_cmp_3885_, v_inst_3886_, v_t_u2081_3887_, v_t_u2082_3888_);
stack->m_num = v_res_3890_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___redArg___boxed(lean_object* v_cmp_3891_, lean_object* v_inst_3892_, lean_object* v_t_u2081_3893_, lean_object* v_t_u2082_3894_){
_start:
{
uint8_t v_res_3895_; lean_object* v_r_3896_; 
v_res_3895_ = l_Std_DTreeMap_Const_beq___redArg(v_cmp_3891_, v_inst_3892_, v_t_u2081_3893_, v_t_u2082_3894_);
v_r_3896_ = lean_box(v_res_3895_);
return v_r_3896_;
}
}
uint8_t l_Std_DTreeMap_Const_beq(lean_object* v_00_u03b1_3897_, lean_object* v_cmp_3898_, lean_object* v_00_u03b2_3899_, lean_object* v_inst_3900_, lean_object* v_t_u2081_3901_, lean_object* v_t_u2082_3902_){
_start:
{
uint8_t v___x_3903_; 
v___x_3903_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3898_, v_inst_3900_, v_t_u2081_3901_, v_t_u2082_3902_);
return v___x_3903_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Const_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3898_ = stack[1].m_obj;
lean_object* v_inst_3900_ = stack[3].m_obj;
lean_object* v_t_u2081_3901_ = stack[4].m_obj;
lean_object* v_t_u2082_3902_ = stack[5].m_obj;
uint8_t v_res_3904_;
v_res_3904_ = l_Std_DTreeMap_Const_beq(lean_box(0), v_cmp_3898_, lean_box(0), v_inst_3900_, v_t_u2081_3901_, v_t_u2082_3902_);
stack->m_num = v_res_3904_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___boxed(lean_object* v_00_u03b1_3905_, lean_object* v_cmp_3906_, lean_object* v_00_u03b2_3907_, lean_object* v_inst_3908_, lean_object* v_t_u2081_3909_, lean_object* v_t_u2082_3910_){
_start:
{
uint8_t v_res_3911_; lean_object* v_r_3912_; 
v_res_3911_ = l_Std_DTreeMap_Const_beq(v_00_u03b1_3905_, v_cmp_3906_, v_00_u03b2_3907_, v_inst_3908_, v_t_u2081_3909_, v_t_u2082_3910_);
v_r_3912_ = lean_box(v_res_3911_);
return v_r_3912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(lean_object* v_cmp_3913_, lean_object* v_k_3914_, lean_object* v_t_3915_){
_start:
{
if (lean_obj_tag(v_t_3915_) == 0)
{
lean_object* v_k_3916_; lean_object* v_v_3917_; lean_object* v_l_3918_; lean_object* v_r_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_4574_; 
v_k_3916_ = lean_ctor_get(v_t_3915_, 1);
v_v_3917_ = lean_ctor_get(v_t_3915_, 2);
v_l_3918_ = lean_ctor_get(v_t_3915_, 3);
v_r_3919_ = lean_ctor_get(v_t_3915_, 4);
v_isSharedCheck_4574_ = !lean_is_exclusive(v_t_3915_);
if (v_isSharedCheck_4574_ == 0)
{
lean_object* v_unused_4575_; 
v_unused_4575_ = lean_ctor_get(v_t_3915_, 0);
lean_dec(v_unused_4575_);
v___x_3921_ = v_t_3915_;
v_isShared_3922_ = v_isSharedCheck_4574_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_r_3919_);
lean_inc(v_l_3918_);
lean_inc(v_v_3917_);
lean_inc(v_k_3916_);
lean_dec(v_t_3915_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_4574_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; uint8_t v___x_3924_; 
lean_inc_ref(v_cmp_3913_);
lean_inc(v_k_3916_);
lean_inc(v_k_3914_);
v___x_3923_ = lean_apply_2(v_cmp_3913_, v_k_3914_, v_k_3916_);
v___x_3924_ = lean_unbox(v___x_3923_);
switch(v___x_3924_)
{
case 0:
{
lean_object* v_impl_3925_; lean_object* v___x_3926_; 
v_impl_3925_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_3913_, v_k_3914_, v_l_3918_);
v___x_3926_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3925_) == 0)
{
if (lean_obj_tag(v_r_3919_) == 0)
{
lean_object* v_size_3927_; lean_object* v_size_3928_; lean_object* v_k_3929_; lean_object* v_v_3930_; lean_object* v_l_3931_; lean_object* v_r_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; uint8_t v___x_3935_; 
v_size_3927_ = lean_ctor_get(v_impl_3925_, 0);
v_size_3928_ = lean_ctor_get(v_r_3919_, 0);
v_k_3929_ = lean_ctor_get(v_r_3919_, 1);
v_v_3930_ = lean_ctor_get(v_r_3919_, 2);
v_l_3931_ = lean_ctor_get(v_r_3919_, 3);
lean_inc(v_l_3931_);
v_r_3932_ = lean_ctor_get(v_r_3919_, 4);
v___x_3933_ = lean_unsigned_to_nat(3u);
v___x_3934_ = lean_nat_mul(v___x_3933_, v_size_3927_);
v___x_3935_ = lean_nat_dec_lt(v___x_3934_, v_size_3928_);
lean_dec(v___x_3934_);
if (v___x_3935_ == 0)
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3939_; 
lean_dec(v_l_3931_);
v___x_3936_ = lean_nat_add(v___x_3926_, v_size_3927_);
v___x_3937_ = lean_nat_add(v___x_3936_, v_size_3928_);
lean_dec(v___x_3936_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 3, v_impl_3925_);
lean_ctor_set(v___x_3921_, 0, v___x_3937_);
v___x_3939_ = v___x_3921_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_3940_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_3940_, 3, v_impl_3925_);
lean_ctor_set(v_reuseFailAlloc_3940_, 4, v_r_3919_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
else
{
lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_4004_; 
lean_inc(v_r_3932_);
lean_inc(v_v_3930_);
lean_inc(v_k_3929_);
lean_inc(v_size_3928_);
v_isSharedCheck_4004_ = !lean_is_exclusive(v_r_3919_);
if (v_isSharedCheck_4004_ == 0)
{
lean_object* v_unused_4005_; lean_object* v_unused_4006_; lean_object* v_unused_4007_; lean_object* v_unused_4008_; lean_object* v_unused_4009_; 
v_unused_4005_ = lean_ctor_get(v_r_3919_, 4);
lean_dec(v_unused_4005_);
v_unused_4006_ = lean_ctor_get(v_r_3919_, 3);
lean_dec(v_unused_4006_);
v_unused_4007_ = lean_ctor_get(v_r_3919_, 2);
lean_dec(v_unused_4007_);
v_unused_4008_ = lean_ctor_get(v_r_3919_, 1);
lean_dec(v_unused_4008_);
v_unused_4009_ = lean_ctor_get(v_r_3919_, 0);
lean_dec(v_unused_4009_);
v___x_3942_ = v_r_3919_;
v_isShared_3943_ = v_isSharedCheck_4004_;
goto v_resetjp_3941_;
}
else
{
lean_dec(v_r_3919_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_4004_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v_size_3944_; lean_object* v_k_3945_; lean_object* v_v_3946_; lean_object* v_l_3947_; lean_object* v_r_3948_; lean_object* v_size_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; uint8_t v___x_3952_; 
v_size_3944_ = lean_ctor_get(v_l_3931_, 0);
v_k_3945_ = lean_ctor_get(v_l_3931_, 1);
v_v_3946_ = lean_ctor_get(v_l_3931_, 2);
v_l_3947_ = lean_ctor_get(v_l_3931_, 3);
v_r_3948_ = lean_ctor_get(v_l_3931_, 4);
v_size_3949_ = lean_ctor_get(v_r_3932_, 0);
v___x_3950_ = lean_unsigned_to_nat(2u);
v___x_3951_ = lean_nat_mul(v___x_3950_, v_size_3949_);
v___x_3952_ = lean_nat_dec_lt(v_size_3944_, v___x_3951_);
lean_dec(v___x_3951_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3980_; 
lean_inc(v_r_3948_);
lean_inc(v_l_3947_);
lean_inc(v_v_3946_);
lean_inc(v_k_3945_);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_l_3931_);
if (v_isSharedCheck_3980_ == 0)
{
lean_object* v_unused_3981_; lean_object* v_unused_3982_; lean_object* v_unused_3983_; lean_object* v_unused_3984_; lean_object* v_unused_3985_; 
v_unused_3981_ = lean_ctor_get(v_l_3931_, 4);
lean_dec(v_unused_3981_);
v_unused_3982_ = lean_ctor_get(v_l_3931_, 3);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_l_3931_, 2);
lean_dec(v_unused_3983_);
v_unused_3984_ = lean_ctor_get(v_l_3931_, 1);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_l_3931_, 0);
lean_dec(v_unused_3985_);
v___x_3954_ = v_l_3931_;
v_isShared_3955_ = v_isSharedCheck_3980_;
goto v_resetjp_3953_;
}
else
{
lean_dec(v_l_3931_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3980_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3970_; 
v___x_3956_ = lean_nat_add(v___x_3926_, v_size_3927_);
v___x_3957_ = lean_nat_add(v___x_3956_, v_size_3928_);
lean_dec(v_size_3928_);
if (lean_obj_tag(v_l_3947_) == 0)
{
lean_object* v_size_3978_; 
v_size_3978_ = lean_ctor_get(v_l_3947_, 0);
lean_inc(v_size_3978_);
v___y_3970_ = v_size_3978_;
goto v___jp_3969_;
}
else
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_unsigned_to_nat(0u);
v___y_3970_ = v___x_3979_;
goto v___jp_3969_;
}
v___jp_3958_:
{
lean_object* v___x_3962_; lean_object* v___x_3964_; 
v___x_3962_ = lean_nat_add(v___y_3959_, v___y_3961_);
lean_dec(v___y_3961_);
lean_dec(v___y_3959_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 4, v_r_3932_);
lean_ctor_set(v___x_3954_, 3, v_r_3948_);
lean_ctor_set(v___x_3954_, 2, v_v_3930_);
lean_ctor_set(v___x_3954_, 1, v_k_3929_);
lean_ctor_set(v___x_3954_, 0, v___x_3962_);
v___x_3964_ = v___x_3954_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3962_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_k_3929_);
lean_ctor_set(v_reuseFailAlloc_3968_, 2, v_v_3930_);
lean_ctor_set(v_reuseFailAlloc_3968_, 3, v_r_3948_);
lean_ctor_set(v_reuseFailAlloc_3968_, 4, v_r_3932_);
v___x_3964_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
lean_object* v___x_3966_; 
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 4, v___x_3964_);
lean_ctor_set(v___x_3942_, 3, v___y_3960_);
lean_ctor_set(v___x_3942_, 2, v_v_3946_);
lean_ctor_set(v___x_3942_, 1, v_k_3945_);
lean_ctor_set(v___x_3942_, 0, v___x_3957_);
v___x_3966_ = v___x_3942_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3957_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_k_3945_);
lean_ctor_set(v_reuseFailAlloc_3967_, 2, v_v_3946_);
lean_ctor_set(v_reuseFailAlloc_3967_, 3, v___y_3960_);
lean_ctor_set(v_reuseFailAlloc_3967_, 4, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
v___jp_3969_:
{
lean_object* v___x_3971_; lean_object* v___x_3973_; 
v___x_3971_ = lean_nat_add(v___x_3956_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec(v___x_3956_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v_l_3947_);
lean_ctor_set(v___x_3921_, 3, v_impl_3925_);
lean_ctor_set(v___x_3921_, 0, v___x_3971_);
v___x_3973_ = v___x_3921_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3971_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_3977_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_3977_, 3, v_impl_3925_);
lean_ctor_set(v_reuseFailAlloc_3977_, 4, v_l_3947_);
v___x_3973_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
lean_object* v___x_3974_; 
v___x_3974_ = lean_nat_add(v___x_3926_, v_size_3949_);
if (lean_obj_tag(v_r_3948_) == 0)
{
lean_object* v_size_3975_; 
v_size_3975_ = lean_ctor_get(v_r_3948_, 0);
lean_inc(v_size_3975_);
v___y_3959_ = v___x_3974_;
v___y_3960_ = v___x_3973_;
v___y_3961_ = v_size_3975_;
goto v___jp_3958_;
}
else
{
lean_object* v___x_3976_; 
v___x_3976_ = lean_unsigned_to_nat(0u);
v___y_3959_ = v___x_3974_;
v___y_3960_ = v___x_3973_;
v___y_3961_ = v___x_3976_;
goto v___jp_3958_;
}
}
}
}
}
else
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3990_; 
lean_del_object(v___x_3921_);
v___x_3986_ = lean_nat_add(v___x_3926_, v_size_3927_);
v___x_3987_ = lean_nat_add(v___x_3986_, v_size_3928_);
lean_dec(v_size_3928_);
v___x_3988_ = lean_nat_add(v___x_3986_, v_size_3944_);
lean_dec(v___x_3986_);
lean_inc_ref(v_impl_3925_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 4, v_l_3931_);
lean_ctor_set(v___x_3942_, 3, v_impl_3925_);
lean_ctor_set(v___x_3942_, 2, v_v_3917_);
lean_ctor_set(v___x_3942_, 1, v_k_3916_);
lean_ctor_set(v___x_3942_, 0, v___x_3988_);
v___x_3990_ = v___x_3942_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_3988_);
lean_ctor_set(v_reuseFailAlloc_4003_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4003_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4003_, 3, v_impl_3925_);
lean_ctor_set(v_reuseFailAlloc_4003_, 4, v_l_3931_);
v___x_3990_ = v_reuseFailAlloc_4003_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
v_isSharedCheck_3997_ = !lean_is_exclusive(v_impl_3925_);
if (v_isSharedCheck_3997_ == 0)
{
lean_object* v_unused_3998_; lean_object* v_unused_3999_; lean_object* v_unused_4000_; lean_object* v_unused_4001_; lean_object* v_unused_4002_; 
v_unused_3998_ = lean_ctor_get(v_impl_3925_, 4);
lean_dec(v_unused_3998_);
v_unused_3999_ = lean_ctor_get(v_impl_3925_, 3);
lean_dec(v_unused_3999_);
v_unused_4000_ = lean_ctor_get(v_impl_3925_, 2);
lean_dec(v_unused_4000_);
v_unused_4001_ = lean_ctor_get(v_impl_3925_, 1);
lean_dec(v_unused_4001_);
v_unused_4002_ = lean_ctor_get(v_impl_3925_, 0);
lean_dec(v_unused_4002_);
v___x_3992_ = v_impl_3925_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_dec(v_impl_3925_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 4, v_r_3932_);
lean_ctor_set(v___x_3992_, 3, v___x_3990_);
lean_ctor_set(v___x_3992_, 2, v_v_3930_);
lean_ctor_set(v___x_3992_, 1, v_k_3929_);
lean_ctor_set(v___x_3992_, 0, v___x_3987_);
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3987_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v_k_3929_);
lean_ctor_set(v_reuseFailAlloc_3996_, 2, v_v_3930_);
lean_ctor_set(v_reuseFailAlloc_3996_, 3, v___x_3990_);
lean_ctor_set(v_reuseFailAlloc_3996_, 4, v_r_3932_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_4010_; lean_object* v___x_4011_; lean_object* v___x_4013_; 
v_size_4010_ = lean_ctor_get(v_impl_3925_, 0);
v___x_4011_ = lean_nat_add(v___x_3926_, v_size_4010_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 3, v_impl_3925_);
lean_ctor_set(v___x_3921_, 0, v___x_4011_);
v___x_4013_ = v___x_3921_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_4011_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4014_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4014_, 3, v_impl_3925_);
lean_ctor_set(v_reuseFailAlloc_4014_, 4, v_r_3919_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
else
{
if (lean_obj_tag(v_r_3919_) == 0)
{
lean_object* v_l_4015_; 
v_l_4015_ = lean_ctor_get(v_r_3919_, 3);
lean_inc(v_l_4015_);
if (lean_obj_tag(v_l_4015_) == 0)
{
lean_object* v_r_4016_; 
v_r_4016_ = lean_ctor_get(v_r_3919_, 4);
lean_inc(v_r_4016_);
if (lean_obj_tag(v_r_4016_) == 0)
{
lean_object* v_size_4017_; lean_object* v_k_4018_; lean_object* v_v_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4032_; 
v_size_4017_ = lean_ctor_get(v_r_3919_, 0);
v_k_4018_ = lean_ctor_get(v_r_3919_, 1);
v_v_4019_ = lean_ctor_get(v_r_3919_, 2);
v_isSharedCheck_4032_ = !lean_is_exclusive(v_r_3919_);
if (v_isSharedCheck_4032_ == 0)
{
lean_object* v_unused_4033_; lean_object* v_unused_4034_; 
v_unused_4033_ = lean_ctor_get(v_r_3919_, 4);
lean_dec(v_unused_4033_);
v_unused_4034_ = lean_ctor_get(v_r_3919_, 3);
lean_dec(v_unused_4034_);
v___x_4021_ = v_r_3919_;
v_isShared_4022_ = v_isSharedCheck_4032_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_v_4019_);
lean_inc(v_k_4018_);
lean_inc(v_size_4017_);
lean_dec(v_r_3919_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4032_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v_size_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4027_; 
v_size_4023_ = lean_ctor_get(v_l_4015_, 0);
v___x_4024_ = lean_nat_add(v___x_3926_, v_size_4017_);
lean_dec(v_size_4017_);
v___x_4025_ = lean_nat_add(v___x_3926_, v_size_4023_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 4, v_l_4015_);
lean_ctor_set(v___x_4021_, 3, v_impl_3925_);
lean_ctor_set(v___x_4021_, 2, v_v_3917_);
lean_ctor_set(v___x_4021_, 1, v_k_3916_);
lean_ctor_set(v___x_4021_, 0, v___x_4025_);
v___x_4027_ = v___x_4021_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4031_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4031_, 3, v_impl_3925_);
lean_ctor_set(v_reuseFailAlloc_4031_, 4, v_l_4015_);
v___x_4027_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4029_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v_r_4016_);
lean_ctor_set(v___x_3921_, 3, v___x_4027_);
lean_ctor_set(v___x_3921_, 2, v_v_4019_);
lean_ctor_set(v___x_3921_, 1, v_k_4018_);
lean_ctor_set(v___x_3921_, 0, v___x_4024_);
v___x_4029_ = v___x_3921_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v___x_4024_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v_k_4018_);
lean_ctor_set(v_reuseFailAlloc_4030_, 2, v_v_4019_);
lean_ctor_set(v_reuseFailAlloc_4030_, 3, v___x_4027_);
lean_ctor_set(v_reuseFailAlloc_4030_, 4, v_r_4016_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
else
{
lean_object* v_k_4035_; lean_object* v_v_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4059_; 
v_k_4035_ = lean_ctor_get(v_r_3919_, 1);
v_v_4036_ = lean_ctor_get(v_r_3919_, 2);
v_isSharedCheck_4059_ = !lean_is_exclusive(v_r_3919_);
if (v_isSharedCheck_4059_ == 0)
{
lean_object* v_unused_4060_; lean_object* v_unused_4061_; lean_object* v_unused_4062_; 
v_unused_4060_ = lean_ctor_get(v_r_3919_, 4);
lean_dec(v_unused_4060_);
v_unused_4061_ = lean_ctor_get(v_r_3919_, 3);
lean_dec(v_unused_4061_);
v_unused_4062_ = lean_ctor_get(v_r_3919_, 0);
lean_dec(v_unused_4062_);
v___x_4038_ = v_r_3919_;
v_isShared_4039_ = v_isSharedCheck_4059_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_v_4036_);
lean_inc(v_k_4035_);
lean_dec(v_r_3919_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4059_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v_k_4040_; lean_object* v_v_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4055_; 
v_k_4040_ = lean_ctor_get(v_l_4015_, 1);
v_v_4041_ = lean_ctor_get(v_l_4015_, 2);
v_isSharedCheck_4055_ = !lean_is_exclusive(v_l_4015_);
if (v_isSharedCheck_4055_ == 0)
{
lean_object* v_unused_4056_; lean_object* v_unused_4057_; lean_object* v_unused_4058_; 
v_unused_4056_ = lean_ctor_get(v_l_4015_, 4);
lean_dec(v_unused_4056_);
v_unused_4057_ = lean_ctor_get(v_l_4015_, 3);
lean_dec(v_unused_4057_);
v_unused_4058_ = lean_ctor_get(v_l_4015_, 0);
lean_dec(v_unused_4058_);
v___x_4043_ = v_l_4015_;
v_isShared_4044_ = v_isSharedCheck_4055_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_v_4041_);
lean_inc(v_k_4040_);
lean_dec(v_l_4015_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4055_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; lean_object* v___x_4047_; 
v___x_4045_ = lean_unsigned_to_nat(3u);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 4, v_r_4016_);
lean_ctor_set(v___x_4043_, 3, v_r_4016_);
lean_ctor_set(v___x_4043_, 2, v_v_3917_);
lean_ctor_set(v___x_4043_, 1, v_k_3916_);
lean_ctor_set(v___x_4043_, 0, v___x_3926_);
v___x_4047_ = v___x_4043_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4054_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4054_, 3, v_r_4016_);
lean_ctor_set(v_reuseFailAlloc_4054_, 4, v_r_4016_);
v___x_4047_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
lean_object* v___x_4049_; 
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 3, v_r_4016_);
lean_ctor_set(v___x_4038_, 0, v___x_3926_);
v___x_4049_ = v___x_4038_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_k_4035_);
lean_ctor_set(v_reuseFailAlloc_4053_, 2, v_v_4036_);
lean_ctor_set(v_reuseFailAlloc_4053_, 3, v_r_4016_);
lean_ctor_set(v_reuseFailAlloc_4053_, 4, v_r_4016_);
v___x_4049_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
lean_object* v___x_4051_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v___x_4049_);
lean_ctor_set(v___x_3921_, 3, v___x_4047_);
lean_ctor_set(v___x_3921_, 2, v_v_4041_);
lean_ctor_set(v___x_3921_, 1, v_k_4040_);
lean_ctor_set(v___x_3921_, 0, v___x_4045_);
v___x_4051_ = v___x_3921_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4045_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v_k_4040_);
lean_ctor_set(v_reuseFailAlloc_4052_, 2, v_v_4041_);
lean_ctor_set(v_reuseFailAlloc_4052_, 3, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4052_, 4, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_4063_; 
v_r_4063_ = lean_ctor_get(v_r_3919_, 4);
lean_inc(v_r_4063_);
if (lean_obj_tag(v_r_4063_) == 0)
{
lean_object* v_k_4064_; lean_object* v_v_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4076_; 
v_k_4064_ = lean_ctor_get(v_r_3919_, 1);
v_v_4065_ = lean_ctor_get(v_r_3919_, 2);
v_isSharedCheck_4076_ = !lean_is_exclusive(v_r_3919_);
if (v_isSharedCheck_4076_ == 0)
{
lean_object* v_unused_4077_; lean_object* v_unused_4078_; lean_object* v_unused_4079_; 
v_unused_4077_ = lean_ctor_get(v_r_3919_, 4);
lean_dec(v_unused_4077_);
v_unused_4078_ = lean_ctor_get(v_r_3919_, 3);
lean_dec(v_unused_4078_);
v_unused_4079_ = lean_ctor_get(v_r_3919_, 0);
lean_dec(v_unused_4079_);
v___x_4067_ = v_r_3919_;
v_isShared_4068_ = v_isSharedCheck_4076_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_v_4065_);
lean_inc(v_k_4064_);
lean_dec(v_r_3919_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4076_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; lean_object* v___x_4071_; 
v___x_4069_ = lean_unsigned_to_nat(3u);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 4, v_l_4015_);
lean_ctor_set(v___x_4067_, 2, v_v_3917_);
lean_ctor_set(v___x_4067_, 1, v_k_3916_);
lean_ctor_set(v___x_4067_, 0, v___x_3926_);
v___x_4071_ = v___x_4067_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_4075_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4075_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4075_, 3, v_l_4015_);
lean_ctor_set(v_reuseFailAlloc_4075_, 4, v_l_4015_);
v___x_4071_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
lean_object* v___x_4073_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v_r_4063_);
lean_ctor_set(v___x_3921_, 3, v___x_4071_);
lean_ctor_set(v___x_3921_, 2, v_v_4065_);
lean_ctor_set(v___x_3921_, 1, v_k_4064_);
lean_ctor_set(v___x_3921_, 0, v___x_4069_);
v___x_4073_ = v___x_3921_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___x_4069_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_k_4064_);
lean_ctor_set(v_reuseFailAlloc_4074_, 2, v_v_4065_);
lean_ctor_set(v_reuseFailAlloc_4074_, 3, v___x_4071_);
lean_ctor_set(v_reuseFailAlloc_4074_, 4, v_r_4063_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
else
{
lean_object* v_size_4080_; lean_object* v_k_4081_; lean_object* v_v_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4093_; 
v_size_4080_ = lean_ctor_get(v_r_3919_, 0);
v_k_4081_ = lean_ctor_get(v_r_3919_, 1);
v_v_4082_ = lean_ctor_get(v_r_3919_, 2);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_r_3919_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; lean_object* v_unused_4095_; 
v_unused_4094_ = lean_ctor_get(v_r_3919_, 4);
lean_dec(v_unused_4094_);
v_unused_4095_ = lean_ctor_get(v_r_3919_, 3);
lean_dec(v_unused_4095_);
v___x_4084_ = v_r_3919_;
v_isShared_4085_ = v_isSharedCheck_4093_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_v_4082_);
lean_inc(v_k_4081_);
lean_inc(v_size_4080_);
lean_dec(v_r_3919_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4093_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 3, v_r_4063_);
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_size_4080_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v_k_4081_);
lean_ctor_set(v_reuseFailAlloc_4092_, 2, v_v_4082_);
lean_ctor_set(v_reuseFailAlloc_4092_, 3, v_r_4063_);
lean_ctor_set(v_reuseFailAlloc_4092_, 4, v_r_4063_);
v___x_4087_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_object* v___x_4088_; lean_object* v___x_4090_; 
v___x_4088_ = lean_unsigned_to_nat(2u);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v___x_4087_);
lean_ctor_set(v___x_3921_, 3, v_r_4063_);
lean_ctor_set(v___x_3921_, 0, v___x_4088_);
v___x_4090_ = v___x_3921_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4088_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4091_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4091_, 3, v_r_4063_);
lean_ctor_set(v_reuseFailAlloc_4091_, 4, v___x_4087_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
}
}
else
{
lean_object* v___x_4097_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 3, v_r_3919_);
lean_ctor_set(v___x_3921_, 0, v___x_3926_);
v___x_4097_ = v___x_3921_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_4098_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4098_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4098_, 3, v_r_3919_);
lean_ctor_set(v_reuseFailAlloc_4098_, 4, v_r_3919_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3921_);
lean_dec(v_v_3917_);
lean_dec(v_k_3916_);
lean_dec(v_k_3914_);
lean_dec_ref(v_cmp_3913_);
if (lean_obj_tag(v_l_3918_) == 0)
{
if (lean_obj_tag(v_r_3919_) == 0)
{
lean_object* v_size_4099_; lean_object* v_k_4100_; lean_object* v_v_4101_; lean_object* v_l_4102_; lean_object* v_r_4103_; lean_object* v_size_4104_; lean_object* v_k_4105_; lean_object* v_v_4106_; lean_object* v_l_4107_; lean_object* v_r_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; 
v_size_4099_ = lean_ctor_get(v_l_3918_, 0);
v_k_4100_ = lean_ctor_get(v_l_3918_, 1);
v_v_4101_ = lean_ctor_get(v_l_3918_, 2);
v_l_4102_ = lean_ctor_get(v_l_3918_, 3);
v_r_4103_ = lean_ctor_get(v_l_3918_, 4);
lean_inc(v_r_4103_);
v_size_4104_ = lean_ctor_get(v_r_3919_, 0);
v_k_4105_ = lean_ctor_get(v_r_3919_, 1);
v_v_4106_ = lean_ctor_get(v_r_3919_, 2);
v_l_4107_ = lean_ctor_get(v_r_3919_, 3);
lean_inc(v_l_4107_);
v_r_4108_ = lean_ctor_get(v_r_3919_, 4);
v___x_4109_ = lean_unsigned_to_nat(1u);
v___x_4110_ = lean_nat_dec_lt(v_size_4099_, v_size_4104_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4246_; 
lean_inc(v_l_4102_);
lean_inc(v_v_4101_);
lean_inc(v_k_4100_);
v_isSharedCheck_4246_ = !lean_is_exclusive(v_l_3918_);
if (v_isSharedCheck_4246_ == 0)
{
lean_object* v_unused_4247_; lean_object* v_unused_4248_; lean_object* v_unused_4249_; lean_object* v_unused_4250_; lean_object* v_unused_4251_; 
v_unused_4247_ = lean_ctor_get(v_l_3918_, 4);
lean_dec(v_unused_4247_);
v_unused_4248_ = lean_ctor_get(v_l_3918_, 3);
lean_dec(v_unused_4248_);
v_unused_4249_ = lean_ctor_get(v_l_3918_, 2);
lean_dec(v_unused_4249_);
v_unused_4250_ = lean_ctor_get(v_l_3918_, 1);
lean_dec(v_unused_4250_);
v_unused_4251_ = lean_ctor_get(v_l_3918_, 0);
lean_dec(v_unused_4251_);
v___x_4112_ = v_l_3918_;
v_isShared_4113_ = v_isSharedCheck_4246_;
goto v_resetjp_4111_;
}
else
{
lean_dec(v_l_3918_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4246_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4114_; lean_object* v_tree_4115_; 
v___x_4114_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_4100_, v_v_4101_, v_l_4102_, v_r_4103_);
v_tree_4115_ = lean_ctor_get(v___x_4114_, 2);
if (lean_obj_tag(v_tree_4115_) == 0)
{
lean_object* v_k_4116_; lean_object* v_v_4117_; lean_object* v_size_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; uint8_t v___x_4121_; 
lean_inc_ref(v_tree_4115_);
v_k_4116_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_k_4116_);
v_v_4117_ = lean_ctor_get(v___x_4114_, 1);
lean_inc(v_v_4117_);
lean_dec_ref(v___x_4114_);
v_size_4118_ = lean_ctor_get(v_tree_4115_, 0);
v___x_4119_ = lean_unsigned_to_nat(3u);
v___x_4120_ = lean_nat_mul(v___x_4119_, v_size_4118_);
v___x_4121_ = lean_nat_dec_lt(v___x_4120_, v_size_4104_);
lean_dec(v___x_4120_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4125_; 
lean_dec(v_l_4107_);
v___x_4122_ = lean_nat_add(v___x_4109_, v_size_4118_);
v___x_4123_ = lean_nat_add(v___x_4122_, v_size_4104_);
lean_dec(v___x_4122_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v_r_3919_);
lean_ctor_set(v___x_4112_, 3, v_tree_4115_);
lean_ctor_set(v___x_4112_, 2, v_v_4117_);
lean_ctor_set(v___x_4112_, 1, v_k_4116_);
lean_ctor_set(v___x_4112_, 0, v___x_4123_);
v___x_4125_ = v___x_4112_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v_k_4116_);
lean_ctor_set(v_reuseFailAlloc_4126_, 2, v_v_4117_);
lean_ctor_set(v_reuseFailAlloc_4126_, 3, v_tree_4115_);
lean_ctor_set(v_reuseFailAlloc_4126_, 4, v_r_3919_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
else
{
lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4181_; 
lean_inc(v_r_4108_);
lean_inc(v_v_4106_);
lean_inc(v_k_4105_);
lean_inc(v_size_4104_);
v_isSharedCheck_4181_ = !lean_is_exclusive(v_r_3919_);
if (v_isSharedCheck_4181_ == 0)
{
lean_object* v_unused_4182_; lean_object* v_unused_4183_; lean_object* v_unused_4184_; lean_object* v_unused_4185_; lean_object* v_unused_4186_; 
v_unused_4182_ = lean_ctor_get(v_r_3919_, 4);
lean_dec(v_unused_4182_);
v_unused_4183_ = lean_ctor_get(v_r_3919_, 3);
lean_dec(v_unused_4183_);
v_unused_4184_ = lean_ctor_get(v_r_3919_, 2);
lean_dec(v_unused_4184_);
v_unused_4185_ = lean_ctor_get(v_r_3919_, 1);
lean_dec(v_unused_4185_);
v_unused_4186_ = lean_ctor_get(v_r_3919_, 0);
lean_dec(v_unused_4186_);
v___x_4128_ = v_r_3919_;
v_isShared_4129_ = v_isSharedCheck_4181_;
goto v_resetjp_4127_;
}
else
{
lean_dec(v_r_3919_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4181_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v_size_4130_; lean_object* v_k_4131_; lean_object* v_v_4132_; lean_object* v_l_4133_; lean_object* v_r_4134_; lean_object* v_size_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; uint8_t v___x_4138_; 
v_size_4130_ = lean_ctor_get(v_l_4107_, 0);
v_k_4131_ = lean_ctor_get(v_l_4107_, 1);
v_v_4132_ = lean_ctor_get(v_l_4107_, 2);
v_l_4133_ = lean_ctor_get(v_l_4107_, 3);
v_r_4134_ = lean_ctor_get(v_l_4107_, 4);
v_size_4135_ = lean_ctor_get(v_r_4108_, 0);
v___x_4136_ = lean_unsigned_to_nat(2u);
v___x_4137_ = lean_nat_mul(v___x_4136_, v_size_4135_);
v___x_4138_ = lean_nat_dec_lt(v_size_4130_, v___x_4137_);
lean_dec(v___x_4137_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4166_; 
lean_inc(v_r_4134_);
lean_inc(v_l_4133_);
lean_inc(v_v_4132_);
lean_inc(v_k_4131_);
v_isSharedCheck_4166_ = !lean_is_exclusive(v_l_4107_);
if (v_isSharedCheck_4166_ == 0)
{
lean_object* v_unused_4167_; lean_object* v_unused_4168_; lean_object* v_unused_4169_; lean_object* v_unused_4170_; lean_object* v_unused_4171_; 
v_unused_4167_ = lean_ctor_get(v_l_4107_, 4);
lean_dec(v_unused_4167_);
v_unused_4168_ = lean_ctor_get(v_l_4107_, 3);
lean_dec(v_unused_4168_);
v_unused_4169_ = lean_ctor_get(v_l_4107_, 2);
lean_dec(v_unused_4169_);
v_unused_4170_ = lean_ctor_get(v_l_4107_, 1);
lean_dec(v_unused_4170_);
v_unused_4171_ = lean_ctor_get(v_l_4107_, 0);
lean_dec(v_unused_4171_);
v___x_4140_ = v_l_4107_;
v_isShared_4141_ = v_isSharedCheck_4166_;
goto v_resetjp_4139_;
}
else
{
lean_dec(v_l_4107_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4166_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4156_; 
v___x_4142_ = lean_nat_add(v___x_4109_, v_size_4118_);
v___x_4143_ = lean_nat_add(v___x_4142_, v_size_4104_);
lean_dec(v_size_4104_);
if (lean_obj_tag(v_l_4133_) == 0)
{
lean_object* v_size_4164_; 
v_size_4164_ = lean_ctor_get(v_l_4133_, 0);
lean_inc(v_size_4164_);
v___y_4156_ = v_size_4164_;
goto v___jp_4155_;
}
else
{
lean_object* v___x_4165_; 
v___x_4165_ = lean_unsigned_to_nat(0u);
v___y_4156_ = v___x_4165_;
goto v___jp_4155_;
}
v___jp_4144_:
{
lean_object* v___x_4148_; lean_object* v___x_4150_; 
v___x_4148_ = lean_nat_add(v___y_4145_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec(v___y_4145_);
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 4, v_r_4108_);
lean_ctor_set(v___x_4140_, 3, v_r_4134_);
lean_ctor_set(v___x_4140_, 2, v_v_4106_);
lean_ctor_set(v___x_4140_, 1, v_k_4105_);
lean_ctor_set(v___x_4140_, 0, v___x_4148_);
v___x_4150_ = v___x_4140_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4148_);
lean_ctor_set(v_reuseFailAlloc_4154_, 1, v_k_4105_);
lean_ctor_set(v_reuseFailAlloc_4154_, 2, v_v_4106_);
lean_ctor_set(v_reuseFailAlloc_4154_, 3, v_r_4134_);
lean_ctor_set(v_reuseFailAlloc_4154_, 4, v_r_4108_);
v___x_4150_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
lean_object* v___x_4152_; 
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 4, v___x_4150_);
lean_ctor_set(v___x_4128_, 3, v___y_4146_);
lean_ctor_set(v___x_4128_, 2, v_v_4132_);
lean_ctor_set(v___x_4128_, 1, v_k_4131_);
lean_ctor_set(v___x_4128_, 0, v___x_4143_);
v___x_4152_ = v___x_4128_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4143_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_k_4131_);
lean_ctor_set(v_reuseFailAlloc_4153_, 2, v_v_4132_);
lean_ctor_set(v_reuseFailAlloc_4153_, 3, v___y_4146_);
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
v___jp_4155_:
{
lean_object* v___x_4157_; lean_object* v___x_4159_; 
v___x_4157_ = lean_nat_add(v___x_4142_, v___y_4156_);
lean_dec(v___y_4156_);
lean_dec(v___x_4142_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v_l_4133_);
lean_ctor_set(v___x_4112_, 3, v_tree_4115_);
lean_ctor_set(v___x_4112_, 2, v_v_4117_);
lean_ctor_set(v___x_4112_, 1, v_k_4116_);
lean_ctor_set(v___x_4112_, 0, v___x_4157_);
v___x_4159_ = v___x_4112_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4157_);
lean_ctor_set(v_reuseFailAlloc_4163_, 1, v_k_4116_);
lean_ctor_set(v_reuseFailAlloc_4163_, 2, v_v_4117_);
lean_ctor_set(v_reuseFailAlloc_4163_, 3, v_tree_4115_);
lean_ctor_set(v_reuseFailAlloc_4163_, 4, v_l_4133_);
v___x_4159_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
lean_object* v___x_4160_; 
v___x_4160_ = lean_nat_add(v___x_4109_, v_size_4135_);
if (lean_obj_tag(v_r_4134_) == 0)
{
lean_object* v_size_4161_; 
v_size_4161_ = lean_ctor_get(v_r_4134_, 0);
lean_inc(v_size_4161_);
v___y_4145_ = v___x_4160_;
v___y_4146_ = v___x_4159_;
v___y_4147_ = v_size_4161_;
goto v___jp_4144_;
}
else
{
lean_object* v___x_4162_; 
v___x_4162_ = lean_unsigned_to_nat(0u);
v___y_4145_ = v___x_4160_;
v___y_4146_ = v___x_4159_;
v___y_4147_ = v___x_4162_;
goto v___jp_4144_;
}
}
}
}
}
else
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4176_; 
v___x_4172_ = lean_nat_add(v___x_4109_, v_size_4118_);
v___x_4173_ = lean_nat_add(v___x_4172_, v_size_4104_);
lean_dec(v_size_4104_);
v___x_4174_ = lean_nat_add(v___x_4172_, v_size_4130_);
lean_dec(v___x_4172_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 4, v_l_4107_);
lean_ctor_set(v___x_4128_, 3, v_tree_4115_);
lean_ctor_set(v___x_4128_, 2, v_v_4117_);
lean_ctor_set(v___x_4128_, 1, v_k_4116_);
lean_ctor_set(v___x_4128_, 0, v___x_4174_);
v___x_4176_ = v___x_4128_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4174_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v_k_4116_);
lean_ctor_set(v_reuseFailAlloc_4180_, 2, v_v_4117_);
lean_ctor_set(v_reuseFailAlloc_4180_, 3, v_tree_4115_);
lean_ctor_set(v_reuseFailAlloc_4180_, 4, v_l_4107_);
v___x_4176_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
lean_object* v___x_4178_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v_r_4108_);
lean_ctor_set(v___x_4112_, 3, v___x_4176_);
lean_ctor_set(v___x_4112_, 2, v_v_4106_);
lean_ctor_set(v___x_4112_, 1, v_k_4105_);
lean_ctor_set(v___x_4112_, 0, v___x_4173_);
v___x_4178_ = v___x_4112_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4173_);
lean_ctor_set(v_reuseFailAlloc_4179_, 1, v_k_4105_);
lean_ctor_set(v_reuseFailAlloc_4179_, 2, v_v_4106_);
lean_ctor_set(v_reuseFailAlloc_4179_, 3, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4179_, 4, v_r_4108_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
}
}
else
{
lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4240_; 
lean_inc(v_r_4108_);
lean_inc(v_v_4106_);
lean_inc(v_k_4105_);
lean_inc(v_size_4104_);
v_isSharedCheck_4240_ = !lean_is_exclusive(v_r_3919_);
if (v_isSharedCheck_4240_ == 0)
{
lean_object* v_unused_4241_; lean_object* v_unused_4242_; lean_object* v_unused_4243_; lean_object* v_unused_4244_; lean_object* v_unused_4245_; 
v_unused_4241_ = lean_ctor_get(v_r_3919_, 4);
lean_dec(v_unused_4241_);
v_unused_4242_ = lean_ctor_get(v_r_3919_, 3);
lean_dec(v_unused_4242_);
v_unused_4243_ = lean_ctor_get(v_r_3919_, 2);
lean_dec(v_unused_4243_);
v_unused_4244_ = lean_ctor_get(v_r_3919_, 1);
lean_dec(v_unused_4244_);
v_unused_4245_ = lean_ctor_get(v_r_3919_, 0);
lean_dec(v_unused_4245_);
v___x_4188_ = v_r_3919_;
v_isShared_4189_ = v_isSharedCheck_4240_;
goto v_resetjp_4187_;
}
else
{
lean_dec(v_r_3919_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4240_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
if (lean_obj_tag(v_l_4107_) == 0)
{
if (lean_obj_tag(v_r_4108_) == 0)
{
lean_object* v_k_4190_; lean_object* v_v_4191_; lean_object* v_size_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4196_; 
lean_inc(v_tree_4115_);
v_k_4190_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_k_4190_);
v_v_4191_ = lean_ctor_get(v___x_4114_, 1);
lean_inc(v_v_4191_);
lean_dec_ref(v___x_4114_);
v_size_4192_ = lean_ctor_get(v_l_4107_, 0);
v___x_4193_ = lean_nat_add(v___x_4109_, v_size_4104_);
lean_dec(v_size_4104_);
v___x_4194_ = lean_nat_add(v___x_4109_, v_size_4192_);
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 4, v_l_4107_);
lean_ctor_set(v___x_4188_, 3, v_tree_4115_);
lean_ctor_set(v___x_4188_, 2, v_v_4191_);
lean_ctor_set(v___x_4188_, 1, v_k_4190_);
lean_ctor_set(v___x_4188_, 0, v___x_4194_);
v___x_4196_ = v___x_4188_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4194_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v_k_4190_);
lean_ctor_set(v_reuseFailAlloc_4200_, 2, v_v_4191_);
lean_ctor_set(v_reuseFailAlloc_4200_, 3, v_tree_4115_);
lean_ctor_set(v_reuseFailAlloc_4200_, 4, v_l_4107_);
v___x_4196_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
lean_object* v___x_4198_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v_r_4108_);
lean_ctor_set(v___x_4112_, 3, v___x_4196_);
lean_ctor_set(v___x_4112_, 2, v_v_4106_);
lean_ctor_set(v___x_4112_, 1, v_k_4105_);
lean_ctor_set(v___x_4112_, 0, v___x_4193_);
v___x_4198_ = v___x_4112_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4193_);
lean_ctor_set(v_reuseFailAlloc_4199_, 1, v_k_4105_);
lean_ctor_set(v_reuseFailAlloc_4199_, 2, v_v_4106_);
lean_ctor_set(v_reuseFailAlloc_4199_, 3, v___x_4196_);
lean_ctor_set(v_reuseFailAlloc_4199_, 4, v_r_4108_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
else
{
lean_object* v_k_4201_; lean_object* v_v_4202_; lean_object* v_k_4203_; lean_object* v_v_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4218_; 
lean_dec(v_size_4104_);
v_k_4201_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_k_4201_);
v_v_4202_ = lean_ctor_get(v___x_4114_, 1);
lean_inc(v_v_4202_);
lean_dec_ref(v___x_4114_);
v_k_4203_ = lean_ctor_get(v_l_4107_, 1);
v_v_4204_ = lean_ctor_get(v_l_4107_, 2);
v_isSharedCheck_4218_ = !lean_is_exclusive(v_l_4107_);
if (v_isSharedCheck_4218_ == 0)
{
lean_object* v_unused_4219_; lean_object* v_unused_4220_; lean_object* v_unused_4221_; 
v_unused_4219_ = lean_ctor_get(v_l_4107_, 4);
lean_dec(v_unused_4219_);
v_unused_4220_ = lean_ctor_get(v_l_4107_, 3);
lean_dec(v_unused_4220_);
v_unused_4221_ = lean_ctor_get(v_l_4107_, 0);
lean_dec(v_unused_4221_);
v___x_4206_ = v_l_4107_;
v_isShared_4207_ = v_isSharedCheck_4218_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_v_4204_);
lean_inc(v_k_4203_);
lean_dec(v_l_4107_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4218_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4208_; lean_object* v___x_4210_; 
v___x_4208_ = lean_unsigned_to_nat(3u);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 4, v_r_4108_);
lean_ctor_set(v___x_4206_, 3, v_r_4108_);
lean_ctor_set(v___x_4206_, 2, v_v_4202_);
lean_ctor_set(v___x_4206_, 1, v_k_4201_);
lean_ctor_set(v___x_4206_, 0, v___x_4109_);
v___x_4210_ = v___x_4206_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_k_4201_);
lean_ctor_set(v_reuseFailAlloc_4217_, 2, v_v_4202_);
lean_ctor_set(v_reuseFailAlloc_4217_, 3, v_r_4108_);
lean_ctor_set(v_reuseFailAlloc_4217_, 4, v_r_4108_);
v___x_4210_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
lean_object* v___x_4212_; 
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 3, v_r_4108_);
lean_ctor_set(v___x_4188_, 0, v___x_4109_);
v___x_4212_ = v___x_4188_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v_k_4105_);
lean_ctor_set(v_reuseFailAlloc_4216_, 2, v_v_4106_);
lean_ctor_set(v_reuseFailAlloc_4216_, 3, v_r_4108_);
lean_ctor_set(v_reuseFailAlloc_4216_, 4, v_r_4108_);
v___x_4212_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
lean_object* v___x_4214_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v___x_4212_);
lean_ctor_set(v___x_4112_, 3, v___x_4210_);
lean_ctor_set(v___x_4112_, 2, v_v_4204_);
lean_ctor_set(v___x_4112_, 1, v_k_4203_);
lean_ctor_set(v___x_4112_, 0, v___x_4208_);
v___x_4214_ = v___x_4112_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v___x_4208_);
lean_ctor_set(v_reuseFailAlloc_4215_, 1, v_k_4203_);
lean_ctor_set(v_reuseFailAlloc_4215_, 2, v_v_4204_);
lean_ctor_set(v_reuseFailAlloc_4215_, 3, v___x_4210_);
lean_ctor_set(v_reuseFailAlloc_4215_, 4, v___x_4212_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4108_) == 0)
{
lean_object* v_k_4222_; lean_object* v_v_4223_; lean_object* v___x_4224_; lean_object* v___x_4226_; 
lean_dec(v_size_4104_);
v_k_4222_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_k_4222_);
v_v_4223_ = lean_ctor_get(v___x_4114_, 1);
lean_inc(v_v_4223_);
lean_dec_ref(v___x_4114_);
v___x_4224_ = lean_unsigned_to_nat(3u);
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 4, v_l_4107_);
lean_ctor_set(v___x_4188_, 2, v_v_4223_);
lean_ctor_set(v___x_4188_, 1, v_k_4222_);
lean_ctor_set(v___x_4188_, 0, v___x_4109_);
v___x_4226_ = v___x_4188_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v_k_4222_);
lean_ctor_set(v_reuseFailAlloc_4230_, 2, v_v_4223_);
lean_ctor_set(v_reuseFailAlloc_4230_, 3, v_l_4107_);
lean_ctor_set(v_reuseFailAlloc_4230_, 4, v_l_4107_);
v___x_4226_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
lean_object* v___x_4228_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v_r_4108_);
lean_ctor_set(v___x_4112_, 3, v___x_4226_);
lean_ctor_set(v___x_4112_, 2, v_v_4106_);
lean_ctor_set(v___x_4112_, 1, v_k_4105_);
lean_ctor_set(v___x_4112_, 0, v___x_4224_);
v___x_4228_ = v___x_4112_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4224_);
lean_ctor_set(v_reuseFailAlloc_4229_, 1, v_k_4105_);
lean_ctor_set(v_reuseFailAlloc_4229_, 2, v_v_4106_);
lean_ctor_set(v_reuseFailAlloc_4229_, 3, v___x_4226_);
lean_ctor_set(v_reuseFailAlloc_4229_, 4, v_r_4108_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
else
{
lean_object* v_k_4231_; lean_object* v_v_4232_; lean_object* v___x_4234_; 
v_k_4231_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_k_4231_);
v_v_4232_ = lean_ctor_get(v___x_4114_, 1);
lean_inc(v_v_4232_);
lean_dec_ref(v___x_4114_);
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 3, v_r_4108_);
v___x_4234_ = v___x_4188_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_size_4104_);
lean_ctor_set(v_reuseFailAlloc_4239_, 1, v_k_4105_);
lean_ctor_set(v_reuseFailAlloc_4239_, 2, v_v_4106_);
lean_ctor_set(v_reuseFailAlloc_4239_, 3, v_r_4108_);
lean_ctor_set(v_reuseFailAlloc_4239_, 4, v_r_4108_);
v___x_4234_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
lean_object* v___x_4235_; lean_object* v___x_4237_; 
v___x_4235_ = lean_unsigned_to_nat(2u);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v___x_4234_);
lean_ctor_set(v___x_4112_, 3, v_r_4108_);
lean_ctor_set(v___x_4112_, 2, v_v_4232_);
lean_ctor_set(v___x_4112_, 1, v_k_4231_);
lean_ctor_set(v___x_4112_, 0, v___x_4235_);
v___x_4237_ = v___x_4112_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4235_);
lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_k_4231_);
lean_ctor_set(v_reuseFailAlloc_4238_, 2, v_v_4232_);
lean_ctor_set(v_reuseFailAlloc_4238_, 3, v_r_4108_);
lean_ctor_set(v_reuseFailAlloc_4238_, 4, v___x_4234_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
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
lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4404_; 
lean_inc(v_r_4108_);
lean_inc(v_v_4106_);
lean_inc(v_k_4105_);
v_isSharedCheck_4404_ = !lean_is_exclusive(v_r_3919_);
if (v_isSharedCheck_4404_ == 0)
{
lean_object* v_unused_4405_; lean_object* v_unused_4406_; lean_object* v_unused_4407_; lean_object* v_unused_4408_; lean_object* v_unused_4409_; 
v_unused_4405_ = lean_ctor_get(v_r_3919_, 4);
lean_dec(v_unused_4405_);
v_unused_4406_ = lean_ctor_get(v_r_3919_, 3);
lean_dec(v_unused_4406_);
v_unused_4407_ = lean_ctor_get(v_r_3919_, 2);
lean_dec(v_unused_4407_);
v_unused_4408_ = lean_ctor_get(v_r_3919_, 1);
lean_dec(v_unused_4408_);
v_unused_4409_ = lean_ctor_get(v_r_3919_, 0);
lean_dec(v_unused_4409_);
v___x_4253_ = v_r_3919_;
v_isShared_4254_ = v_isSharedCheck_4404_;
goto v_resetjp_4252_;
}
else
{
lean_dec(v_r_3919_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4404_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4255_; lean_object* v_tree_4256_; 
v___x_4255_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_4105_, v_v_4106_, v_l_4107_, v_r_4108_);
v_tree_4256_ = lean_ctor_get(v___x_4255_, 2);
lean_inc(v_tree_4256_);
if (lean_obj_tag(v_tree_4256_) == 0)
{
lean_object* v_k_4257_; lean_object* v_v_4258_; lean_object* v_size_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; 
v_k_4257_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_k_4257_);
v_v_4258_ = lean_ctor_get(v___x_4255_, 1);
lean_inc(v_v_4258_);
lean_dec_ref(v___x_4255_);
v_size_4259_ = lean_ctor_get(v_tree_4256_, 0);
v___x_4260_ = lean_unsigned_to_nat(3u);
v___x_4261_ = lean_nat_mul(v___x_4260_, v_size_4259_);
v___x_4262_ = lean_nat_dec_lt(v___x_4261_, v_size_4099_);
lean_dec(v___x_4261_);
if (v___x_4262_ == 0)
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4266_; 
lean_dec(v_r_4103_);
v___x_4263_ = lean_nat_add(v___x_4109_, v_size_4099_);
v___x_4264_ = lean_nat_add(v___x_4263_, v_size_4259_);
lean_dec(v___x_4263_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 4, v_tree_4256_);
lean_ctor_set(v___x_4253_, 3, v_l_3918_);
lean_ctor_set(v___x_4253_, 2, v_v_4258_);
lean_ctor_set(v___x_4253_, 1, v_k_4257_);
lean_ctor_set(v___x_4253_, 0, v___x_4264_);
v___x_4266_ = v___x_4253_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4264_);
lean_ctor_set(v_reuseFailAlloc_4267_, 1, v_k_4257_);
lean_ctor_set(v_reuseFailAlloc_4267_, 2, v_v_4258_);
lean_ctor_set(v_reuseFailAlloc_4267_, 3, v_l_3918_);
lean_ctor_set(v_reuseFailAlloc_4267_, 4, v_tree_4256_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
else
{
lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4333_; 
lean_inc(v_l_4102_);
lean_inc(v_v_4101_);
lean_inc(v_k_4100_);
lean_inc(v_size_4099_);
v_isSharedCheck_4333_ = !lean_is_exclusive(v_l_3918_);
if (v_isSharedCheck_4333_ == 0)
{
lean_object* v_unused_4334_; lean_object* v_unused_4335_; lean_object* v_unused_4336_; lean_object* v_unused_4337_; lean_object* v_unused_4338_; 
v_unused_4334_ = lean_ctor_get(v_l_3918_, 4);
lean_dec(v_unused_4334_);
v_unused_4335_ = lean_ctor_get(v_l_3918_, 3);
lean_dec(v_unused_4335_);
v_unused_4336_ = lean_ctor_get(v_l_3918_, 2);
lean_dec(v_unused_4336_);
v_unused_4337_ = lean_ctor_get(v_l_3918_, 1);
lean_dec(v_unused_4337_);
v_unused_4338_ = lean_ctor_get(v_l_3918_, 0);
lean_dec(v_unused_4338_);
v___x_4269_ = v_l_3918_;
v_isShared_4270_ = v_isSharedCheck_4333_;
goto v_resetjp_4268_;
}
else
{
lean_dec(v_l_3918_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4333_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v_size_4271_; lean_object* v_size_4272_; lean_object* v_k_4273_; lean_object* v_v_4274_; lean_object* v_l_4275_; lean_object* v_r_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; uint8_t v___x_4279_; 
v_size_4271_ = lean_ctor_get(v_l_4102_, 0);
v_size_4272_ = lean_ctor_get(v_r_4103_, 0);
v_k_4273_ = lean_ctor_get(v_r_4103_, 1);
v_v_4274_ = lean_ctor_get(v_r_4103_, 2);
v_l_4275_ = lean_ctor_get(v_r_4103_, 3);
v_r_4276_ = lean_ctor_get(v_r_4103_, 4);
v___x_4277_ = lean_unsigned_to_nat(2u);
v___x_4278_ = lean_nat_mul(v___x_4277_, v_size_4271_);
v___x_4279_ = lean_nat_dec_lt(v_size_4272_, v___x_4278_);
lean_dec(v___x_4278_);
if (v___x_4279_ == 0)
{
lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4317_; 
lean_inc(v_r_4276_);
lean_inc(v_l_4275_);
lean_inc(v_v_4274_);
lean_inc(v_k_4273_);
lean_del_object(v___x_4269_);
v_isSharedCheck_4317_ = !lean_is_exclusive(v_r_4103_);
if (v_isSharedCheck_4317_ == 0)
{
lean_object* v_unused_4318_; lean_object* v_unused_4319_; lean_object* v_unused_4320_; lean_object* v_unused_4321_; lean_object* v_unused_4322_; 
v_unused_4318_ = lean_ctor_get(v_r_4103_, 4);
lean_dec(v_unused_4318_);
v_unused_4319_ = lean_ctor_get(v_r_4103_, 3);
lean_dec(v_unused_4319_);
v_unused_4320_ = lean_ctor_get(v_r_4103_, 2);
lean_dec(v_unused_4320_);
v_unused_4321_ = lean_ctor_get(v_r_4103_, 1);
lean_dec(v_unused_4321_);
v_unused_4322_ = lean_ctor_get(v_r_4103_, 0);
lean_dec(v_unused_4322_);
v___x_4281_ = v_r_4103_;
v_isShared_4282_ = v_isSharedCheck_4317_;
goto v_resetjp_4280_;
}
else
{
lean_dec(v_r_4103_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4317_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___x_4305_; lean_object* v___y_4307_; 
v___x_4283_ = lean_nat_add(v___x_4109_, v_size_4099_);
lean_dec(v_size_4099_);
v___x_4284_ = lean_nat_add(v___x_4283_, v_size_4259_);
lean_dec(v___x_4283_);
v___x_4305_ = lean_nat_add(v___x_4109_, v_size_4271_);
if (lean_obj_tag(v_l_4275_) == 0)
{
lean_object* v_size_4315_; 
v_size_4315_ = lean_ctor_get(v_l_4275_, 0);
lean_inc(v_size_4315_);
v___y_4307_ = v_size_4315_;
goto v___jp_4306_;
}
else
{
lean_object* v___x_4316_; 
v___x_4316_ = lean_unsigned_to_nat(0u);
v___y_4307_ = v___x_4316_;
goto v___jp_4306_;
}
v___jp_4285_:
{
lean_object* v___x_4289_; lean_object* v___x_4291_; 
v___x_4289_ = lean_nat_add(v___y_4286_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec(v___y_4286_);
lean_inc_ref(v_tree_4256_);
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 4, v_tree_4256_);
lean_ctor_set(v___x_4281_, 3, v_r_4276_);
lean_ctor_set(v___x_4281_, 2, v_v_4258_);
lean_ctor_set(v___x_4281_, 1, v_k_4257_);
lean_ctor_set(v___x_4281_, 0, v___x_4289_);
v___x_4291_ = v___x_4281_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v___x_4289_);
lean_ctor_set(v_reuseFailAlloc_4304_, 1, v_k_4257_);
lean_ctor_set(v_reuseFailAlloc_4304_, 2, v_v_4258_);
lean_ctor_set(v_reuseFailAlloc_4304_, 3, v_r_4276_);
lean_ctor_set(v_reuseFailAlloc_4304_, 4, v_tree_4256_);
v___x_4291_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
v_isSharedCheck_4298_ = !lean_is_exclusive(v_tree_4256_);
if (v_isSharedCheck_4298_ == 0)
{
lean_object* v_unused_4299_; lean_object* v_unused_4300_; lean_object* v_unused_4301_; lean_object* v_unused_4302_; lean_object* v_unused_4303_; 
v_unused_4299_ = lean_ctor_get(v_tree_4256_, 4);
lean_dec(v_unused_4299_);
v_unused_4300_ = lean_ctor_get(v_tree_4256_, 3);
lean_dec(v_unused_4300_);
v_unused_4301_ = lean_ctor_get(v_tree_4256_, 2);
lean_dec(v_unused_4301_);
v_unused_4302_ = lean_ctor_get(v_tree_4256_, 1);
lean_dec(v_unused_4302_);
v_unused_4303_ = lean_ctor_get(v_tree_4256_, 0);
lean_dec(v_unused_4303_);
v___x_4293_ = v_tree_4256_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_dec(v_tree_4256_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
lean_ctor_set(v___x_4293_, 4, v___x_4291_);
lean_ctor_set(v___x_4293_, 3, v___y_4287_);
lean_ctor_set(v___x_4293_, 2, v_v_4274_);
lean_ctor_set(v___x_4293_, 1, v_k_4273_);
lean_ctor_set(v___x_4293_, 0, v___x_4284_);
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v___x_4284_);
lean_ctor_set(v_reuseFailAlloc_4297_, 1, v_k_4273_);
lean_ctor_set(v_reuseFailAlloc_4297_, 2, v_v_4274_);
lean_ctor_set(v_reuseFailAlloc_4297_, 3, v___y_4287_);
lean_ctor_set(v_reuseFailAlloc_4297_, 4, v___x_4291_);
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
v___jp_4306_:
{
lean_object* v___x_4308_; lean_object* v___x_4310_; 
v___x_4308_ = lean_nat_add(v___x_4305_, v___y_4307_);
lean_dec(v___y_4307_);
lean_dec(v___x_4305_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 4, v_l_4275_);
lean_ctor_set(v___x_4253_, 3, v_l_4102_);
lean_ctor_set(v___x_4253_, 2, v_v_4101_);
lean_ctor_set(v___x_4253_, 1, v_k_4100_);
lean_ctor_set(v___x_4253_, 0, v___x_4308_);
v___x_4310_ = v___x_4253_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v___x_4308_);
lean_ctor_set(v_reuseFailAlloc_4314_, 1, v_k_4100_);
lean_ctor_set(v_reuseFailAlloc_4314_, 2, v_v_4101_);
lean_ctor_set(v_reuseFailAlloc_4314_, 3, v_l_4102_);
lean_ctor_set(v_reuseFailAlloc_4314_, 4, v_l_4275_);
v___x_4310_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
lean_object* v___x_4311_; 
v___x_4311_ = lean_nat_add(v___x_4109_, v_size_4259_);
if (lean_obj_tag(v_r_4276_) == 0)
{
lean_object* v_size_4312_; 
v_size_4312_ = lean_ctor_get(v_r_4276_, 0);
lean_inc(v_size_4312_);
v___y_4286_ = v___x_4311_;
v___y_4287_ = v___x_4310_;
v___y_4288_ = v_size_4312_;
goto v___jp_4285_;
}
else
{
lean_object* v___x_4313_; 
v___x_4313_ = lean_unsigned_to_nat(0u);
v___y_4286_ = v___x_4311_;
v___y_4287_ = v___x_4310_;
v___y_4288_ = v___x_4313_;
goto v___jp_4285_;
}
}
}
}
}
else
{
lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4328_; 
v___x_4323_ = lean_nat_add(v___x_4109_, v_size_4099_);
lean_dec(v_size_4099_);
v___x_4324_ = lean_nat_add(v___x_4323_, v_size_4259_);
lean_dec(v___x_4323_);
v___x_4325_ = lean_nat_add(v___x_4109_, v_size_4259_);
v___x_4326_ = lean_nat_add(v___x_4325_, v_size_4272_);
lean_dec(v___x_4325_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 4, v_tree_4256_);
lean_ctor_set(v___x_4253_, 3, v_r_4103_);
lean_ctor_set(v___x_4253_, 2, v_v_4258_);
lean_ctor_set(v___x_4253_, 1, v_k_4257_);
lean_ctor_set(v___x_4253_, 0, v___x_4326_);
v___x_4328_ = v___x_4253_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4326_);
lean_ctor_set(v_reuseFailAlloc_4332_, 1, v_k_4257_);
lean_ctor_set(v_reuseFailAlloc_4332_, 2, v_v_4258_);
lean_ctor_set(v_reuseFailAlloc_4332_, 3, v_r_4103_);
lean_ctor_set(v_reuseFailAlloc_4332_, 4, v_tree_4256_);
v___x_4328_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
lean_object* v___x_4330_; 
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 4, v___x_4328_);
lean_ctor_set(v___x_4269_, 0, v___x_4324_);
v___x_4330_ = v___x_4269_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4324_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v_k_4100_);
lean_ctor_set(v_reuseFailAlloc_4331_, 2, v_v_4101_);
lean_ctor_set(v_reuseFailAlloc_4331_, 3, v_l_4102_);
lean_ctor_set(v_reuseFailAlloc_4331_, 4, v___x_4328_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_4102_) == 0)
{
lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4362_; 
lean_inc_ref(v_l_4102_);
lean_inc(v_v_4101_);
lean_inc(v_k_4100_);
lean_inc(v_size_4099_);
v_isSharedCheck_4362_ = !lean_is_exclusive(v_l_3918_);
if (v_isSharedCheck_4362_ == 0)
{
lean_object* v_unused_4363_; lean_object* v_unused_4364_; lean_object* v_unused_4365_; lean_object* v_unused_4366_; lean_object* v_unused_4367_; 
v_unused_4363_ = lean_ctor_get(v_l_3918_, 4);
lean_dec(v_unused_4363_);
v_unused_4364_ = lean_ctor_get(v_l_3918_, 3);
lean_dec(v_unused_4364_);
v_unused_4365_ = lean_ctor_get(v_l_3918_, 2);
lean_dec(v_unused_4365_);
v_unused_4366_ = lean_ctor_get(v_l_3918_, 1);
lean_dec(v_unused_4366_);
v_unused_4367_ = lean_ctor_get(v_l_3918_, 0);
lean_dec(v_unused_4367_);
v___x_4340_ = v_l_3918_;
v_isShared_4341_ = v_isSharedCheck_4362_;
goto v_resetjp_4339_;
}
else
{
lean_dec(v_l_3918_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4362_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
if (lean_obj_tag(v_r_4103_) == 0)
{
lean_object* v_k_4342_; lean_object* v_v_4343_; lean_object* v_size_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4348_; 
v_k_4342_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_k_4342_);
v_v_4343_ = lean_ctor_get(v___x_4255_, 1);
lean_inc(v_v_4343_);
lean_dec_ref(v___x_4255_);
v_size_4344_ = lean_ctor_get(v_r_4103_, 0);
v___x_4345_ = lean_nat_add(v___x_4109_, v_size_4099_);
lean_dec(v_size_4099_);
v___x_4346_ = lean_nat_add(v___x_4109_, v_size_4344_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 4, v_tree_4256_);
lean_ctor_set(v___x_4253_, 3, v_r_4103_);
lean_ctor_set(v___x_4253_, 2, v_v_4343_);
lean_ctor_set(v___x_4253_, 1, v_k_4342_);
lean_ctor_set(v___x_4253_, 0, v___x_4346_);
v___x_4348_ = v___x_4253_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4346_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v_k_4342_);
lean_ctor_set(v_reuseFailAlloc_4352_, 2, v_v_4343_);
lean_ctor_set(v_reuseFailAlloc_4352_, 3, v_r_4103_);
lean_ctor_set(v_reuseFailAlloc_4352_, 4, v_tree_4256_);
v___x_4348_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
lean_object* v___x_4350_; 
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 4, v___x_4348_);
lean_ctor_set(v___x_4340_, 0, v___x_4345_);
v___x_4350_ = v___x_4340_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4345_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v_k_4100_);
lean_ctor_set(v_reuseFailAlloc_4351_, 2, v_v_4101_);
lean_ctor_set(v_reuseFailAlloc_4351_, 3, v_l_4102_);
lean_ctor_set(v_reuseFailAlloc_4351_, 4, v___x_4348_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
else
{
lean_object* v_k_4353_; lean_object* v_v_4354_; lean_object* v___x_4355_; lean_object* v___x_4357_; 
lean_dec(v_size_4099_);
v_k_4353_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_k_4353_);
v_v_4354_ = lean_ctor_get(v___x_4255_, 1);
lean_inc(v_v_4354_);
lean_dec_ref(v___x_4255_);
v___x_4355_ = lean_unsigned_to_nat(3u);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 4, v_r_4103_);
lean_ctor_set(v___x_4253_, 3, v_r_4103_);
lean_ctor_set(v___x_4253_, 2, v_v_4354_);
lean_ctor_set(v___x_4253_, 1, v_k_4353_);
lean_ctor_set(v___x_4253_, 0, v___x_4109_);
v___x_4357_ = v___x_4253_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4361_, 1, v_k_4353_);
lean_ctor_set(v_reuseFailAlloc_4361_, 2, v_v_4354_);
lean_ctor_set(v_reuseFailAlloc_4361_, 3, v_r_4103_);
lean_ctor_set(v_reuseFailAlloc_4361_, 4, v_r_4103_);
v___x_4357_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
lean_object* v___x_4359_; 
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 4, v___x_4357_);
lean_ctor_set(v___x_4340_, 0, v___x_4355_);
v___x_4359_ = v___x_4340_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4360_, 1, v_k_4100_);
lean_ctor_set(v_reuseFailAlloc_4360_, 2, v_v_4101_);
lean_ctor_set(v_reuseFailAlloc_4360_, 3, v_l_4102_);
lean_ctor_set(v_reuseFailAlloc_4360_, 4, v___x_4357_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4103_) == 0)
{
lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4392_; 
lean_inc(v_l_4102_);
lean_inc(v_v_4101_);
lean_inc(v_k_4100_);
v_isSharedCheck_4392_ = !lean_is_exclusive(v_l_3918_);
if (v_isSharedCheck_4392_ == 0)
{
lean_object* v_unused_4393_; lean_object* v_unused_4394_; lean_object* v_unused_4395_; lean_object* v_unused_4396_; lean_object* v_unused_4397_; 
v_unused_4393_ = lean_ctor_get(v_l_3918_, 4);
lean_dec(v_unused_4393_);
v_unused_4394_ = lean_ctor_get(v_l_3918_, 3);
lean_dec(v_unused_4394_);
v_unused_4395_ = lean_ctor_get(v_l_3918_, 2);
lean_dec(v_unused_4395_);
v_unused_4396_ = lean_ctor_get(v_l_3918_, 1);
lean_dec(v_unused_4396_);
v_unused_4397_ = lean_ctor_get(v_l_3918_, 0);
lean_dec(v_unused_4397_);
v___x_4369_ = v_l_3918_;
v_isShared_4370_ = v_isSharedCheck_4392_;
goto v_resetjp_4368_;
}
else
{
lean_dec(v_l_3918_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4392_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v_k_4371_; lean_object* v_v_4372_; lean_object* v_k_4373_; lean_object* v_v_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4388_; 
v_k_4371_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_k_4371_);
v_v_4372_ = lean_ctor_get(v___x_4255_, 1);
lean_inc(v_v_4372_);
lean_dec_ref(v___x_4255_);
v_k_4373_ = lean_ctor_get(v_r_4103_, 1);
v_v_4374_ = lean_ctor_get(v_r_4103_, 2);
v_isSharedCheck_4388_ = !lean_is_exclusive(v_r_4103_);
if (v_isSharedCheck_4388_ == 0)
{
lean_object* v_unused_4389_; lean_object* v_unused_4390_; lean_object* v_unused_4391_; 
v_unused_4389_ = lean_ctor_get(v_r_4103_, 4);
lean_dec(v_unused_4389_);
v_unused_4390_ = lean_ctor_get(v_r_4103_, 3);
lean_dec(v_unused_4390_);
v_unused_4391_ = lean_ctor_get(v_r_4103_, 0);
lean_dec(v_unused_4391_);
v___x_4376_ = v_r_4103_;
v_isShared_4377_ = v_isSharedCheck_4388_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_v_4374_);
lean_inc(v_k_4373_);
lean_dec(v_r_4103_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4388_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4378_; lean_object* v___x_4380_; 
v___x_4378_ = lean_unsigned_to_nat(3u);
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 4, v_l_4102_);
lean_ctor_set(v___x_4376_, 3, v_l_4102_);
lean_ctor_set(v___x_4376_, 2, v_v_4101_);
lean_ctor_set(v___x_4376_, 1, v_k_4100_);
lean_ctor_set(v___x_4376_, 0, v___x_4109_);
v___x_4380_ = v___x_4376_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_k_4100_);
lean_ctor_set(v_reuseFailAlloc_4387_, 2, v_v_4101_);
lean_ctor_set(v_reuseFailAlloc_4387_, 3, v_l_4102_);
lean_ctor_set(v_reuseFailAlloc_4387_, 4, v_l_4102_);
v___x_4380_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
lean_object* v___x_4382_; 
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 4, v_l_4102_);
lean_ctor_set(v___x_4253_, 3, v_l_4102_);
lean_ctor_set(v___x_4253_, 2, v_v_4372_);
lean_ctor_set(v___x_4253_, 1, v_k_4371_);
lean_ctor_set(v___x_4253_, 0, v___x_4109_);
v___x_4382_ = v___x_4253_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4386_, 1, v_k_4371_);
lean_ctor_set(v_reuseFailAlloc_4386_, 2, v_v_4372_);
lean_ctor_set(v_reuseFailAlloc_4386_, 3, v_l_4102_);
lean_ctor_set(v_reuseFailAlloc_4386_, 4, v_l_4102_);
v___x_4382_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
lean_object* v___x_4384_; 
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 4, v___x_4382_);
lean_ctor_set(v___x_4369_, 3, v___x_4380_);
lean_ctor_set(v___x_4369_, 2, v_v_4374_);
lean_ctor_set(v___x_4369_, 1, v_k_4373_);
lean_ctor_set(v___x_4369_, 0, v___x_4378_);
v___x_4384_ = v___x_4369_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4378_);
lean_ctor_set(v_reuseFailAlloc_4385_, 1, v_k_4373_);
lean_ctor_set(v_reuseFailAlloc_4385_, 2, v_v_4374_);
lean_ctor_set(v_reuseFailAlloc_4385_, 3, v___x_4380_);
lean_ctor_set(v_reuseFailAlloc_4385_, 4, v___x_4382_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
}
}
else
{
lean_object* v_k_4398_; lean_object* v_v_4399_; lean_object* v___x_4400_; lean_object* v___x_4402_; 
v_k_4398_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_k_4398_);
v_v_4399_ = lean_ctor_get(v___x_4255_, 1);
lean_inc(v_v_4399_);
lean_dec_ref(v___x_4255_);
v___x_4400_ = lean_unsigned_to_nat(2u);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 4, v_r_4103_);
lean_ctor_set(v___x_4253_, 3, v_l_3918_);
lean_ctor_set(v___x_4253_, 2, v_v_4399_);
lean_ctor_set(v___x_4253_, 1, v_k_4398_);
lean_ctor_set(v___x_4253_, 0, v___x_4400_);
v___x_4402_ = v___x_4253_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v_k_4398_);
lean_ctor_set(v_reuseFailAlloc_4403_, 2, v_v_4399_);
lean_ctor_set(v_reuseFailAlloc_4403_, 3, v_l_3918_);
lean_ctor_set(v_reuseFailAlloc_4403_, 4, v_r_4103_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
}
}
}
else
{
return v_l_3918_;
}
}
else
{
return v_r_3919_;
}
}
default: 
{
lean_object* v_impl_4410_; lean_object* v___x_4411_; 
v_impl_4410_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_3913_, v_k_3914_, v_r_3919_);
v___x_4411_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_4410_) == 0)
{
if (lean_obj_tag(v_l_3918_) == 0)
{
lean_object* v_size_4412_; lean_object* v_size_4413_; lean_object* v_k_4414_; lean_object* v_v_4415_; lean_object* v_l_4416_; lean_object* v_r_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; uint8_t v___x_4420_; 
v_size_4412_ = lean_ctor_get(v_impl_4410_, 0);
v_size_4413_ = lean_ctor_get(v_l_3918_, 0);
v_k_4414_ = lean_ctor_get(v_l_3918_, 1);
v_v_4415_ = lean_ctor_get(v_l_3918_, 2);
v_l_4416_ = lean_ctor_get(v_l_3918_, 3);
v_r_4417_ = lean_ctor_get(v_l_3918_, 4);
lean_inc(v_r_4417_);
v___x_4418_ = lean_unsigned_to_nat(3u);
v___x_4419_ = lean_nat_mul(v___x_4418_, v_size_4412_);
v___x_4420_ = lean_nat_dec_lt(v___x_4419_, v_size_4413_);
lean_dec(v___x_4419_);
if (v___x_4420_ == 0)
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4424_; 
lean_dec(v_r_4417_);
v___x_4421_ = lean_nat_add(v___x_4411_, v_size_4413_);
v___x_4422_ = lean_nat_add(v___x_4421_, v_size_4412_);
lean_dec(v___x_4421_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v_impl_4410_);
lean_ctor_set(v___x_3921_, 0, v___x_4422_);
v___x_4424_ = v___x_3921_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4425_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4425_, 3, v_l_3918_);
lean_ctor_set(v_reuseFailAlloc_4425_, 4, v_impl_4410_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
else
{
lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4491_; 
lean_inc(v_l_4416_);
lean_inc(v_v_4415_);
lean_inc(v_k_4414_);
lean_inc(v_size_4413_);
v_isSharedCheck_4491_ = !lean_is_exclusive(v_l_3918_);
if (v_isSharedCheck_4491_ == 0)
{
lean_object* v_unused_4492_; lean_object* v_unused_4493_; lean_object* v_unused_4494_; lean_object* v_unused_4495_; lean_object* v_unused_4496_; 
v_unused_4492_ = lean_ctor_get(v_l_3918_, 4);
lean_dec(v_unused_4492_);
v_unused_4493_ = lean_ctor_get(v_l_3918_, 3);
lean_dec(v_unused_4493_);
v_unused_4494_ = lean_ctor_get(v_l_3918_, 2);
lean_dec(v_unused_4494_);
v_unused_4495_ = lean_ctor_get(v_l_3918_, 1);
lean_dec(v_unused_4495_);
v_unused_4496_ = lean_ctor_get(v_l_3918_, 0);
lean_dec(v_unused_4496_);
v___x_4427_ = v_l_3918_;
v_isShared_4428_ = v_isSharedCheck_4491_;
goto v_resetjp_4426_;
}
else
{
lean_dec(v_l_3918_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4491_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v_size_4429_; lean_object* v_size_4430_; lean_object* v_k_4431_; lean_object* v_v_4432_; lean_object* v_l_4433_; lean_object* v_r_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; uint8_t v___x_4437_; 
v_size_4429_ = lean_ctor_get(v_l_4416_, 0);
v_size_4430_ = lean_ctor_get(v_r_4417_, 0);
v_k_4431_ = lean_ctor_get(v_r_4417_, 1);
v_v_4432_ = lean_ctor_get(v_r_4417_, 2);
v_l_4433_ = lean_ctor_get(v_r_4417_, 3);
v_r_4434_ = lean_ctor_get(v_r_4417_, 4);
v___x_4435_ = lean_unsigned_to_nat(2u);
v___x_4436_ = lean_nat_mul(v___x_4435_, v_size_4429_);
v___x_4437_ = lean_nat_dec_lt(v_size_4430_, v___x_4436_);
lean_dec(v___x_4436_);
if (v___x_4437_ == 0)
{
lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4466_; 
lean_inc(v_r_4434_);
lean_inc(v_l_4433_);
lean_inc(v_v_4432_);
lean_inc(v_k_4431_);
v_isSharedCheck_4466_ = !lean_is_exclusive(v_r_4417_);
if (v_isSharedCheck_4466_ == 0)
{
lean_object* v_unused_4467_; lean_object* v_unused_4468_; lean_object* v_unused_4469_; lean_object* v_unused_4470_; lean_object* v_unused_4471_; 
v_unused_4467_ = lean_ctor_get(v_r_4417_, 4);
lean_dec(v_unused_4467_);
v_unused_4468_ = lean_ctor_get(v_r_4417_, 3);
lean_dec(v_unused_4468_);
v_unused_4469_ = lean_ctor_get(v_r_4417_, 2);
lean_dec(v_unused_4469_);
v_unused_4470_ = lean_ctor_get(v_r_4417_, 1);
lean_dec(v_unused_4470_);
v_unused_4471_ = lean_ctor_get(v_r_4417_, 0);
lean_dec(v_unused_4471_);
v___x_4439_ = v_r_4417_;
v_isShared_4440_ = v_isSharedCheck_4466_;
goto v_resetjp_4438_;
}
else
{
lean_dec(v_r_4417_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4466_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___x_4454_; lean_object* v___y_4456_; 
v___x_4441_ = lean_nat_add(v___x_4411_, v_size_4413_);
lean_dec(v_size_4413_);
v___x_4442_ = lean_nat_add(v___x_4441_, v_size_4412_);
lean_dec(v___x_4441_);
v___x_4454_ = lean_nat_add(v___x_4411_, v_size_4429_);
if (lean_obj_tag(v_l_4433_) == 0)
{
lean_object* v_size_4464_; 
v_size_4464_ = lean_ctor_get(v_l_4433_, 0);
lean_inc(v_size_4464_);
v___y_4456_ = v_size_4464_;
goto v___jp_4455_;
}
else
{
lean_object* v___x_4465_; 
v___x_4465_ = lean_unsigned_to_nat(0u);
v___y_4456_ = v___x_4465_;
goto v___jp_4455_;
}
v___jp_4443_:
{
lean_object* v___x_4447_; lean_object* v___x_4449_; 
v___x_4447_ = lean_nat_add(v___y_4445_, v___y_4446_);
lean_dec(v___y_4446_);
lean_dec(v___y_4445_);
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 4, v_impl_4410_);
lean_ctor_set(v___x_4439_, 3, v_r_4434_);
lean_ctor_set(v___x_4439_, 2, v_v_3917_);
lean_ctor_set(v___x_4439_, 1, v_k_3916_);
lean_ctor_set(v___x_4439_, 0, v___x_4447_);
v___x_4449_ = v___x_4439_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4447_);
lean_ctor_set(v_reuseFailAlloc_4453_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4453_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4453_, 3, v_r_4434_);
lean_ctor_set(v_reuseFailAlloc_4453_, 4, v_impl_4410_);
v___x_4449_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
lean_object* v___x_4451_; 
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 4, v___x_4449_);
lean_ctor_set(v___x_4427_, 3, v___y_4444_);
lean_ctor_set(v___x_4427_, 2, v_v_4432_);
lean_ctor_set(v___x_4427_, 1, v_k_4431_);
lean_ctor_set(v___x_4427_, 0, v___x_4442_);
v___x_4451_ = v___x_4427_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v___x_4442_);
lean_ctor_set(v_reuseFailAlloc_4452_, 1, v_k_4431_);
lean_ctor_set(v_reuseFailAlloc_4452_, 2, v_v_4432_);
lean_ctor_set(v_reuseFailAlloc_4452_, 3, v___y_4444_);
lean_ctor_set(v_reuseFailAlloc_4452_, 4, v___x_4449_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
v___jp_4455_:
{
lean_object* v___x_4457_; lean_object* v___x_4459_; 
v___x_4457_ = lean_nat_add(v___x_4454_, v___y_4456_);
lean_dec(v___y_4456_);
lean_dec(v___x_4454_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v_l_4433_);
lean_ctor_set(v___x_3921_, 3, v_l_4416_);
lean_ctor_set(v___x_3921_, 2, v_v_4415_);
lean_ctor_set(v___x_3921_, 1, v_k_4414_);
lean_ctor_set(v___x_3921_, 0, v___x_4457_);
v___x_4459_ = v___x_3921_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v___x_4457_);
lean_ctor_set(v_reuseFailAlloc_4463_, 1, v_k_4414_);
lean_ctor_set(v_reuseFailAlloc_4463_, 2, v_v_4415_);
lean_ctor_set(v_reuseFailAlloc_4463_, 3, v_l_4416_);
lean_ctor_set(v_reuseFailAlloc_4463_, 4, v_l_4433_);
v___x_4459_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4460_; 
v___x_4460_ = lean_nat_add(v___x_4411_, v_size_4412_);
if (lean_obj_tag(v_r_4434_) == 0)
{
lean_object* v_size_4461_; 
v_size_4461_ = lean_ctor_get(v_r_4434_, 0);
lean_inc(v_size_4461_);
v___y_4444_ = v___x_4459_;
v___y_4445_ = v___x_4460_;
v___y_4446_ = v_size_4461_;
goto v___jp_4443_;
}
else
{
lean_object* v___x_4462_; 
v___x_4462_ = lean_unsigned_to_nat(0u);
v___y_4444_ = v___x_4459_;
v___y_4445_ = v___x_4460_;
v___y_4446_ = v___x_4462_;
goto v___jp_4443_;
}
}
}
}
}
else
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4477_; 
lean_del_object(v___x_3921_);
v___x_4472_ = lean_nat_add(v___x_4411_, v_size_4413_);
lean_dec(v_size_4413_);
v___x_4473_ = lean_nat_add(v___x_4472_, v_size_4412_);
lean_dec(v___x_4472_);
v___x_4474_ = lean_nat_add(v___x_4411_, v_size_4412_);
v___x_4475_ = lean_nat_add(v___x_4474_, v_size_4430_);
lean_dec(v___x_4474_);
lean_inc_ref(v_impl_4410_);
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 4, v_impl_4410_);
lean_ctor_set(v___x_4427_, 3, v_r_4417_);
lean_ctor_set(v___x_4427_, 2, v_v_3917_);
lean_ctor_set(v___x_4427_, 1, v_k_3916_);
lean_ctor_set(v___x_4427_, 0, v___x_4475_);
v___x_4477_ = v___x_4427_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4475_);
lean_ctor_set(v_reuseFailAlloc_4490_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4490_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4490_, 3, v_r_4417_);
lean_ctor_set(v_reuseFailAlloc_4490_, 4, v_impl_4410_);
v___x_4477_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
v_isSharedCheck_4484_ = !lean_is_exclusive(v_impl_4410_);
if (v_isSharedCheck_4484_ == 0)
{
lean_object* v_unused_4485_; lean_object* v_unused_4486_; lean_object* v_unused_4487_; lean_object* v_unused_4488_; lean_object* v_unused_4489_; 
v_unused_4485_ = lean_ctor_get(v_impl_4410_, 4);
lean_dec(v_unused_4485_);
v_unused_4486_ = lean_ctor_get(v_impl_4410_, 3);
lean_dec(v_unused_4486_);
v_unused_4487_ = lean_ctor_get(v_impl_4410_, 2);
lean_dec(v_unused_4487_);
v_unused_4488_ = lean_ctor_get(v_impl_4410_, 1);
lean_dec(v_unused_4488_);
v_unused_4489_ = lean_ctor_get(v_impl_4410_, 0);
lean_dec(v_unused_4489_);
v___x_4479_ = v_impl_4410_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_dec(v_impl_4410_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 4, v___x_4477_);
lean_ctor_set(v___x_4479_, 3, v_l_4416_);
lean_ctor_set(v___x_4479_, 2, v_v_4415_);
lean_ctor_set(v___x_4479_, 1, v_k_4414_);
lean_ctor_set(v___x_4479_, 0, v___x_4473_);
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4473_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v_k_4414_);
lean_ctor_set(v_reuseFailAlloc_4483_, 2, v_v_4415_);
lean_ctor_set(v_reuseFailAlloc_4483_, 3, v_l_4416_);
lean_ctor_set(v_reuseFailAlloc_4483_, 4, v___x_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_4497_; lean_object* v___x_4498_; lean_object* v___x_4500_; 
v_size_4497_ = lean_ctor_get(v_impl_4410_, 0);
v___x_4498_ = lean_nat_add(v___x_4411_, v_size_4497_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v_impl_4410_);
lean_ctor_set(v___x_3921_, 0, v___x_4498_);
v___x_4500_ = v___x_3921_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4498_);
lean_ctor_set(v_reuseFailAlloc_4501_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4501_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4501_, 3, v_l_3918_);
lean_ctor_set(v_reuseFailAlloc_4501_, 4, v_impl_4410_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
else
{
if (lean_obj_tag(v_l_3918_) == 0)
{
lean_object* v_l_4502_; 
v_l_4502_ = lean_ctor_get(v_l_3918_, 3);
if (lean_obj_tag(v_l_4502_) == 0)
{
lean_object* v_r_4503_; 
lean_inc_ref(v_l_4502_);
v_r_4503_ = lean_ctor_get(v_l_3918_, 4);
lean_inc(v_r_4503_);
if (lean_obj_tag(v_r_4503_) == 0)
{
lean_object* v_size_4504_; lean_object* v_k_4505_; lean_object* v_v_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4519_; 
v_size_4504_ = lean_ctor_get(v_l_3918_, 0);
v_k_4505_ = lean_ctor_get(v_l_3918_, 1);
v_v_4506_ = lean_ctor_get(v_l_3918_, 2);
v_isSharedCheck_4519_ = !lean_is_exclusive(v_l_3918_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; lean_object* v_unused_4521_; 
v_unused_4520_ = lean_ctor_get(v_l_3918_, 4);
lean_dec(v_unused_4520_);
v_unused_4521_ = lean_ctor_get(v_l_3918_, 3);
lean_dec(v_unused_4521_);
v___x_4508_ = v_l_3918_;
v_isShared_4509_ = v_isSharedCheck_4519_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_v_4506_);
lean_inc(v_k_4505_);
lean_inc(v_size_4504_);
lean_dec(v_l_3918_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4519_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v_size_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4514_; 
v_size_4510_ = lean_ctor_get(v_r_4503_, 0);
v___x_4511_ = lean_nat_add(v___x_4411_, v_size_4504_);
lean_dec(v_size_4504_);
v___x_4512_ = lean_nat_add(v___x_4411_, v_size_4510_);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 4, v_impl_4410_);
lean_ctor_set(v___x_4508_, 3, v_r_4503_);
lean_ctor_set(v___x_4508_, 2, v_v_3917_);
lean_ctor_set(v___x_4508_, 1, v_k_3916_);
lean_ctor_set(v___x_4508_, 0, v___x_4512_);
v___x_4514_ = v___x_4508_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4512_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4518_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4518_, 3, v_r_4503_);
lean_ctor_set(v_reuseFailAlloc_4518_, 4, v_impl_4410_);
v___x_4514_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
lean_object* v___x_4516_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v___x_4514_);
lean_ctor_set(v___x_3921_, 3, v_l_4502_);
lean_ctor_set(v___x_3921_, 2, v_v_4506_);
lean_ctor_set(v___x_3921_, 1, v_k_4505_);
lean_ctor_set(v___x_3921_, 0, v___x_4511_);
v___x_4516_ = v___x_3921_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4511_);
lean_ctor_set(v_reuseFailAlloc_4517_, 1, v_k_4505_);
lean_ctor_set(v_reuseFailAlloc_4517_, 2, v_v_4506_);
lean_ctor_set(v_reuseFailAlloc_4517_, 3, v_l_4502_);
lean_ctor_set(v_reuseFailAlloc_4517_, 4, v___x_4514_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
else
{
lean_object* v_k_4522_; lean_object* v_v_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4534_; 
v_k_4522_ = lean_ctor_get(v_l_3918_, 1);
v_v_4523_ = lean_ctor_get(v_l_3918_, 2);
v_isSharedCheck_4534_ = !lean_is_exclusive(v_l_3918_);
if (v_isSharedCheck_4534_ == 0)
{
lean_object* v_unused_4535_; lean_object* v_unused_4536_; lean_object* v_unused_4537_; 
v_unused_4535_ = lean_ctor_get(v_l_3918_, 4);
lean_dec(v_unused_4535_);
v_unused_4536_ = lean_ctor_get(v_l_3918_, 3);
lean_dec(v_unused_4536_);
v_unused_4537_ = lean_ctor_get(v_l_3918_, 0);
lean_dec(v_unused_4537_);
v___x_4525_ = v_l_3918_;
v_isShared_4526_ = v_isSharedCheck_4534_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_v_4523_);
lean_inc(v_k_4522_);
lean_dec(v_l_3918_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4534_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4527_; lean_object* v___x_4529_; 
v___x_4527_ = lean_unsigned_to_nat(3u);
if (v_isShared_4526_ == 0)
{
lean_ctor_set(v___x_4525_, 3, v_r_4503_);
lean_ctor_set(v___x_4525_, 2, v_v_3917_);
lean_ctor_set(v___x_4525_, 1, v_k_3916_);
lean_ctor_set(v___x_4525_, 0, v___x_4411_);
v___x_4529_ = v___x_4525_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4411_);
lean_ctor_set(v_reuseFailAlloc_4533_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4533_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4533_, 3, v_r_4503_);
lean_ctor_set(v_reuseFailAlloc_4533_, 4, v_r_4503_);
v___x_4529_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
lean_object* v___x_4531_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v___x_4529_);
lean_ctor_set(v___x_3921_, 3, v_l_4502_);
lean_ctor_set(v___x_3921_, 2, v_v_4523_);
lean_ctor_set(v___x_3921_, 1, v_k_4522_);
lean_ctor_set(v___x_3921_, 0, v___x_4527_);
v___x_4531_ = v___x_3921_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4527_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v_k_4522_);
lean_ctor_set(v_reuseFailAlloc_4532_, 2, v_v_4523_);
lean_ctor_set(v_reuseFailAlloc_4532_, 3, v_l_4502_);
lean_ctor_set(v_reuseFailAlloc_4532_, 4, v___x_4529_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
}
else
{
lean_object* v_r_4538_; 
v_r_4538_ = lean_ctor_get(v_l_3918_, 4);
lean_inc(v_r_4538_);
if (lean_obj_tag(v_r_4538_) == 0)
{
lean_object* v_k_4539_; lean_object* v_v_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4563_; 
lean_inc(v_l_4502_);
v_k_4539_ = lean_ctor_get(v_l_3918_, 1);
v_v_4540_ = lean_ctor_get(v_l_3918_, 2);
v_isSharedCheck_4563_ = !lean_is_exclusive(v_l_3918_);
if (v_isSharedCheck_4563_ == 0)
{
lean_object* v_unused_4564_; lean_object* v_unused_4565_; lean_object* v_unused_4566_; 
v_unused_4564_ = lean_ctor_get(v_l_3918_, 4);
lean_dec(v_unused_4564_);
v_unused_4565_ = lean_ctor_get(v_l_3918_, 3);
lean_dec(v_unused_4565_);
v_unused_4566_ = lean_ctor_get(v_l_3918_, 0);
lean_dec(v_unused_4566_);
v___x_4542_ = v_l_3918_;
v_isShared_4543_ = v_isSharedCheck_4563_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_v_4540_);
lean_inc(v_k_4539_);
lean_dec(v_l_3918_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4563_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v_k_4544_; lean_object* v_v_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4559_; 
v_k_4544_ = lean_ctor_get(v_r_4538_, 1);
v_v_4545_ = lean_ctor_get(v_r_4538_, 2);
v_isSharedCheck_4559_ = !lean_is_exclusive(v_r_4538_);
if (v_isSharedCheck_4559_ == 0)
{
lean_object* v_unused_4560_; lean_object* v_unused_4561_; lean_object* v_unused_4562_; 
v_unused_4560_ = lean_ctor_get(v_r_4538_, 4);
lean_dec(v_unused_4560_);
v_unused_4561_ = lean_ctor_get(v_r_4538_, 3);
lean_dec(v_unused_4561_);
v_unused_4562_ = lean_ctor_get(v_r_4538_, 0);
lean_dec(v_unused_4562_);
v___x_4547_ = v_r_4538_;
v_isShared_4548_ = v_isSharedCheck_4559_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_v_4545_);
lean_inc(v_k_4544_);
lean_dec(v_r_4538_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4559_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4549_; lean_object* v___x_4551_; 
v___x_4549_ = lean_unsigned_to_nat(3u);
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 4, v_l_4502_);
lean_ctor_set(v___x_4547_, 3, v_l_4502_);
lean_ctor_set(v___x_4547_, 2, v_v_4540_);
lean_ctor_set(v___x_4547_, 1, v_k_4539_);
lean_ctor_set(v___x_4547_, 0, v___x_4411_);
v___x_4551_ = v___x_4547_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4411_);
lean_ctor_set(v_reuseFailAlloc_4558_, 1, v_k_4539_);
lean_ctor_set(v_reuseFailAlloc_4558_, 2, v_v_4540_);
lean_ctor_set(v_reuseFailAlloc_4558_, 3, v_l_4502_);
lean_ctor_set(v_reuseFailAlloc_4558_, 4, v_l_4502_);
v___x_4551_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
lean_object* v___x_4553_; 
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 4, v_l_4502_);
lean_ctor_set(v___x_4542_, 2, v_v_3917_);
lean_ctor_set(v___x_4542_, 1, v_k_3916_);
lean_ctor_set(v___x_4542_, 0, v___x_4411_);
v___x_4553_ = v___x_4542_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4411_);
lean_ctor_set(v_reuseFailAlloc_4557_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4557_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4557_, 3, v_l_4502_);
lean_ctor_set(v_reuseFailAlloc_4557_, 4, v_l_4502_);
v___x_4553_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
lean_object* v___x_4555_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v___x_4553_);
lean_ctor_set(v___x_3921_, 3, v___x_4551_);
lean_ctor_set(v___x_3921_, 2, v_v_4545_);
lean_ctor_set(v___x_3921_, 1, v_k_4544_);
lean_ctor_set(v___x_3921_, 0, v___x_4549_);
v___x_4555_ = v___x_3921_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4549_);
lean_ctor_set(v_reuseFailAlloc_4556_, 1, v_k_4544_);
lean_ctor_set(v_reuseFailAlloc_4556_, 2, v_v_4545_);
lean_ctor_set(v_reuseFailAlloc_4556_, 3, v___x_4551_);
lean_ctor_set(v_reuseFailAlloc_4556_, 4, v___x_4553_);
v___x_4555_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
return v___x_4555_;
}
}
}
}
}
}
else
{
lean_object* v___x_4567_; lean_object* v___x_4569_; 
v___x_4567_ = lean_unsigned_to_nat(2u);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v_r_4538_);
lean_ctor_set(v___x_3921_, 0, v___x_4567_);
v___x_4569_ = v___x_3921_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
lean_ctor_set(v_reuseFailAlloc_4570_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4570_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4570_, 3, v_l_3918_);
lean_ctor_set(v_reuseFailAlloc_4570_, 4, v_r_4538_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
else
{
lean_object* v___x_4572_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v_l_3918_);
lean_ctor_set(v___x_3921_, 0, v___x_4411_);
v___x_4572_ = v___x_3921_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4411_);
lean_ctor_set(v_reuseFailAlloc_4573_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_4573_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_4573_, 3, v_l_3918_);
lean_ctor_set(v_reuseFailAlloc_4573_, 4, v_l_3918_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_3914_);
lean_dec_ref(v_cmp_3913_);
return v_t_3915_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(lean_object* v_cmp_4576_, lean_object* v_init_4577_, lean_object* v_x_4578_){
_start:
{
if (lean_obj_tag(v_x_4578_) == 0)
{
lean_object* v_k_4579_; lean_object* v_l_4580_; lean_object* v_r_4581_; lean_object* v___x_4582_; lean_object* v_a_4583_; lean_object* v_r_4584_; 
v_k_4579_ = lean_ctor_get(v_x_4578_, 1);
lean_inc(v_k_4579_);
v_l_4580_ = lean_ctor_get(v_x_4578_, 3);
lean_inc(v_l_4580_);
v_r_4581_ = lean_ctor_get(v_x_4578_, 4);
lean_inc(v_r_4581_);
lean_dec_ref_known(v_x_4578_, 5);
lean_inc_ref_n(v_cmp_4576_, 2);
v___x_4582_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4576_, v_init_4577_, v_l_4580_);
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4583_);
lean_dec_ref(v___x_4582_);
v_r_4584_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_4576_, v_k_4579_, v_a_4583_);
v_init_4577_ = v_r_4584_;
v_x_4578_ = v_r_4581_;
goto _start;
}
else
{
lean_object* v___x_4586_; 
lean_dec_ref(v_cmp_4576_);
v___x_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4586_, 0, v_init_4577_);
return v___x_4586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(lean_object* v_cmp_4587_, lean_object* v_t_u2082_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v_t_4591_){
_start:
{
if (lean_obj_tag(v_t_4591_) == 0)
{
lean_object* v_k_4592_; lean_object* v_v_4593_; lean_object* v_l_4594_; lean_object* v_r_4595_; uint8_t v___x_4600_; 
v_k_4592_ = lean_ctor_get(v_t_4591_, 1);
lean_inc_n(v_k_4592_, 2);
v_v_4593_ = lean_ctor_get(v_t_4591_, 2);
lean_inc(v_v_4593_);
v_l_4594_ = lean_ctor_get(v_t_4591_, 3);
lean_inc(v_l_4594_);
v_r_4595_ = lean_ctor_get(v_t_4591_, 4);
lean_inc(v_r_4595_);
lean_dec_ref_known(v_t_4591_, 5);
lean_inc(v_t_u2082_4588_);
lean_inc_ref(v_cmp_4587_);
v___x_4600_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_4587_, v_k_4592_, v_t_u2082_4588_);
if (v___x_4600_ == 0)
{
uint8_t v___x_4601_; 
v___x_4601_ = lean_nat_dec_le(v___y_4589_, v___y_4590_);
if (v___x_4601_ == 0)
{
lean_dec(v_v_4593_);
lean_dec(v_k_4592_);
goto v___jp_4596_;
}
else
{
lean_object* v_impl_4602_; lean_object* v_impl_4603_; lean_object* v___x_4604_; 
lean_inc(v_t_u2082_4588_);
lean_inc_ref(v_cmp_4587_);
v_impl_4602_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4587_, v_t_u2082_4588_, v___y_4589_, v___y_4590_, v_l_4594_);
v_impl_4603_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4587_, v_t_u2082_4588_, v___y_4589_, v___y_4590_, v_r_4595_);
v___x_4604_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_4592_, v_v_4593_, v_impl_4602_, v_impl_4603_);
return v___x_4604_;
}
}
else
{
lean_dec(v_v_4593_);
lean_dec(v_k_4592_);
goto v___jp_4596_;
}
v___jp_4596_:
{
lean_object* v_impl_4597_; lean_object* v_impl_4598_; lean_object* v___x_4599_; 
lean_inc(v_t_u2082_4588_);
lean_inc_ref(v_cmp_4587_);
v_impl_4597_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4587_, v_t_u2082_4588_, v___y_4589_, v___y_4590_, v_l_4594_);
v_impl_4598_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4587_, v_t_u2082_4588_, v___y_4589_, v___y_4590_, v_r_4595_);
v___x_4599_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_4597_, v_impl_4598_);
return v___x_4599_;
}
}
else
{
lean_dec(v_t_u2082_4588_);
lean_dec_ref(v_cmp_4587_);
return v_t_4591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg___boxed(lean_object* v_cmp_4605_, lean_object* v_t_u2082_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v_t_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4605_, v_t_u2082_4606_, v___y_4607_, v___y_4608_, v_t_4609_);
lean_dec(v___y_4608_);
lean_dec(v___y_4607_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object* v_cmp_4611_, lean_object* v_t_u2081_4612_, lean_object* v_t_u2082_4613_){
_start:
{
lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4622_; 
if (lean_obj_tag(v_t_u2081_4612_) == 0)
{
lean_object* v_size_4625_; 
v_size_4625_ = lean_ctor_get(v_t_u2081_4612_, 0);
lean_inc(v_size_4625_);
v___y_4622_ = v_size_4625_;
goto v___jp_4621_;
}
else
{
lean_object* v___x_4626_; 
v___x_4626_ = lean_unsigned_to_nat(0u);
v___y_4622_ = v___x_4626_;
goto v___jp_4621_;
}
v___jp_4614_:
{
uint8_t v___x_4617_; 
v___x_4617_ = lean_nat_dec_le(v___y_4615_, v___y_4616_);
if (v___x_4617_ == 0)
{
lean_object* v___x_4618_; lean_object* v_a_4619_; 
lean_dec(v___y_4616_);
lean_dec(v___y_4615_);
v___x_4618_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4611_, v_t_u2081_4612_, v_t_u2082_4613_);
v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
lean_inc(v_a_4619_);
lean_dec_ref(v___x_4618_);
return v_a_4619_;
}
else
{
lean_object* v___x_4620_; 
v___x_4620_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4611_, v_t_u2082_4613_, v___y_4615_, v___y_4616_, v_t_u2081_4612_);
lean_dec(v___y_4616_);
lean_dec(v___y_4615_);
return v___x_4620_;
}
}
v___jp_4621_:
{
if (lean_obj_tag(v_t_u2082_4613_) == 0)
{
lean_object* v_size_4623_; 
v_size_4623_ = lean_ctor_get(v_t_u2082_4613_, 0);
lean_inc(v_size_4623_);
v___y_4615_ = v___y_4622_;
v___y_4616_ = v_size_4623_;
goto v___jp_4614_;
}
else
{
lean_object* v___x_4624_; 
v___x_4624_ = lean_unsigned_to_nat(0u);
v___y_4615_ = v___y_4622_;
v___y_4616_ = v___x_4624_;
goto v___jp_4614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff___redArg(lean_object* v_cmp_4627_, lean_object* v_t_u2081_4628_, lean_object* v_t_u2082_4629_){
_start:
{
lean_object* v___x_4630_; 
v___x_4630_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4627_, v_t_u2081_4628_, v_t_u2082_4629_);
return v___x_4630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_diff(lean_object* v_00_u03b1_4631_, lean_object* v_00_u03b2_4632_, lean_object* v_cmp_4633_, lean_object* v_t_u2081_4634_, lean_object* v_t_u2082_4635_){
_start:
{
lean_object* v___x_4636_; 
v___x_4636_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4633_, v_t_u2081_4634_, v_t_u2082_4635_);
return v___x_4636_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0(lean_object* v_00_u03b1_4637_, lean_object* v_cmp_4638_, lean_object* v_00_u03b2_4639_, lean_object* v_t_u2081_4640_, lean_object* v_t_u2082_4641_, lean_object* v_h_u2081_4642_){
_start:
{
lean_object* v___x_4643_; 
v___x_4643_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_4638_, v_t_u2081_4640_, v_t_u2082_4641_);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0(lean_object* v_00_u03b1_4644_, lean_object* v_cmp_4645_, lean_object* v_00_u03b2_4646_, lean_object* v_k_4647_, lean_object* v_t_4648_, lean_object* v_h_4649_){
_start:
{
lean_object* v___x_4650_; 
v___x_4650_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_4645_, v_k_4647_, v_t_4648_);
return v___x_4650_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1(lean_object* v_00_u03b1_4651_, lean_object* v_00_u03b2_4652_, lean_object* v_cmp_4653_, lean_object* v_init_4654_, lean_object* v_x_4655_){
_start:
{
lean_object* v___x_4656_; 
v___x_4656_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_4653_, v_init_4654_, v_x_4655_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2(lean_object* v_00_u03b1_4657_, lean_object* v_00_u03b2_4658_, lean_object* v_cmp_4659_, lean_object* v_t_u2082_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v_t_4663_, lean_object* v_hl_4664_){
_start:
{
lean_object* v___x_4665_; 
v___x_4665_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_4659_, v_t_u2082_4660_, v___y_4661_, v___y_4662_, v_t_4663_);
return v___x_4665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4666_, lean_object* v_00_u03b2_4667_, lean_object* v_cmp_4668_, lean_object* v_t_u2082_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v_t_4672_, lean_object* v_hl_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2(v_00_u03b1_4666_, v_00_u03b2_4667_, v_cmp_4668_, v_t_u2082_4669_, v___y_4670_, v___y_4671_, v_t_4672_, v_hl_4673_);
lean_dec(v___y_4671_);
lean_dec(v___y_4670_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSDiff___redArg(lean_object* v_cmp_4675_){
_start:
{
lean_object* v___x_4676_; 
v___x_4676_ = lean_alloc_closure((void*)(l_Std_DTreeMap_diff), 5, 3);
lean_closure_set(v___x_4676_, 0, lean_box(0));
lean_closure_set(v___x_4676_, 1, lean_box(0));
lean_closure_set(v___x_4676_, 2, v_cmp_4675_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instSDiff(lean_object* v_00_u03b1_4677_, lean_object* v_00_u03b2_4678_, lean_object* v_cmp_4679_){
_start:
{
lean_object* v___x_4680_; 
v___x_4680_ = lean_alloc_closure((void*)(l_Std_DTreeMap_diff), 5, 3);
lean_closure_set(v___x_4680_, 0, lean_box(0));
lean_closure_set(v___x_4680_, 1, lean_box(0));
lean_closure_set(v___x_4680_, 2, v_cmp_4679_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_4681_, lean_object* v_a_4682_, lean_object* v_____s_4683_){
_start:
{
lean_object* v_r_4684_; lean_object* v___x_4685_; 
v_r_4684_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_4681_, v_a_4682_, v_____s_4683_);
v___x_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4685_, 0, v_r_4684_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany___redArg(lean_object* v_cmp_4686_, lean_object* v_inst_4687_, lean_object* v_t_4688_, lean_object* v_l_4689_){
_start:
{
lean_object* v___f_4690_; lean_object* v___x_4691_; 
v___f_4690_ = lean_alloc_closure((void*)(l_Std_DTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4690_, 0, v_cmp_4686_);
v___x_4691_ = lean_apply_4(v_inst_4687_, lean_box(0), v_l_4689_, v_t_4688_, v___f_4690_);
return v___x_4691_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_eraseMany(lean_object* v_00_u03b1_4692_, lean_object* v_00_u03b2_4693_, lean_object* v_cmp_4694_, lean_object* v_00_u03c1_4695_, lean_object* v_inst_4696_, lean_object* v_t_4697_, lean_object* v_l_4698_){
_start:
{
lean_object* v___f_4699_; lean_object* v___x_4700_; 
v___f_4699_ = lean_alloc_closure((void*)(l_Std_DTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4699_, 0, v_cmp_4694_);
v___x_4700_ = lean_apply_4(v_inst_4696_, lean_box(0), v_l_4698_, v_t_4697_, v___f_4699_);
return v___x_4700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany___redArg___lam__0(lean_object* v_cmp_4701_, lean_object* v_x_4702_, lean_object* v_____s_4703_){
_start:
{
lean_object* v_fst_4704_; lean_object* v_snd_4705_; lean_object* v_r_4706_; lean_object* v___x_4707_; 
v_fst_4704_ = lean_ctor_get(v_x_4702_, 0);
lean_inc(v_fst_4704_);
v_snd_4705_ = lean_ctor_get(v_x_4702_, 1);
lean_inc(v_snd_4705_);
lean_dec_ref(v_x_4702_);
v_r_4706_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4701_, v_fst_4704_, v_snd_4705_, v_____s_4703_);
v___x_4707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4707_, 0, v_r_4706_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany___redArg(lean_object* v_cmp_4708_, lean_object* v_inst_4709_, lean_object* v_t_4710_, lean_object* v_l_4711_){
_start:
{
lean_object* v___f_4712_; lean_object* v___x_4713_; 
v___f_4712_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4712_, 0, v_cmp_4708_);
v___x_4713_ = lean_apply_4(v_inst_4709_, lean_box(0), v_l_4711_, v_t_4710_, v___f_4712_);
return v___x_4713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertMany(lean_object* v_00_u03b1_4714_, lean_object* v_cmp_4715_, lean_object* v_00_u03b2_4716_, lean_object* v_00_u03c1_4717_, lean_object* v_inst_4718_, lean_object* v_t_4719_, lean_object* v_l_4720_){
_start:
{
lean_object* v___f_4721_; lean_object* v___x_4722_; 
v___f_4721_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4721_, 0, v_cmp_4715_);
v___x_4722_ = lean_apply_4(v_inst_4718_, lean_box(0), v_l_4720_, v_t_4719_, v___f_4721_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_4723_, lean_object* v_a_4724_, lean_object* v_____s_4725_){
_start:
{
uint8_t v___x_4726_; 
lean_inc(v_____s_4725_);
lean_inc(v_a_4724_);
lean_inc_ref(v_cmp_4723_);
v___x_4726_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4723_, v_a_4724_, v_____s_4725_);
if (v___x_4726_ == 0)
{
lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4727_ = lean_box(0);
v___x_4728_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4723_, v_a_4724_, v___x_4727_, v_____s_4725_);
v___x_4729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4728_);
return v___x_4729_;
}
else
{
lean_object* v___x_4730_; 
lean_dec(v_a_4724_);
lean_dec_ref(v_cmp_4723_);
v___x_4730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4730_, 0, v_____s_4725_);
return v___x_4730_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_4731_, lean_object* v_inst_4732_, lean_object* v_t_4733_, lean_object* v_l_4734_){
_start:
{
lean_object* v___f_4735_; lean_object* v___x_4736_; 
v___f_4735_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4735_, 0, v_cmp_4731_);
v___x_4736_ = lean_apply_4(v_inst_4732_, lean_box(0), v_l_4734_, v_t_4733_, v___f_4735_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_4737_, lean_object* v_cmp_4738_, lean_object* v_00_u03c1_4739_, lean_object* v_inst_4740_, lean_object* v_t_4741_, lean_object* v_l_4742_){
_start:
{
lean_object* v___f_4743_; lean_object* v___x_4744_; 
v___f_4743_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4743_, 0, v_cmp_4738_);
v___x_4744_ = lean_apply_4(v_inst_4740_, lean_box(0), v_l_4742_, v_t_4741_, v___f_4743_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1(lean_object* v___f_4748_, lean_object* v___x_4749_, lean_object* v_m_4750_, lean_object* v_prec_4751_){
_start:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4752_ = ((lean_object*)(l_Std_DTreeMap_instRepr___redArg___lam__1___closed__1));
v___x_4753_ = lean_box(0);
v___x_4754_ = ((lean_object*)(l_Std_DTreeMap_foldr___redArg___closed__9));
v___x_4755_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_4754_, v___f_4748_, v___x_4753_, v_m_4750_);
v___x_4756_ = l_List_repr___redArg(v___x_4749_, v___x_4755_);
v___x_4757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4752_);
lean_ctor_set(v___x_4757_, 1, v___x_4756_);
v___x_4758_ = l_Repr_addAppParen(v___x_4757_, v_prec_4751_);
return v___x_4758_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg___lam__1___boxed(lean_object* v___f_4759_, lean_object* v___x_4760_, lean_object* v_m_4761_, lean_object* v_prec_4762_){
_start:
{
lean_object* v_res_4763_; 
v_res_4763_ = l_Std_DTreeMap_instRepr___redArg___lam__1(v___f_4759_, v___x_4760_, v_m_4761_, v_prec_4762_);
lean_dec(v_prec_4762_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___redArg(lean_object* v_inst_4764_, lean_object* v_inst_4765_){
_start:
{
lean_object* v___f_4766_; lean_object* v___x_4767_; lean_object* v___f_4768_; 
v___f_4766_ = ((lean_object*)(l_Std_DTreeMap_toList___redArg___closed__0));
v___x_4767_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_4767_, 0, lean_box(0));
lean_closure_set(v___x_4767_, 1, lean_box(0));
lean_closure_set(v___x_4767_, 2, v_inst_4764_);
lean_closure_set(v___x_4767_, 3, v_inst_4765_);
v___f_4768_ = lean_alloc_closure((void*)(l_Std_DTreeMap_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4768_, 0, v___f_4766_);
lean_closure_set(v___f_4768_, 1, v___x_4767_);
return v___f_4768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr(lean_object* v_00_u03b1_4769_, lean_object* v_00_u03b2_4770_, lean_object* v_cmp_4771_, lean_object* v_inst_4772_, lean_object* v_inst_4773_){
_start:
{
lean_object* v___x_4774_; 
v___x_4774_ = l_Std_DTreeMap_instRepr___redArg(v_inst_4772_, v_inst_4773_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instRepr___boxed(lean_object* v_00_u03b1_4775_, lean_object* v_00_u03b2_4776_, lean_object* v_cmp_4777_, lean_object* v_inst_4778_, lean_object* v_inst_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_Std_DTreeMap_instRepr(v_00_u03b1_4775_, v_00_u03b2_4776_, v_cmp_4777_, v_inst_4778_, v_inst_4779_);
lean_dec_ref(v_cmp_4777_);
return v_res_4780_;
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
