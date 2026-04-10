// Lean compiler output
// Module: Std.Data.DTreeMap.Raw.Basic
// Imports: public import Std.Data.DTreeMap.Basic
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntry___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sigma_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__1(lean_object*);
static const lean_string_object l_Std_DTreeMap_Raw___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Raw___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Raw___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__2 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__2_value;
static const lean_string_object l_Std_DTreeMap_Raw___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__3 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__4 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__4_value;
static const lean_array_object l_Std_DTreeMap_Raw___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__5 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Raw___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__6 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__7 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__7_value;
static const lean_string_object l_Std_DTreeMap_Raw___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__8 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__9 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__9_value;
static const lean_string_object l_Std_DTreeMap_Raw___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__10 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__10_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__11 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__11_value;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__12;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__13;
static const lean_string_object l_Std_DTreeMap_Raw___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__14 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__14_value;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__15;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__16;
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__17 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__17_value;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__18;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__19;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__20;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__21;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__22;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__23;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__24;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__25;
static lean_once_cell_t l_Std_DTreeMap_Raw___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Raw_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_DTreeMap_Raw_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DTreeMap"};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__1 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_DTreeMap_Raw_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Raw"};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__2 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__2_value;
static const lean_string_object l_Std_DTreeMap_Raw_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__3 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_term___x7em___00__closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DTreeMap_Raw_term___x7em___00__closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__4_value_aux_0),((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 1, 106, 2, 110, 100, 218, 30)}};
static const lean_ctor_object l_Std_DTreeMap_Raw_term___x7em___00__closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__4_value_aux_1),((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 94, 91, 238, 10, 104, 84, 255)}};
static const lean_ctor_object l_Std_DTreeMap_Raw_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__4_value_aux_2),((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 150, 141, 27, 40, 233, 61, 36)}};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__4 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__4_value;
static const lean_string_object l_Std_DTreeMap_Raw_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__5 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__5_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__6 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__6_value;
static const lean_string_object l_Std_DTreeMap_Raw_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__7 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__7_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__7_value)}};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__8 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__8_value;
static const lean_string_object l_Std_DTreeMap_Raw_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__9 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__10 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__10_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__11 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__6_value),((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__8_value),((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__12 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__12_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_term___x7em___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__4_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__12_value)}};
static const lean_object* l_Std_DTreeMap_Raw_term___x7em___00__closed__13 = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__13_value;
LEAN_EXPORT const lean_object* l_Std_DTreeMap_Raw_term___x7em__ = (const lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__13_value;
static const lean_string_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__1_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2_value_aux_0),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2_value_aux_1),((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2_value_aux_2),((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2 = (const lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__3 = (const lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__3_value;
static lean_once_cell_t l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4;
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__5 = (const lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__5_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__6_value_aux_0),((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 1, 106, 2, 110, 100, 218, 30)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__6_value_aux_1),((lean_object*)&l_Std_DTreeMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 94, 91, 238, 10, 104, 84, 255)}};
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__6_value_aux_2),((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(50, 231, 245, 191, 156, 210, 197, 84)}};
static const lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__6 = (const lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__7 = (const lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__6_value)}};
static const lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__8 = (const lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__9 = (const lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__7_value),((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__9_value)}};
static const lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__10 = (const lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__10_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_foldr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_foldr___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__0_value;
static const lean_closure_object l_Std_DTreeMap_Raw_foldr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_foldr___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__1_value;
static const lean_closure_object l_Std_DTreeMap_Raw_foldr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_foldr___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__2_value;
static const lean_closure_object l_Std_DTreeMap_Raw_foldr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_foldr___redArg___closed__3 = (const lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__3_value;
static const lean_closure_object l_Std_DTreeMap_Raw_foldr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_foldr___redArg___closed__4 = (const lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__4_value;
static const lean_closure_object l_Std_DTreeMap_Raw_foldr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_foldr___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__5_value;
static const lean_closure_object l_Std_DTreeMap_Raw_foldr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_foldr___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_foldr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__0_value),((lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__1_value)}};
static const lean_object* l_Std_DTreeMap_Raw_foldr___redArg___closed__7 = (const lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__7_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_foldr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__7_value),((lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__2_value),((lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__3_value),((lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__4_value),((lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__5_value)}};
static const lean_object* l_Std_DTreeMap_Raw_foldr___redArg___closed__8 = (const lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_foldr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__8_value),((lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__6_value)}};
static const lean_object* l_Std_DTreeMap_Raw_foldr___redArg___closed__9 = (const lean_object*)&l_Std_DTreeMap_Raw_foldr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Raw_partition___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Raw_partition___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_partition___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Raw_any___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Raw_any___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_any___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_keys___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_keys___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_keysArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_values___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_values___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_toList___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_toArray___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_Const_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_Const_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.DTreeMap.Raw.ofList "};
static const lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__1(lean_object* v_00_u03b1_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__12(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__10));
v___x_30_ = l_Lean_mkAtom(v___x_29_);
return v___x_30_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__13(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__12, &l_Std_DTreeMap_Raw___auto__1___closed__12_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__12);
v___x_32_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_33_ = lean_array_push(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__15(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__14));
v___x_36_ = lean_string_utf8_byte_size(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__16(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_37_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__15, &l_Std_DTreeMap_Raw___auto__1___closed__15_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__15);
v___x_38_ = lean_unsigned_to_nat(0u);
v___x_39_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__14));
v___x_40_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
lean_ctor_set(v___x_40_, 2, v___x_37_);
return v___x_40_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__18(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_43_ = lean_box(0);
v___x_44_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__17));
v___x_45_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__16, &l_Std_DTreeMap_Raw___auto__1___closed__16_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__16);
v___x_46_ = lean_box(2);
v___x_47_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_45_);
lean_ctor_set(v___x_47_, 2, v___x_44_);
lean_ctor_set(v___x_47_, 3, v___x_43_);
return v___x_47_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__19(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__18, &l_Std_DTreeMap_Raw___auto__1___closed__18_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__18);
v___x_49_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__13, &l_Std_DTreeMap_Raw___auto__1___closed__13_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__13);
v___x_50_ = lean_array_push(v___x_49_, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__19, &l_Std_DTreeMap_Raw___auto__1___closed__19_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__19);
v___x_52_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__11));
v___x_53_ = lean_box(2);
v___x_54_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v___x_52_);
lean_ctor_set(v___x_54_, 2, v___x_51_);
return v___x_54_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__21(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__20, &l_Std_DTreeMap_Raw___auto__1___closed__20_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__20);
v___x_56_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_57_ = lean_array_push(v___x_56_, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__22(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__21, &l_Std_DTreeMap_Raw___auto__1___closed__21_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__21);
v___x_59_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__9));
v___x_60_ = lean_box(2);
v___x_61_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
lean_ctor_set(v___x_61_, 2, v___x_58_);
return v___x_61_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__23(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__22, &l_Std_DTreeMap_Raw___auto__1___closed__22_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__22);
v___x_63_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_64_ = lean_array_push(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__24(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__23, &l_Std_DTreeMap_Raw___auto__1___closed__23_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__23);
v___x_66_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__7));
v___x_67_ = lean_box(2);
v___x_68_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
lean_ctor_set(v___x_68_, 2, v___x_65_);
return v___x_68_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__25(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__24, &l_Std_DTreeMap_Raw___auto__1___closed__24_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__24);
v___x_70_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_71_ = lean_array_push(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__26(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_72_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
v___x_73_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__4));
v___x_74_ = lean_box(2);
v___x_75_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
lean_ctor_set(v___x_75_, 2, v___x_72_);
return v___x_75_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1(void){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_cmp_79_, lean_object* v_t_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(0);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner___boxed(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_cmp_84_, lean_object* v_t_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_DTreeMap_Raw_instCoeWFWFInner(v_00_u03b1_82_, v_00_u03b2_83_, v_cmp_84_, v_t_85_);
lean_dec(v_t_85_);
lean_dec_ref(v_cmp_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_cmp_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(1);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___boxed(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_cmp_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_DTreeMap_Raw_empty(v_00_u03b1_91_, v_00_u03b2_92_, v_cmp_93_);
lean_dec_ref(v_cmp_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_cmp_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_box(1);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___boxed(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_cmp_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_DTreeMap_Raw_instEmptyCollection(v_00_u03b1_99_, v_00_u03b2_100_, v_cmp_101_);
lean_dec_ref(v_cmp_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited(lean_object* v_00_u03b1_103_, lean_object* v_00_u03b2_104_, lean_object* v_cmp_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(1);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited___boxed(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_cmp_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_DTreeMap_Raw_instInhabited(v_00_u03b1_107_, v_00_u03b2_108_, v_cmp_109_);
lean_dec_ref(v_cmp_109_);
return v_res_110_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__3));
v___x_151_ = l_String_toRawSubstring_x27(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1(lean_object* v_x_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_170_);
v___x_174_ = l_Lean_Syntax_isOfKind(v_x_170_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_x_170_);
v___x_175_ = lean_box(1);
v___x_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_a_172_);
return v___x_176_;
}
else
{
lean_object* v_quotContext_177_; lean_object* v_currMacroScope_178_; lean_object* v_ref_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_quotContext_177_ = lean_ctor_get(v_a_171_, 1);
v_currMacroScope_178_ = lean_ctor_get(v_a_171_, 2);
v_ref_179_ = lean_ctor_get(v_a_171_, 5);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = l_Lean_Syntax_getArg(v_x_170_, v___x_180_);
v___x_182_ = lean_unsigned_to_nat(2u);
v___x_183_ = l_Lean_Syntax_getArg(v_x_170_, v___x_182_);
lean_dec(v_x_170_);
v___x_184_ = 0;
v___x_185_ = l_Lean_SourceInfo_fromRef(v_ref_179_, v___x_184_);
v___x_186_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2));
v___x_187_ = lean_obj_once(&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4, &l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4_once, _init_l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4);
v___x_188_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_178_);
lean_inc(v_quotContext_177_);
v___x_189_ = l_Lean_addMacroScope(v_quotContext_177_, v___x_188_, v_currMacroScope_178_);
v___x_190_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__10));
lean_inc_n(v___x_185_, 2);
v___x_191_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_191_, 0, v___x_185_);
lean_ctor_set(v___x_191_, 1, v___x_187_);
lean_ctor_set(v___x_191_, 2, v___x_189_);
lean_ctor_set(v___x_191_, 3, v___x_190_);
v___x_192_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__9));
v___x_193_ = l_Lean_Syntax_node2(v___x_185_, v___x_192_, v___x_181_, v___x_183_);
v___x_194_ = l_Lean_Syntax_node2(v___x_185_, v___x_186_, v___x_191_, v___x_193_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_a_172_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___boxed(lean_object* v_x_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1(v_x_196_, v_a_197_, v_a_198_);
lean_dec_ref(v_a_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1(lean_object* v_x_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2));
lean_inc(v_x_203_);
v___x_207_ = l_Lean_Syntax_isOfKind(v_x_203_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec(v_x_203_);
v___x_208_ = lean_box(0);
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v_a_205_);
return v___x_209_;
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = l_Lean_Syntax_getArg(v_x_203_, v___x_210_);
v___x_212_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_211_);
v___x_213_ = l_Lean_Syntax_isOfKind(v___x_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v___x_211_);
lean_dec(v_x_203_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v_a_205_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = l_Lean_Syntax_getArg(v_x_203_, v___x_216_);
lean_dec(v_x_203_);
v___x_218_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_217_);
v___x_219_ = l_Lean_Syntax_matchesNull(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v___x_217_);
lean_dec(v___x_211_);
v___x_220_ = lean_box(0);
v___x_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v_a_205_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_ref_224_; uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_222_ = l_Lean_Syntax_getArg(v___x_217_, v___x_210_);
v___x_223_ = l_Lean_Syntax_getArg(v___x_217_, v___x_216_);
lean_dec(v___x_217_);
v_ref_224_ = l_Lean_replaceRef(v___x_211_, v_a_204_);
lean_dec(v___x_211_);
v___x_225_ = 0;
v___x_226_ = l_Lean_SourceInfo_fromRef(v_ref_224_, v___x_225_);
lean_dec(v_ref_224_);
v___x_227_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__4));
v___x_228_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_226_);
v___x_229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_226_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = l_Lean_Syntax_node3(v___x_226_, v___x_227_, v___x_222_, v___x_229_, v___x_223_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_a_205_);
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___boxed(lean_object* v_x_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1(v_x_232_, v_a_233_, v_a_234_);
lean_dec(v_a_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insert___redArg(lean_object* v_cmp_236_, lean_object* v_t_237_, lean_object* v_a_238_, lean_object* v_b_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_236_, v_a_238_, v_b_239_, v_t_237_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insert(lean_object* v_00_u03b1_241_, lean_object* v_00_u03b2_242_, lean_object* v_cmp_243_, lean_object* v_t_244_, lean_object* v_a_245_, lean_object* v_b_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_243_, v_a_245_, v_b_246_, v_t_244_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0(lean_object* v_cmp_248_, lean_object* v_e_249_){
_start:
{
lean_object* v_fst_250_; lean_object* v_snd_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_fst_250_ = lean_ctor_get(v_e_249_, 0);
lean_inc(v_fst_250_);
v_snd_251_ = lean_ctor_get(v_e_249_, 1);
lean_inc(v_snd_251_);
lean_dec_ref(v_e_249_);
v___x_252_ = lean_box(1);
v___x_253_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_248_, v_fst_250_, v_snd_251_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma___redArg(lean_object* v_cmp_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_255_, 0, v_cmp_254_);
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_cmp_258_){
_start:
{
lean_object* v___f_259_; 
v___f_259_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_259_, 0, v_cmp_258_);
return v___f_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0(lean_object* v_cmp_260_, lean_object* v_e_261_, lean_object* v_s_262_){
_start:
{
lean_object* v_fst_263_; lean_object* v_snd_264_; lean_object* v___x_265_; 
v_fst_263_ = lean_ctor_get(v_e_261_, 0);
lean_inc(v_fst_263_);
v_snd_264_ = lean_ctor_get(v_e_261_, 1);
lean_inc(v_snd_264_);
lean_dec_ref(v_e_261_);
v___x_265_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_260_, v_fst_263_, v_snd_264_, v_s_262_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma___redArg(lean_object* v_cmp_266_){
_start:
{
lean_object* v___f_267_; 
v___f_267_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_267_, 0, v_cmp_266_);
return v___f_267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma(lean_object* v_00_u03b1_268_, lean_object* v_00_u03b2_269_, lean_object* v_cmp_270_){
_start:
{
lean_object* v___f_271_; 
v___f_271_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_271_, 0, v_cmp_270_);
return v___f_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertIfNew___redArg(lean_object* v_cmp_272_, lean_object* v_t_273_, lean_object* v_a_274_, lean_object* v_b_275_){
_start:
{
uint8_t v___x_276_; 
lean_inc(v_t_273_);
lean_inc(v_a_274_);
lean_inc_ref(v_cmp_272_);
v___x_276_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_272_, v_a_274_, v_t_273_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_272_, v_a_274_, v_b_275_, v_t_273_);
return v___x_277_;
}
else
{
lean_dec(v_b_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_cmp_272_);
return v_t_273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertIfNew(lean_object* v_00_u03b1_278_, lean_object* v_00_u03b2_279_, lean_object* v_cmp_280_, lean_object* v_t_281_, lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
uint8_t v___x_284_; 
lean_inc(v_t_281_);
lean_inc(v_a_282_);
lean_inc_ref(v_cmp_280_);
v___x_284_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_280_, v_a_282_, v_t_281_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; 
v___x_285_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_280_, v_a_282_, v_b_283_, v_t_281_);
return v___x_285_;
}
else
{
lean_dec(v_b_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_cmp_280_);
return v_t_281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsert___redArg(lean_object* v_cmp_286_, lean_object* v_t_287_, lean_object* v_a_288_, lean_object* v_b_289_){
_start:
{
lean_object* v_sz_290_; lean_object* v_m_291_; lean_object* v___y_293_; 
v_sz_290_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_287_);
v_m_291_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_286_, v_a_288_, v_b_289_, v_t_287_);
if (lean_obj_tag(v_m_291_) == 0)
{
lean_object* v_size_297_; 
v_size_297_ = lean_ctor_get(v_m_291_, 0);
lean_inc(v_size_297_);
v___y_293_ = v_size_297_;
goto v___jp_292_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___y_293_ = v___x_298_;
goto v___jp_292_;
}
v___jp_292_:
{
uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_nat_dec_eq(v_sz_290_, v___y_293_);
lean_dec(v___y_293_);
lean_dec(v_sz_290_);
v___x_295_ = lean_box(v___x_294_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v_m_291_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsert(lean_object* v_00_u03b1_299_, lean_object* v_00_u03b2_300_, lean_object* v_cmp_301_, lean_object* v_t_302_, lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
lean_object* v_sz_305_; lean_object* v_m_306_; lean_object* v___y_308_; 
v_sz_305_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_302_);
v_m_306_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_301_, v_a_303_, v_b_304_, v_t_302_);
if (lean_obj_tag(v_m_306_) == 0)
{
lean_object* v_size_312_; 
v_size_312_ = lean_ctor_get(v_m_306_, 0);
lean_inc(v_size_312_);
v___y_308_ = v_size_312_;
goto v___jp_307_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___y_308_ = v___x_313_;
goto v___jp_307_;
}
v___jp_307_:
{
uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_nat_dec_eq(v_sz_305_, v___y_308_);
lean_dec(v___y_308_);
lean_dec(v_sz_305_);
v___x_310_ = lean_box(v___x_309_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_m_306_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_cmp_314_, lean_object* v_t_315_, lean_object* v_a_316_, lean_object* v_b_317_){
_start:
{
uint8_t v___x_318_; 
lean_inc(v_t_315_);
lean_inc(v_a_316_);
lean_inc_ref(v_cmp_314_);
v___x_318_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_314_, v_a_316_, v_t_315_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_314_, v_a_316_, v_b_317_, v_t_315_);
v___x_320_ = lean_box(v___x_318_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec(v_b_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_cmp_314_);
v___x_322_ = lean_box(v___x_318_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_t_315_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_324_, lean_object* v_00_u03b2_325_, lean_object* v_cmp_326_, lean_object* v_t_327_, lean_object* v_a_328_, lean_object* v_b_329_){
_start:
{
uint8_t v___x_330_; 
lean_inc(v_t_327_);
lean_inc(v_a_328_);
lean_inc_ref(v_cmp_326_);
v___x_330_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_326_, v_a_328_, v_t_327_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_326_, v_a_328_, v_b_329_, v_t_327_);
v___x_332_ = lean_box(v___x_330_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec(v_b_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_cmp_326_);
v___x_334_ = lean_box(v___x_330_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_t_327_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_336_, lean_object* v_t_337_, lean_object* v_a_338_, lean_object* v_b_339_){
_start:
{
lean_object* v___x_340_; 
lean_inc(v_a_338_);
lean_inc(v_t_337_);
lean_inc_ref(v_cmp_336_);
v___x_340_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_336_, v_t_337_, v_a_338_);
if (lean_obj_tag(v___x_340_) == 0)
{
uint8_t v___x_341_; 
lean_inc(v_t_337_);
lean_inc(v_a_338_);
lean_inc_ref(v_cmp_336_);
v___x_341_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_336_, v_a_338_, v_t_337_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_336_, v_a_338_, v_b_339_, v_t_337_);
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
lean_dec_ref(v_cmp_336_);
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
lean_dec_ref(v_cmp_336_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_340_);
lean_ctor_set(v___x_345_, 1, v_t_337_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_cmp_348_, lean_object* v_inst_349_, lean_object* v_t_350_, lean_object* v_a_351_, lean_object* v_b_352_){
_start:
{
lean_object* v___x_353_; 
lean_inc(v_a_351_);
lean_inc(v_t_350_);
lean_inc_ref(v_cmp_348_);
v___x_353_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_348_, v_t_350_, v_a_351_);
if (lean_obj_tag(v___x_353_) == 0)
{
uint8_t v___x_354_; 
lean_inc(v_t_350_);
lean_inc(v_a_351_);
lean_inc_ref(v_cmp_348_);
v___x_354_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_348_, v_a_351_, v_t_350_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_348_, v_a_351_, v_b_352_, v_t_350_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_353_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; 
lean_dec(v_b_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_cmp_348_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_353_);
lean_ctor_set(v___x_357_, 1, v_t_350_);
return v___x_357_;
}
}
else
{
lean_object* v___x_358_; 
lean_dec(v_b_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_cmp_348_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_353_);
lean_ctor_set(v___x_358_, 1, v_t_350_);
return v___x_358_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_contains___redArg(lean_object* v_cmp_359_, lean_object* v_t_360_, lean_object* v_a_361_){
_start:
{
uint8_t v___x_362_; 
v___x_362_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_359_, v_a_361_, v_t_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_contains___redArg___boxed(lean_object* v_cmp_363_, lean_object* v_t_364_, lean_object* v_a_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Std_DTreeMap_Raw_contains___redArg(v_cmp_363_, v_t_364_, v_a_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_contains(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_cmp_370_, lean_object* v_t_371_, lean_object* v_a_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_370_, v_a_372_, v_t_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_contains___boxed(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_cmp_376_, lean_object* v_t_377_, lean_object* v_a_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = l_Std_DTreeMap_Raw_contains(v_00_u03b1_374_, v_00_u03b2_375_, v_cmp_376_, v_t_377_, v_a_378_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership(lean_object* v_00_u03b1_381_, lean_object* v_00_u03b2_382_, lean_object* v_cmp_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_box(0);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___boxed(lean_object* v_00_u03b1_385_, lean_object* v_00_u03b2_386_, lean_object* v_cmp_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_DTreeMap_Raw_instMembership(v_00_u03b1_385_, v_00_u03b2_386_, v_cmp_387_);
lean_dec_ref(v_cmp_387_);
return v_res_388_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableMem___redArg(lean_object* v_cmp_389_, lean_object* v_t_390_, lean_object* v_a_391_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_389_, v_a_391_, v_t_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_393_, lean_object* v_t_394_, lean_object* v_a_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Std_DTreeMap_Raw_instDecidableMem___redArg(v_cmp_393_, v_t_394_, v_a_395_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableMem(lean_object* v_00_u03b1_398_, lean_object* v_00_u03b2_399_, lean_object* v_cmp_400_, lean_object* v_t_401_, lean_object* v_a_402_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_400_, v_a_402_, v_t_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_404_, lean_object* v_00_u03b2_405_, lean_object* v_cmp_406_, lean_object* v_t_407_, lean_object* v_a_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l_Std_DTreeMap_Raw_instDecidableMem(v_00_u03b1_404_, v_00_u03b2_405_, v_cmp_406_, v_t_407_, v_a_408_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___redArg(lean_object* v_t_411_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___redArg___boxed(lean_object* v_t_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_DTreeMap_Raw_size___redArg(v_t_414_);
lean_dec(v_t_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size(lean_object* v_00_u03b1_416_, lean_object* v_00_u03b2_417_, lean_object* v_cmp_418_, lean_object* v_t_419_){
_start:
{
if (lean_obj_tag(v_t_419_) == 0)
{
lean_object* v_size_420_; 
v_size_420_ = lean_ctor_get(v_t_419_, 0);
lean_inc(v_size_420_);
return v_size_420_;
}
else
{
lean_object* v___x_421_; 
v___x_421_ = lean_unsigned_to_nat(0u);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___boxed(lean_object* v_00_u03b1_422_, lean_object* v_00_u03b2_423_, lean_object* v_cmp_424_, lean_object* v_t_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_DTreeMap_Raw_size(v_00_u03b1_422_, v_00_u03b2_423_, v_cmp_424_, v_t_425_);
lean_dec(v_t_425_);
lean_dec_ref(v_cmp_424_);
return v_res_426_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_isEmpty___redArg(lean_object* v_t_427_){
_start:
{
if (lean_obj_tag(v_t_427_) == 0)
{
uint8_t v___x_428_; 
v___x_428_ = 0;
return v___x_428_;
}
else
{
uint8_t v___x_429_; 
v___x_429_ = 1;
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_isEmpty___redArg___boxed(lean_object* v_t_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_Std_DTreeMap_Raw_isEmpty___redArg(v_t_430_);
lean_dec(v_t_430_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_isEmpty(lean_object* v_00_u03b1_433_, lean_object* v_00_u03b2_434_, lean_object* v_cmp_435_, lean_object* v_t_436_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_439_, lean_object* v_00_u03b2_440_, lean_object* v_cmp_441_, lean_object* v_t_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Std_DTreeMap_Raw_isEmpty(v_00_u03b1_439_, v_00_u03b2_440_, v_cmp_441_, v_t_442_);
lean_dec(v_t_442_);
lean_dec_ref(v_cmp_441_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_erase___redArg(lean_object* v_cmp_445_, lean_object* v_t_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_445_, v_a_447_, v_t_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_erase(lean_object* v_00_u03b1_449_, lean_object* v_00_u03b2_450_, lean_object* v_cmp_451_, lean_object* v_t_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_451_, v_a_453_, v_t_452_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x3f___redArg(lean_object* v_cmp_455_, lean_object* v_t_456_, lean_object* v_a_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_455_, v_t_456_, v_a_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x3f(lean_object* v_00_u03b1_459_, lean_object* v_00_u03b2_460_, lean_object* v_cmp_461_, lean_object* v_inst_462_, lean_object* v_t_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_461_, v_t_463_, v_a_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get___redArg(lean_object* v_cmp_466_, lean_object* v_t_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_466_, v_t_467_, v_a_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get(lean_object* v_00_u03b1_470_, lean_object* v_00_u03b2_471_, lean_object* v_cmp_472_, lean_object* v_inst_473_, lean_object* v_t_474_, lean_object* v_a_475_, lean_object* v_h_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_472_, v_t_474_, v_a_475_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___redArg(lean_object* v_cmp_478_, lean_object* v_t_479_, lean_object* v_a_480_, lean_object* v_inst_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_478_, v_t_479_, v_a_480_, v_inst_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___redArg___boxed(lean_object* v_cmp_483_, lean_object* v_t_484_, lean_object* v_a_485_, lean_object* v_inst_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_DTreeMap_Raw_get_x21___redArg(v_cmp_483_, v_t_484_, v_a_485_, v_inst_486_);
lean_dec(v_inst_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21(lean_object* v_00_u03b1_488_, lean_object* v_00_u03b2_489_, lean_object* v_cmp_490_, lean_object* v_inst_491_, lean_object* v_t_492_, lean_object* v_a_493_, lean_object* v_inst_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_490_, v_t_492_, v_a_493_, v_inst_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_496_, lean_object* v_00_u03b2_497_, lean_object* v_cmp_498_, lean_object* v_inst_499_, lean_object* v_t_500_, lean_object* v_a_501_, lean_object* v_inst_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_DTreeMap_Raw_get_x21(v_00_u03b1_496_, v_00_u03b2_497_, v_cmp_498_, v_inst_499_, v_t_500_, v_a_501_, v_inst_502_);
lean_dec(v_inst_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg(lean_object* v_cmp_504_, lean_object* v_t_505_, lean_object* v_a_506_, lean_object* v_fallback_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_504_, v_t_505_, v_a_506_, v_fallback_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg___boxed(lean_object* v_cmp_509_, lean_object* v_t_510_, lean_object* v_a_511_, lean_object* v_fallback_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_DTreeMap_Raw_getD___redArg(v_cmp_509_, v_t_510_, v_a_511_, v_fallback_512_);
lean_dec(v_fallback_512_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD(lean_object* v_00_u03b1_514_, lean_object* v_00_u03b2_515_, lean_object* v_cmp_516_, lean_object* v_inst_517_, lean_object* v_t_518_, lean_object* v_a_519_, lean_object* v_fallback_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_516_, v_t_518_, v_a_519_, v_fallback_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___boxed(lean_object* v_00_u03b1_522_, lean_object* v_00_u03b2_523_, lean_object* v_cmp_524_, lean_object* v_inst_525_, lean_object* v_t_526_, lean_object* v_a_527_, lean_object* v_fallback_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_DTreeMap_Raw_getD(v_00_u03b1_522_, v_00_u03b2_523_, v_cmp_524_, v_inst_525_, v_t_526_, v_a_527_, v_fallback_528_);
lean_dec(v_fallback_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f___redArg(lean_object* v_cmp_530_, lean_object* v_t_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_530_, v_t_531_, v_a_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f(lean_object* v_00_u03b1_534_, lean_object* v_00_u03b2_535_, lean_object* v_cmp_536_, lean_object* v_t_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_536_, v_t_537_, v_a_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry___redArg(lean_object* v_cmp_540_, lean_object* v_t_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_540_, v_t_541_, v_a_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry(lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_, lean_object* v_cmp_546_, lean_object* v_inst_547_, lean_object* v_t_548_, lean_object* v_a_549_, lean_object* v_h_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_546_, v_t_548_, v_a_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___redArg(lean_object* v_cmp_552_, lean_object* v_inst_553_, lean_object* v_t_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_552_, v_inst_553_, v_t_554_, v_a_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___redArg___boxed(lean_object* v_cmp_557_, lean_object* v_inst_558_, lean_object* v_t_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DTreeMap_Raw_getEntry_x21___redArg(v_cmp_557_, v_inst_558_, v_t_559_, v_a_560_);
lean_dec_ref(v_inst_558_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21(lean_object* v_00_u03b1_562_, lean_object* v_00_u03b2_563_, lean_object* v_cmp_564_, lean_object* v_inst_565_, lean_object* v_t_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_564_, v_inst_565_, v_t_566_, v_a_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___boxed(lean_object* v_00_u03b1_569_, lean_object* v_00_u03b2_570_, lean_object* v_cmp_571_, lean_object* v_inst_572_, lean_object* v_t_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_DTreeMap_Raw_getEntry_x21(v_00_u03b1_569_, v_00_u03b2_570_, v_cmp_571_, v_inst_572_, v_t_573_, v_a_574_);
lean_dec_ref(v_inst_572_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg(lean_object* v_cmp_576_, lean_object* v_t_577_, lean_object* v_a_578_, lean_object* v_fallback_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_576_, v_t_577_, v_a_578_, v_fallback_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg___boxed(lean_object* v_cmp_581_, lean_object* v_t_582_, lean_object* v_a_583_, lean_object* v_fallback_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DTreeMap_Raw_getEntryD___redArg(v_cmp_581_, v_t_582_, v_a_583_, v_fallback_584_);
lean_dec_ref(v_fallback_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD(lean_object* v_00_u03b1_586_, lean_object* v_00_u03b2_587_, lean_object* v_cmp_588_, lean_object* v_t_589_, lean_object* v_a_590_, lean_object* v_fallback_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_588_, v_t_589_, v_a_590_, v_fallback_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___boxed(lean_object* v_00_u03b1_593_, lean_object* v_00_u03b2_594_, lean_object* v_cmp_595_, lean_object* v_t_596_, lean_object* v_a_597_, lean_object* v_fallback_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_DTreeMap_Raw_getEntryD(v_00_u03b1_593_, v_00_u03b2_594_, v_cmp_595_, v_t_596_, v_a_597_, v_fallback_598_);
lean_dec_ref(v_fallback_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f___redArg(lean_object* v_cmp_600_, lean_object* v_t_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_600_, v_t_601_, v_a_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f(lean_object* v_00_u03b1_604_, lean_object* v_00_u03b2_605_, lean_object* v_cmp_606_, lean_object* v_t_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_606_, v_t_607_, v_a_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey___redArg(lean_object* v_cmp_610_, lean_object* v_t_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_610_, v_t_611_, v_a_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey(lean_object* v_00_u03b1_614_, lean_object* v_00_u03b2_615_, lean_object* v_cmp_616_, lean_object* v_t_617_, lean_object* v_a_618_, lean_object* v_h_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_616_, v_t_617_, v_a_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___redArg(lean_object* v_cmp_621_, lean_object* v_inst_622_, lean_object* v_t_623_, lean_object* v_a_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_621_, v_t_623_, v_a_624_, v_inst_622_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___redArg___boxed(lean_object* v_cmp_626_, lean_object* v_inst_627_, lean_object* v_t_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_DTreeMap_Raw_getKey_x21___redArg(v_cmp_626_, v_inst_627_, v_t_628_, v_a_629_);
lean_dec(v_inst_627_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21(lean_object* v_00_u03b1_631_, lean_object* v_00_u03b2_632_, lean_object* v_cmp_633_, lean_object* v_inst_634_, lean_object* v_t_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_633_, v_t_635_, v_a_636_, v_inst_634_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_638_, lean_object* v_00_u03b2_639_, lean_object* v_cmp_640_, lean_object* v_inst_641_, lean_object* v_t_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Std_DTreeMap_Raw_getKey_x21(v_00_u03b1_638_, v_00_u03b2_639_, v_cmp_640_, v_inst_641_, v_t_642_, v_a_643_);
lean_dec(v_inst_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___redArg(lean_object* v_cmp_645_, lean_object* v_t_646_, lean_object* v_a_647_, lean_object* v_fallback_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_645_, v_t_646_, v_a_647_, v_fallback_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___redArg___boxed(lean_object* v_cmp_650_, lean_object* v_t_651_, lean_object* v_a_652_, lean_object* v_fallback_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_DTreeMap_Raw_getKeyD___redArg(v_cmp_650_, v_t_651_, v_a_652_, v_fallback_653_);
lean_dec(v_fallback_653_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD(lean_object* v_00_u03b1_655_, lean_object* v_00_u03b2_656_, lean_object* v_cmp_657_, lean_object* v_t_658_, lean_object* v_a_659_, lean_object* v_fallback_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_657_, v_t_658_, v_a_659_, v_fallback_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_cmp_664_, lean_object* v_t_665_, lean_object* v_a_666_, lean_object* v_fallback_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_DTreeMap_Raw_getKeyD(v_00_u03b1_662_, v_00_u03b2_663_, v_cmp_664_, v_t_665_, v_a_666_, v_fallback_667_);
lean_dec(v_fallback_667_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___redArg(lean_object* v_t_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___redArg___boxed(lean_object* v_t_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Std_DTreeMap_Raw_minEntry_x3f___redArg(v_t_671_);
lean_dec(v_t_671_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f(lean_object* v_00_u03b1_673_, lean_object* v_00_u03b2_674_, lean_object* v_cmp_675_, lean_object* v_t_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___boxed(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_cmp_680_, lean_object* v_t_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Std_DTreeMap_Raw_minEntry_x3f(v_00_u03b1_678_, v_00_u03b2_679_, v_cmp_680_, v_t_681_);
lean_dec(v_t_681_);
lean_dec_ref(v_cmp_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___redArg(lean_object* v_inst_683_, lean_object* v_t_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_683_, v_t_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___redArg___boxed(lean_object* v_inst_686_, lean_object* v_t_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Std_DTreeMap_Raw_minEntry_x21___redArg(v_inst_686_, v_t_687_);
lean_dec(v_t_687_);
lean_dec_ref(v_inst_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21(lean_object* v_00_u03b1_689_, lean_object* v_00_u03b2_690_, lean_object* v_cmp_691_, lean_object* v_inst_692_, lean_object* v_t_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_692_, v_t_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___boxed(lean_object* v_00_u03b1_695_, lean_object* v_00_u03b2_696_, lean_object* v_cmp_697_, lean_object* v_inst_698_, lean_object* v_t_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Std_DTreeMap_Raw_minEntry_x21(v_00_u03b1_695_, v_00_u03b2_696_, v_cmp_697_, v_inst_698_, v_t_699_);
lean_dec(v_t_699_);
lean_dec_ref(v_inst_698_);
lean_dec_ref(v_cmp_697_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___redArg(lean_object* v_t_701_, lean_object* v_fallback_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_701_, v_fallback_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___redArg___boxed(lean_object* v_t_704_, lean_object* v_fallback_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_DTreeMap_Raw_minEntryD___redArg(v_t_704_, v_fallback_705_);
lean_dec_ref(v_fallback_705_);
lean_dec(v_t_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD(lean_object* v_00_u03b1_707_, lean_object* v_00_u03b2_708_, lean_object* v_cmp_709_, lean_object* v_t_710_, lean_object* v_fallback_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_710_, v_fallback_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___boxed(lean_object* v_00_u03b1_713_, lean_object* v_00_u03b2_714_, lean_object* v_cmp_715_, lean_object* v_t_716_, lean_object* v_fallback_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_DTreeMap_Raw_minEntryD(v_00_u03b1_713_, v_00_u03b2_714_, v_cmp_715_, v_t_716_, v_fallback_717_);
lean_dec_ref(v_fallback_717_);
lean_dec(v_t_716_);
lean_dec_ref(v_cmp_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___redArg(lean_object* v_t_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___redArg___boxed(lean_object* v_t_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_DTreeMap_Raw_maxEntry_x3f___redArg(v_t_721_);
lean_dec(v_t_721_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_cmp_725_, lean_object* v_t_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___boxed(lean_object* v_00_u03b1_728_, lean_object* v_00_u03b2_729_, lean_object* v_cmp_730_, lean_object* v_t_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Std_DTreeMap_Raw_maxEntry_x3f(v_00_u03b1_728_, v_00_u03b2_729_, v_cmp_730_, v_t_731_);
lean_dec(v_t_731_);
lean_dec_ref(v_cmp_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___redArg(lean_object* v_inst_733_, lean_object* v_t_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_733_, v_t_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___redArg___boxed(lean_object* v_inst_736_, lean_object* v_t_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_DTreeMap_Raw_maxEntry_x21___redArg(v_inst_736_, v_t_737_);
lean_dec(v_t_737_);
lean_dec_ref(v_inst_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21(lean_object* v_00_u03b1_739_, lean_object* v_00_u03b2_740_, lean_object* v_cmp_741_, lean_object* v_inst_742_, lean_object* v_t_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_742_, v_t_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___boxed(lean_object* v_00_u03b1_745_, lean_object* v_00_u03b2_746_, lean_object* v_cmp_747_, lean_object* v_inst_748_, lean_object* v_t_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_DTreeMap_Raw_maxEntry_x21(v_00_u03b1_745_, v_00_u03b2_746_, v_cmp_747_, v_inst_748_, v_t_749_);
lean_dec(v_t_749_);
lean_dec_ref(v_inst_748_);
lean_dec_ref(v_cmp_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___redArg(lean_object* v_t_751_, lean_object* v_fallback_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_751_, v_fallback_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___redArg___boxed(lean_object* v_t_754_, lean_object* v_fallback_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_DTreeMap_Raw_maxEntryD___redArg(v_t_754_, v_fallback_755_);
lean_dec_ref(v_fallback_755_);
lean_dec(v_t_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD(lean_object* v_00_u03b1_757_, lean_object* v_00_u03b2_758_, lean_object* v_cmp_759_, lean_object* v_t_760_, lean_object* v_fallback_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_760_, v_fallback_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___boxed(lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_cmp_765_, lean_object* v_t_766_, lean_object* v_fallback_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_DTreeMap_Raw_maxEntryD(v_00_u03b1_763_, v_00_u03b2_764_, v_cmp_765_, v_t_766_, v_fallback_767_);
lean_dec_ref(v_fallback_767_);
lean_dec(v_t_766_);
lean_dec_ref(v_cmp_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___redArg(lean_object* v_t_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___redArg___boxed(lean_object* v_t_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_DTreeMap_Raw_minKey_x3f___redArg(v_t_771_);
lean_dec(v_t_771_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f(lean_object* v_00_u03b1_773_, lean_object* v_00_u03b2_774_, lean_object* v_cmp_775_, lean_object* v_t_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___boxed(lean_object* v_00_u03b1_778_, lean_object* v_00_u03b2_779_, lean_object* v_cmp_780_, lean_object* v_t_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Std_DTreeMap_Raw_minKey_x3f(v_00_u03b1_778_, v_00_u03b2_779_, v_cmp_780_, v_t_781_);
lean_dec(v_t_781_);
lean_dec_ref(v_cmp_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___redArg(lean_object* v_t_783_, lean_object* v_fallback_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_783_, v_fallback_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___redArg___boxed(lean_object* v_t_786_, lean_object* v_fallback_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_DTreeMap_Raw_minKeyD___redArg(v_t_786_, v_fallback_787_);
lean_dec(v_fallback_787_);
lean_dec(v_t_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD(lean_object* v_00_u03b1_789_, lean_object* v_00_u03b2_790_, lean_object* v_cmp_791_, lean_object* v_t_792_, lean_object* v_fallback_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_792_, v_fallback_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___boxed(lean_object* v_00_u03b1_795_, lean_object* v_00_u03b2_796_, lean_object* v_cmp_797_, lean_object* v_t_798_, lean_object* v_fallback_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_DTreeMap_Raw_minKeyD(v_00_u03b1_795_, v_00_u03b2_796_, v_cmp_797_, v_t_798_, v_fallback_799_);
lean_dec(v_fallback_799_);
lean_dec(v_t_798_);
lean_dec_ref(v_cmp_797_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___redArg(lean_object* v_inst_801_, lean_object* v_t_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_801_, v_t_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___redArg___boxed(lean_object* v_inst_804_, lean_object* v_t_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_DTreeMap_Raw_minKey_x21___redArg(v_inst_804_, v_t_805_);
lean_dec(v_t_805_);
lean_dec(v_inst_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21(lean_object* v_00_u03b1_807_, lean_object* v_00_u03b2_808_, lean_object* v_cmp_809_, lean_object* v_inst_810_, lean_object* v_t_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_810_, v_t_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___boxed(lean_object* v_00_u03b1_813_, lean_object* v_00_u03b2_814_, lean_object* v_cmp_815_, lean_object* v_inst_816_, lean_object* v_t_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_DTreeMap_Raw_minKey_x21(v_00_u03b1_813_, v_00_u03b2_814_, v_cmp_815_, v_inst_816_, v_t_817_);
lean_dec(v_t_817_);
lean_dec(v_inst_816_);
lean_dec_ref(v_cmp_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___redArg(lean_object* v_t_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___redArg___boxed(lean_object* v_t_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DTreeMap_Raw_maxKey_x3f___redArg(v_t_821_);
lean_dec(v_t_821_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f(lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_cmp_825_, lean_object* v_t_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___boxed(lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_cmp_830_, lean_object* v_t_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_DTreeMap_Raw_maxKey_x3f(v_00_u03b1_828_, v_00_u03b2_829_, v_cmp_830_, v_t_831_);
lean_dec(v_t_831_);
lean_dec_ref(v_cmp_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___redArg(lean_object* v_inst_833_, lean_object* v_t_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_833_, v_t_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___redArg___boxed(lean_object* v_inst_836_, lean_object* v_t_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_DTreeMap_Raw_maxKey_x21___redArg(v_inst_836_, v_t_837_);
lean_dec(v_t_837_);
lean_dec(v_inst_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21(lean_object* v_00_u03b1_839_, lean_object* v_00_u03b2_840_, lean_object* v_cmp_841_, lean_object* v_inst_842_, lean_object* v_t_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_842_, v_t_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___boxed(lean_object* v_00_u03b1_845_, lean_object* v_00_u03b2_846_, lean_object* v_cmp_847_, lean_object* v_inst_848_, lean_object* v_t_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_DTreeMap_Raw_maxKey_x21(v_00_u03b1_845_, v_00_u03b2_846_, v_cmp_847_, v_inst_848_, v_t_849_);
lean_dec(v_t_849_);
lean_dec(v_inst_848_);
lean_dec_ref(v_cmp_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___redArg(lean_object* v_t_851_, lean_object* v_fallback_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_851_, v_fallback_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___redArg___boxed(lean_object* v_t_854_, lean_object* v_fallback_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DTreeMap_Raw_maxKeyD___redArg(v_t_854_, v_fallback_855_);
lean_dec(v_fallback_855_);
lean_dec(v_t_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD(lean_object* v_00_u03b1_857_, lean_object* v_00_u03b2_858_, lean_object* v_cmp_859_, lean_object* v_t_860_, lean_object* v_fallback_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_860_, v_fallback_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___boxed(lean_object* v_00_u03b1_863_, lean_object* v_00_u03b2_864_, lean_object* v_cmp_865_, lean_object* v_t_866_, lean_object* v_fallback_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_DTreeMap_Raw_maxKeyD(v_00_u03b1_863_, v_00_u03b2_864_, v_cmp_865_, v_t_866_, v_fallback_867_);
lean_dec(v_fallback_867_);
lean_dec(v_t_866_);
lean_dec_ref(v_cmp_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg(lean_object* v_t_869_, lean_object* v_n_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_869_, v_n_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_872_, lean_object* v_n_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg(v_t_872_, v_n_873_);
lean_dec(v_t_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f(lean_object* v_00_u03b1_875_, lean_object* v_00_u03b2_876_, lean_object* v_cmp_877_, lean_object* v_t_878_, lean_object* v_n_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_878_, v_n_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_cmp_883_, lean_object* v_t_884_, lean_object* v_n_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Std_DTreeMap_Raw_entryAtIdx_x3f(v_00_u03b1_881_, v_00_u03b2_882_, v_cmp_883_, v_t_884_, v_n_885_);
lean_dec(v_t_884_);
lean_dec_ref(v_cmp_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg(lean_object* v_inst_887_, lean_object* v_t_888_, lean_object* v_n_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_887_, v_t_888_, v_n_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_891_, lean_object* v_t_892_, lean_object* v_n_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg(v_inst_891_, v_t_892_, v_n_893_);
lean_dec(v_t_892_);
lean_dec_ref(v_inst_891_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21(lean_object* v_00_u03b1_895_, lean_object* v_00_u03b2_896_, lean_object* v_cmp_897_, lean_object* v_inst_898_, lean_object* v_t_899_, lean_object* v_n_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_898_, v_t_899_, v_n_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_cmp_904_, lean_object* v_inst_905_, lean_object* v_t_906_, lean_object* v_n_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_DTreeMap_Raw_entryAtIdx_x21(v_00_u03b1_902_, v_00_u03b2_903_, v_cmp_904_, v_inst_905_, v_t_906_, v_n_907_);
lean_dec(v_t_906_);
lean_dec_ref(v_inst_905_);
lean_dec_ref(v_cmp_904_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___redArg(lean_object* v_t_909_, lean_object* v_n_910_, lean_object* v_fallback_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_909_, v_n_910_, v_fallback_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___redArg___boxed(lean_object* v_t_913_, lean_object* v_n_914_, lean_object* v_fallback_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Std_DTreeMap_Raw_entryAtIdxD___redArg(v_t_913_, v_n_914_, v_fallback_915_);
lean_dec_ref(v_fallback_915_);
lean_dec(v_t_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD(lean_object* v_00_u03b1_917_, lean_object* v_00_u03b2_918_, lean_object* v_cmp_919_, lean_object* v_t_920_, lean_object* v_n_921_, lean_object* v_fallback_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_920_, v_n_921_, v_fallback_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___boxed(lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_cmp_926_, lean_object* v_t_927_, lean_object* v_n_928_, lean_object* v_fallback_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Std_DTreeMap_Raw_entryAtIdxD(v_00_u03b1_924_, v_00_u03b2_925_, v_cmp_926_, v_t_927_, v_n_928_, v_fallback_929_);
lean_dec_ref(v_fallback_929_);
lean_dec(v_t_927_);
lean_dec_ref(v_cmp_926_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg(lean_object* v_t_931_, lean_object* v_n_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_931_, v_n_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_934_, lean_object* v_n_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg(v_t_934_, v_n_935_);
lean_dec(v_t_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f(lean_object* v_00_u03b1_937_, lean_object* v_00_u03b2_938_, lean_object* v_cmp_939_, lean_object* v_t_940_, lean_object* v_n_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_940_, v_n_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_943_, lean_object* v_00_u03b2_944_, lean_object* v_cmp_945_, lean_object* v_t_946_, lean_object* v_n_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Std_DTreeMap_Raw_keyAtIdx_x3f(v_00_u03b1_943_, v_00_u03b2_944_, v_cmp_945_, v_t_946_, v_n_947_);
lean_dec(v_t_946_);
lean_dec_ref(v_cmp_945_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg(lean_object* v_inst_949_, lean_object* v_t_950_, lean_object* v_n_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_949_, v_t_950_, v_n_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_953_, lean_object* v_t_954_, lean_object* v_n_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg(v_inst_953_, v_t_954_, v_n_955_);
lean_dec(v_t_954_);
lean_dec(v_inst_953_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21(lean_object* v_00_u03b1_957_, lean_object* v_00_u03b2_958_, lean_object* v_cmp_959_, lean_object* v_inst_960_, lean_object* v_t_961_, lean_object* v_n_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_960_, v_t_961_, v_n_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_964_, lean_object* v_00_u03b2_965_, lean_object* v_cmp_966_, lean_object* v_inst_967_, lean_object* v_t_968_, lean_object* v_n_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_DTreeMap_Raw_keyAtIdx_x21(v_00_u03b1_964_, v_00_u03b2_965_, v_cmp_966_, v_inst_967_, v_t_968_, v_n_969_);
lean_dec(v_t_968_);
lean_dec(v_inst_967_);
lean_dec_ref(v_cmp_966_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___redArg(lean_object* v_t_971_, lean_object* v_n_972_, lean_object* v_fallback_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_971_, v_n_972_, v_fallback_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___redArg___boxed(lean_object* v_t_975_, lean_object* v_n_976_, lean_object* v_fallback_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_DTreeMap_Raw_keyAtIdxD___redArg(v_t_975_, v_n_976_, v_fallback_977_);
lean_dec(v_fallback_977_);
lean_dec(v_t_975_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD(lean_object* v_00_u03b1_979_, lean_object* v_00_u03b2_980_, lean_object* v_cmp_981_, lean_object* v_t_982_, lean_object* v_n_983_, lean_object* v_fallback_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_982_, v_n_983_, v_fallback_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___boxed(lean_object* v_00_u03b1_986_, lean_object* v_00_u03b2_987_, lean_object* v_cmp_988_, lean_object* v_t_989_, lean_object* v_n_990_, lean_object* v_fallback_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_DTreeMap_Raw_keyAtIdxD(v_00_u03b1_986_, v_00_u03b2_987_, v_cmp_988_, v_t_989_, v_n_990_, v_fallback_991_);
lean_dec(v_fallback_991_);
lean_dec(v_t_989_);
lean_dec_ref(v_cmp_988_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x3f___redArg(lean_object* v_cmp_993_, lean_object* v_t_994_, lean_object* v_k_995_){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_box(0);
v___x_997_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_993_, v_k_995_, v___x_996_, v_t_994_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x3f(lean_object* v_00_u03b1_998_, lean_object* v_00_u03b2_999_, lean_object* v_cmp_1000_, lean_object* v_t_1001_, lean_object* v_k_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_box(0);
v___x_1004_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1000_, v_k_1002_, v___x_1003_, v_t_1001_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x3f___redArg(lean_object* v_cmp_1005_, lean_object* v_t_1006_, lean_object* v_k_1007_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_box(0);
v___x_1009_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1005_, v_k_1007_, v___x_1008_, v_t_1006_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x3f(lean_object* v_00_u03b1_1010_, lean_object* v_00_u03b2_1011_, lean_object* v_cmp_1012_, lean_object* v_t_1013_, lean_object* v_k_1014_){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1012_, v_k_1014_, v___x_1015_, v_t_1013_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x3f___redArg(lean_object* v_cmp_1017_, lean_object* v_t_1018_, lean_object* v_k_1019_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1017_, v_k_1019_, v___x_1020_, v_t_1018_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x3f(lean_object* v_00_u03b1_1022_, lean_object* v_00_u03b2_1023_, lean_object* v_cmp_1024_, lean_object* v_t_1025_, lean_object* v_k_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1024_, v_k_1026_, v___x_1027_, v_t_1025_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x3f___redArg(lean_object* v_cmp_1029_, lean_object* v_t_1030_, lean_object* v_k_1031_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1029_, v_k_1031_, v___x_1032_, v_t_1030_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x3f(lean_object* v_00_u03b1_1034_, lean_object* v_00_u03b2_1035_, lean_object* v_cmp_1036_, lean_object* v_t_1037_, lean_object* v_k_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1036_, v_k_1038_, v___x_1039_, v_t_1037_);
return v___x_1040_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1044_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__2));
v___x_1045_ = lean_unsigned_to_nat(14u);
v___x_1046_ = lean_unsigned_to_nat(22u);
v___x_1047_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__1));
v___x_1048_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__0));
v___x_1049_ = l_mkPanicMessageWithDecl(v___x_1048_, v___x_1047_, v___x_1046_, v___x_1045_, v___x_1044_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg(lean_object* v_cmp_1050_, lean_object* v_inst_1051_, lean_object* v_t_1052_, lean_object* v_k_1053_){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1050_, v_k_1053_, v___x_1054_, v_t_1052_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1057_ = l_panic___redArg(v_inst_1051_, v___x_1056_);
return v___x_1057_;
}
else
{
lean_object* v_val_1058_; 
v_val_1058_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_val_1058_);
lean_dec_ref(v___x_1055_);
return v_val_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1059_, lean_object* v_inst_1060_, lean_object* v_t_1061_, lean_object* v_k_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Std_DTreeMap_Raw_getEntryGE_x21___redArg(v_cmp_1059_, v_inst_1060_, v_t_1061_, v_k_1062_);
lean_dec_ref(v_inst_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21(lean_object* v_00_u03b1_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_cmp_1066_, lean_object* v_inst_1067_, lean_object* v_t_1068_, lean_object* v_k_1069_){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_box(0);
v___x_1071_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1066_, v_k_1069_, v___x_1070_, v_t_1068_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1073_ = l_panic___redArg(v_inst_1067_, v___x_1072_);
return v___x_1073_;
}
else
{
lean_object* v_val_1074_; 
v_val_1074_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_val_1074_);
lean_dec_ref(v___x_1071_);
return v_val_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1075_, lean_object* v_00_u03b2_1076_, lean_object* v_cmp_1077_, lean_object* v_inst_1078_, lean_object* v_t_1079_, lean_object* v_k_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Std_DTreeMap_Raw_getEntryGE_x21(v_00_u03b1_1075_, v_00_u03b2_1076_, v_cmp_1077_, v_inst_1078_, v_t_1079_, v_k_1080_);
lean_dec_ref(v_inst_1078_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___redArg(lean_object* v_cmp_1082_, lean_object* v_inst_1083_, lean_object* v_t_1084_, lean_object* v_k_1085_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_box(0);
v___x_1087_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1082_, v_k_1085_, v___x_1086_, v_t_1084_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1089_ = l_panic___redArg(v_inst_1083_, v___x_1088_);
return v___x_1089_;
}
else
{
lean_object* v_val_1090_; 
v_val_1090_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_val_1090_);
lean_dec_ref(v___x_1087_);
return v_val_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1091_, lean_object* v_inst_1092_, lean_object* v_t_1093_, lean_object* v_k_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Std_DTreeMap_Raw_getEntryGT_x21___redArg(v_cmp_1091_, v_inst_1092_, v_t_1093_, v_k_1094_);
lean_dec_ref(v_inst_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21(lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_cmp_1098_, lean_object* v_inst_1099_, lean_object* v_t_1100_, lean_object* v_k_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_box(0);
v___x_1103_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1098_, v_k_1101_, v___x_1102_, v_t_1100_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1105_ = l_panic___redArg(v_inst_1099_, v___x_1104_);
return v___x_1105_;
}
else
{
lean_object* v_val_1106_; 
v_val_1106_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_val_1106_);
lean_dec_ref(v___x_1103_);
return v_val_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1107_, lean_object* v_00_u03b2_1108_, lean_object* v_cmp_1109_, lean_object* v_inst_1110_, lean_object* v_t_1111_, lean_object* v_k_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Std_DTreeMap_Raw_getEntryGT_x21(v_00_u03b1_1107_, v_00_u03b2_1108_, v_cmp_1109_, v_inst_1110_, v_t_1111_, v_k_1112_);
lean_dec_ref(v_inst_1110_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___redArg(lean_object* v_cmp_1114_, lean_object* v_inst_1115_, lean_object* v_t_1116_, lean_object* v_k_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_box(0);
v___x_1119_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1114_, v_k_1117_, v___x_1118_, v_t_1116_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1121_ = l_panic___redArg(v_inst_1115_, v___x_1120_);
return v___x_1121_;
}
else
{
lean_object* v_val_1122_; 
v_val_1122_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_val_1122_);
lean_dec_ref(v___x_1119_);
return v_val_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1123_, lean_object* v_inst_1124_, lean_object* v_t_1125_, lean_object* v_k_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_DTreeMap_Raw_getEntryLE_x21___redArg(v_cmp_1123_, v_inst_1124_, v_t_1125_, v_k_1126_);
lean_dec_ref(v_inst_1124_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21(lean_object* v_00_u03b1_1128_, lean_object* v_00_u03b2_1129_, lean_object* v_cmp_1130_, lean_object* v_inst_1131_, lean_object* v_t_1132_, lean_object* v_k_1133_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_box(0);
v___x_1135_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1130_, v_k_1133_, v___x_1134_, v_t_1132_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1137_ = l_panic___redArg(v_inst_1131_, v___x_1136_);
return v___x_1137_;
}
else
{
lean_object* v_val_1138_; 
v_val_1138_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_val_1138_);
lean_dec_ref(v___x_1135_);
return v_val_1138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1139_, lean_object* v_00_u03b2_1140_, lean_object* v_cmp_1141_, lean_object* v_inst_1142_, lean_object* v_t_1143_, lean_object* v_k_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Std_DTreeMap_Raw_getEntryLE_x21(v_00_u03b1_1139_, v_00_u03b2_1140_, v_cmp_1141_, v_inst_1142_, v_t_1143_, v_k_1144_);
lean_dec_ref(v_inst_1142_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___redArg(lean_object* v_cmp_1146_, lean_object* v_inst_1147_, lean_object* v_t_1148_, lean_object* v_k_1149_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_box(0);
v___x_1151_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1146_, v_k_1149_, v___x_1150_, v_t_1148_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1153_ = l_panic___redArg(v_inst_1147_, v___x_1152_);
return v___x_1153_;
}
else
{
lean_object* v_val_1154_; 
v_val_1154_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_val_1154_);
lean_dec_ref(v___x_1151_);
return v_val_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1155_, lean_object* v_inst_1156_, lean_object* v_t_1157_, lean_object* v_k_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Std_DTreeMap_Raw_getEntryLT_x21___redArg(v_cmp_1155_, v_inst_1156_, v_t_1157_, v_k_1158_);
lean_dec_ref(v_inst_1156_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21(lean_object* v_00_u03b1_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_cmp_1162_, lean_object* v_inst_1163_, lean_object* v_t_1164_, lean_object* v_k_1165_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_box(0);
v___x_1167_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1162_, v_k_1165_, v___x_1166_, v_t_1164_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1169_ = l_panic___redArg(v_inst_1163_, v___x_1168_);
return v___x_1169_;
}
else
{
lean_object* v_val_1170_; 
v_val_1170_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_val_1170_);
lean_dec_ref(v___x_1167_);
return v_val_1170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_00_u03b2_1172_, lean_object* v_cmp_1173_, lean_object* v_inst_1174_, lean_object* v_t_1175_, lean_object* v_k_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_DTreeMap_Raw_getEntryLT_x21(v_00_u03b1_1171_, v_00_u03b2_1172_, v_cmp_1173_, v_inst_1174_, v_t_1175_, v_k_1176_);
lean_dec_ref(v_inst_1174_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___redArg(lean_object* v_cmp_1178_, lean_object* v_t_1179_, lean_object* v_k_1180_, lean_object* v_fallback_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1178_, v_k_1180_, v___x_1182_, v_t_1179_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_inc_ref(v_fallback_1181_);
return v_fallback_1181_;
}
else
{
lean_object* v_val_1184_; 
v_val_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_val_1184_);
lean_dec_ref(v___x_1183_);
return v_val_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___redArg___boxed(lean_object* v_cmp_1185_, lean_object* v_t_1186_, lean_object* v_k_1187_, lean_object* v_fallback_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Std_DTreeMap_Raw_getEntryGED___redArg(v_cmp_1185_, v_t_1186_, v_k_1187_, v_fallback_1188_);
lean_dec_ref(v_fallback_1188_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED(lean_object* v_00_u03b1_1190_, lean_object* v_00_u03b2_1191_, lean_object* v_cmp_1192_, lean_object* v_t_1193_, lean_object* v_k_1194_, lean_object* v_fallback_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_box(0);
v___x_1197_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1192_, v_k_1194_, v___x_1196_, v_t_1193_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_inc_ref(v_fallback_1195_);
return v_fallback_1195_;
}
else
{
lean_object* v_val_1198_; 
v_val_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_val_1198_);
lean_dec_ref(v___x_1197_);
return v_val_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___boxed(lean_object* v_00_u03b1_1199_, lean_object* v_00_u03b2_1200_, lean_object* v_cmp_1201_, lean_object* v_t_1202_, lean_object* v_k_1203_, lean_object* v_fallback_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Std_DTreeMap_Raw_getEntryGED(v_00_u03b1_1199_, v_00_u03b2_1200_, v_cmp_1201_, v_t_1202_, v_k_1203_, v_fallback_1204_);
lean_dec_ref(v_fallback_1204_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___redArg(lean_object* v_cmp_1206_, lean_object* v_t_1207_, lean_object* v_k_1208_, lean_object* v_fallback_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_box(0);
v___x_1211_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1206_, v_k_1208_, v___x_1210_, v_t_1207_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_inc_ref(v_fallback_1209_);
return v_fallback_1209_;
}
else
{
lean_object* v_val_1212_; 
v_val_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_val_1212_);
lean_dec_ref(v___x_1211_);
return v_val_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___redArg___boxed(lean_object* v_cmp_1213_, lean_object* v_t_1214_, lean_object* v_k_1215_, lean_object* v_fallback_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_DTreeMap_Raw_getEntryGTD___redArg(v_cmp_1213_, v_t_1214_, v_k_1215_, v_fallback_1216_);
lean_dec_ref(v_fallback_1216_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD(lean_object* v_00_u03b1_1218_, lean_object* v_00_u03b2_1219_, lean_object* v_cmp_1220_, lean_object* v_t_1221_, lean_object* v_k_1222_, lean_object* v_fallback_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = lean_box(0);
v___x_1225_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1220_, v_k_1222_, v___x_1224_, v_t_1221_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_inc_ref(v_fallback_1223_);
return v_fallback_1223_;
}
else
{
lean_object* v_val_1226_; 
v_val_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_val_1226_);
lean_dec_ref(v___x_1225_);
return v_val_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___boxed(lean_object* v_00_u03b1_1227_, lean_object* v_00_u03b2_1228_, lean_object* v_cmp_1229_, lean_object* v_t_1230_, lean_object* v_k_1231_, lean_object* v_fallback_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Std_DTreeMap_Raw_getEntryGTD(v_00_u03b1_1227_, v_00_u03b2_1228_, v_cmp_1229_, v_t_1230_, v_k_1231_, v_fallback_1232_);
lean_dec_ref(v_fallback_1232_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___redArg(lean_object* v_cmp_1234_, lean_object* v_t_1235_, lean_object* v_k_1236_, lean_object* v_fallback_1237_){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_box(0);
v___x_1239_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1234_, v_k_1236_, v___x_1238_, v_t_1235_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_inc_ref(v_fallback_1237_);
return v_fallback_1237_;
}
else
{
lean_object* v_val_1240_; 
v_val_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_val_1240_);
lean_dec_ref(v___x_1239_);
return v_val_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___redArg___boxed(lean_object* v_cmp_1241_, lean_object* v_t_1242_, lean_object* v_k_1243_, lean_object* v_fallback_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Std_DTreeMap_Raw_getEntryLED___redArg(v_cmp_1241_, v_t_1242_, v_k_1243_, v_fallback_1244_);
lean_dec_ref(v_fallback_1244_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED(lean_object* v_00_u03b1_1246_, lean_object* v_00_u03b2_1247_, lean_object* v_cmp_1248_, lean_object* v_t_1249_, lean_object* v_k_1250_, lean_object* v_fallback_1251_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_box(0);
v___x_1253_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1248_, v_k_1250_, v___x_1252_, v_t_1249_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_inc_ref(v_fallback_1251_);
return v_fallback_1251_;
}
else
{
lean_object* v_val_1254_; 
v_val_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_val_1254_);
lean_dec_ref(v___x_1253_);
return v_val_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___boxed(lean_object* v_00_u03b1_1255_, lean_object* v_00_u03b2_1256_, lean_object* v_cmp_1257_, lean_object* v_t_1258_, lean_object* v_k_1259_, lean_object* v_fallback_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Std_DTreeMap_Raw_getEntryLED(v_00_u03b1_1255_, v_00_u03b2_1256_, v_cmp_1257_, v_t_1258_, v_k_1259_, v_fallback_1260_);
lean_dec_ref(v_fallback_1260_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___redArg(lean_object* v_cmp_1262_, lean_object* v_t_1263_, lean_object* v_k_1264_, lean_object* v_fallback_1265_){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_box(0);
v___x_1267_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1262_, v_k_1264_, v___x_1266_, v_t_1263_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_inc_ref(v_fallback_1265_);
return v_fallback_1265_;
}
else
{
lean_object* v_val_1268_; 
v_val_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_val_1268_);
lean_dec_ref(v___x_1267_);
return v_val_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___redArg___boxed(lean_object* v_cmp_1269_, lean_object* v_t_1270_, lean_object* v_k_1271_, lean_object* v_fallback_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Std_DTreeMap_Raw_getEntryLTD___redArg(v_cmp_1269_, v_t_1270_, v_k_1271_, v_fallback_1272_);
lean_dec_ref(v_fallback_1272_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_cmp_1276_, lean_object* v_t_1277_, lean_object* v_k_1278_, lean_object* v_fallback_1279_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_box(0);
v___x_1281_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1276_, v_k_1278_, v___x_1280_, v_t_1277_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_inc_ref(v_fallback_1279_);
return v_fallback_1279_;
}
else
{
lean_object* v_val_1282_; 
v_val_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_val_1282_);
lean_dec_ref(v___x_1281_);
return v_val_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_00_u03b2_1284_, lean_object* v_cmp_1285_, lean_object* v_t_1286_, lean_object* v_k_1287_, lean_object* v_fallback_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Std_DTreeMap_Raw_getEntryLTD(v_00_u03b1_1283_, v_00_u03b2_1284_, v_cmp_1285_, v_t_1286_, v_k_1287_, v_fallback_1288_);
lean_dec_ref(v_fallback_1288_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x3f___redArg(lean_object* v_cmp_1290_, lean_object* v_t_1291_, lean_object* v_k_1292_){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_box(0);
v___x_1294_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1290_, v_k_1292_, v___x_1293_, v_t_1291_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x3f(lean_object* v_00_u03b1_1295_, lean_object* v_00_u03b2_1296_, lean_object* v_cmp_1297_, lean_object* v_t_1298_, lean_object* v_k_1299_){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = lean_box(0);
v___x_1301_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1297_, v_k_1299_, v___x_1300_, v_t_1298_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x3f___redArg(lean_object* v_cmp_1302_, lean_object* v_t_1303_, lean_object* v_k_1304_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_box(0);
v___x_1306_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1302_, v_k_1304_, v___x_1305_, v_t_1303_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x3f(lean_object* v_00_u03b1_1307_, lean_object* v_00_u03b2_1308_, lean_object* v_cmp_1309_, lean_object* v_t_1310_, lean_object* v_k_1311_){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_box(0);
v___x_1313_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1309_, v_k_1311_, v___x_1312_, v_t_1310_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x3f___redArg(lean_object* v_cmp_1314_, lean_object* v_t_1315_, lean_object* v_k_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_box(0);
v___x_1318_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1314_, v_k_1316_, v___x_1317_, v_t_1315_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x3f(lean_object* v_00_u03b1_1319_, lean_object* v_00_u03b2_1320_, lean_object* v_cmp_1321_, lean_object* v_t_1322_, lean_object* v_k_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1321_, v_k_1323_, v___x_1324_, v_t_1322_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x3f___redArg(lean_object* v_cmp_1326_, lean_object* v_t_1327_, lean_object* v_k_1328_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_box(0);
v___x_1330_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1326_, v_k_1328_, v___x_1329_, v_t_1327_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x3f(lean_object* v_00_u03b1_1331_, lean_object* v_00_u03b2_1332_, lean_object* v_cmp_1333_, lean_object* v_t_1334_, lean_object* v_k_1335_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1333_, v_k_1335_, v___x_1336_, v_t_1334_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___redArg(lean_object* v_cmp_1338_, lean_object* v_inst_1339_, lean_object* v_t_1340_, lean_object* v_k_1341_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_box(0);
v___x_1343_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1338_, v_k_1341_, v___x_1342_, v_t_1340_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1345_ = l_panic___redArg(v_inst_1339_, v___x_1344_);
return v___x_1345_;
}
else
{
lean_object* v_val_1346_; 
v_val_1346_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_val_1346_);
lean_dec_ref(v___x_1343_);
return v_val_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1347_, lean_object* v_inst_1348_, lean_object* v_t_1349_, lean_object* v_k_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Std_DTreeMap_Raw_getKeyGE_x21___redArg(v_cmp_1347_, v_inst_1348_, v_t_1349_, v_k_1350_);
lean_dec(v_inst_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21(lean_object* v_00_u03b1_1352_, lean_object* v_00_u03b2_1353_, lean_object* v_cmp_1354_, lean_object* v_inst_1355_, lean_object* v_t_1356_, lean_object* v_k_1357_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_box(0);
v___x_1359_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1354_, v_k_1357_, v___x_1358_, v_t_1356_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1361_ = l_panic___redArg(v_inst_1355_, v___x_1360_);
return v___x_1361_;
}
else
{
lean_object* v_val_1362_; 
v_val_1362_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_val_1362_);
lean_dec_ref(v___x_1359_);
return v_val_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_00_u03b2_1364_, lean_object* v_cmp_1365_, lean_object* v_inst_1366_, lean_object* v_t_1367_, lean_object* v_k_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Std_DTreeMap_Raw_getKeyGE_x21(v_00_u03b1_1363_, v_00_u03b2_1364_, v_cmp_1365_, v_inst_1366_, v_t_1367_, v_k_1368_);
lean_dec(v_inst_1366_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___redArg(lean_object* v_cmp_1370_, lean_object* v_inst_1371_, lean_object* v_t_1372_, lean_object* v_k_1373_){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1370_, v_k_1373_, v___x_1374_, v_t_1372_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1377_ = l_panic___redArg(v_inst_1371_, v___x_1376_);
return v___x_1377_;
}
else
{
lean_object* v_val_1378_; 
v_val_1378_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_val_1378_);
lean_dec_ref(v___x_1375_);
return v_val_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1379_, lean_object* v_inst_1380_, lean_object* v_t_1381_, lean_object* v_k_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Std_DTreeMap_Raw_getKeyGT_x21___redArg(v_cmp_1379_, v_inst_1380_, v_t_1381_, v_k_1382_);
lean_dec(v_inst_1380_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21(lean_object* v_00_u03b1_1384_, lean_object* v_00_u03b2_1385_, lean_object* v_cmp_1386_, lean_object* v_inst_1387_, lean_object* v_t_1388_, lean_object* v_k_1389_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_box(0);
v___x_1391_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1386_, v_k_1389_, v___x_1390_, v_t_1388_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1393_ = l_panic___redArg(v_inst_1387_, v___x_1392_);
return v___x_1393_;
}
else
{
lean_object* v_val_1394_; 
v_val_1394_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_val_1394_);
lean_dec_ref(v___x_1391_);
return v_val_1394_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1395_, lean_object* v_00_u03b2_1396_, lean_object* v_cmp_1397_, lean_object* v_inst_1398_, lean_object* v_t_1399_, lean_object* v_k_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Std_DTreeMap_Raw_getKeyGT_x21(v_00_u03b1_1395_, v_00_u03b2_1396_, v_cmp_1397_, v_inst_1398_, v_t_1399_, v_k_1400_);
lean_dec(v_inst_1398_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___redArg(lean_object* v_cmp_1402_, lean_object* v_inst_1403_, lean_object* v_t_1404_, lean_object* v_k_1405_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_box(0);
v___x_1407_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1402_, v_k_1405_, v___x_1406_, v_t_1404_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1409_ = l_panic___redArg(v_inst_1403_, v___x_1408_);
return v___x_1409_;
}
else
{
lean_object* v_val_1410_; 
v_val_1410_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_val_1410_);
lean_dec_ref(v___x_1407_);
return v_val_1410_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1411_, lean_object* v_inst_1412_, lean_object* v_t_1413_, lean_object* v_k_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Std_DTreeMap_Raw_getKeyLE_x21___redArg(v_cmp_1411_, v_inst_1412_, v_t_1413_, v_k_1414_);
lean_dec(v_inst_1412_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21(lean_object* v_00_u03b1_1416_, lean_object* v_00_u03b2_1417_, lean_object* v_cmp_1418_, lean_object* v_inst_1419_, lean_object* v_t_1420_, lean_object* v_k_1421_){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_box(0);
v___x_1423_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1418_, v_k_1421_, v___x_1422_, v_t_1420_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1425_ = l_panic___redArg(v_inst_1419_, v___x_1424_);
return v___x_1425_;
}
else
{
lean_object* v_val_1426_; 
v_val_1426_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_val_1426_);
lean_dec_ref(v___x_1423_);
return v_val_1426_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1427_, lean_object* v_00_u03b2_1428_, lean_object* v_cmp_1429_, lean_object* v_inst_1430_, lean_object* v_t_1431_, lean_object* v_k_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Std_DTreeMap_Raw_getKeyLE_x21(v_00_u03b1_1427_, v_00_u03b2_1428_, v_cmp_1429_, v_inst_1430_, v_t_1431_, v_k_1432_);
lean_dec(v_inst_1430_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___redArg(lean_object* v_cmp_1434_, lean_object* v_inst_1435_, lean_object* v_t_1436_, lean_object* v_k_1437_){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_box(0);
v___x_1439_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1434_, v_k_1437_, v___x_1438_, v_t_1436_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1441_ = l_panic___redArg(v_inst_1435_, v___x_1440_);
return v___x_1441_;
}
else
{
lean_object* v_val_1442_; 
v_val_1442_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_val_1442_);
lean_dec_ref(v___x_1439_);
return v_val_1442_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1443_, lean_object* v_inst_1444_, lean_object* v_t_1445_, lean_object* v_k_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Std_DTreeMap_Raw_getKeyLT_x21___redArg(v_cmp_1443_, v_inst_1444_, v_t_1445_, v_k_1446_);
lean_dec(v_inst_1444_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21(lean_object* v_00_u03b1_1448_, lean_object* v_00_u03b2_1449_, lean_object* v_cmp_1450_, lean_object* v_inst_1451_, lean_object* v_t_1452_, lean_object* v_k_1453_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_box(0);
v___x_1455_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1450_, v_k_1453_, v___x_1454_, v_t_1452_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1457_ = l_panic___redArg(v_inst_1451_, v___x_1456_);
return v___x_1457_;
}
else
{
lean_object* v_val_1458_; 
v_val_1458_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_val_1458_);
lean_dec_ref(v___x_1455_);
return v_val_1458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1459_, lean_object* v_00_u03b2_1460_, lean_object* v_cmp_1461_, lean_object* v_inst_1462_, lean_object* v_t_1463_, lean_object* v_k_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Std_DTreeMap_Raw_getKeyLT_x21(v_00_u03b1_1459_, v_00_u03b2_1460_, v_cmp_1461_, v_inst_1462_, v_t_1463_, v_k_1464_);
lean_dec(v_inst_1462_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___redArg(lean_object* v_cmp_1466_, lean_object* v_t_1467_, lean_object* v_k_1468_, lean_object* v_fallback_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_box(0);
v___x_1471_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1466_, v_k_1468_, v___x_1470_, v_t_1467_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_inc(v_fallback_1469_);
return v_fallback_1469_;
}
else
{
lean_object* v_val_1472_; 
v_val_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_val_1472_);
lean_dec_ref(v___x_1471_);
return v_val_1472_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___redArg___boxed(lean_object* v_cmp_1473_, lean_object* v_t_1474_, lean_object* v_k_1475_, lean_object* v_fallback_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Std_DTreeMap_Raw_getKeyGED___redArg(v_cmp_1473_, v_t_1474_, v_k_1475_, v_fallback_1476_);
lean_dec(v_fallback_1476_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED(lean_object* v_00_u03b1_1478_, lean_object* v_00_u03b2_1479_, lean_object* v_cmp_1480_, lean_object* v_t_1481_, lean_object* v_k_1482_, lean_object* v_fallback_1483_){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_box(0);
v___x_1485_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1480_, v_k_1482_, v___x_1484_, v_t_1481_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_inc(v_fallback_1483_);
return v_fallback_1483_;
}
else
{
lean_object* v_val_1486_; 
v_val_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_val_1486_);
lean_dec_ref(v___x_1485_);
return v_val_1486_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___boxed(lean_object* v_00_u03b1_1487_, lean_object* v_00_u03b2_1488_, lean_object* v_cmp_1489_, lean_object* v_t_1490_, lean_object* v_k_1491_, lean_object* v_fallback_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Std_DTreeMap_Raw_getKeyGED(v_00_u03b1_1487_, v_00_u03b2_1488_, v_cmp_1489_, v_t_1490_, v_k_1491_, v_fallback_1492_);
lean_dec(v_fallback_1492_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___redArg(lean_object* v_cmp_1494_, lean_object* v_t_1495_, lean_object* v_k_1496_, lean_object* v_fallback_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_box(0);
v___x_1499_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1494_, v_k_1496_, v___x_1498_, v_t_1495_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_inc(v_fallback_1497_);
return v_fallback_1497_;
}
else
{
lean_object* v_val_1500_; 
v_val_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_val_1500_);
lean_dec_ref(v___x_1499_);
return v_val_1500_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___redArg___boxed(lean_object* v_cmp_1501_, lean_object* v_t_1502_, lean_object* v_k_1503_, lean_object* v_fallback_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Std_DTreeMap_Raw_getKeyGTD___redArg(v_cmp_1501_, v_t_1502_, v_k_1503_, v_fallback_1504_);
lean_dec(v_fallback_1504_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD(lean_object* v_00_u03b1_1506_, lean_object* v_00_u03b2_1507_, lean_object* v_cmp_1508_, lean_object* v_t_1509_, lean_object* v_k_1510_, lean_object* v_fallback_1511_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1508_, v_k_1510_, v___x_1512_, v_t_1509_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_inc(v_fallback_1511_);
return v_fallback_1511_;
}
else
{
lean_object* v_val_1514_; 
v_val_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_val_1514_);
lean_dec_ref(v___x_1513_);
return v_val_1514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___boxed(lean_object* v_00_u03b1_1515_, lean_object* v_00_u03b2_1516_, lean_object* v_cmp_1517_, lean_object* v_t_1518_, lean_object* v_k_1519_, lean_object* v_fallback_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Std_DTreeMap_Raw_getKeyGTD(v_00_u03b1_1515_, v_00_u03b2_1516_, v_cmp_1517_, v_t_1518_, v_k_1519_, v_fallback_1520_);
lean_dec(v_fallback_1520_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___redArg(lean_object* v_cmp_1522_, lean_object* v_t_1523_, lean_object* v_k_1524_, lean_object* v_fallback_1525_){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_box(0);
v___x_1527_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1522_, v_k_1524_, v___x_1526_, v_t_1523_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_inc(v_fallback_1525_);
return v_fallback_1525_;
}
else
{
lean_object* v_val_1528_; 
v_val_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_val_1528_);
lean_dec_ref(v___x_1527_);
return v_val_1528_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___redArg___boxed(lean_object* v_cmp_1529_, lean_object* v_t_1530_, lean_object* v_k_1531_, lean_object* v_fallback_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Std_DTreeMap_Raw_getKeyLED___redArg(v_cmp_1529_, v_t_1530_, v_k_1531_, v_fallback_1532_);
lean_dec(v_fallback_1532_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED(lean_object* v_00_u03b1_1534_, lean_object* v_00_u03b2_1535_, lean_object* v_cmp_1536_, lean_object* v_t_1537_, lean_object* v_k_1538_, lean_object* v_fallback_1539_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_box(0);
v___x_1541_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1536_, v_k_1538_, v___x_1540_, v_t_1537_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_inc(v_fallback_1539_);
return v_fallback_1539_;
}
else
{
lean_object* v_val_1542_; 
v_val_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_val_1542_);
lean_dec_ref(v___x_1541_);
return v_val_1542_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___boxed(lean_object* v_00_u03b1_1543_, lean_object* v_00_u03b2_1544_, lean_object* v_cmp_1545_, lean_object* v_t_1546_, lean_object* v_k_1547_, lean_object* v_fallback_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Std_DTreeMap_Raw_getKeyLED(v_00_u03b1_1543_, v_00_u03b2_1544_, v_cmp_1545_, v_t_1546_, v_k_1547_, v_fallback_1548_);
lean_dec(v_fallback_1548_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___redArg(lean_object* v_cmp_1550_, lean_object* v_t_1551_, lean_object* v_k_1552_, lean_object* v_fallback_1553_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1550_, v_k_1552_, v___x_1554_, v_t_1551_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_inc(v_fallback_1553_);
return v_fallback_1553_;
}
else
{
lean_object* v_val_1556_; 
v_val_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_val_1556_);
lean_dec_ref(v___x_1555_);
return v_val_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___redArg___boxed(lean_object* v_cmp_1557_, lean_object* v_t_1558_, lean_object* v_k_1559_, lean_object* v_fallback_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Std_DTreeMap_Raw_getKeyLTD___redArg(v_cmp_1557_, v_t_1558_, v_k_1559_, v_fallback_1560_);
lean_dec(v_fallback_1560_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD(lean_object* v_00_u03b1_1562_, lean_object* v_00_u03b2_1563_, lean_object* v_cmp_1564_, lean_object* v_t_1565_, lean_object* v_k_1566_, lean_object* v_fallback_1567_){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_box(0);
v___x_1569_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1564_, v_k_1566_, v___x_1568_, v_t_1565_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_inc(v_fallback_1567_);
return v_fallback_1567_;
}
else
{
lean_object* v_val_1570_; 
v_val_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_val_1570_);
lean_dec_ref(v___x_1569_);
return v_val_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___boxed(lean_object* v_00_u03b1_1571_, lean_object* v_00_u03b2_1572_, lean_object* v_cmp_1573_, lean_object* v_t_1574_, lean_object* v_k_1575_, lean_object* v_fallback_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Std_DTreeMap_Raw_getKeyLTD(v_00_u03b1_1571_, v_00_u03b2_1572_, v_cmp_1573_, v_t_1574_, v_k_1575_, v_fallback_1576_);
lean_dec(v_fallback_1576_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1578_, lean_object* v_t_1579_, lean_object* v_a_1580_, lean_object* v_b_1581_){
_start:
{
lean_object* v___x_1582_; 
lean_inc(v_a_1580_);
lean_inc(v_t_1579_);
lean_inc_ref(v_cmp_1578_);
v___x_1582_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1578_, v_t_1579_, v_a_1580_);
if (lean_obj_tag(v___x_1582_) == 0)
{
uint8_t v___x_1583_; 
lean_inc(v_t_1579_);
lean_inc(v_a_1580_);
lean_inc_ref(v_cmp_1578_);
v___x_1583_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1578_, v_a_1580_, v_t_1579_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1578_, v_a_1580_, v_b_1581_, v_t_1579_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1582_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; 
lean_dec(v_b_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_cmp_1578_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1582_);
lean_ctor_set(v___x_1586_, 1, v_t_1579_);
return v___x_1586_;
}
}
else
{
lean_object* v___x_1587_; 
lean_dec(v_b_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_cmp_1578_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1582_);
lean_ctor_set(v___x_1587_, 1, v_t_1579_);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1588_, lean_object* v_cmp_1589_, lean_object* v_00_u03b2_1590_, lean_object* v_t_1591_, lean_object* v_a_1592_, lean_object* v_b_1593_){
_start:
{
lean_object* v___x_1594_; 
lean_inc(v_a_1592_);
lean_inc(v_t_1591_);
lean_inc_ref(v_cmp_1589_);
v___x_1594_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1589_, v_t_1591_, v_a_1592_);
if (lean_obj_tag(v___x_1594_) == 0)
{
uint8_t v___x_1595_; 
lean_inc(v_t_1591_);
lean_inc(v_a_1592_);
lean_inc_ref(v_cmp_1589_);
v___x_1595_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1589_, v_a_1592_, v_t_1591_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1589_, v_a_1592_, v_b_1593_, v_t_1591_);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1594_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
return v___x_1597_;
}
else
{
lean_object* v___x_1598_; 
lean_dec(v_b_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_cmp_1589_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1594_);
lean_ctor_set(v___x_1598_, 1, v_t_1591_);
return v___x_1598_;
}
}
else
{
lean_object* v___x_1599_; 
lean_dec(v_b_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_cmp_1589_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1594_);
lean_ctor_set(v___x_1599_, 1, v_t_1591_);
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x3f___redArg(lean_object* v_cmp_1600_, lean_object* v_t_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1600_, v_t_1601_, v_a_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x3f(lean_object* v_00_u03b1_1604_, lean_object* v_cmp_1605_, lean_object* v_00_u03b2_1606_, lean_object* v_t_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1605_, v_t_1607_, v_a_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get___redArg(lean_object* v_cmp_1610_, lean_object* v_t_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1610_, v_t_1611_, v_a_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get(lean_object* v_00_u03b1_1614_, lean_object* v_cmp_1615_, lean_object* v_00_u03b2_1616_, lean_object* v_t_1617_, lean_object* v_a_1618_, lean_object* v_h_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1615_, v_t_1617_, v_a_1618_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___redArg(lean_object* v_cmp_1621_, lean_object* v_inst_1622_, lean_object* v_t_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1621_, v_inst_1622_, v_t_1623_, v_a_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___redArg___boxed(lean_object* v_cmp_1626_, lean_object* v_inst_1627_, lean_object* v_t_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Std_DTreeMap_Raw_Const_get_x21___redArg(v_cmp_1626_, v_inst_1627_, v_t_1628_, v_a_1629_);
lean_dec(v_inst_1627_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21(lean_object* v_00_u03b1_1631_, lean_object* v_cmp_1632_, lean_object* v_00_u03b2_1633_, lean_object* v_inst_1634_, lean_object* v_t_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1632_, v_inst_1634_, v_t_1635_, v_a_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___boxed(lean_object* v_00_u03b1_1638_, lean_object* v_cmp_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_inst_1641_, lean_object* v_t_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Std_DTreeMap_Raw_Const_get_x21(v_00_u03b1_1638_, v_cmp_1639_, v_00_u03b2_1640_, v_inst_1641_, v_t_1642_, v_a_1643_);
lean_dec(v_inst_1641_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___redArg(lean_object* v_cmp_1645_, lean_object* v_t_1646_, lean_object* v_a_1647_, lean_object* v_fallback_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1645_, v_t_1646_, v_a_1647_, v_fallback_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___redArg___boxed(lean_object* v_cmp_1650_, lean_object* v_t_1651_, lean_object* v_a_1652_, lean_object* v_fallback_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Std_DTreeMap_Raw_Const_getD___redArg(v_cmp_1650_, v_t_1651_, v_a_1652_, v_fallback_1653_);
lean_dec(v_fallback_1653_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD(lean_object* v_00_u03b1_1655_, lean_object* v_cmp_1656_, lean_object* v_00_u03b2_1657_, lean_object* v_t_1658_, lean_object* v_a_1659_, lean_object* v_fallback_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1656_, v_t_1658_, v_a_1659_, v_fallback_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___boxed(lean_object* v_00_u03b1_1662_, lean_object* v_cmp_1663_, lean_object* v_00_u03b2_1664_, lean_object* v_t_1665_, lean_object* v_a_1666_, lean_object* v_fallback_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Std_DTreeMap_Raw_Const_getD(v_00_u03b1_1662_, v_cmp_1663_, v_00_u03b2_1664_, v_t_1665_, v_a_1666_, v_fallback_1667_);
lean_dec(v_fallback_1667_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg(lean_object* v_t_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg(v_t_1671_);
lean_dec(v_t_1671_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f(lean_object* v_00_u03b1_1673_, lean_object* v_cmp_1674_, lean_object* v_00_u03b2_1675_, lean_object* v_t_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1678_, lean_object* v_cmp_1679_, lean_object* v_00_u03b2_1680_, lean_object* v_t_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Std_DTreeMap_Raw_Const_minEntry_x3f(v_00_u03b1_1678_, v_cmp_1679_, v_00_u03b2_1680_, v_t_1681_);
lean_dec(v_t_1681_);
lean_dec_ref(v_cmp_1679_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg(lean_object* v_inst_1683_, lean_object* v_t_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1683_, v_t_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1686_, lean_object* v_t_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg(v_inst_1686_, v_t_1687_);
lean_dec(v_t_1687_);
lean_dec_ref(v_inst_1686_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21(lean_object* v_00_u03b1_1689_, lean_object* v_cmp_1690_, lean_object* v_00_u03b2_1691_, lean_object* v_inst_1692_, lean_object* v_t_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1692_, v_t_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_cmp_1696_, lean_object* v_00_u03b2_1697_, lean_object* v_inst_1698_, lean_object* v_t_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_DTreeMap_Raw_Const_minEntry_x21(v_00_u03b1_1695_, v_cmp_1696_, v_00_u03b2_1697_, v_inst_1698_, v_t_1699_);
lean_dec(v_t_1699_);
lean_dec_ref(v_inst_1698_);
lean_dec_ref(v_cmp_1696_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___redArg(lean_object* v_t_1701_, lean_object* v_fallback_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1701_, v_fallback_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___redArg___boxed(lean_object* v_t_1704_, lean_object* v_fallback_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Std_DTreeMap_Raw_Const_minEntryD___redArg(v_t_1704_, v_fallback_1705_);
lean_dec_ref(v_fallback_1705_);
lean_dec(v_t_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD(lean_object* v_00_u03b1_1707_, lean_object* v_cmp_1708_, lean_object* v_00_u03b2_1709_, lean_object* v_t_1710_, lean_object* v_fallback_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1710_, v_fallback_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_cmp_1714_, lean_object* v_00_u03b2_1715_, lean_object* v_t_1716_, lean_object* v_fallback_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Std_DTreeMap_Raw_Const_minEntryD(v_00_u03b1_1713_, v_cmp_1714_, v_00_u03b2_1715_, v_t_1716_, v_fallback_1717_);
lean_dec_ref(v_fallback_1717_);
lean_dec(v_t_1716_);
lean_dec_ref(v_cmp_1714_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg(lean_object* v_t_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg(v_t_1721_);
lean_dec(v_t_1721_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f(lean_object* v_00_u03b1_1723_, lean_object* v_cmp_1724_, lean_object* v_00_u03b2_1725_, lean_object* v_t_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1728_, lean_object* v_cmp_1729_, lean_object* v_00_u03b2_1730_, lean_object* v_t_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Std_DTreeMap_Raw_Const_maxEntry_x3f(v_00_u03b1_1728_, v_cmp_1729_, v_00_u03b2_1730_, v_t_1731_);
lean_dec(v_t_1731_);
lean_dec_ref(v_cmp_1729_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg(lean_object* v_inst_1733_, lean_object* v_t_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1733_, v_t_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_1736_, lean_object* v_t_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg(v_inst_1736_, v_t_1737_);
lean_dec(v_t_1737_);
lean_dec_ref(v_inst_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21(lean_object* v_00_u03b1_1739_, lean_object* v_cmp_1740_, lean_object* v_00_u03b2_1741_, lean_object* v_inst_1742_, lean_object* v_t_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1742_, v_t_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_cmp_1746_, lean_object* v_00_u03b2_1747_, lean_object* v_inst_1748_, lean_object* v_t_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Std_DTreeMap_Raw_Const_maxEntry_x21(v_00_u03b1_1745_, v_cmp_1746_, v_00_u03b2_1747_, v_inst_1748_, v_t_1749_);
lean_dec(v_t_1749_);
lean_dec_ref(v_inst_1748_);
lean_dec_ref(v_cmp_1746_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___redArg(lean_object* v_t_1751_, lean_object* v_fallback_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1751_, v_fallback_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___redArg___boxed(lean_object* v_t_1754_, lean_object* v_fallback_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Std_DTreeMap_Raw_Const_maxEntryD___redArg(v_t_1754_, v_fallback_1755_);
lean_dec_ref(v_fallback_1755_);
lean_dec(v_t_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD(lean_object* v_00_u03b1_1757_, lean_object* v_cmp_1758_, lean_object* v_00_u03b2_1759_, lean_object* v_t_1760_, lean_object* v_fallback_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1760_, v_fallback_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___boxed(lean_object* v_00_u03b1_1763_, lean_object* v_cmp_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_t_1766_, lean_object* v_fallback_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Std_DTreeMap_Raw_Const_maxEntryD(v_00_u03b1_1763_, v_cmp_1764_, v_00_u03b2_1765_, v_t_1766_, v_fallback_1767_);
lean_dec_ref(v_fallback_1767_);
lean_dec(v_t_1766_);
lean_dec_ref(v_cmp_1764_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg(lean_object* v_t_1769_, lean_object* v_n_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1769_, v_n_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_1772_, lean_object* v_n_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg(v_t_1772_, v_n_1773_);
lean_dec(v_t_1772_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_1775_, lean_object* v_cmp_1776_, lean_object* v_00_u03b2_1777_, lean_object* v_t_1778_, lean_object* v_n_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1778_, v_n_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1781_, lean_object* v_cmp_1782_, lean_object* v_00_u03b2_1783_, lean_object* v_t_1784_, lean_object* v_n_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f(v_00_u03b1_1781_, v_cmp_1782_, v_00_u03b2_1783_, v_t_1784_, v_n_1785_);
lean_dec(v_t_1784_);
lean_dec_ref(v_cmp_1782_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg(lean_object* v_inst_1787_, lean_object* v_t_1788_, lean_object* v_n_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1787_, v_t_1788_, v_n_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_1791_, lean_object* v_t_1792_, lean_object* v_n_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg(v_inst_1791_, v_t_1792_, v_n_1793_);
lean_dec(v_t_1792_);
lean_dec_ref(v_inst_1791_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21(lean_object* v_00_u03b1_1795_, lean_object* v_cmp_1796_, lean_object* v_00_u03b2_1797_, lean_object* v_inst_1798_, lean_object* v_t_1799_, lean_object* v_n_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1798_, v_t_1799_, v_n_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_1802_, lean_object* v_cmp_1803_, lean_object* v_00_u03b2_1804_, lean_object* v_inst_1805_, lean_object* v_t_1806_, lean_object* v_n_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x21(v_00_u03b1_1802_, v_cmp_1803_, v_00_u03b2_1804_, v_inst_1805_, v_t_1806_, v_n_1807_);
lean_dec(v_t_1806_);
lean_dec_ref(v_inst_1805_);
lean_dec_ref(v_cmp_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg(lean_object* v_t_1809_, lean_object* v_n_1810_, lean_object* v_fallback_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1809_, v_n_1810_, v_fallback_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_1813_, lean_object* v_n_1814_, lean_object* v_fallback_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg(v_t_1813_, v_n_1814_, v_fallback_1815_);
lean_dec_ref(v_fallback_1815_);
lean_dec(v_t_1813_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD(lean_object* v_00_u03b1_1817_, lean_object* v_cmp_1818_, lean_object* v_00_u03b2_1819_, lean_object* v_t_1820_, lean_object* v_n_1821_, lean_object* v_fallback_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1820_, v_n_1821_, v_fallback_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_cmp_1825_, lean_object* v_00_u03b2_1826_, lean_object* v_t_1827_, lean_object* v_n_1828_, lean_object* v_fallback_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Std_DTreeMap_Raw_Const_entryAtIdxD(v_00_u03b1_1824_, v_cmp_1825_, v_00_u03b2_1826_, v_t_1827_, v_n_1828_, v_fallback_1829_);
lean_dec_ref(v_fallback_1829_);
lean_dec(v_t_1827_);
lean_dec_ref(v_cmp_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_1831_, lean_object* v_t_1832_, lean_object* v_k_1833_){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_box(0);
v___x_1835_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1831_, v_k_1833_, v___x_1834_, v_t_1832_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x3f(lean_object* v_00_u03b1_1836_, lean_object* v_cmp_1837_, lean_object* v_00_u03b2_1838_, lean_object* v_t_1839_, lean_object* v_k_1840_){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_box(0);
v___x_1842_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1837_, v_k_1840_, v___x_1841_, v_t_1839_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_1843_, lean_object* v_t_1844_, lean_object* v_k_1845_){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_box(0);
v___x_1847_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1843_, v_k_1845_, v___x_1846_, v_t_1844_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x3f(lean_object* v_00_u03b1_1848_, lean_object* v_cmp_1849_, lean_object* v_00_u03b2_1850_, lean_object* v_t_1851_, lean_object* v_k_1852_){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_box(0);
v___x_1854_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1849_, v_k_1852_, v___x_1853_, v_t_1851_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_1855_, lean_object* v_t_1856_, lean_object* v_k_1857_){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = lean_box(0);
v___x_1859_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1855_, v_k_1857_, v___x_1858_, v_t_1856_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x3f(lean_object* v_00_u03b1_1860_, lean_object* v_cmp_1861_, lean_object* v_00_u03b2_1862_, lean_object* v_t_1863_, lean_object* v_k_1864_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_box(0);
v___x_1866_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1861_, v_k_1864_, v___x_1865_, v_t_1863_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_1867_, lean_object* v_t_1868_, lean_object* v_k_1869_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_box(0);
v___x_1871_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1867_, v_k_1869_, v___x_1870_, v_t_1868_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x3f(lean_object* v_00_u03b1_1872_, lean_object* v_cmp_1873_, lean_object* v_00_u03b2_1874_, lean_object* v_t_1875_, lean_object* v_k_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_box(0);
v___x_1878_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1873_, v_k_1876_, v___x_1877_, v_t_1875_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg(lean_object* v_cmp_1879_, lean_object* v_inst_1880_, lean_object* v_t_1881_, lean_object* v_k_1882_){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_box(0);
v___x_1884_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1879_, v_k_1882_, v___x_1883_, v_t_1881_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1886_ = l_panic___redArg(v_inst_1880_, v___x_1885_);
return v___x_1886_;
}
else
{
lean_object* v_val_1887_; 
v_val_1887_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_val_1887_);
lean_dec_ref(v___x_1884_);
return v_val_1887_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1888_, lean_object* v_inst_1889_, lean_object* v_t_1890_, lean_object* v_k_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg(v_cmp_1888_, v_inst_1889_, v_t_1890_, v_k_1891_);
lean_dec_ref(v_inst_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21(lean_object* v_00_u03b1_1893_, lean_object* v_cmp_1894_, lean_object* v_00_u03b2_1895_, lean_object* v_inst_1896_, lean_object* v_t_1897_, lean_object* v_k_1898_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_box(0);
v___x_1900_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1894_, v_k_1898_, v___x_1899_, v_t_1897_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1902_ = l_panic___redArg(v_inst_1896_, v___x_1901_);
return v___x_1902_;
}
else
{
lean_object* v_val_1903_; 
v_val_1903_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_val_1903_);
lean_dec_ref(v___x_1900_);
return v_val_1903_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1904_, lean_object* v_cmp_1905_, lean_object* v_00_u03b2_1906_, lean_object* v_inst_1907_, lean_object* v_t_1908_, lean_object* v_k_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Std_DTreeMap_Raw_Const_getEntryGE_x21(v_00_u03b1_1904_, v_cmp_1905_, v_00_u03b2_1906_, v_inst_1907_, v_t_1908_, v_k_1909_);
lean_dec_ref(v_inst_1907_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg(lean_object* v_cmp_1911_, lean_object* v_inst_1912_, lean_object* v_t_1913_, lean_object* v_k_1914_){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_box(0);
v___x_1916_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1911_, v_k_1914_, v___x_1915_, v_t_1913_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1918_ = l_panic___redArg(v_inst_1912_, v___x_1917_);
return v___x_1918_;
}
else
{
lean_object* v_val_1919_; 
v_val_1919_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_val_1919_);
lean_dec_ref(v___x_1916_);
return v_val_1919_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1920_, lean_object* v_inst_1921_, lean_object* v_t_1922_, lean_object* v_k_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg(v_cmp_1920_, v_inst_1921_, v_t_1922_, v_k_1923_);
lean_dec_ref(v_inst_1921_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21(lean_object* v_00_u03b1_1925_, lean_object* v_cmp_1926_, lean_object* v_00_u03b2_1927_, lean_object* v_inst_1928_, lean_object* v_t_1929_, lean_object* v_k_1930_){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = lean_box(0);
v___x_1932_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1926_, v_k_1930_, v___x_1931_, v_t_1929_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1934_ = l_panic___redArg(v_inst_1928_, v___x_1933_);
return v___x_1934_;
}
else
{
lean_object* v_val_1935_; 
v_val_1935_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_val_1935_);
lean_dec_ref(v___x_1932_);
return v_val_1935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1936_, lean_object* v_cmp_1937_, lean_object* v_00_u03b2_1938_, lean_object* v_inst_1939_, lean_object* v_t_1940_, lean_object* v_k_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Std_DTreeMap_Raw_Const_getEntryGT_x21(v_00_u03b1_1936_, v_cmp_1937_, v_00_u03b2_1938_, v_inst_1939_, v_t_1940_, v_k_1941_);
lean_dec_ref(v_inst_1939_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg(lean_object* v_cmp_1943_, lean_object* v_inst_1944_, lean_object* v_t_1945_, lean_object* v_k_1946_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_box(0);
v___x_1948_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1943_, v_k_1946_, v___x_1947_, v_t_1945_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1950_ = l_panic___redArg(v_inst_1944_, v___x_1949_);
return v___x_1950_;
}
else
{
lean_object* v_val_1951_; 
v_val_1951_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_val_1951_);
lean_dec_ref(v___x_1948_);
return v_val_1951_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1952_, lean_object* v_inst_1953_, lean_object* v_t_1954_, lean_object* v_k_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg(v_cmp_1952_, v_inst_1953_, v_t_1954_, v_k_1955_);
lean_dec_ref(v_inst_1953_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21(lean_object* v_00_u03b1_1957_, lean_object* v_cmp_1958_, lean_object* v_00_u03b2_1959_, lean_object* v_inst_1960_, lean_object* v_t_1961_, lean_object* v_k_1962_){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = lean_box(0);
v___x_1964_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1958_, v_k_1962_, v___x_1963_, v_t_1961_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1966_ = l_panic___redArg(v_inst_1960_, v___x_1965_);
return v___x_1966_;
}
else
{
lean_object* v_val_1967_; 
v_val_1967_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_val_1967_);
lean_dec_ref(v___x_1964_);
return v_val_1967_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1968_, lean_object* v_cmp_1969_, lean_object* v_00_u03b2_1970_, lean_object* v_inst_1971_, lean_object* v_t_1972_, lean_object* v_k_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Std_DTreeMap_Raw_Const_getEntryLE_x21(v_00_u03b1_1968_, v_cmp_1969_, v_00_u03b2_1970_, v_inst_1971_, v_t_1972_, v_k_1973_);
lean_dec_ref(v_inst_1971_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg(lean_object* v_cmp_1975_, lean_object* v_inst_1976_, lean_object* v_t_1977_, lean_object* v_k_1978_){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_box(0);
v___x_1980_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1975_, v_k_1978_, v___x_1979_, v_t_1977_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1982_ = l_panic___redArg(v_inst_1976_, v___x_1981_);
return v___x_1982_;
}
else
{
lean_object* v_val_1983_; 
v_val_1983_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_val_1983_);
lean_dec_ref(v___x_1980_);
return v_val_1983_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1984_, lean_object* v_inst_1985_, lean_object* v_t_1986_, lean_object* v_k_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg(v_cmp_1984_, v_inst_1985_, v_t_1986_, v_k_1987_);
lean_dec_ref(v_inst_1985_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21(lean_object* v_00_u03b1_1989_, lean_object* v_cmp_1990_, lean_object* v_00_u03b2_1991_, lean_object* v_inst_1992_, lean_object* v_t_1993_, lean_object* v_k_1994_){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_box(0);
v___x_1996_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1990_, v_k_1994_, v___x_1995_, v_t_1993_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1998_ = l_panic___redArg(v_inst_1992_, v___x_1997_);
return v___x_1998_;
}
else
{
lean_object* v_val_1999_; 
v_val_1999_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_val_1999_);
lean_dec_ref(v___x_1996_);
return v_val_1999_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2000_, lean_object* v_cmp_2001_, lean_object* v_00_u03b2_2002_, lean_object* v_inst_2003_, lean_object* v_t_2004_, lean_object* v_k_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Std_DTreeMap_Raw_Const_getEntryLT_x21(v_00_u03b1_2000_, v_cmp_2001_, v_00_u03b2_2002_, v_inst_2003_, v_t_2004_, v_k_2005_);
lean_dec_ref(v_inst_2003_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___redArg(lean_object* v_cmp_2007_, lean_object* v_t_2008_, lean_object* v_k_2009_, lean_object* v_fallback_2010_){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = lean_box(0);
v___x_2012_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2007_, v_k_2009_, v___x_2011_, v_t_2008_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_inc_ref(v_fallback_2010_);
return v_fallback_2010_;
}
else
{
lean_object* v_val_2013_; 
v_val_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_val_2013_);
lean_dec_ref(v___x_2012_);
return v_val_2013_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2014_, lean_object* v_t_2015_, lean_object* v_k_2016_, lean_object* v_fallback_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Std_DTreeMap_Raw_Const_getEntryGED___redArg(v_cmp_2014_, v_t_2015_, v_k_2016_, v_fallback_2017_);
lean_dec_ref(v_fallback_2017_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED(lean_object* v_00_u03b1_2019_, lean_object* v_cmp_2020_, lean_object* v_00_u03b2_2021_, lean_object* v_t_2022_, lean_object* v_k_2023_, lean_object* v_fallback_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_box(0);
v___x_2026_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2020_, v_k_2023_, v___x_2025_, v_t_2022_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_inc_ref(v_fallback_2024_);
return v_fallback_2024_;
}
else
{
lean_object* v_val_2027_; 
v_val_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_val_2027_);
lean_dec_ref(v___x_2026_);
return v_val_2027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2028_, lean_object* v_cmp_2029_, lean_object* v_00_u03b2_2030_, lean_object* v_t_2031_, lean_object* v_k_2032_, lean_object* v_fallback_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Std_DTreeMap_Raw_Const_getEntryGED(v_00_u03b1_2028_, v_cmp_2029_, v_00_u03b2_2030_, v_t_2031_, v_k_2032_, v_fallback_2033_);
lean_dec_ref(v_fallback_2033_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg(lean_object* v_cmp_2035_, lean_object* v_t_2036_, lean_object* v_k_2037_, lean_object* v_fallback_2038_){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_box(0);
v___x_2040_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2035_, v_k_2037_, v___x_2039_, v_t_2036_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_inc_ref(v_fallback_2038_);
return v_fallback_2038_;
}
else
{
lean_object* v_val_2041_; 
v_val_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_val_2041_);
lean_dec_ref(v___x_2040_);
return v_val_2041_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2042_, lean_object* v_t_2043_, lean_object* v_k_2044_, lean_object* v_fallback_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg(v_cmp_2042_, v_t_2043_, v_k_2044_, v_fallback_2045_);
lean_dec_ref(v_fallback_2045_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD(lean_object* v_00_u03b1_2047_, lean_object* v_cmp_2048_, lean_object* v_00_u03b2_2049_, lean_object* v_t_2050_, lean_object* v_k_2051_, lean_object* v_fallback_2052_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_box(0);
v___x_2054_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2048_, v_k_2051_, v___x_2053_, v_t_2050_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_inc_ref(v_fallback_2052_);
return v_fallback_2052_;
}
else
{
lean_object* v_val_2055_; 
v_val_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_val_2055_);
lean_dec_ref(v___x_2054_);
return v_val_2055_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2056_, lean_object* v_cmp_2057_, lean_object* v_00_u03b2_2058_, lean_object* v_t_2059_, lean_object* v_k_2060_, lean_object* v_fallback_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Std_DTreeMap_Raw_Const_getEntryGTD(v_00_u03b1_2056_, v_cmp_2057_, v_00_u03b2_2058_, v_t_2059_, v_k_2060_, v_fallback_2061_);
lean_dec_ref(v_fallback_2061_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___redArg(lean_object* v_cmp_2063_, lean_object* v_t_2064_, lean_object* v_k_2065_, lean_object* v_fallback_2066_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_box(0);
v___x_2068_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2063_, v_k_2065_, v___x_2067_, v_t_2064_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_inc_ref(v_fallback_2066_);
return v_fallback_2066_;
}
else
{
lean_object* v_val_2069_; 
v_val_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_val_2069_);
lean_dec_ref(v___x_2068_);
return v_val_2069_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2070_, lean_object* v_t_2071_, lean_object* v_k_2072_, lean_object* v_fallback_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Std_DTreeMap_Raw_Const_getEntryLED___redArg(v_cmp_2070_, v_t_2071_, v_k_2072_, v_fallback_2073_);
lean_dec_ref(v_fallback_2073_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED(lean_object* v_00_u03b1_2075_, lean_object* v_cmp_2076_, lean_object* v_00_u03b2_2077_, lean_object* v_t_2078_, lean_object* v_k_2079_, lean_object* v_fallback_2080_){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_box(0);
v___x_2082_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2076_, v_k_2079_, v___x_2081_, v_t_2078_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_inc_ref(v_fallback_2080_);
return v_fallback_2080_;
}
else
{
lean_object* v_val_2083_; 
v_val_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_val_2083_);
lean_dec_ref(v___x_2082_);
return v_val_2083_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2084_, lean_object* v_cmp_2085_, lean_object* v_00_u03b2_2086_, lean_object* v_t_2087_, lean_object* v_k_2088_, lean_object* v_fallback_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Std_DTreeMap_Raw_Const_getEntryLED(v_00_u03b1_2084_, v_cmp_2085_, v_00_u03b2_2086_, v_t_2087_, v_k_2088_, v_fallback_2089_);
lean_dec_ref(v_fallback_2089_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg(lean_object* v_cmp_2091_, lean_object* v_t_2092_, lean_object* v_k_2093_, lean_object* v_fallback_2094_){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = lean_box(0);
v___x_2096_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2091_, v_k_2093_, v___x_2095_, v_t_2092_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_inc_ref(v_fallback_2094_);
return v_fallback_2094_;
}
else
{
lean_object* v_val_2097_; 
v_val_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_val_2097_);
lean_dec_ref(v___x_2096_);
return v_val_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2098_, lean_object* v_t_2099_, lean_object* v_k_2100_, lean_object* v_fallback_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg(v_cmp_2098_, v_t_2099_, v_k_2100_, v_fallback_2101_);
lean_dec_ref(v_fallback_2101_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD(lean_object* v_00_u03b1_2103_, lean_object* v_cmp_2104_, lean_object* v_00_u03b2_2105_, lean_object* v_t_2106_, lean_object* v_k_2107_, lean_object* v_fallback_2108_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_box(0);
v___x_2110_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2104_, v_k_2107_, v___x_2109_, v_t_2106_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_inc_ref(v_fallback_2108_);
return v_fallback_2108_;
}
else
{
lean_object* v_val_2111_; 
v_val_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_val_2111_);
lean_dec_ref(v___x_2110_);
return v_val_2111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2112_, lean_object* v_cmp_2113_, lean_object* v_00_u03b2_2114_, lean_object* v_t_2115_, lean_object* v_k_2116_, lean_object* v_fallback_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Std_DTreeMap_Raw_Const_getEntryLTD(v_00_u03b1_2112_, v_cmp_2113_, v_00_u03b2_2114_, v_t_2115_, v_k_2116_, v_fallback_2117_);
lean_dec_ref(v_fallback_2117_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter___redArg(lean_object* v_f_2119_, lean_object* v_t_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_2119_, v_t_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter(lean_object* v_00_u03b1_2122_, lean_object* v_00_u03b2_2123_, lean_object* v_cmp_2124_, lean_object* v_f_2125_, lean_object* v_t_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_2125_, v_t_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter___boxed(lean_object* v_00_u03b1_2128_, lean_object* v_00_u03b2_2129_, lean_object* v_cmp_2130_, lean_object* v_f_2131_, lean_object* v_t_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Std_DTreeMap_Raw_filter(v_00_u03b1_2128_, v_00_u03b2_2129_, v_cmp_2130_, v_f_2131_, v_t_2132_);
lean_dec_ref(v_cmp_2130_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM___redArg(lean_object* v_inst_2134_, lean_object* v_f_2135_, lean_object* v_init_2136_, lean_object* v_t_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2134_, v_f_2135_, v_init_2136_, v_t_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM(lean_object* v_00_u03b1_2139_, lean_object* v_00_u03b2_2140_, lean_object* v_cmp_2141_, lean_object* v_00_u03b4_2142_, lean_object* v_m_2143_, lean_object* v_inst_2144_, lean_object* v_f_2145_, lean_object* v_init_2146_, lean_object* v_t_2147_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2144_, v_f_2145_, v_init_2146_, v_t_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM___boxed(lean_object* v_00_u03b1_2149_, lean_object* v_00_u03b2_2150_, lean_object* v_cmp_2151_, lean_object* v_00_u03b4_2152_, lean_object* v_m_2153_, lean_object* v_inst_2154_, lean_object* v_f_2155_, lean_object* v_init_2156_, lean_object* v_t_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Std_DTreeMap_Raw_foldlM(v_00_u03b1_2149_, v_00_u03b2_2150_, v_cmp_2151_, v_00_u03b4_2152_, v_m_2153_, v_inst_2154_, v_f_2155_, v_init_2156_, v_t_2157_);
lean_dec_ref(v_cmp_2151_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl___redArg(lean_object* v_f_2159_, lean_object* v_init_2160_, lean_object* v_t_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2159_, v_init_2160_, v_t_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl(lean_object* v_00_u03b1_2163_, lean_object* v_00_u03b2_2164_, lean_object* v_cmp_2165_, lean_object* v_00_u03b4_2166_, lean_object* v_f_2167_, lean_object* v_init_2168_, lean_object* v_t_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2167_, v_init_2168_, v_t_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl___boxed(lean_object* v_00_u03b1_2171_, lean_object* v_00_u03b2_2172_, lean_object* v_cmp_2173_, lean_object* v_00_u03b4_2174_, lean_object* v_f_2175_, lean_object* v_init_2176_, lean_object* v_t_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Std_DTreeMap_Raw_foldl(v_00_u03b1_2171_, v_00_u03b2_2172_, v_cmp_2173_, v_00_u03b4_2174_, v_f_2175_, v_init_2176_, v_t_2177_);
lean_dec_ref(v_cmp_2173_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM___redArg(lean_object* v_inst_2179_, lean_object* v_f_2180_, lean_object* v_init_2181_, lean_object* v_t_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2179_, v_f_2180_, v_init_2181_, v_t_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM(lean_object* v_00_u03b1_2184_, lean_object* v_00_u03b2_2185_, lean_object* v_cmp_2186_, lean_object* v_00_u03b4_2187_, lean_object* v_m_2188_, lean_object* v_inst_2189_, lean_object* v_f_2190_, lean_object* v_init_2191_, lean_object* v_t_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2189_, v_f_2190_, v_init_2191_, v_t_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM___boxed(lean_object* v_00_u03b1_2194_, lean_object* v_00_u03b2_2195_, lean_object* v_cmp_2196_, lean_object* v_00_u03b4_2197_, lean_object* v_m_2198_, lean_object* v_inst_2199_, lean_object* v_f_2200_, lean_object* v_init_2201_, lean_object* v_t_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Std_DTreeMap_Raw_foldrM(v_00_u03b1_2194_, v_00_u03b2_2195_, v_cmp_2196_, v_00_u03b4_2197_, v_m_2198_, v_inst_2199_, v_f_2200_, v_init_2201_, v_t_2202_);
lean_dec_ref(v_cmp_2196_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___redArg___lam__0(lean_object* v_f_2204_, lean_object* v_x1_2205_, lean_object* v_x2_2206_, lean_object* v_x3_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = lean_apply_3(v_f_2204_, v_x1_2205_, v_x2_2206_, v_x3_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___redArg(lean_object* v_f_2228_, lean_object* v_init_2229_, lean_object* v_t_2230_){
_start:
{
lean_object* v___f_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___f_2231_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2231_, 0, v_f_2228_);
v___x_2232_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2233_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2232_, v___f_2231_, v_init_2229_, v_t_2230_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr(lean_object* v_00_u03b1_2234_, lean_object* v_00_u03b2_2235_, lean_object* v_cmp_2236_, lean_object* v_00_u03b4_2237_, lean_object* v_f_2238_, lean_object* v_init_2239_, lean_object* v_t_2240_){
_start:
{
lean_object* v___f_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___f_2241_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2241_, 0, v_f_2238_);
v___x_2242_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2243_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2242_, v___f_2241_, v_init_2239_, v_t_2240_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___boxed(lean_object* v_00_u03b1_2244_, lean_object* v_00_u03b2_2245_, lean_object* v_cmp_2246_, lean_object* v_00_u03b4_2247_, lean_object* v_f_2248_, lean_object* v_init_2249_, lean_object* v_t_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Std_DTreeMap_Raw_foldr(v_00_u03b1_2244_, v_00_u03b2_2245_, v_cmp_2246_, v_00_u03b4_2247_, v_f_2248_, v_init_2249_, v_t_2250_);
lean_dec_ref(v_cmp_2246_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition___redArg___lam__0(lean_object* v_f_2252_, lean_object* v_cmp_2253_, lean_object* v_x_2254_, lean_object* v_a_2255_, lean_object* v_b_2256_){
_start:
{
lean_object* v_fst_2257_; lean_object* v_snd_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2272_; 
v_fst_2257_ = lean_ctor_get(v_x_2254_, 0);
v_snd_2258_ = lean_ctor_get(v_x_2254_, 1);
v_isSharedCheck_2272_ = !lean_is_exclusive(v_x_2254_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2260_ = v_x_2254_;
v_isShared_2261_ = v_isSharedCheck_2272_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_snd_2258_);
lean_inc(v_fst_2257_);
lean_dec(v_x_2254_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2272_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; uint8_t v___x_2263_; 
lean_inc(v_b_2256_);
lean_inc(v_a_2255_);
v___x_2262_ = lean_apply_2(v_f_2252_, v_a_2255_, v_b_2256_);
v___x_2263_ = lean_unbox(v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2264_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2253_, v_a_2255_, v_b_2256_, v_snd_2258_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 1, v___x_2264_);
v___x_2266_ = v___x_2260_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_fst_2257_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2268_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2253_, v_a_2255_, v_b_2256_, v_fst_2257_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2268_);
v___x_2270_ = v___x_2260_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_snd_2258_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition___redArg(lean_object* v_cmp_2275_, lean_object* v_f_2276_, lean_object* v_t_2277_){
_start:
{
lean_object* v___f_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___f_2278_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2278_, 0, v_f_2276_);
lean_closure_set(v___f_2278_, 1, v_cmp_2275_);
v___x_2279_ = ((lean_object*)(l_Std_DTreeMap_Raw_partition___redArg___closed__0));
v___x_2280_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2278_, v___x_2279_, v_t_2277_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition(lean_object* v_00_u03b1_2281_, lean_object* v_00_u03b2_2282_, lean_object* v_cmp_2283_, lean_object* v_f_2284_, lean_object* v_t_2285_){
_start:
{
lean_object* v___f_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___f_2286_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2286_, 0, v_f_2284_);
lean_closure_set(v___f_2286_, 1, v_cmp_2283_);
v___x_2287_ = ((lean_object*)(l_Std_DTreeMap_Raw_partition___redArg___closed__0));
v___x_2288_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2286_, v___x_2287_, v_t_2285_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___redArg___lam__0(lean_object* v_f_2289_, lean_object* v_x_2290_, lean_object* v_k_2291_, lean_object* v_v_2292_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_apply_2(v_f_2289_, v_k_2291_, v_v_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___redArg(lean_object* v_inst_2294_, lean_object* v_f_2295_, lean_object* v_t_2296_){
_start:
{
lean_object* v___f_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___f_2297_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2297_, 0, v_f_2295_);
v___x_2298_ = lean_box(0);
v___x_2299_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2294_, v___f_2297_, v___x_2298_, v_t_2296_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM(lean_object* v_00_u03b1_2300_, lean_object* v_00_u03b2_2301_, lean_object* v_cmp_2302_, lean_object* v_m_2303_, lean_object* v_inst_2304_, lean_object* v_f_2305_, lean_object* v_t_2306_){
_start:
{
lean_object* v___f_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___f_2307_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2307_, 0, v_f_2305_);
v___x_2308_ = lean_box(0);
v___x_2309_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2304_, v___f_2307_, v___x_2308_, v_t_2306_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___boxed(lean_object* v_00_u03b1_2310_, lean_object* v_00_u03b2_2311_, lean_object* v_cmp_2312_, lean_object* v_m_2313_, lean_object* v_inst_2314_, lean_object* v_f_2315_, lean_object* v_t_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Std_DTreeMap_Raw_forM(v_00_u03b1_2310_, v_00_u03b2_2311_, v_cmp_2312_, v_m_2313_, v_inst_2314_, v_f_2315_, v_t_2316_);
lean_dec_ref(v_cmp_2312_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___redArg___lam__0(lean_object* v_toPure_2318_, lean_object* v_____do__lift_2319_){
_start:
{
lean_object* v_a_2320_; lean_object* v___x_2321_; 
v_a_2320_ = lean_ctor_get(v_____do__lift_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref(v_____do__lift_2319_);
v___x_2321_ = lean_apply_2(v_toPure_2318_, lean_box(0), v_a_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___redArg(lean_object* v_inst_2322_, lean_object* v_f_2323_, lean_object* v_init_2324_, lean_object* v_t_2325_){
_start:
{
lean_object* v_toApplicative_2326_; lean_object* v_toBind_2327_; lean_object* v_toPure_2328_; lean_object* v___x_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; 
v_toApplicative_2326_ = lean_ctor_get(v_inst_2322_, 0);
v_toBind_2327_ = lean_ctor_get(v_inst_2322_, 1);
lean_inc(v_toBind_2327_);
v_toPure_2328_ = lean_ctor_get(v_toApplicative_2326_, 1);
lean_inc(v_toPure_2328_);
v___x_2329_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2322_, v_f_2323_, v_init_2324_, v_t_2325_);
v___f_2330_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2330_, 0, v_toPure_2328_);
v___x_2331_ = lean_apply_4(v_toBind_2327_, lean_box(0), lean_box(0), v___x_2329_, v___f_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn(lean_object* v_00_u03b1_2332_, lean_object* v_00_u03b2_2333_, lean_object* v_cmp_2334_, lean_object* v_00_u03b4_2335_, lean_object* v_m_2336_, lean_object* v_inst_2337_, lean_object* v_f_2338_, lean_object* v_init_2339_, lean_object* v_t_2340_){
_start:
{
lean_object* v_toApplicative_2341_; lean_object* v_toBind_2342_; lean_object* v_toPure_2343_; lean_object* v___x_2344_; lean_object* v___f_2345_; lean_object* v___x_2346_; 
v_toApplicative_2341_ = lean_ctor_get(v_inst_2337_, 0);
v_toBind_2342_ = lean_ctor_get(v_inst_2337_, 1);
lean_inc(v_toBind_2342_);
v_toPure_2343_ = lean_ctor_get(v_toApplicative_2341_, 1);
lean_inc(v_toPure_2343_);
v___x_2344_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2337_, v_f_2338_, v_init_2339_, v_t_2340_);
v___f_2345_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2345_, 0, v_toPure_2343_);
v___x_2346_ = lean_apply_4(v_toBind_2342_, lean_box(0), lean_box(0), v___x_2344_, v___f_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___boxed(lean_object* v_00_u03b1_2347_, lean_object* v_00_u03b2_2348_, lean_object* v_cmp_2349_, lean_object* v_00_u03b4_2350_, lean_object* v_m_2351_, lean_object* v_inst_2352_, lean_object* v_f_2353_, lean_object* v_init_2354_, lean_object* v_t_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Std_DTreeMap_Raw_forIn(v_00_u03b1_2347_, v_00_u03b2_2348_, v_cmp_2349_, v_00_u03b4_2350_, v_m_2351_, v_inst_2352_, v_f_2353_, v_init_2354_, v_t_2355_);
lean_dec_ref(v_cmp_2349_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_2357_, lean_object* v_x_2358_, lean_object* v_k_2359_, lean_object* v_v_2360_){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2361_, 0, v_k_2359_);
lean_ctor_set(v___x_2361_, 1, v_v_2360_);
v___x_2362_ = lean_apply_1(v_f_2357_, v___x_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1(lean_object* v_inst_2363_, lean_object* v_t_2364_, lean_object* v_f_2365_){
_start:
{
lean_object* v___f_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___f_2366_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2366_, 0, v_f_2365_);
v___x_2367_ = lean_box(0);
v___x_2368_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2363_, v___f_2366_, v___x_2367_, v_t_2364_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg(lean_object* v_inst_2369_){
_start:
{
lean_object* v___f_2370_; 
v___f_2370_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2370_, 0, v_inst_2369_);
return v___f_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad(lean_object* v_00_u03b1_2371_, lean_object* v_00_u03b2_2372_, lean_object* v_cmp_2373_, lean_object* v_m_2374_, lean_object* v_inst_2375_){
_start:
{
lean_object* v___f_2376_; 
v___f_2376_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2376_, 0, v_inst_2375_);
return v___f_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___boxed(lean_object* v_00_u03b1_2377_, lean_object* v_00_u03b2_2378_, lean_object* v_cmp_2379_, lean_object* v_m_2380_, lean_object* v_inst_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Std_DTreeMap_Raw_instForMSigmaOfMonad(v_00_u03b1_2377_, v_00_u03b2_2378_, v_cmp_2379_, v_m_2380_, v_inst_2381_);
lean_dec_ref(v_cmp_2379_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_2383_, lean_object* v_a_2384_, lean_object* v_b_2385_, lean_object* v_acc_2386_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v_a_2384_);
lean_ctor_set(v___x_2387_, 1, v_b_2385_);
v___x_2388_ = lean_apply_2(v_f_2383_, v___x_2387_, v_acc_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_2389_, lean_object* v_00_u03b2_2390_, lean_object* v_t_2391_, lean_object* v_init_2392_, lean_object* v_f_2393_){
_start:
{
lean_object* v_toApplicative_2394_; lean_object* v_toBind_2395_; lean_object* v_toPure_2396_; lean_object* v___f_2397_; lean_object* v___x_2398_; lean_object* v___f_2399_; lean_object* v___x_2400_; 
v_toApplicative_2394_ = lean_ctor_get(v_inst_2389_, 0);
v_toBind_2395_ = lean_ctor_get(v_inst_2389_, 1);
lean_inc(v_toBind_2395_);
v_toPure_2396_ = lean_ctor_get(v_toApplicative_2394_, 1);
lean_inc(v_toPure_2396_);
v___f_2397_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2397_, 0, v_f_2393_);
v___x_2398_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2389_, v___f_2397_, v_init_2392_, v_t_2391_);
v___f_2399_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2399_, 0, v_toPure_2396_);
v___x_2400_ = lean_apply_4(v_toBind_2395_, lean_box(0), lean_box(0), v___x_2398_, v___f_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg(lean_object* v_inst_2401_){
_start:
{
lean_object* v___f_2402_; 
v___f_2402_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2402_, 0, v_inst_2401_);
return v___f_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad(lean_object* v_00_u03b1_2403_, lean_object* v_00_u03b2_2404_, lean_object* v_cmp_2405_, lean_object* v_m_2406_, lean_object* v_inst_2407_){
_start:
{
lean_object* v___f_2408_; 
v___f_2408_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2408_, 0, v_inst_2407_);
return v___f_2408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___boxed(lean_object* v_00_u03b1_2409_, lean_object* v_00_u03b2_2410_, lean_object* v_cmp_2411_, lean_object* v_m_2412_, lean_object* v_inst_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Std_DTreeMap_Raw_instForInSigmaOfMonad(v_00_u03b1_2409_, v_00_u03b2_2410_, v_cmp_2411_, v_m_2412_, v_inst_2413_);
lean_dec_ref(v_cmp_2411_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2415_, lean_object* v_x_2416_, lean_object* v_k_2417_, lean_object* v_v_2418_){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v_k_2417_);
lean_ctor_set(v___x_2419_, 1, v_v_2418_);
v___x_2420_ = lean_apply_1(v_f_2415_, v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___redArg(lean_object* v_inst_2421_, lean_object* v_f_2422_, lean_object* v_t_2423_){
_start:
{
lean_object* v___f_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___f_2424_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2424_, 0, v_f_2422_);
v___x_2425_ = lean_box(0);
v___x_2426_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2421_, v___f_2424_, v___x_2425_, v_t_2423_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried(lean_object* v_00_u03b1_2427_, lean_object* v_cmp_2428_, lean_object* v_m_2429_, lean_object* v_inst_2430_, lean_object* v_00_u03b2_2431_, lean_object* v_f_2432_, lean_object* v_t_2433_){
_start:
{
lean_object* v___f_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___f_2434_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2434_, 0, v_f_2432_);
v___x_2435_ = lean_box(0);
v___x_2436_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2430_, v___f_2434_, v___x_2435_, v_t_2433_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2437_, lean_object* v_cmp_2438_, lean_object* v_m_2439_, lean_object* v_inst_2440_, lean_object* v_00_u03b2_2441_, lean_object* v_f_2442_, lean_object* v_t_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Std_DTreeMap_Raw_Const_forMUncurried(v_00_u03b1_2437_, v_cmp_2438_, v_m_2439_, v_inst_2440_, v_00_u03b2_2441_, v_f_2442_, v_t_2443_);
lean_dec_ref(v_cmp_2438_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2445_, lean_object* v_a_2446_, lean_object* v_b_2447_, lean_object* v_d_2448_){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v_a_2446_);
lean_ctor_set(v___x_2449_, 1, v_b_2447_);
v___x_2450_ = lean_apply_2(v_f_2445_, v___x_2449_, v_d_2448_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___redArg(lean_object* v_inst_2451_, lean_object* v_f_2452_, lean_object* v_init_2453_, lean_object* v_t_2454_){
_start:
{
lean_object* v_toApplicative_2455_; lean_object* v_toBind_2456_; lean_object* v_toPure_2457_; lean_object* v___f_2458_; lean_object* v___x_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; 
v_toApplicative_2455_ = lean_ctor_get(v_inst_2451_, 0);
v_toBind_2456_ = lean_ctor_get(v_inst_2451_, 1);
lean_inc(v_toBind_2456_);
v_toPure_2457_ = lean_ctor_get(v_toApplicative_2455_, 1);
lean_inc(v_toPure_2457_);
v___f_2458_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2458_, 0, v_f_2452_);
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2451_, v___f_2458_, v_init_2453_, v_t_2454_);
v___f_2460_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2460_, 0, v_toPure_2457_);
v___x_2461_ = lean_apply_4(v_toBind_2456_, lean_box(0), lean_box(0), v___x_2459_, v___f_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried(lean_object* v_00_u03b1_2462_, lean_object* v_cmp_2463_, lean_object* v_00_u03b4_2464_, lean_object* v_m_2465_, lean_object* v_inst_2466_, lean_object* v_00_u03b2_2467_, lean_object* v_f_2468_, lean_object* v_init_2469_, lean_object* v_t_2470_){
_start:
{
lean_object* v_toApplicative_2471_; lean_object* v_toBind_2472_; lean_object* v_toPure_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v___f_2476_; lean_object* v___x_2477_; 
v_toApplicative_2471_ = lean_ctor_get(v_inst_2466_, 0);
v_toBind_2472_ = lean_ctor_get(v_inst_2466_, 1);
lean_inc(v_toBind_2472_);
v_toPure_2473_ = lean_ctor_get(v_toApplicative_2471_, 1);
lean_inc(v_toPure_2473_);
v___f_2474_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2474_, 0, v_f_2468_);
v___x_2475_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2466_, v___f_2474_, v_init_2469_, v_t_2470_);
v___f_2476_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2476_, 0, v_toPure_2473_);
v___x_2477_ = lean_apply_4(v_toBind_2472_, lean_box(0), lean_box(0), v___x_2475_, v___f_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2478_, lean_object* v_cmp_2479_, lean_object* v_00_u03b4_2480_, lean_object* v_m_2481_, lean_object* v_inst_2482_, lean_object* v_00_u03b2_2483_, lean_object* v_f_2484_, lean_object* v_init_2485_, lean_object* v_t_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Std_DTreeMap_Raw_Const_forInUncurried(v_00_u03b1_2478_, v_cmp_2479_, v_00_u03b4_2480_, v_m_2481_, v_inst_2482_, v_00_u03b2_2483_, v_f_2484_, v_init_2485_, v_t_2486_);
lean_dec_ref(v_cmp_2479_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___lam__0(lean_object* v_p_2488_, lean_object* v___x_2489_, lean_object* v___x_2490_, lean_object* v_a_2491_, lean_object* v_b_2492_, lean_object* v_acc_2493_){
_start:
{
lean_object* v___x_2494_; uint8_t v___x_2495_; 
v___x_2494_ = lean_apply_2(v_p_2488_, v_a_2491_, v_b_2492_);
v___x_2495_ = lean_unbox(v___x_2494_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; 
v___x_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2489_);
return v___x_2496_;
}
else
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec_ref(v___x_2489_);
v___x_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2494_);
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
lean_ctor_set(v___x_2498_, 1, v___x_2490_);
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
return v___x_2499_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_2500_, lean_object* v___x_2501_, lean_object* v___x_2502_, lean_object* v_a_2503_, lean_object* v_b_2504_, lean_object* v_acc_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Std_DTreeMap_Raw_any___redArg___lam__0(v_p_2500_, v___x_2501_, v___x_2502_, v_a_2503_, v_b_2504_, v_acc_2505_);
lean_dec_ref(v_acc_2505_);
return v_res_2506_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_any___redArg(lean_object* v_t_2510_, lean_object* v_p_2511_){
_start:
{
lean_object* v___y_2513_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___f_2521_; lean_object* v___x_2522_; lean_object* v_a_2523_; 
v___x_2518_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2519_ = lean_box(0);
v___x_2520_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2521_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2521_, 0, v_p_2511_);
lean_closure_set(v___f_2521_, 1, v___x_2520_);
lean_closure_set(v___f_2521_, 2, v___x_2519_);
v___x_2522_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2518_, v___f_2521_, v___x_2520_, v_t_2510_);
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___y_2513_ = v_a_2523_;
goto v___jp_2512_;
v___jp_2512_:
{
lean_object* v_fst_2514_; 
v_fst_2514_ = lean_ctor_get(v___y_2513_, 0);
lean_inc(v_fst_2514_);
lean_dec_ref(v___y_2513_);
if (lean_obj_tag(v_fst_2514_) == 0)
{
uint8_t v___x_2515_; 
v___x_2515_ = 0;
return v___x_2515_;
}
else
{
lean_object* v_val_2516_; uint8_t v___x_2517_; 
v_val_2516_ = lean_ctor_get(v_fst_2514_, 0);
lean_inc(v_val_2516_);
lean_dec_ref(v_fst_2514_);
v___x_2517_ = lean_unbox(v_val_2516_);
lean_dec(v_val_2516_);
return v___x_2517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___boxed(lean_object* v_t_2524_, lean_object* v_p_2525_){
_start:
{
uint8_t v_res_2526_; lean_object* v_r_2527_; 
v_res_2526_ = l_Std_DTreeMap_Raw_any___redArg(v_t_2524_, v_p_2525_);
v_r_2527_ = lean_box(v_res_2526_);
return v_r_2527_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_any(lean_object* v_00_u03b1_2528_, lean_object* v_00_u03b2_2529_, lean_object* v_cmp_2530_, lean_object* v_t_2531_, lean_object* v_p_2532_){
_start:
{
lean_object* v___y_2534_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___f_2542_; lean_object* v___x_2543_; lean_object* v_a_2544_; 
v___x_2539_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2540_ = lean_box(0);
v___x_2541_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2542_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2542_, 0, v_p_2532_);
lean_closure_set(v___f_2542_, 1, v___x_2541_);
lean_closure_set(v___f_2542_, 2, v___x_2540_);
v___x_2543_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2539_, v___f_2542_, v___x_2541_, v_t_2531_);
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___y_2534_ = v_a_2544_;
goto v___jp_2533_;
v___jp_2533_:
{
lean_object* v_fst_2535_; 
v_fst_2535_ = lean_ctor_get(v___y_2534_, 0);
lean_inc(v_fst_2535_);
lean_dec_ref(v___y_2534_);
if (lean_obj_tag(v_fst_2535_) == 0)
{
uint8_t v___x_2536_; 
v___x_2536_ = 0;
return v___x_2536_;
}
else
{
lean_object* v_val_2537_; uint8_t v___x_2538_; 
v_val_2537_ = lean_ctor_get(v_fst_2535_, 0);
lean_inc(v_val_2537_);
lean_dec_ref(v_fst_2535_);
v___x_2538_ = lean_unbox(v_val_2537_);
lean_dec(v_val_2537_);
return v___x_2538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___boxed(lean_object* v_00_u03b1_2545_, lean_object* v_00_u03b2_2546_, lean_object* v_cmp_2547_, lean_object* v_t_2548_, lean_object* v_p_2549_){
_start:
{
uint8_t v_res_2550_; lean_object* v_r_2551_; 
v_res_2550_ = l_Std_DTreeMap_Raw_any(v_00_u03b1_2545_, v_00_u03b2_2546_, v_cmp_2547_, v_t_2548_, v_p_2549_);
lean_dec_ref(v_cmp_2547_);
v_r_2551_ = lean_box(v_res_2550_);
return v_r_2551_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___lam__0(lean_object* v_p_2552_, lean_object* v___x_2553_, lean_object* v___x_2554_, lean_object* v_a_2555_, lean_object* v_b_2556_, lean_object* v_acc_2557_){
_start:
{
lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2558_ = lean_apply_2(v_p_2552_, v_a_2555_, v_b_2556_);
v___x_2559_ = lean_unbox(v___x_2558_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_dec_ref(v___x_2554_);
v___x_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
lean_ctor_set(v___x_2561_, 1, v___x_2553_);
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
return v___x_2562_;
}
else
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2554_);
return v___x_2563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_2564_, lean_object* v___x_2565_, lean_object* v___x_2566_, lean_object* v_a_2567_, lean_object* v_b_2568_, lean_object* v_acc_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Std_DTreeMap_Raw_all___redArg___lam__0(v_p_2564_, v___x_2565_, v___x_2566_, v_a_2567_, v_b_2568_, v_acc_2569_);
lean_dec_ref(v_acc_2569_);
return v_res_2570_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_all___redArg(lean_object* v_t_2571_, lean_object* v_p_2572_){
_start:
{
lean_object* v___y_2574_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___f_2582_; lean_object* v___x_2583_; lean_object* v_a_2584_; 
v___x_2579_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2580_ = lean_box(0);
v___x_2581_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2582_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2582_, 0, v_p_2572_);
lean_closure_set(v___f_2582_, 1, v___x_2580_);
lean_closure_set(v___f_2582_, 2, v___x_2581_);
v___x_2583_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2579_, v___f_2582_, v___x_2581_, v_t_2571_);
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___y_2574_ = v_a_2584_;
goto v___jp_2573_;
v___jp_2573_:
{
lean_object* v_fst_2575_; 
v_fst_2575_ = lean_ctor_get(v___y_2574_, 0);
lean_inc(v_fst_2575_);
lean_dec_ref(v___y_2574_);
if (lean_obj_tag(v_fst_2575_) == 0)
{
uint8_t v___x_2576_; 
v___x_2576_ = 1;
return v___x_2576_;
}
else
{
lean_object* v_val_2577_; uint8_t v___x_2578_; 
v_val_2577_ = lean_ctor_get(v_fst_2575_, 0);
lean_inc(v_val_2577_);
lean_dec_ref(v_fst_2575_);
v___x_2578_ = lean_unbox(v_val_2577_);
lean_dec(v_val_2577_);
return v___x_2578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___boxed(lean_object* v_t_2585_, lean_object* v_p_2586_){
_start:
{
uint8_t v_res_2587_; lean_object* v_r_2588_; 
v_res_2587_ = l_Std_DTreeMap_Raw_all___redArg(v_t_2585_, v_p_2586_);
v_r_2588_ = lean_box(v_res_2587_);
return v_r_2588_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_all(lean_object* v_00_u03b1_2589_, lean_object* v_00_u03b2_2590_, lean_object* v_cmp_2591_, lean_object* v_t_2592_, lean_object* v_p_2593_){
_start:
{
lean_object* v___y_2595_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___f_2603_; lean_object* v___x_2604_; lean_object* v_a_2605_; 
v___x_2600_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2601_ = lean_box(0);
v___x_2602_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2603_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2603_, 0, v_p_2593_);
lean_closure_set(v___f_2603_, 1, v___x_2601_);
lean_closure_set(v___f_2603_, 2, v___x_2602_);
v___x_2604_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2600_, v___f_2603_, v___x_2602_, v_t_2592_);
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec(v___x_2604_);
v___y_2595_ = v_a_2605_;
goto v___jp_2594_;
v___jp_2594_:
{
lean_object* v_fst_2596_; 
v_fst_2596_ = lean_ctor_get(v___y_2595_, 0);
lean_inc(v_fst_2596_);
lean_dec_ref(v___y_2595_);
if (lean_obj_tag(v_fst_2596_) == 0)
{
uint8_t v___x_2597_; 
v___x_2597_ = 1;
return v___x_2597_;
}
else
{
lean_object* v_val_2598_; uint8_t v___x_2599_; 
v_val_2598_ = lean_ctor_get(v_fst_2596_, 0);
lean_inc(v_val_2598_);
lean_dec_ref(v_fst_2596_);
v___x_2599_ = lean_unbox(v_val_2598_);
lean_dec(v_val_2598_);
return v___x_2599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___boxed(lean_object* v_00_u03b1_2606_, lean_object* v_00_u03b2_2607_, lean_object* v_cmp_2608_, lean_object* v_t_2609_, lean_object* v_p_2610_){
_start:
{
uint8_t v_res_2611_; lean_object* v_r_2612_; 
v_res_2611_ = l_Std_DTreeMap_Raw_all(v_00_u03b1_2606_, v_00_u03b2_2607_, v_cmp_2608_, v_t_2609_, v_p_2610_);
lean_dec_ref(v_cmp_2608_);
v_r_2612_ = lean_box(v_res_2611_);
return v_r_2612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg___lam__0(lean_object* v_x1_2613_, lean_object* v_x2_2614_, lean_object* v_x3_2615_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2616_, 0, v_x1_2613_);
lean_ctor_set(v___x_2616_, 1, v_x3_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_x1_2617_, lean_object* v_x2_2618_, lean_object* v_x3_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Std_DTreeMap_Raw_keys___redArg___lam__0(v_x1_2617_, v_x2_2618_, v_x3_2619_);
lean_dec(v_x2_2618_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg(lean_object* v_t_2622_){
_start:
{
lean_object* v___f_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___f_2623_ = ((lean_object*)(l_Std_DTreeMap_Raw_keys___redArg___closed__0));
v___x_2624_ = lean_box(0);
v___x_2625_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2626_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2625_, v___f_2623_, v___x_2624_, v_t_2622_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys(lean_object* v_00_u03b1_2627_, lean_object* v_00_u03b2_2628_, lean_object* v_cmp_2629_, lean_object* v_t_2630_){
_start:
{
lean_object* v___f_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___f_2631_ = ((lean_object*)(l_Std_DTreeMap_Raw_keys___redArg___closed__0));
v___x_2632_ = lean_box(0);
v___x_2633_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2634_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2633_, v___f_2631_, v___x_2632_, v_t_2630_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___boxed(lean_object* v_00_u03b1_2635_, lean_object* v_00_u03b2_2636_, lean_object* v_cmp_2637_, lean_object* v_t_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Std_DTreeMap_Raw_keys(v_00_u03b1_2635_, v_00_u03b2_2636_, v_cmp_2637_, v_t_2638_);
lean_dec_ref(v_cmp_2637_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___lam__0(lean_object* v_l_2640_, lean_object* v_k_2641_, lean_object* v_x_2642_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = lean_array_push(v_l_2640_, v_k_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_l_2644_, lean_object* v_k_2645_, lean_object* v_x_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Std_DTreeMap_Raw_keysArray___redArg___lam__0(v_l_2644_, v_k_2645_, v_x_2646_);
lean_dec(v_x_2646_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg(lean_object* v_t_2649_){
_start:
{
lean_object* v___f_2650_; lean_object* v___y_2652_; 
v___f_2650_ = ((lean_object*)(l_Std_DTreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2649_) == 0)
{
lean_object* v_size_2655_; 
v_size_2655_ = lean_ctor_get(v_t_2649_, 0);
lean_inc(v_size_2655_);
v___y_2652_ = v_size_2655_;
goto v___jp_2651_;
}
else
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_unsigned_to_nat(0u);
v___y_2652_ = v___x_2656_;
goto v___jp_2651_;
}
v___jp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_mk_empty_array_with_capacity(v___y_2652_);
lean_dec(v___y_2652_);
v___x_2654_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2650_, v___x_2653_, v_t_2649_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray(lean_object* v_00_u03b1_2657_, lean_object* v_00_u03b2_2658_, lean_object* v_cmp_2659_, lean_object* v_t_2660_){
_start:
{
lean_object* v___f_2661_; lean_object* v___y_2663_; 
v___f_2661_ = ((lean_object*)(l_Std_DTreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2660_) == 0)
{
lean_object* v_size_2666_; 
v_size_2666_ = lean_ctor_get(v_t_2660_, 0);
lean_inc(v_size_2666_);
v___y_2663_ = v_size_2666_;
goto v___jp_2662_;
}
else
{
lean_object* v___x_2667_; 
v___x_2667_ = lean_unsigned_to_nat(0u);
v___y_2663_ = v___x_2667_;
goto v___jp_2662_;
}
v___jp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_mk_empty_array_with_capacity(v___y_2663_);
lean_dec(v___y_2663_);
v___x_2665_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2661_, v___x_2664_, v_t_2660_);
return v___x_2665_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___boxed(lean_object* v_00_u03b1_2668_, lean_object* v_00_u03b2_2669_, lean_object* v_cmp_2670_, lean_object* v_t_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Std_DTreeMap_Raw_keysArray(v_00_u03b1_2668_, v_00_u03b2_2669_, v_cmp_2670_, v_t_2671_);
lean_dec_ref(v_cmp_2670_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg___lam__0(lean_object* v_x1_2673_, lean_object* v_x2_2674_, lean_object* v_x3_2675_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2676_, 0, v_x2_2674_);
lean_ctor_set(v___x_2676_, 1, v_x3_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg___lam__0___boxed(lean_object* v_x1_2677_, lean_object* v_x2_2678_, lean_object* v_x3_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Std_DTreeMap_Raw_values___redArg___lam__0(v_x1_2677_, v_x2_2678_, v_x3_2679_);
lean_dec(v_x1_2677_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg(lean_object* v_t_2682_){
_start:
{
lean_object* v___f_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___f_2683_ = ((lean_object*)(l_Std_DTreeMap_Raw_values___redArg___closed__0));
v___x_2684_ = lean_box(0);
v___x_2685_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2686_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2685_, v___f_2683_, v___x_2684_, v_t_2682_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values(lean_object* v_00_u03b1_2687_, lean_object* v_cmp_2688_, lean_object* v_00_u03b2_2689_, lean_object* v_t_2690_){
_start:
{
lean_object* v___f_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___f_2691_ = ((lean_object*)(l_Std_DTreeMap_Raw_values___redArg___closed__0));
v___x_2692_ = lean_box(0);
v___x_2693_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2694_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2693_, v___f_2691_, v___x_2692_, v_t_2690_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___boxed(lean_object* v_00_u03b1_2695_, lean_object* v_cmp_2696_, lean_object* v_00_u03b2_2697_, lean_object* v_t_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Std_DTreeMap_Raw_values(v_00_u03b1_2695_, v_cmp_2696_, v_00_u03b2_2697_, v_t_2698_);
lean_dec_ref(v_cmp_2696_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0(lean_object* v_l_2700_, lean_object* v_x_2701_, lean_object* v_v_2702_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_array_push(v_l_2700_, v_v_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2704_, lean_object* v_x_2705_, lean_object* v_v_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0(v_l_2704_, v_x_2705_, v_v_2706_);
lean_dec(v_x_2705_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg(lean_object* v_t_2709_){
_start:
{
lean_object* v___f_2710_; lean_object* v___y_2712_; 
v___f_2710_ = ((lean_object*)(l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2709_) == 0)
{
lean_object* v_size_2715_; 
v_size_2715_ = lean_ctor_get(v_t_2709_, 0);
lean_inc(v_size_2715_);
v___y_2712_ = v_size_2715_;
goto v___jp_2711_;
}
else
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_unsigned_to_nat(0u);
v___y_2712_ = v___x_2716_;
goto v___jp_2711_;
}
v___jp_2711_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_mk_empty_array_with_capacity(v___y_2712_);
lean_dec(v___y_2712_);
v___x_2714_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2710_, v___x_2713_, v_t_2709_);
return v___x_2714_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray(lean_object* v_00_u03b1_2717_, lean_object* v_cmp_2718_, lean_object* v_00_u03b2_2719_, lean_object* v_t_2720_){
_start:
{
lean_object* v___f_2721_; lean_object* v___y_2723_; 
v___f_2721_ = ((lean_object*)(l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2720_) == 0)
{
lean_object* v_size_2726_; 
v_size_2726_ = lean_ctor_get(v_t_2720_, 0);
lean_inc(v_size_2726_);
v___y_2723_ = v_size_2726_;
goto v___jp_2722_;
}
else
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_unsigned_to_nat(0u);
v___y_2723_ = v___x_2727_;
goto v___jp_2722_;
}
v___jp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_mk_empty_array_with_capacity(v___y_2723_);
lean_dec(v___y_2723_);
v___x_2725_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2721_, v___x_2724_, v_t_2720_);
return v___x_2725_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___boxed(lean_object* v_00_u03b1_2728_, lean_object* v_cmp_2729_, lean_object* v_00_u03b2_2730_, lean_object* v_t_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Std_DTreeMap_Raw_valuesArray(v_00_u03b1_2728_, v_cmp_2729_, v_00_u03b2_2730_, v_t_2731_);
lean_dec_ref(v_cmp_2729_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___redArg___lam__0(lean_object* v_x1_2733_, lean_object* v_x2_2734_, lean_object* v_x3_2735_){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2736_, 0, v_x1_2733_);
lean_ctor_set(v___x_2736_, 1, v_x2_2734_);
v___x_2737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
lean_ctor_set(v___x_2737_, 1, v_x3_2735_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___redArg(lean_object* v_t_2739_){
_start:
{
lean_object* v___f_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___f_2740_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_2741_ = lean_box(0);
v___x_2742_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2743_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2742_, v___f_2740_, v___x_2741_, v_t_2739_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList(lean_object* v_00_u03b1_2744_, lean_object* v_00_u03b2_2745_, lean_object* v_cmp_2746_, lean_object* v_t_2747_){
_start:
{
lean_object* v___f_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___f_2748_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_2749_ = lean_box(0);
v___x_2750_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2751_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2750_, v___f_2748_, v___x_2749_, v_t_2747_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___boxed(lean_object* v_00_u03b1_2752_, lean_object* v_00_u03b2_2753_, lean_object* v_cmp_2754_, lean_object* v_t_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Std_DTreeMap_Raw_toList(v_00_u03b1_2752_, v_00_u03b2_2753_, v_cmp_2754_, v_t_2755_);
lean_dec_ref(v_cmp_2754_);
return v_res_2756_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg___lam__0(lean_object* v_cmp_2758_, lean_object* v_a_2759_, lean_object* v_x_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_fst_2762_; lean_object* v_snd_2763_; lean_object* v_r_2764_; lean_object* v___x_2765_; 
v_fst_2762_ = lean_ctor_get(v_a_2759_, 0);
lean_inc(v_fst_2762_);
v_snd_2763_ = lean_ctor_get(v_a_2759_, 1);
lean_inc(v_snd_2763_);
lean_dec_ref(v_a_2759_);
v_r_2764_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2758_, v_fst_2762_, v_snd_2763_, v___y_2761_);
v___x_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2765_, 0, v_r_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg(lean_object* v_l_2766_, lean_object* v_cmp_2767_){
_start:
{
lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v_r_2770_; lean_object* v___x_2771_; 
v___f_2768_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2768_, 0, v_cmp_2767_);
v___x_2769_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2770_ = lean_box(1);
v___x_2771_ = l_List_forIn_x27_loop___redArg(v___x_2769_, v___f_2768_, v_l_2766_, v_r_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList(lean_object* v_00_u03b1_2772_, lean_object* v_00_u03b2_2773_, lean_object* v_l_2774_, lean_object* v_cmp_2775_){
_start:
{
lean_object* v___f_2776_; lean_object* v___x_2777_; lean_object* v_r_2778_; lean_object* v___x_2779_; 
v___f_2776_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2776_, 0, v_cmp_2775_);
v___x_2777_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2778_ = lean_box(1);
v___x_2779_ = l_List_forIn_x27_loop___redArg(v___x_2777_, v___f_2776_, v_l_2774_, v_r_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg___lam__0(lean_object* v_l_2780_, lean_object* v_k_2781_, lean_object* v_v_2782_){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2783_, 0, v_k_2781_);
lean_ctor_set(v___x_2783_, 1, v_v_2782_);
v___x_2784_ = lean_array_push(v_l_2780_, v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg(lean_object* v_t_2786_){
_start:
{
lean_object* v___f_2787_; lean_object* v___y_2789_; 
v___f_2787_ = ((lean_object*)(l_Std_DTreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2786_) == 0)
{
lean_object* v_size_2792_; 
v_size_2792_ = lean_ctor_get(v_t_2786_, 0);
lean_inc(v_size_2792_);
v___y_2789_ = v_size_2792_;
goto v___jp_2788_;
}
else
{
lean_object* v___x_2793_; 
v___x_2793_ = lean_unsigned_to_nat(0u);
v___y_2789_ = v___x_2793_;
goto v___jp_2788_;
}
v___jp_2788_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_mk_empty_array_with_capacity(v___y_2789_);
lean_dec(v___y_2789_);
v___x_2791_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2787_, v___x_2790_, v_t_2786_);
return v___x_2791_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray(lean_object* v_00_u03b1_2794_, lean_object* v_00_u03b2_2795_, lean_object* v_cmp_2796_, lean_object* v_t_2797_){
_start:
{
lean_object* v___f_2798_; lean_object* v___y_2800_; 
v___f_2798_ = ((lean_object*)(l_Std_DTreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2797_) == 0)
{
lean_object* v_size_2803_; 
v_size_2803_ = lean_ctor_get(v_t_2797_, 0);
lean_inc(v_size_2803_);
v___y_2800_ = v_size_2803_;
goto v___jp_2799_;
}
else
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_unsigned_to_nat(0u);
v___y_2800_ = v___x_2804_;
goto v___jp_2799_;
}
v___jp_2799_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_mk_empty_array_with_capacity(v___y_2800_);
lean_dec(v___y_2800_);
v___x_2802_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2798_, v___x_2801_, v_t_2797_);
return v___x_2802_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___boxed(lean_object* v_00_u03b1_2805_, lean_object* v_00_u03b2_2806_, lean_object* v_cmp_2807_, lean_object* v_t_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Std_DTreeMap_Raw_toArray(v_00_u03b1_2805_, v_00_u03b2_2806_, v_cmp_2807_, v_t_2808_);
lean_dec_ref(v_cmp_2807_);
return v_res_2809_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray___redArg(lean_object* v_a_2811_, lean_object* v_cmp_2812_){
_start:
{
lean_object* v___f_2813_; lean_object* v___x_2814_; lean_object* v_r_2815_; size_t v_sz_2816_; size_t v___x_2817_; lean_object* v___x_2818_; 
v___f_2813_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2813_, 0, v_cmp_2812_);
v___x_2814_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2815_ = lean_box(1);
v_sz_2816_ = lean_array_size(v_a_2811_);
v___x_2817_ = ((size_t)0ULL);
v___x_2818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2814_, v_a_2811_, v___f_2813_, v_sz_2816_, v___x_2817_, v_r_2815_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray(lean_object* v_00_u03b1_2819_, lean_object* v_00_u03b2_2820_, lean_object* v_a_2821_, lean_object* v_cmp_2822_){
_start:
{
lean_object* v___f_2823_; lean_object* v___x_2824_; lean_object* v_r_2825_; size_t v_sz_2826_; size_t v___x_2827_; lean_object* v___x_2828_; 
v___f_2823_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2823_, 0, v_cmp_2822_);
v___x_2824_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2825_ = lean_box(1);
v_sz_2826_ = lean_array_size(v_a_2821_);
v___x_2827_ = ((size_t)0ULL);
v___x_2828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2824_, v_a_2821_, v___f_2823_, v_sz_2826_, v___x_2827_, v_r_2825_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify___redArg(lean_object* v_cmp_2829_, lean_object* v_t_2830_, lean_object* v_a_2831_, lean_object* v_f_2832_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2829_, v_a_2831_, v_f_2832_, v_t_2830_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify(lean_object* v_00_u03b1_2834_, lean_object* v_00_u03b2_2835_, lean_object* v_cmp_2836_, lean_object* v_inst_2837_, lean_object* v_t_2838_, lean_object* v_a_2839_, lean_object* v_f_2840_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2836_, v_a_2839_, v_f_2840_, v_t_2838_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter___redArg(lean_object* v_cmp_2842_, lean_object* v_t_2843_, lean_object* v_a_2844_, lean_object* v_f_2845_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2842_, v_a_2844_, v_f_2845_, v_t_2843_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter(lean_object* v_00_u03b1_2847_, lean_object* v_00_u03b2_2848_, lean_object* v_cmp_2849_, lean_object* v_inst_2850_, lean_object* v_t_2851_, lean_object* v_a_2852_, lean_object* v_f_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2849_, v_a_2852_, v_f_2853_, v_t_2851_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2855_, lean_object* v_mergeFn_2856_, lean_object* v_a_2857_, lean_object* v_x_2858_){
_start:
{
if (lean_obj_tag(v_x_2858_) == 0)
{
lean_object* v___x_2859_; 
lean_dec(v_a_2857_);
lean_dec(v_mergeFn_2856_);
v___x_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2859_, 0, v_b_u2082_2855_);
return v___x_2859_;
}
else
{
lean_object* v_val_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2868_; 
v_val_2860_ = lean_ctor_get(v_x_2858_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_x_2858_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2862_ = v_x_2858_;
v_isShared_2863_ = v_isSharedCheck_2868_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_val_2860_);
lean_dec(v_x_2858_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2868_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2864_ = lean_apply_3(v_mergeFn_2856_, v_a_2857_, v_val_2860_, v_b_u2082_2855_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2864_);
v___x_2866_ = v___x_2862_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2869_, lean_object* v_cmp_2870_, lean_object* v_t_2871_, lean_object* v_a_2872_, lean_object* v_b_u2082_2873_){
_start:
{
lean_object* v___f_2874_; lean_object* v___x_2875_; 
lean_inc(v_a_2872_);
v___f_2874_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2874_, 0, v_b_u2082_2873_);
lean_closure_set(v___f_2874_, 1, v_mergeFn_2869_);
lean_closure_set(v___f_2874_, 2, v_a_2872_);
v___x_2875_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2870_, v_a_2872_, v___f_2874_, v_t_2871_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg(lean_object* v_cmp_2876_, lean_object* v_mergeFn_2877_, lean_object* v_t_u2081_2878_, lean_object* v_t_u2082_2879_){
_start:
{
lean_object* v___f_2880_; lean_object* v___x_2881_; 
v___f_2880_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2880_, 0, v_mergeFn_2877_);
lean_closure_set(v___f_2880_, 1, v_cmp_2876_);
v___x_2881_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2880_, v_t_u2081_2878_, v_t_u2082_2879_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith(lean_object* v_00_u03b1_2882_, lean_object* v_00_u03b2_2883_, lean_object* v_cmp_2884_, lean_object* v_inst_2885_, lean_object* v_mergeFn_2886_, lean_object* v_t_u2081_2887_, lean_object* v_t_u2082_2888_){
_start:
{
lean_object* v___f_2889_; lean_object* v___x_2890_; 
v___f_2889_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2889_, 0, v_mergeFn_2886_);
lean_closure_set(v___f_2889_, 1, v_cmp_2884_);
v___x_2890_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2889_, v_t_u2081_2887_, v_t_u2082_2888_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg___lam__0(lean_object* v_x1_2891_, lean_object* v_x2_2892_, lean_object* v_x3_2893_){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v_x1_2891_);
lean_ctor_set(v___x_2894_, 1, v_x2_2892_);
v___x_2895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
lean_ctor_set(v___x_2895_, 1, v_x3_2893_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg(lean_object* v_t_2897_){
_start:
{
lean_object* v___f_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___f_2898_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0));
v___x_2899_ = lean_box(0);
v___x_2900_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2901_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2900_, v___f_2898_, v___x_2899_, v_t_2897_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList(lean_object* v_00_u03b1_2902_, lean_object* v_cmp_2903_, lean_object* v_00_u03b2_2904_, lean_object* v_t_2905_){
_start:
{
lean_object* v___f_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___f_2906_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0));
v___x_2907_ = lean_box(0);
v___x_2908_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2909_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2908_, v___f_2906_, v___x_2907_, v_t_2905_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___boxed(lean_object* v_00_u03b1_2910_, lean_object* v_cmp_2911_, lean_object* v_00_u03b2_2912_, lean_object* v_t_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Std_DTreeMap_Raw_Const_toList(v_00_u03b1_2910_, v_cmp_2911_, v_00_u03b2_2912_, v_t_2913_);
lean_dec_ref(v_cmp_2911_);
return v_res_2914_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0(lean_object* v_cmp_2916_, lean_object* v_a_2917_, lean_object* v_x_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_fst_2920_; lean_object* v_snd_2921_; lean_object* v_r_2922_; lean_object* v___x_2923_; 
v_fst_2920_ = lean_ctor_get(v_a_2917_, 0);
lean_inc(v_fst_2920_);
v_snd_2921_ = lean_ctor_get(v_a_2917_, 1);
lean_inc(v_snd_2921_);
lean_dec_ref(v_a_2917_);
v_r_2922_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2916_, v_fst_2920_, v_snd_2921_, v___y_2919_);
v___x_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_r_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg(lean_object* v_l_2924_, lean_object* v_cmp_2925_){
_start:
{
lean_object* v___f_2926_; lean_object* v___x_2927_; lean_object* v_r_2928_; lean_object* v___x_2929_; 
v___f_2926_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2926_, 0, v_cmp_2925_);
v___x_2927_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2928_ = lean_box(1);
v___x_2929_ = l_List_forIn_x27_loop___redArg(v___x_2927_, v___f_2926_, v_l_2924_, v_r_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList(lean_object* v_00_u03b1_2930_, lean_object* v_00_u03b2_2931_, lean_object* v_l_2932_, lean_object* v_cmp_2933_){
_start:
{
lean_object* v___f_2934_; lean_object* v___x_2935_; lean_object* v_r_2936_; lean_object* v___x_2937_; 
v___f_2934_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2934_, 0, v_cmp_2933_);
v___x_2935_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2936_ = lean_box(1);
v___x_2937_ = l_List_forIn_x27_loop___redArg(v___x_2935_, v___f_2934_, v_l_2932_, v_r_2936_);
return v___x_2937_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_2939_, lean_object* v_a_2940_, lean_object* v_x_2941_, lean_object* v___y_2942_){
_start:
{
uint8_t v___x_2943_; 
lean_inc(v___y_2942_);
lean_inc(v_a_2940_);
lean_inc_ref(v_cmp_2939_);
v___x_2943_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2939_, v_a_2940_, v___y_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = lean_box(0);
v___x_2945_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2939_, v_a_2940_, v___x_2944_, v___y_2942_);
v___x_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
return v___x_2946_;
}
else
{
lean_object* v___x_2947_; 
lean_dec(v_a_2940_);
lean_dec_ref(v_cmp_2939_);
v___x_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2947_, 0, v___y_2942_);
return v___x_2947_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg(lean_object* v_l_2948_, lean_object* v_cmp_2949_){
_start:
{
lean_object* v___f_2950_; lean_object* v___x_2951_; lean_object* v_r_2952_; lean_object* v___x_2953_; 
v___f_2950_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2950_, 0, v_cmp_2949_);
v___x_2951_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2952_ = lean_box(1);
v___x_2953_ = l_List_forIn_x27_loop___redArg(v___x_2951_, v___f_2950_, v_l_2948_, v_r_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList(lean_object* v_00_u03b1_2954_, lean_object* v_l_2955_, lean_object* v_cmp_2956_){
_start:
{
lean_object* v___f_2957_; lean_object* v___x_2958_; lean_object* v_r_2959_; lean_object* v___x_2960_; 
v___f_2957_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2957_, 0, v_cmp_2956_);
v___x_2958_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2959_ = lean_box(1);
v___x_2960_ = l_List_forIn_x27_loop___redArg(v___x_2958_, v___f_2957_, v_l_2955_, v_r_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg___lam__0(lean_object* v_l_2961_, lean_object* v_k_2962_, lean_object* v_v_2963_){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v_k_2962_);
lean_ctor_set(v___x_2964_, 1, v_v_2963_);
v___x_2965_ = lean_array_push(v_l_2961_, v___x_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg(lean_object* v_t_2967_){
_start:
{
lean_object* v___f_2968_; lean_object* v___y_2970_; 
v___f_2968_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0));
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray(lean_object* v_00_u03b1_2975_, lean_object* v_cmp_2976_, lean_object* v_00_u03b2_2977_, lean_object* v_t_2978_){
_start:
{
lean_object* v___f_2979_; lean_object* v___y_2981_; 
v___f_2979_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2978_) == 0)
{
lean_object* v_size_2984_; 
v_size_2984_ = lean_ctor_get(v_t_2978_, 0);
lean_inc(v_size_2984_);
v___y_2981_ = v_size_2984_;
goto v___jp_2980_;
}
else
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_unsigned_to_nat(0u);
v___y_2981_ = v___x_2985_;
goto v___jp_2980_;
}
v___jp_2980_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_mk_empty_array_with_capacity(v___y_2981_);
lean_dec(v___y_2981_);
v___x_2983_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2979_, v___x_2982_, v_t_2978_);
return v___x_2983_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___boxed(lean_object* v_00_u03b1_2986_, lean_object* v_cmp_2987_, lean_object* v_00_u03b2_2988_, lean_object* v_t_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Std_DTreeMap_Raw_Const_toArray(v_00_u03b1_2986_, v_cmp_2987_, v_00_u03b2_2988_, v_t_2989_);
lean_dec_ref(v_cmp_2987_);
return v_res_2990_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray___redArg(lean_object* v_a_2992_, lean_object* v_cmp_2993_){
_start:
{
lean_object* v___f_2994_; lean_object* v___x_2995_; lean_object* v_r_2996_; size_t v_sz_2997_; size_t v___x_2998_; lean_object* v___x_2999_; 
v___f_2994_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2994_, 0, v_cmp_2993_);
v___x_2995_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2996_ = lean_box(1);
v_sz_2997_ = lean_array_size(v_a_2992_);
v___x_2998_ = ((size_t)0ULL);
v___x_2999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2995_, v_a_2992_, v___f_2994_, v_sz_2997_, v___x_2998_, v_r_2996_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray(lean_object* v_00_u03b1_3000_, lean_object* v_00_u03b2_3001_, lean_object* v_a_3002_, lean_object* v_cmp_3003_){
_start:
{
lean_object* v___f_3004_; lean_object* v___x_3005_; lean_object* v_r_3006_; size_t v_sz_3007_; size_t v___x_3008_; lean_object* v___x_3009_; 
v___f_3004_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3004_, 0, v_cmp_3003_);
v___x_3005_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3006_ = lean_box(1);
v_sz_3007_ = lean_array_size(v_a_3002_);
v___x_3008_ = ((size_t)0ULL);
v___x_3009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3005_, v_a_3002_, v___f_3004_, v_sz_3007_, v___x_3008_, v_r_3006_);
return v___x_3009_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray___redArg(lean_object* v_a_3011_, lean_object* v_cmp_3012_){
_start:
{
lean_object* v___f_3013_; lean_object* v___x_3014_; lean_object* v_r_3015_; size_t v_sz_3016_; size_t v___x_3017_; lean_object* v___x_3018_; 
v___f_3013_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3013_, 0, v_cmp_3012_);
v___x_3014_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3015_ = lean_box(1);
v_sz_3016_ = lean_array_size(v_a_3011_);
v___x_3017_ = ((size_t)0ULL);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3014_, v_a_3011_, v___f_3013_, v_sz_3016_, v___x_3017_, v_r_3015_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray(lean_object* v_00_u03b1_3019_, lean_object* v_a_3020_, lean_object* v_cmp_3021_){
_start:
{
lean_object* v___f_3022_; lean_object* v___x_3023_; lean_object* v_r_3024_; size_t v_sz_3025_; size_t v___x_3026_; lean_object* v___x_3027_; 
v___f_3022_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3022_, 0, v_cmp_3021_);
v___x_3023_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3024_ = lean_box(1);
v_sz_3025_ = lean_array_size(v_a_3020_);
v___x_3026_ = ((size_t)0ULL);
v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3023_, v_a_3020_, v___f_3022_, v_sz_3025_, v___x_3026_, v_r_3024_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify___redArg(lean_object* v_cmp_3028_, lean_object* v_t_3029_, lean_object* v_a_3030_, lean_object* v_f_3031_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3028_, v_a_3030_, v_f_3031_, v_t_3029_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify(lean_object* v_00_u03b1_3033_, lean_object* v_cmp_3034_, lean_object* v_00_u03b2_3035_, lean_object* v_t_3036_, lean_object* v_a_3037_, lean_object* v_f_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3034_, v_a_3037_, v_f_3038_, v_t_3036_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter___redArg(lean_object* v_cmp_3040_, lean_object* v_t_3041_, lean_object* v_a_3042_, lean_object* v_f_3043_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3040_, v_a_3042_, v_f_3043_, v_t_3041_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter(lean_object* v_00_u03b1_3045_, lean_object* v_cmp_3046_, lean_object* v_00_u03b2_3047_, lean_object* v_t_3048_, lean_object* v_a_3049_, lean_object* v_f_3050_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3046_, v_a_3049_, v_f_3050_, v_t_3048_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3052_, lean_object* v_cmp_3053_, lean_object* v_t_3054_, lean_object* v_a_3055_, lean_object* v_b_u2082_3056_){
_start:
{
lean_object* v___f_3057_; lean_object* v___x_3058_; 
lean_inc(v_a_3055_);
v___f_3057_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3057_, 0, v_b_u2082_3056_);
lean_closure_set(v___f_3057_, 1, v_mergeFn_3052_);
lean_closure_set(v___f_3057_, 2, v_a_3055_);
v___x_3058_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3053_, v_a_3055_, v___f_3057_, v_t_3054_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg(lean_object* v_cmp_3059_, lean_object* v_mergeFn_3060_, lean_object* v_t_u2081_3061_, lean_object* v_t_u2082_3062_){
_start:
{
lean_object* v___f_3063_; lean_object* v___x_3064_; 
v___f_3063_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3063_, 0, v_mergeFn_3060_);
lean_closure_set(v___f_3063_, 1, v_cmp_3059_);
v___x_3064_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3063_, v_t_u2081_3061_, v_t_u2082_3062_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith(lean_object* v_00_u03b1_3065_, lean_object* v_cmp_3066_, lean_object* v_00_u03b2_3067_, lean_object* v_mergeFn_3068_, lean_object* v_t_u2081_3069_, lean_object* v_t_u2082_3070_){
_start:
{
lean_object* v___f_3071_; lean_object* v___x_3072_; 
v___f_3071_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3071_, 0, v_mergeFn_3068_);
lean_closure_set(v___f_3071_, 1, v_cmp_3066_);
v___x_3072_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3071_, v_t_u2081_3069_, v_t_u2082_3070_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_3073_, lean_object* v_x_3074_, lean_object* v_____s_3075_){
_start:
{
lean_object* v_fst_3076_; lean_object* v_snd_3077_; lean_object* v_r_3078_; lean_object* v___x_3079_; 
v_fst_3076_ = lean_ctor_get(v_x_3074_, 0);
lean_inc(v_fst_3076_);
v_snd_3077_ = lean_ctor_get(v_x_3074_, 1);
lean_inc(v_snd_3077_);
lean_dec_ref(v_x_3074_);
v_r_3078_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_3073_, v_fst_3076_, v_snd_3077_, v_____s_3075_);
v___x_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3079_, 0, v_r_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg(lean_object* v_cmp_3080_, lean_object* v_inst_3081_, lean_object* v_t_3082_, lean_object* v_l_3083_){
_start:
{
lean_object* v___f_3084_; lean_object* v___x_3085_; 
v___f_3084_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3084_, 0, v_cmp_3080_);
v___x_3085_ = lean_apply_4(v_inst_3081_, lean_box(0), v_l_3083_, v_t_3082_, v___f_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany(lean_object* v_00_u03b1_3086_, lean_object* v_00_u03b2_3087_, lean_object* v_cmp_3088_, lean_object* v_00_u03c1_3089_, lean_object* v_inst_3090_, lean_object* v_t_3091_, lean_object* v_l_3092_){
_start:
{
lean_object* v___f_3093_; lean_object* v___x_3094_; 
v___f_3093_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3093_, 0, v_cmp_3088_);
v___x_3094_ = lean_apply_4(v_inst_3090_, lean_box(0), v_l_3092_, v_t_3091_, v___f_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_3095_){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_box(1);
v___x_3097_ = lean_panic_fn_borrowed(v___x_3096_, v_msg_3095_);
return v___x_3097_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3101_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__2));
v___x_3102_ = lean_unsigned_to_nat(35u);
v___x_3103_ = lean_unsigned_to_nat(182u);
v___x_3104_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__1));
v___x_3105_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0));
v___x_3106_ = l_mkPanicMessageWithDecl(v___x_3105_, v___x_3104_, v___x_3103_, v___x_3102_, v___x_3101_);
return v___x_3106_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3107_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__2));
v___x_3108_ = lean_unsigned_to_nat(21u);
v___x_3109_ = lean_unsigned_to_nat(183u);
v___x_3110_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__1));
v___x_3111_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0));
v___x_3112_ = l_mkPanicMessageWithDecl(v___x_3111_, v___x_3110_, v___x_3109_, v___x_3108_, v___x_3107_);
return v___x_3112_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3115_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__6));
v___x_3116_ = lean_unsigned_to_nat(35u);
v___x_3117_ = lean_unsigned_to_nat(276u);
v___x_3118_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__5));
v___x_3119_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0));
v___x_3120_ = l_mkPanicMessageWithDecl(v___x_3119_, v___x_3118_, v___x_3117_, v___x_3116_, v___x_3115_);
return v___x_3120_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3121_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__6));
v___x_3122_ = lean_unsigned_to_nat(21u);
v___x_3123_ = lean_unsigned_to_nat(277u);
v___x_3124_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__5));
v___x_3125_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0));
v___x_3126_ = l_mkPanicMessageWithDecl(v___x_3125_, v___x_3124_, v___x_3123_, v___x_3122_, v___x_3121_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(lean_object* v_cmp_3127_, lean_object* v_k_3128_, lean_object* v_v_3129_, lean_object* v_t_3130_){
_start:
{
if (lean_obj_tag(v_t_3130_) == 0)
{
lean_object* v_size_3131_; lean_object* v_k_3132_; lean_object* v_v_3133_; lean_object* v_l_3134_; lean_object* v_r_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3492_; 
v_size_3131_ = lean_ctor_get(v_t_3130_, 0);
v_k_3132_ = lean_ctor_get(v_t_3130_, 1);
v_v_3133_ = lean_ctor_get(v_t_3130_, 2);
v_l_3134_ = lean_ctor_get(v_t_3130_, 3);
v_r_3135_ = lean_ctor_get(v_t_3130_, 4);
v_isSharedCheck_3492_ = !lean_is_exclusive(v_t_3130_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3137_ = v_t_3130_;
v_isShared_3138_ = v_isSharedCheck_3492_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_r_3135_);
lean_inc(v_l_3134_);
lean_inc(v_v_3133_);
lean_inc(v_k_3132_);
lean_inc(v_size_3131_);
lean_dec(v_t_3130_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3492_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3139_; uint8_t v___x_3140_; 
lean_inc_ref(v_cmp_3127_);
lean_inc(v_k_3132_);
lean_inc(v_k_3128_);
v___x_3139_ = lean_apply_2(v_cmp_3127_, v_k_3128_, v_k_3132_);
v___x_3140_ = lean_unbox(v___x_3139_);
switch(v___x_3140_)
{
case 0:
{
lean_object* v___x_3141_; 
lean_dec(v_size_3131_);
v___x_3141_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3127_, v_k_3128_, v_v_3129_, v_l_3134_);
if (lean_obj_tag(v_r_3135_) == 0)
{
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_size_3142_; lean_object* v_size_3143_; lean_object* v_k_3144_; lean_object* v_v_3145_; lean_object* v_l_3146_; lean_object* v_r_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v_size_3142_ = lean_ctor_get(v_r_3135_, 0);
v_size_3143_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_size_3143_);
v_k_3144_ = lean_ctor_get(v___x_3141_, 1);
lean_inc(v_k_3144_);
v_v_3145_ = lean_ctor_get(v___x_3141_, 2);
lean_inc(v_v_3145_);
v_l_3146_ = lean_ctor_get(v___x_3141_, 3);
lean_inc(v_l_3146_);
v_r_3147_ = lean_ctor_get(v___x_3141_, 4);
lean_inc(v_r_3147_);
v___x_3148_ = lean_unsigned_to_nat(3u);
v___x_3149_ = lean_nat_mul(v___x_3148_, v_size_3142_);
v___x_3150_ = lean_nat_dec_lt(v___x_3149_, v_size_3143_);
lean_dec(v___x_3149_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; 
lean_dec(v_r_3147_);
lean_dec(v_l_3146_);
lean_dec(v_v_3145_);
lean_dec(v_k_3144_);
v___x_3151_ = lean_unsigned_to_nat(1u);
v___x_3152_ = lean_nat_add(v___x_3151_, v_size_3143_);
lean_dec(v_size_3143_);
v___x_3153_ = lean_nat_add(v___x_3152_, v_size_3142_);
lean_dec(v___x_3152_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 3, v___x_3141_);
lean_ctor_set(v___x_3137_, 0, v___x_3153_);
v___x_3155_ = v___x_3137_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3153_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3156_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3156_, 3, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3156_, 4, v_r_3135_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
else
{
lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3228_; 
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; lean_object* v_unused_3230_; lean_object* v_unused_3231_; lean_object* v_unused_3232_; lean_object* v_unused_3233_; 
v_unused_3229_ = lean_ctor_get(v___x_3141_, 4);
lean_dec(v_unused_3229_);
v_unused_3230_ = lean_ctor_get(v___x_3141_, 3);
lean_dec(v_unused_3230_);
v_unused_3231_ = lean_ctor_get(v___x_3141_, 2);
lean_dec(v_unused_3231_);
v_unused_3232_ = lean_ctor_get(v___x_3141_, 1);
lean_dec(v_unused_3232_);
v_unused_3233_ = lean_ctor_get(v___x_3141_, 0);
lean_dec(v_unused_3233_);
v___x_3158_ = v___x_3141_;
v_isShared_3159_ = v_isSharedCheck_3228_;
goto v_resetjp_3157_;
}
else
{
lean_dec(v___x_3141_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3228_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
if (lean_obj_tag(v_l_3146_) == 0)
{
if (lean_obj_tag(v_r_3147_) == 0)
{
lean_object* v_size_3160_; lean_object* v_size_3161_; lean_object* v_k_3162_; lean_object* v_v_3163_; lean_object* v_l_3164_; lean_object* v_r_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; 
v_size_3160_ = lean_ctor_get(v_l_3146_, 0);
v_size_3161_ = lean_ctor_get(v_r_3147_, 0);
v_k_3162_ = lean_ctor_get(v_r_3147_, 1);
v_v_3163_ = lean_ctor_get(v_r_3147_, 2);
v_l_3164_ = lean_ctor_get(v_r_3147_, 3);
v_r_3165_ = lean_ctor_get(v_r_3147_, 4);
v___x_3166_ = lean_unsigned_to_nat(2u);
v___x_3167_ = lean_nat_mul(v___x_3166_, v_size_3160_);
v___x_3168_ = lean_nat_dec_lt(v_size_3161_, v___x_3167_);
lean_dec(v___x_3167_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3198_; 
lean_inc(v_r_3165_);
lean_inc(v_l_3164_);
lean_inc(v_v_3163_);
lean_inc(v_k_3162_);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_r_3147_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; lean_object* v_unused_3200_; lean_object* v_unused_3201_; lean_object* v_unused_3202_; lean_object* v_unused_3203_; 
v_unused_3199_ = lean_ctor_get(v_r_3147_, 4);
lean_dec(v_unused_3199_);
v_unused_3200_ = lean_ctor_get(v_r_3147_, 3);
lean_dec(v_unused_3200_);
v_unused_3201_ = lean_ctor_get(v_r_3147_, 2);
lean_dec(v_unused_3201_);
v_unused_3202_ = lean_ctor_get(v_r_3147_, 1);
lean_dec(v_unused_3202_);
v_unused_3203_ = lean_ctor_get(v_r_3147_, 0);
lean_dec(v_unused_3203_);
v___x_3170_ = v_r_3147_;
v_isShared_3171_ = v_isSharedCheck_3198_;
goto v_resetjp_3169_;
}
else
{
lean_dec(v_r_3147_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3198_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___x_3186_; lean_object* v___y_3188_; 
v___x_3172_ = lean_unsigned_to_nat(1u);
v___x_3173_ = lean_nat_add(v___x_3172_, v_size_3143_);
lean_dec(v_size_3143_);
v___x_3174_ = lean_nat_add(v___x_3173_, v_size_3142_);
lean_dec(v___x_3173_);
v___x_3186_ = lean_nat_add(v___x_3172_, v_size_3160_);
if (lean_obj_tag(v_l_3164_) == 0)
{
lean_object* v_size_3196_; 
v_size_3196_ = lean_ctor_get(v_l_3164_, 0);
lean_inc(v_size_3196_);
v___y_3188_ = v_size_3196_;
goto v___jp_3187_;
}
else
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_unsigned_to_nat(0u);
v___y_3188_ = v___x_3197_;
goto v___jp_3187_;
}
v___jp_3175_:
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3179_ = lean_nat_add(v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec(v___y_3177_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 4, v_r_3135_);
lean_ctor_set(v___x_3170_, 3, v_r_3165_);
lean_ctor_set(v___x_3170_, 2, v_v_3133_);
lean_ctor_set(v___x_3170_, 1, v_k_3132_);
lean_ctor_set(v___x_3170_, 0, v___x_3179_);
v___x_3181_ = v___x_3170_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3185_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3185_, 3, v_r_3165_);
lean_ctor_set(v_reuseFailAlloc_3185_, 4, v_r_3135_);
v___x_3181_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3183_; 
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 4, v___x_3181_);
lean_ctor_set(v___x_3158_, 3, v___y_3176_);
lean_ctor_set(v___x_3158_, 2, v_v_3163_);
lean_ctor_set(v___x_3158_, 1, v_k_3162_);
lean_ctor_set(v___x_3158_, 0, v___x_3174_);
v___x_3183_ = v___x_3158_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_k_3162_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_v_3163_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v___y_3176_);
lean_ctor_set(v_reuseFailAlloc_3184_, 4, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
v___jp_3187_:
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3189_ = lean_nat_add(v___x_3186_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec(v___x_3186_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v_l_3164_);
lean_ctor_set(v___x_3137_, 3, v_l_3146_);
lean_ctor_set(v___x_3137_, 2, v_v_3145_);
lean_ctor_set(v___x_3137_, 1, v_k_3144_);
lean_ctor_set(v___x_3137_, 0, v___x_3189_);
v___x_3191_ = v___x_3137_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_k_3144_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_v_3145_);
lean_ctor_set(v_reuseFailAlloc_3195_, 3, v_l_3146_);
lean_ctor_set(v_reuseFailAlloc_3195_, 4, v_l_3164_);
v___x_3191_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3192_; 
v___x_3192_ = lean_nat_add(v___x_3172_, v_size_3142_);
if (lean_obj_tag(v_r_3165_) == 0)
{
lean_object* v_size_3193_; 
v_size_3193_ = lean_ctor_get(v_r_3165_, 0);
lean_inc(v_size_3193_);
v___y_3176_ = v___x_3191_;
v___y_3177_ = v___x_3192_;
v___y_3178_ = v_size_3193_;
goto v___jp_3175_;
}
else
{
lean_object* v___x_3194_; 
v___x_3194_ = lean_unsigned_to_nat(0u);
v___y_3176_ = v___x_3191_;
v___y_3177_ = v___x_3192_;
v___y_3178_ = v___x_3194_;
goto v___jp_3175_;
}
}
}
}
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3210_; 
lean_del_object(v___x_3137_);
v___x_3204_ = lean_unsigned_to_nat(1u);
v___x_3205_ = lean_nat_add(v___x_3204_, v_size_3143_);
lean_dec(v_size_3143_);
v___x_3206_ = lean_nat_add(v___x_3205_, v_size_3142_);
lean_dec(v___x_3205_);
v___x_3207_ = lean_nat_add(v___x_3204_, v_size_3142_);
v___x_3208_ = lean_nat_add(v___x_3207_, v_size_3161_);
lean_dec(v___x_3207_);
lean_inc_ref(v_r_3135_);
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 4, v_r_3135_);
lean_ctor_set(v___x_3158_, 3, v_r_3147_);
lean_ctor_set(v___x_3158_, 2, v_v_3133_);
lean_ctor_set(v___x_3158_, 1, v_k_3132_);
lean_ctor_set(v___x_3158_, 0, v___x_3208_);
v___x_3210_ = v___x_3158_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3208_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3223_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3223_, 3, v_r_3147_);
lean_ctor_set(v_reuseFailAlloc_3223_, 4, v_r_3135_);
v___x_3210_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
v_isSharedCheck_3217_ = !lean_is_exclusive(v_r_3135_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; lean_object* v_unused_3219_; lean_object* v_unused_3220_; lean_object* v_unused_3221_; lean_object* v_unused_3222_; 
v_unused_3218_ = lean_ctor_get(v_r_3135_, 4);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_r_3135_, 3);
lean_dec(v_unused_3219_);
v_unused_3220_ = lean_ctor_get(v_r_3135_, 2);
lean_dec(v_unused_3220_);
v_unused_3221_ = lean_ctor_get(v_r_3135_, 1);
lean_dec(v_unused_3221_);
v_unused_3222_ = lean_ctor_get(v_r_3135_, 0);
lean_dec(v_unused_3222_);
v___x_3212_ = v_r_3135_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_dec(v_r_3135_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 4, v___x_3210_);
lean_ctor_set(v___x_3212_, 3, v_l_3146_);
lean_ctor_set(v___x_3212_, 2, v_v_3145_);
lean_ctor_set(v___x_3212_, 1, v_k_3144_);
lean_ctor_set(v___x_3212_, 0, v___x_3206_);
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v_k_3144_);
lean_ctor_set(v_reuseFailAlloc_3216_, 2, v_v_3145_);
lean_ctor_set(v_reuseFailAlloc_3216_, 3, v_l_3146_);
lean_ctor_set(v_reuseFailAlloc_3216_, 4, v___x_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
}
else
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_dec_ref(v_l_3146_);
lean_del_object(v___x_3158_);
lean_dec(v_v_3145_);
lean_dec(v_k_3144_);
lean_dec(v_size_3143_);
lean_dec_ref(v_r_3135_);
lean_del_object(v___x_3137_);
lean_dec(v_v_3133_);
lean_dec(v_k_3132_);
v___x_3224_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3);
v___x_3225_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_3224_);
return v___x_3225_;
}
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_del_object(v___x_3158_);
lean_dec(v_r_3147_);
lean_dec(v_v_3145_);
lean_dec(v_k_3144_);
lean_dec(v_size_3143_);
lean_dec_ref(v_r_3135_);
lean_del_object(v___x_3137_);
lean_dec(v_v_3133_);
lean_dec(v_k_3132_);
v___x_3226_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4);
v___x_3227_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_3226_);
return v___x_3227_;
}
}
}
}
else
{
lean_object* v_size_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v_size_3234_ = lean_ctor_get(v_r_3135_, 0);
v___x_3235_ = lean_unsigned_to_nat(1u);
v___x_3236_ = lean_nat_add(v___x_3235_, v_size_3234_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 3, v___x_3141_);
lean_ctor_set(v___x_3137_, 0, v___x_3236_);
v___x_3238_ = v___x_3137_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3239_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3239_, 3, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3239_, 4, v_r_3135_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
else
{
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_l_3240_; 
v_l_3240_ = lean_ctor_get(v___x_3141_, 3);
lean_inc(v_l_3240_);
if (lean_obj_tag(v_l_3240_) == 0)
{
lean_object* v_r_3241_; 
v_r_3241_ = lean_ctor_get(v___x_3141_, 4);
lean_inc(v_r_3241_);
if (lean_obj_tag(v_r_3241_) == 0)
{
lean_object* v_size_3242_; lean_object* v_k_3243_; lean_object* v_v_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3258_; 
v_size_3242_ = lean_ctor_get(v___x_3141_, 0);
v_k_3243_ = lean_ctor_get(v___x_3141_, 1);
v_v_3244_ = lean_ctor_get(v___x_3141_, 2);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; lean_object* v_unused_3260_; 
v_unused_3259_ = lean_ctor_get(v___x_3141_, 4);
lean_dec(v_unused_3259_);
v_unused_3260_ = lean_ctor_get(v___x_3141_, 3);
lean_dec(v_unused_3260_);
v___x_3246_ = v___x_3141_;
v_isShared_3247_ = v_isSharedCheck_3258_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_v_3244_);
lean_inc(v_k_3243_);
lean_inc(v_size_3242_);
lean_dec(v___x_3141_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3258_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v_size_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3253_; 
v_size_3248_ = lean_ctor_get(v_r_3241_, 0);
v___x_3249_ = lean_unsigned_to_nat(1u);
v___x_3250_ = lean_nat_add(v___x_3249_, v_size_3242_);
lean_dec(v_size_3242_);
v___x_3251_ = lean_nat_add(v___x_3249_, v_size_3248_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v_r_3135_);
lean_ctor_set(v___x_3246_, 3, v_r_3241_);
lean_ctor_set(v___x_3246_, 2, v_v_3133_);
lean_ctor_set(v___x_3246_, 1, v_k_3132_);
lean_ctor_set(v___x_3246_, 0, v___x_3251_);
v___x_3253_ = v___x_3246_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3257_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3257_, 3, v_r_3241_);
lean_ctor_set(v_reuseFailAlloc_3257_, 4, v_r_3135_);
v___x_3253_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3255_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v___x_3253_);
lean_ctor_set(v___x_3137_, 3, v_l_3240_);
lean_ctor_set(v___x_3137_, 2, v_v_3244_);
lean_ctor_set(v___x_3137_, 1, v_k_3243_);
lean_ctor_set(v___x_3137_, 0, v___x_3250_);
v___x_3255_ = v___x_3137_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_k_3243_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_v_3244_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_l_3240_);
lean_ctor_set(v_reuseFailAlloc_3256_, 4, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
else
{
lean_object* v_k_3261_; lean_object* v_v_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3274_; 
v_k_3261_ = lean_ctor_get(v___x_3141_, 1);
v_v_3262_ = lean_ctor_get(v___x_3141_, 2);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3274_ == 0)
{
lean_object* v_unused_3275_; lean_object* v_unused_3276_; lean_object* v_unused_3277_; 
v_unused_3275_ = lean_ctor_get(v___x_3141_, 4);
lean_dec(v_unused_3275_);
v_unused_3276_ = lean_ctor_get(v___x_3141_, 3);
lean_dec(v_unused_3276_);
v_unused_3277_ = lean_ctor_get(v___x_3141_, 0);
lean_dec(v_unused_3277_);
v___x_3264_ = v___x_3141_;
v_isShared_3265_ = v_isSharedCheck_3274_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_v_3262_);
lean_inc(v_k_3261_);
lean_dec(v___x_3141_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3274_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3269_; 
v___x_3266_ = lean_unsigned_to_nat(3u);
v___x_3267_ = lean_unsigned_to_nat(1u);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 3, v_r_3241_);
lean_ctor_set(v___x_3264_, 2, v_v_3133_);
lean_ctor_set(v___x_3264_, 1, v_k_3132_);
lean_ctor_set(v___x_3264_, 0, v___x_3267_);
v___x_3269_ = v___x_3264_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3273_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3273_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3273_, 3, v_r_3241_);
lean_ctor_set(v_reuseFailAlloc_3273_, 4, v_r_3241_);
v___x_3269_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
lean_object* v___x_3271_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v___x_3269_);
lean_ctor_set(v___x_3137_, 3, v_l_3240_);
lean_ctor_set(v___x_3137_, 2, v_v_3262_);
lean_ctor_set(v___x_3137_, 1, v_k_3261_);
lean_ctor_set(v___x_3137_, 0, v___x_3266_);
v___x_3271_ = v___x_3137_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_k_3261_);
lean_ctor_set(v_reuseFailAlloc_3272_, 2, v_v_3262_);
lean_ctor_set(v_reuseFailAlloc_3272_, 3, v_l_3240_);
lean_ctor_set(v_reuseFailAlloc_3272_, 4, v___x_3269_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
else
{
lean_object* v_r_3278_; 
v_r_3278_ = lean_ctor_get(v___x_3141_, 4);
lean_inc(v_r_3278_);
if (lean_obj_tag(v_r_3278_) == 0)
{
lean_object* v_k_3279_; lean_object* v_v_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3304_; 
v_k_3279_ = lean_ctor_get(v___x_3141_, 1);
v_v_3280_ = lean_ctor_get(v___x_3141_, 2);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3304_ == 0)
{
lean_object* v_unused_3305_; lean_object* v_unused_3306_; lean_object* v_unused_3307_; 
v_unused_3305_ = lean_ctor_get(v___x_3141_, 4);
lean_dec(v_unused_3305_);
v_unused_3306_ = lean_ctor_get(v___x_3141_, 3);
lean_dec(v_unused_3306_);
v_unused_3307_ = lean_ctor_get(v___x_3141_, 0);
lean_dec(v_unused_3307_);
v___x_3282_ = v___x_3141_;
v_isShared_3283_ = v_isSharedCheck_3304_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_v_3280_);
lean_inc(v_k_3279_);
lean_dec(v___x_3141_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3304_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v_k_3284_; lean_object* v_v_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3300_; 
v_k_3284_ = lean_ctor_get(v_r_3278_, 1);
v_v_3285_ = lean_ctor_get(v_r_3278_, 2);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_r_3278_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; lean_object* v_unused_3302_; lean_object* v_unused_3303_; 
v_unused_3301_ = lean_ctor_get(v_r_3278_, 4);
lean_dec(v_unused_3301_);
v_unused_3302_ = lean_ctor_get(v_r_3278_, 3);
lean_dec(v_unused_3302_);
v_unused_3303_ = lean_ctor_get(v_r_3278_, 0);
lean_dec(v_unused_3303_);
v___x_3287_ = v_r_3278_;
v_isShared_3288_ = v_isSharedCheck_3300_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_v_3285_);
lean_inc(v_k_3284_);
lean_dec(v_r_3278_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3300_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3292_; 
v___x_3289_ = lean_unsigned_to_nat(3u);
v___x_3290_ = lean_unsigned_to_nat(1u);
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 4, v_l_3240_);
lean_ctor_set(v___x_3287_, 3, v_l_3240_);
lean_ctor_set(v___x_3287_, 2, v_v_3280_);
lean_ctor_set(v___x_3287_, 1, v_k_3279_);
lean_ctor_set(v___x_3287_, 0, v___x_3290_);
v___x_3292_ = v___x_3287_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3290_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v_k_3279_);
lean_ctor_set(v_reuseFailAlloc_3299_, 2, v_v_3280_);
lean_ctor_set(v_reuseFailAlloc_3299_, 3, v_l_3240_);
lean_ctor_set(v_reuseFailAlloc_3299_, 4, v_l_3240_);
v___x_3292_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
lean_object* v___x_3294_; 
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 4, v_l_3240_);
lean_ctor_set(v___x_3282_, 2, v_v_3133_);
lean_ctor_set(v___x_3282_, 1, v_k_3132_);
lean_ctor_set(v___x_3282_, 0, v___x_3290_);
v___x_3294_ = v___x_3282_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3290_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3298_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3298_, 3, v_l_3240_);
lean_ctor_set(v_reuseFailAlloc_3298_, 4, v_l_3240_);
v___x_3294_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3296_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v___x_3294_);
lean_ctor_set(v___x_3137_, 3, v___x_3292_);
lean_ctor_set(v___x_3137_, 2, v_v_3285_);
lean_ctor_set(v___x_3137_, 1, v_k_3284_);
lean_ctor_set(v___x_3137_, 0, v___x_3289_);
v___x_3296_ = v___x_3137_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3289_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_k_3284_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v_v_3285_);
lean_ctor_set(v_reuseFailAlloc_3297_, 3, v___x_3292_);
lean_ctor_set(v_reuseFailAlloc_3297_, 4, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
}
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3310_; 
v___x_3308_ = lean_unsigned_to_nat(2u);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v_r_3278_);
lean_ctor_set(v___x_3137_, 3, v___x_3141_);
lean_ctor_set(v___x_3137_, 0, v___x_3308_);
v___x_3310_ = v___x_3137_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3311_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3311_, 3, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3311_, 4, v_r_3278_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
else
{
lean_object* v___x_3312_; lean_object* v___x_3314_; 
v___x_3312_ = lean_unsigned_to_nat(1u);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v___x_3141_);
lean_ctor_set(v___x_3137_, 3, v___x_3141_);
lean_ctor_set(v___x_3137_, 0, v___x_3312_);
v___x_3314_ = v___x_3137_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3312_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3315_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3315_, 3, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3315_, 4, v___x_3141_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
case 1:
{
lean_object* v___x_3317_; 
lean_dec(v_v_3133_);
lean_dec(v_k_3132_);
lean_dec_ref(v_cmp_3127_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 2, v_v_3129_);
lean_ctor_set(v___x_3137_, 1, v_k_3128_);
v___x_3317_ = v___x_3137_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_size_3131_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v_k_3128_);
lean_ctor_set(v_reuseFailAlloc_3318_, 2, v_v_3129_);
lean_ctor_set(v_reuseFailAlloc_3318_, 3, v_l_3134_);
lean_ctor_set(v_reuseFailAlloc_3318_, 4, v_r_3135_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
default: 
{
lean_object* v___x_3319_; 
lean_dec(v_size_3131_);
v___x_3319_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3127_, v_k_3128_, v_v_3129_, v_r_3135_);
if (lean_obj_tag(v_l_3134_) == 0)
{
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_size_3320_; lean_object* v_size_3321_; lean_object* v_k_3322_; lean_object* v_v_3323_; lean_object* v_l_3324_; lean_object* v_r_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v_size_3320_ = lean_ctor_get(v_l_3134_, 0);
v_size_3321_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_size_3321_);
v_k_3322_ = lean_ctor_get(v___x_3319_, 1);
lean_inc(v_k_3322_);
v_v_3323_ = lean_ctor_get(v___x_3319_, 2);
lean_inc(v_v_3323_);
v_l_3324_ = lean_ctor_get(v___x_3319_, 3);
lean_inc(v_l_3324_);
v_r_3325_ = lean_ctor_get(v___x_3319_, 4);
lean_inc(v_r_3325_);
v___x_3326_ = lean_unsigned_to_nat(3u);
v___x_3327_ = lean_nat_mul(v___x_3326_, v_size_3320_);
v___x_3328_ = lean_nat_dec_lt(v___x_3327_, v_size_3321_);
lean_dec(v___x_3327_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3333_; 
lean_dec(v_r_3325_);
lean_dec(v_l_3324_);
lean_dec(v_v_3323_);
lean_dec(v_k_3322_);
v___x_3329_ = lean_unsigned_to_nat(1u);
v___x_3330_ = lean_nat_add(v___x_3329_, v_size_3320_);
v___x_3331_ = lean_nat_add(v___x_3330_, v_size_3321_);
lean_dec(v_size_3321_);
lean_dec(v___x_3330_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v___x_3319_);
lean_ctor_set(v___x_3137_, 0, v___x_3331_);
v___x_3333_ = v___x_3137_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3331_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v_l_3134_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v___x_3319_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
else
{
lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3404_; 
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3404_ == 0)
{
lean_object* v_unused_3405_; lean_object* v_unused_3406_; lean_object* v_unused_3407_; lean_object* v_unused_3408_; lean_object* v_unused_3409_; 
v_unused_3405_ = lean_ctor_get(v___x_3319_, 4);
lean_dec(v_unused_3405_);
v_unused_3406_ = lean_ctor_get(v___x_3319_, 3);
lean_dec(v_unused_3406_);
v_unused_3407_ = lean_ctor_get(v___x_3319_, 2);
lean_dec(v_unused_3407_);
v_unused_3408_ = lean_ctor_get(v___x_3319_, 1);
lean_dec(v_unused_3408_);
v_unused_3409_ = lean_ctor_get(v___x_3319_, 0);
lean_dec(v_unused_3409_);
v___x_3336_ = v___x_3319_;
v_isShared_3337_ = v_isSharedCheck_3404_;
goto v_resetjp_3335_;
}
else
{
lean_dec(v___x_3319_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3404_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
if (lean_obj_tag(v_l_3324_) == 0)
{
if (lean_obj_tag(v_r_3325_) == 0)
{
lean_object* v_size_3338_; lean_object* v_k_3339_; lean_object* v_v_3340_; lean_object* v_l_3341_; lean_object* v_r_3342_; lean_object* v_size_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; 
v_size_3338_ = lean_ctor_get(v_l_3324_, 0);
v_k_3339_ = lean_ctor_get(v_l_3324_, 1);
v_v_3340_ = lean_ctor_get(v_l_3324_, 2);
v_l_3341_ = lean_ctor_get(v_l_3324_, 3);
v_r_3342_ = lean_ctor_get(v_l_3324_, 4);
v_size_3343_ = lean_ctor_get(v_r_3325_, 0);
v___x_3344_ = lean_unsigned_to_nat(2u);
v___x_3345_ = lean_nat_mul(v___x_3344_, v_size_3343_);
v___x_3346_ = lean_nat_dec_lt(v_size_3338_, v___x_3345_);
lean_dec(v___x_3345_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3375_; 
lean_inc(v_r_3342_);
lean_inc(v_l_3341_);
lean_inc(v_v_3340_);
lean_inc(v_k_3339_);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_l_3324_);
if (v_isSharedCheck_3375_ == 0)
{
lean_object* v_unused_3376_; lean_object* v_unused_3377_; lean_object* v_unused_3378_; lean_object* v_unused_3379_; lean_object* v_unused_3380_; 
v_unused_3376_ = lean_ctor_get(v_l_3324_, 4);
lean_dec(v_unused_3376_);
v_unused_3377_ = lean_ctor_get(v_l_3324_, 3);
lean_dec(v_unused_3377_);
v_unused_3378_ = lean_ctor_get(v_l_3324_, 2);
lean_dec(v_unused_3378_);
v_unused_3379_ = lean_ctor_get(v_l_3324_, 1);
lean_dec(v_unused_3379_);
v_unused_3380_ = lean_ctor_get(v_l_3324_, 0);
lean_dec(v_unused_3380_);
v___x_3348_ = v_l_3324_;
v_isShared_3349_ = v_isSharedCheck_3375_;
goto v_resetjp_3347_;
}
else
{
lean_dec(v_l_3324_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3375_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3365_; 
v___x_3350_ = lean_unsigned_to_nat(1u);
v___x_3351_ = lean_nat_add(v___x_3350_, v_size_3320_);
v___x_3352_ = lean_nat_add(v___x_3351_, v_size_3321_);
lean_dec(v_size_3321_);
if (lean_obj_tag(v_l_3341_) == 0)
{
lean_object* v_size_3373_; 
v_size_3373_ = lean_ctor_get(v_l_3341_, 0);
lean_inc(v_size_3373_);
v___y_3365_ = v_size_3373_;
goto v___jp_3364_;
}
else
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_unsigned_to_nat(0u);
v___y_3365_ = v___x_3374_;
goto v___jp_3364_;
}
v___jp_3353_:
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3357_ = lean_nat_add(v___y_3354_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec(v___y_3354_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 4, v_r_3325_);
lean_ctor_set(v___x_3348_, 3, v_r_3342_);
lean_ctor_set(v___x_3348_, 2, v_v_3323_);
lean_ctor_set(v___x_3348_, 1, v_k_3322_);
lean_ctor_set(v___x_3348_, 0, v___x_3357_);
v___x_3359_ = v___x_3348_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_3322_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_3323_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_r_3342_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_r_3325_);
v___x_3359_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3361_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 4, v___x_3359_);
lean_ctor_set(v___x_3336_, 3, v___y_3355_);
lean_ctor_set(v___x_3336_, 2, v_v_3340_);
lean_ctor_set(v___x_3336_, 1, v_k_3339_);
lean_ctor_set(v___x_3336_, 0, v___x_3352_);
v___x_3361_ = v___x_3336_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3352_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_k_3339_);
lean_ctor_set(v_reuseFailAlloc_3362_, 2, v_v_3340_);
lean_ctor_set(v_reuseFailAlloc_3362_, 3, v___y_3355_);
lean_ctor_set(v_reuseFailAlloc_3362_, 4, v___x_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
v___jp_3364_:
{
lean_object* v___x_3366_; lean_object* v___x_3368_; 
v___x_3366_ = lean_nat_add(v___x_3351_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec(v___x_3351_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v_l_3341_);
lean_ctor_set(v___x_3137_, 0, v___x_3366_);
v___x_3368_ = v___x_3137_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3372_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3372_, 3, v_l_3134_);
lean_ctor_set(v_reuseFailAlloc_3372_, 4, v_l_3341_);
v___x_3368_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_nat_add(v___x_3350_, v_size_3343_);
if (lean_obj_tag(v_r_3342_) == 0)
{
lean_object* v_size_3370_; 
v_size_3370_ = lean_ctor_get(v_r_3342_, 0);
lean_inc(v_size_3370_);
v___y_3354_ = v___x_3369_;
v___y_3355_ = v___x_3368_;
v___y_3356_ = v_size_3370_;
goto v___jp_3353_;
}
else
{
lean_object* v___x_3371_; 
v___x_3371_ = lean_unsigned_to_nat(0u);
v___y_3354_ = v___x_3369_;
v___y_3355_ = v___x_3368_;
v___y_3356_ = v___x_3371_;
goto v___jp_3353_;
}
}
}
}
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3386_; 
lean_del_object(v___x_3137_);
v___x_3381_ = lean_unsigned_to_nat(1u);
v___x_3382_ = lean_nat_add(v___x_3381_, v_size_3320_);
v___x_3383_ = lean_nat_add(v___x_3382_, v_size_3321_);
lean_dec(v_size_3321_);
v___x_3384_ = lean_nat_add(v___x_3382_, v_size_3338_);
lean_dec(v___x_3382_);
lean_inc_ref(v_l_3134_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 4, v_l_3324_);
lean_ctor_set(v___x_3336_, 3, v_l_3134_);
lean_ctor_set(v___x_3336_, 2, v_v_3133_);
lean_ctor_set(v___x_3336_, 1, v_k_3132_);
lean_ctor_set(v___x_3336_, 0, v___x_3384_);
v___x_3386_ = v___x_3336_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3399_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3399_, 3, v_l_3134_);
lean_ctor_set(v_reuseFailAlloc_3399_, 4, v_l_3324_);
v___x_3386_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
v_isSharedCheck_3393_ = !lean_is_exclusive(v_l_3134_);
if (v_isSharedCheck_3393_ == 0)
{
lean_object* v_unused_3394_; lean_object* v_unused_3395_; lean_object* v_unused_3396_; lean_object* v_unused_3397_; lean_object* v_unused_3398_; 
v_unused_3394_ = lean_ctor_get(v_l_3134_, 4);
lean_dec(v_unused_3394_);
v_unused_3395_ = lean_ctor_get(v_l_3134_, 3);
lean_dec(v_unused_3395_);
v_unused_3396_ = lean_ctor_get(v_l_3134_, 2);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v_l_3134_, 1);
lean_dec(v_unused_3397_);
v_unused_3398_ = lean_ctor_get(v_l_3134_, 0);
lean_dec(v_unused_3398_);
v___x_3388_ = v_l_3134_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_dec(v_l_3134_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 4, v_r_3325_);
lean_ctor_set(v___x_3388_, 3, v___x_3386_);
lean_ctor_set(v___x_3388_, 2, v_v_3323_);
lean_ctor_set(v___x_3388_, 1, v_k_3322_);
lean_ctor_set(v___x_3388_, 0, v___x_3383_);
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_k_3322_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_v_3323_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_r_3325_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
lean_dec_ref(v_l_3324_);
lean_del_object(v___x_3336_);
lean_dec(v_v_3323_);
lean_dec(v_k_3322_);
lean_dec(v_size_3321_);
lean_dec_ref(v_l_3134_);
lean_del_object(v___x_3137_);
lean_dec(v_v_3133_);
lean_dec(v_k_3132_);
v___x_3400_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7);
v___x_3401_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_3400_);
return v___x_3401_;
}
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_del_object(v___x_3336_);
lean_dec(v_r_3325_);
lean_dec(v_v_3323_);
lean_dec(v_k_3322_);
lean_dec(v_size_3321_);
lean_dec_ref(v_l_3134_);
lean_del_object(v___x_3137_);
lean_dec(v_v_3133_);
lean_dec(v_k_3132_);
v___x_3402_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8);
v___x_3403_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_3402_);
return v___x_3403_;
}
}
}
}
else
{
lean_object* v_size_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
v_size_3410_ = lean_ctor_get(v_l_3134_, 0);
v___x_3411_ = lean_unsigned_to_nat(1u);
v___x_3412_ = lean_nat_add(v___x_3411_, v_size_3410_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v___x_3319_);
lean_ctor_set(v___x_3137_, 0, v___x_3412_);
v___x_3414_ = v___x_3137_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3412_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3415_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3415_, 3, v_l_3134_);
lean_ctor_set(v_reuseFailAlloc_3415_, 4, v___x_3319_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
else
{
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_l_3416_; 
v_l_3416_ = lean_ctor_get(v___x_3319_, 3);
lean_inc(v_l_3416_);
if (lean_obj_tag(v_l_3416_) == 0)
{
lean_object* v_r_3417_; 
v_r_3417_ = lean_ctor_get(v___x_3319_, 4);
lean_inc(v_r_3417_);
if (lean_obj_tag(v_r_3417_) == 0)
{
lean_object* v_size_3418_; lean_object* v_k_3419_; lean_object* v_v_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3434_; 
v_size_3418_ = lean_ctor_get(v___x_3319_, 0);
v_k_3419_ = lean_ctor_get(v___x_3319_, 1);
v_v_3420_ = lean_ctor_get(v___x_3319_, 2);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; lean_object* v_unused_3436_; 
v_unused_3435_ = lean_ctor_get(v___x_3319_, 4);
lean_dec(v_unused_3435_);
v_unused_3436_ = lean_ctor_get(v___x_3319_, 3);
lean_dec(v_unused_3436_);
v___x_3422_ = v___x_3319_;
v_isShared_3423_ = v_isSharedCheck_3434_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_v_3420_);
lean_inc(v_k_3419_);
lean_inc(v_size_3418_);
lean_dec(v___x_3319_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3434_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v_size_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3429_; 
v_size_3424_ = lean_ctor_get(v_l_3416_, 0);
v___x_3425_ = lean_unsigned_to_nat(1u);
v___x_3426_ = lean_nat_add(v___x_3425_, v_size_3418_);
lean_dec(v_size_3418_);
v___x_3427_ = lean_nat_add(v___x_3425_, v_size_3424_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 4, v_l_3416_);
lean_ctor_set(v___x_3422_, 3, v_l_3134_);
lean_ctor_set(v___x_3422_, 2, v_v_3133_);
lean_ctor_set(v___x_3422_, 1, v_k_3132_);
lean_ctor_set(v___x_3422_, 0, v___x_3427_);
v___x_3429_ = v___x_3422_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3427_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3433_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3433_, 3, v_l_3134_);
lean_ctor_set(v_reuseFailAlloc_3433_, 4, v_l_3416_);
v___x_3429_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3431_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v_r_3417_);
lean_ctor_set(v___x_3137_, 3, v___x_3429_);
lean_ctor_set(v___x_3137_, 2, v_v_3420_);
lean_ctor_set(v___x_3137_, 1, v_k_3419_);
lean_ctor_set(v___x_3137_, 0, v___x_3426_);
v___x_3431_ = v___x_3137_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3426_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_k_3419_);
lean_ctor_set(v_reuseFailAlloc_3432_, 2, v_v_3420_);
lean_ctor_set(v_reuseFailAlloc_3432_, 3, v___x_3429_);
lean_ctor_set(v_reuseFailAlloc_3432_, 4, v_r_3417_);
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
else
{
lean_object* v_k_3437_; lean_object* v_v_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3462_; 
v_k_3437_ = lean_ctor_get(v___x_3319_, 1);
v_v_3438_ = lean_ctor_get(v___x_3319_, 2);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3462_ == 0)
{
lean_object* v_unused_3463_; lean_object* v_unused_3464_; lean_object* v_unused_3465_; 
v_unused_3463_ = lean_ctor_get(v___x_3319_, 4);
lean_dec(v_unused_3463_);
v_unused_3464_ = lean_ctor_get(v___x_3319_, 3);
lean_dec(v_unused_3464_);
v_unused_3465_ = lean_ctor_get(v___x_3319_, 0);
lean_dec(v_unused_3465_);
v___x_3440_ = v___x_3319_;
v_isShared_3441_ = v_isSharedCheck_3462_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_v_3438_);
lean_inc(v_k_3437_);
lean_dec(v___x_3319_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3462_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v_k_3442_; lean_object* v_v_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3458_; 
v_k_3442_ = lean_ctor_get(v_l_3416_, 1);
v_v_3443_ = lean_ctor_get(v_l_3416_, 2);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_l_3416_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; lean_object* v_unused_3460_; lean_object* v_unused_3461_; 
v_unused_3459_ = lean_ctor_get(v_l_3416_, 4);
lean_dec(v_unused_3459_);
v_unused_3460_ = lean_ctor_get(v_l_3416_, 3);
lean_dec(v_unused_3460_);
v_unused_3461_ = lean_ctor_get(v_l_3416_, 0);
lean_dec(v_unused_3461_);
v___x_3445_ = v_l_3416_;
v_isShared_3446_ = v_isSharedCheck_3458_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_v_3443_);
lean_inc(v_k_3442_);
lean_dec(v_l_3416_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3458_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
v___x_3447_ = lean_unsigned_to_nat(3u);
v___x_3448_ = lean_unsigned_to_nat(1u);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 4, v_r_3417_);
lean_ctor_set(v___x_3445_, 3, v_r_3417_);
lean_ctor_set(v___x_3445_, 2, v_v_3133_);
lean_ctor_set(v___x_3445_, 1, v_k_3132_);
lean_ctor_set(v___x_3445_, 0, v___x_3448_);
v___x_3450_ = v___x_3445_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3457_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3457_, 3, v_r_3417_);
lean_ctor_set(v_reuseFailAlloc_3457_, 4, v_r_3417_);
v___x_3450_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 3, v_r_3417_);
lean_ctor_set(v___x_3440_, 0, v___x_3448_);
v___x_3452_ = v___x_3440_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_k_3437_);
lean_ctor_set(v_reuseFailAlloc_3456_, 2, v_v_3438_);
lean_ctor_set(v_reuseFailAlloc_3456_, 3, v_r_3417_);
lean_ctor_set(v_reuseFailAlloc_3456_, 4, v_r_3417_);
v___x_3452_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3454_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v___x_3452_);
lean_ctor_set(v___x_3137_, 3, v___x_3450_);
lean_ctor_set(v___x_3137_, 2, v_v_3443_);
lean_ctor_set(v___x_3137_, 1, v_k_3442_);
lean_ctor_set(v___x_3137_, 0, v___x_3447_);
v___x_3454_ = v___x_3137_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3447_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_k_3442_);
lean_ctor_set(v_reuseFailAlloc_3455_, 2, v_v_3443_);
lean_ctor_set(v_reuseFailAlloc_3455_, 3, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3455_, 4, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3466_; 
v_r_3466_ = lean_ctor_get(v___x_3319_, 4);
lean_inc(v_r_3466_);
if (lean_obj_tag(v_r_3466_) == 0)
{
lean_object* v_k_3467_; lean_object* v_v_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3480_; 
v_k_3467_ = lean_ctor_get(v___x_3319_, 1);
v_v_3468_ = lean_ctor_get(v___x_3319_, 2);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3480_ == 0)
{
lean_object* v_unused_3481_; lean_object* v_unused_3482_; lean_object* v_unused_3483_; 
v_unused_3481_ = lean_ctor_get(v___x_3319_, 4);
lean_dec(v_unused_3481_);
v_unused_3482_ = lean_ctor_get(v___x_3319_, 3);
lean_dec(v_unused_3482_);
v_unused_3483_ = lean_ctor_get(v___x_3319_, 0);
lean_dec(v_unused_3483_);
v___x_3470_ = v___x_3319_;
v_isShared_3471_ = v_isSharedCheck_3480_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_v_3468_);
lean_inc(v_k_3467_);
lean_dec(v___x_3319_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3480_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3472_ = lean_unsigned_to_nat(3u);
v___x_3473_ = lean_unsigned_to_nat(1u);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 4, v_l_3416_);
lean_ctor_set(v___x_3470_, 2, v_v_3133_);
lean_ctor_set(v___x_3470_, 1, v_k_3132_);
lean_ctor_set(v___x_3470_, 0, v___x_3473_);
v___x_3475_ = v___x_3470_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3479_, 3, v_l_3416_);
lean_ctor_set(v_reuseFailAlloc_3479_, 4, v_l_3416_);
v___x_3475_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3477_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v_r_3466_);
lean_ctor_set(v___x_3137_, 3, v___x_3475_);
lean_ctor_set(v___x_3137_, 2, v_v_3468_);
lean_ctor_set(v___x_3137_, 1, v_k_3467_);
lean_ctor_set(v___x_3137_, 0, v___x_3472_);
v___x_3477_ = v___x_3137_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3472_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_k_3467_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_v_3468_);
lean_ctor_set(v_reuseFailAlloc_3478_, 3, v___x_3475_);
lean_ctor_set(v_reuseFailAlloc_3478_, 4, v_r_3466_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3484_ = lean_unsigned_to_nat(2u);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v___x_3319_);
lean_ctor_set(v___x_3137_, 3, v_r_3466_);
lean_ctor_set(v___x_3137_, 0, v___x_3484_);
v___x_3486_ = v___x_3137_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3487_, 3, v_r_3466_);
lean_ctor_set(v_reuseFailAlloc_3487_, 4, v___x_3319_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_object* v___x_3488_; lean_object* v___x_3490_; 
v___x_3488_ = lean_unsigned_to_nat(1u);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v___x_3319_);
lean_ctor_set(v___x_3137_, 3, v___x_3319_);
lean_ctor_set(v___x_3137_, 0, v___x_3488_);
v___x_3490_ = v___x_3137_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3491_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3491_, 3, v___x_3319_);
lean_ctor_set(v_reuseFailAlloc_3491_, 4, v___x_3319_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
lean_dec_ref(v_cmp_3127_);
v___x_3493_ = lean_unsigned_to_nat(1u);
v___x_3494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v_k_3128_);
lean_ctor_set(v___x_3494_, 2, v_v_3129_);
lean_ctor_set(v___x_3494_, 3, v_t_3130_);
lean_ctor_set(v___x_3494_, 4, v_t_3130_);
return v___x_3494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(lean_object* v_cmp_3495_, lean_object* v_init_3496_, lean_object* v_x_3497_){
_start:
{
if (lean_obj_tag(v_x_3497_) == 0)
{
lean_object* v_k_3498_; lean_object* v_v_3499_; lean_object* v_l_3500_; lean_object* v_r_3501_; lean_object* v___x_3502_; lean_object* v_a_3503_; lean_object* v_r_3504_; 
v_k_3498_ = lean_ctor_get(v_x_3497_, 1);
lean_inc(v_k_3498_);
v_v_3499_ = lean_ctor_get(v_x_3497_, 2);
lean_inc(v_v_3499_);
v_l_3500_ = lean_ctor_get(v_x_3497_, 3);
lean_inc(v_l_3500_);
v_r_3501_ = lean_ctor_get(v_x_3497_, 4);
lean_inc(v_r_3501_);
lean_dec_ref(v_x_3497_);
lean_inc_ref_n(v_cmp_3495_, 2);
v___x_3502_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3495_, v_init_3496_, v_l_3500_);
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref(v___x_3502_);
v_r_3504_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3495_, v_k_3498_, v_v_3499_, v_a_3503_);
v_init_3496_ = v_r_3504_;
v_x_3497_ = v_r_3501_;
goto _start;
}
else
{
lean_object* v___x_3506_; 
lean_dec_ref(v_cmp_3495_);
v___x_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3506_, 0, v_init_3496_);
return v___x_3506_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(lean_object* v_cmp_3507_, lean_object* v_k_3508_, lean_object* v_t_3509_){
_start:
{
if (lean_obj_tag(v_t_3509_) == 0)
{
lean_object* v_k_3510_; lean_object* v_l_3511_; lean_object* v_r_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
v_k_3510_ = lean_ctor_get(v_t_3509_, 1);
lean_inc(v_k_3510_);
v_l_3511_ = lean_ctor_get(v_t_3509_, 3);
lean_inc(v_l_3511_);
v_r_3512_ = lean_ctor_get(v_t_3509_, 4);
lean_inc(v_r_3512_);
lean_dec_ref(v_t_3509_);
lean_inc_ref(v_cmp_3507_);
lean_inc(v_k_3508_);
v___x_3513_ = lean_apply_2(v_cmp_3507_, v_k_3508_, v_k_3510_);
v___x_3514_ = lean_unbox(v___x_3513_);
switch(v___x_3514_)
{
case 0:
{
lean_dec(v_r_3512_);
v_t_3509_ = v_l_3511_;
goto _start;
}
case 1:
{
uint8_t v___x_3516_; 
lean_dec(v_r_3512_);
lean_dec(v_l_3511_);
lean_dec(v_k_3508_);
lean_dec_ref(v_cmp_3507_);
v___x_3516_ = 1;
return v___x_3516_;
}
default: 
{
lean_dec(v_l_3511_);
v_t_3509_ = v_r_3512_;
goto _start;
}
}
}
else
{
uint8_t v___x_3518_; 
lean_dec(v_k_3508_);
lean_dec_ref(v_cmp_3507_);
v___x_3518_ = 0;
return v___x_3518_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_3519_, lean_object* v_k_3520_, lean_object* v_t_3521_){
_start:
{
uint8_t v_res_3522_; lean_object* v_r_3523_; 
v_res_3522_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3519_, v_k_3520_, v_t_3521_);
v_r_3523_ = lean_box(v_res_3522_);
return v_r_3523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(lean_object* v_cmp_3524_, lean_object* v_init_3525_, lean_object* v_x_3526_){
_start:
{
if (lean_obj_tag(v_x_3526_) == 0)
{
lean_object* v_k_3527_; lean_object* v_v_3528_; lean_object* v_l_3529_; lean_object* v_r_3530_; lean_object* v___x_3531_; lean_object* v_a_3532_; uint8_t v___x_3533_; 
v_k_3527_ = lean_ctor_get(v_x_3526_, 1);
lean_inc_n(v_k_3527_, 2);
v_v_3528_ = lean_ctor_get(v_x_3526_, 2);
lean_inc(v_v_3528_);
v_l_3529_ = lean_ctor_get(v_x_3526_, 3);
lean_inc(v_l_3529_);
v_r_3530_ = lean_ctor_get(v_x_3526_, 4);
lean_inc(v_r_3530_);
lean_dec_ref(v_x_3526_);
lean_inc_ref_n(v_cmp_3524_, 2);
v___x_3531_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3524_, v_init_3525_, v_l_3529_);
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc_n(v_a_3532_, 2);
lean_dec_ref(v___x_3531_);
v___x_3533_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3524_, v_k_3527_, v_a_3532_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; 
lean_inc_ref(v_cmp_3524_);
v___x_3534_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3524_, v_k_3527_, v_v_3528_, v_a_3532_);
v_init_3525_ = v___x_3534_;
v_x_3526_ = v_r_3530_;
goto _start;
}
else
{
lean_dec(v_v_3528_);
lean_dec(v_k_3527_);
v_init_3525_ = v_a_3532_;
v_x_3526_ = v_r_3530_;
goto _start;
}
}
else
{
lean_object* v___x_3537_; 
lean_dec_ref(v_cmp_3524_);
v___x_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3537_, 0, v_init_3525_);
return v___x_3537_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(lean_object* v_cmp_3538_, lean_object* v_t_u2081_3539_, lean_object* v_t_u2082_3540_){
_start:
{
lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3550_; 
if (lean_obj_tag(v_t_u2081_3539_) == 0)
{
lean_object* v_size_3553_; 
v_size_3553_ = lean_ctor_get(v_t_u2081_3539_, 0);
lean_inc(v_size_3553_);
v___y_3550_ = v_size_3553_;
goto v___jp_3549_;
}
else
{
lean_object* v___x_3554_; 
v___x_3554_ = lean_unsigned_to_nat(0u);
v___y_3550_ = v___x_3554_;
goto v___jp_3549_;
}
v___jp_3541_:
{
uint8_t v___x_3544_; 
v___x_3544_ = lean_nat_dec_le(v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec(v___y_3542_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; lean_object* v_a_3546_; 
v___x_3545_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3538_, v_t_u2081_3539_, v_t_u2082_3540_);
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref(v___x_3545_);
return v_a_3546_;
}
else
{
lean_object* v___x_3547_; lean_object* v_a_3548_; 
v___x_3547_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3538_, v_t_u2082_3540_, v_t_u2081_3539_);
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref(v___x_3547_);
return v_a_3548_;
}
}
v___jp_3549_:
{
if (lean_obj_tag(v_t_u2082_3540_) == 0)
{
lean_object* v_size_3551_; 
v_size_3551_ = lean_ctor_get(v_t_u2082_3540_, 0);
lean_inc(v_size_3551_);
v___y_3542_ = v___y_3550_;
v___y_3543_ = v_size_3551_;
goto v___jp_3541_;
}
else
{
lean_object* v___x_3552_; 
v___x_3552_ = lean_unsigned_to_nat(0u);
v___y_3542_ = v___y_3550_;
v___y_3543_ = v___x_3552_;
goto v___jp_3541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union___redArg(lean_object* v_cmp_3555_, lean_object* v_t_u2081_3556_, lean_object* v_t_u2082_3557_){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3555_, v_t_u2081_3556_, v_t_u2082_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union(lean_object* v_00_u03b1_3559_, lean_object* v_00_u03b2_3560_, lean_object* v_cmp_3561_, lean_object* v_t_u2081_3562_, lean_object* v_t_u2082_3563_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3561_, v_t_u2081_3562_, v_t_u2082_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0(lean_object* v_00_u03b1_3565_, lean_object* v_cmp_3566_, lean_object* v_00_u03b2_3567_, lean_object* v_t_u2081_3568_, lean_object* v_t_u2082_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3566_, v_t_u2081_3568_, v_t_u2082_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0(lean_object* v_00_u03b1_3571_, lean_object* v_cmp_3572_, lean_object* v_00_u03b2_3573_, lean_object* v_k_3574_, lean_object* v_t_3575_){
_start:
{
uint8_t v___x_3576_; 
v___x_3576_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3572_, v_k_3574_, v_t_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3577_, lean_object* v_cmp_3578_, lean_object* v_00_u03b2_3579_, lean_object* v_k_3580_, lean_object* v_t_3581_){
_start:
{
uint8_t v_res_3582_; lean_object* v_r_3583_; 
v_res_3582_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0(v_00_u03b1_3577_, v_cmp_3578_, v_00_u03b2_3579_, v_k_3580_, v_t_3581_);
v_r_3583_ = lean_box(v_res_3582_);
return v_r_3583_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3584_, lean_object* v_00_u03b2_3585_, lean_object* v_msg_3586_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v_msg_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1(lean_object* v_00_u03b1_3588_, lean_object* v_cmp_3589_, lean_object* v_00_u03b2_3590_, lean_object* v_k_3591_, lean_object* v_v_3592_, lean_object* v_t_3593_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3589_, v_k_3591_, v_v_3592_, v_t_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2(lean_object* v_00_u03b1_3595_, lean_object* v_00_u03b2_3596_, lean_object* v_cmp_3597_, lean_object* v_init_3598_, lean_object* v_x_3599_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3597_, v_init_3598_, v_x_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3(lean_object* v_00_u03b1_3601_, lean_object* v_00_u03b2_3602_, lean_object* v_cmp_3603_, lean_object* v_init_3604_, lean_object* v_x_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3603_, v_init_3604_, v_x_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion___redArg(lean_object* v_cmp_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_3608_, 0, lean_box(0));
lean_closure_set(v___x_3608_, 1, lean_box(0));
lean_closure_set(v___x_3608_, 2, v_cmp_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion(lean_object* v_00_u03b1_3609_, lean_object* v_00_u03b2_3610_, lean_object* v_cmp_3611_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_3612_, 0, lean_box(0));
lean_closure_set(v___x_3612_, 1, lean_box(0));
lean_closure_set(v___x_3612_, 2, v_cmp_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(lean_object* v_cmp_3613_, lean_object* v_k_3614_, lean_object* v_v_3615_, lean_object* v_t_3616_){
_start:
{
if (lean_obj_tag(v_t_3616_) == 0)
{
lean_object* v_size_3617_; lean_object* v_k_3618_; lean_object* v_v_3619_; lean_object* v_l_3620_; lean_object* v_r_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3902_; 
v_size_3617_ = lean_ctor_get(v_t_3616_, 0);
v_k_3618_ = lean_ctor_get(v_t_3616_, 1);
v_v_3619_ = lean_ctor_get(v_t_3616_, 2);
v_l_3620_ = lean_ctor_get(v_t_3616_, 3);
v_r_3621_ = lean_ctor_get(v_t_3616_, 4);
v_isSharedCheck_3902_ = !lean_is_exclusive(v_t_3616_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3623_ = v_t_3616_;
v_isShared_3624_ = v_isSharedCheck_3902_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_r_3621_);
lean_inc(v_l_3620_);
lean_inc(v_v_3619_);
lean_inc(v_k_3618_);
lean_inc(v_size_3617_);
lean_dec(v_t_3616_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3902_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3625_; uint8_t v___x_3626_; 
lean_inc_ref(v_cmp_3613_);
lean_inc(v_k_3618_);
lean_inc(v_k_3614_);
v___x_3625_ = lean_apply_2(v_cmp_3613_, v_k_3614_, v_k_3618_);
v___x_3626_ = lean_unbox(v___x_3625_);
switch(v___x_3626_)
{
case 0:
{
lean_object* v_impl_3627_; lean_object* v___x_3628_; 
lean_dec(v_size_3617_);
v_impl_3627_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3613_, v_k_3614_, v_v_3615_, v_l_3620_);
v___x_3628_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3621_) == 0)
{
lean_object* v_size_3629_; lean_object* v_size_3630_; lean_object* v_k_3631_; lean_object* v_v_3632_; lean_object* v_l_3633_; lean_object* v_r_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v_size_3629_ = lean_ctor_get(v_r_3621_, 0);
v_size_3630_ = lean_ctor_get(v_impl_3627_, 0);
lean_inc(v_size_3630_);
v_k_3631_ = lean_ctor_get(v_impl_3627_, 1);
lean_inc(v_k_3631_);
v_v_3632_ = lean_ctor_get(v_impl_3627_, 2);
lean_inc(v_v_3632_);
v_l_3633_ = lean_ctor_get(v_impl_3627_, 3);
lean_inc(v_l_3633_);
v_r_3634_ = lean_ctor_get(v_impl_3627_, 4);
lean_inc(v_r_3634_);
v___x_3635_ = lean_unsigned_to_nat(3u);
v___x_3636_ = lean_nat_mul(v___x_3635_, v_size_3629_);
v___x_3637_ = lean_nat_dec_lt(v___x_3636_, v_size_3630_);
lean_dec(v___x_3636_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3641_; 
lean_dec(v_r_3634_);
lean_dec(v_l_3633_);
lean_dec(v_v_3632_);
lean_dec(v_k_3631_);
v___x_3638_ = lean_nat_add(v___x_3628_, v_size_3630_);
lean_dec(v_size_3630_);
v___x_3639_ = lean_nat_add(v___x_3638_, v_size_3629_);
lean_dec(v___x_3638_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 3, v_impl_3627_);
lean_ctor_set(v___x_3623_, 0, v___x_3639_);
v___x_3641_ = v___x_3623_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3639_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3642_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3642_, 3, v_impl_3627_);
lean_ctor_set(v_reuseFailAlloc_3642_, 4, v_r_3621_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
else
{
lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3708_; 
v_isSharedCheck_3708_ = !lean_is_exclusive(v_impl_3627_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; lean_object* v_unused_3710_; lean_object* v_unused_3711_; lean_object* v_unused_3712_; lean_object* v_unused_3713_; 
v_unused_3709_ = lean_ctor_get(v_impl_3627_, 4);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_impl_3627_, 3);
lean_dec(v_unused_3710_);
v_unused_3711_ = lean_ctor_get(v_impl_3627_, 2);
lean_dec(v_unused_3711_);
v_unused_3712_ = lean_ctor_get(v_impl_3627_, 1);
lean_dec(v_unused_3712_);
v_unused_3713_ = lean_ctor_get(v_impl_3627_, 0);
lean_dec(v_unused_3713_);
v___x_3644_ = v_impl_3627_;
v_isShared_3645_ = v_isSharedCheck_3708_;
goto v_resetjp_3643_;
}
else
{
lean_dec(v_impl_3627_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3708_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v_size_3646_; lean_object* v_size_3647_; lean_object* v_k_3648_; lean_object* v_v_3649_; lean_object* v_l_3650_; lean_object* v_r_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
v_size_3646_ = lean_ctor_get(v_l_3633_, 0);
v_size_3647_ = lean_ctor_get(v_r_3634_, 0);
v_k_3648_ = lean_ctor_get(v_r_3634_, 1);
v_v_3649_ = lean_ctor_get(v_r_3634_, 2);
v_l_3650_ = lean_ctor_get(v_r_3634_, 3);
v_r_3651_ = lean_ctor_get(v_r_3634_, 4);
v___x_3652_ = lean_unsigned_to_nat(2u);
v___x_3653_ = lean_nat_mul(v___x_3652_, v_size_3646_);
v___x_3654_ = lean_nat_dec_lt(v_size_3647_, v___x_3653_);
lean_dec(v___x_3653_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3683_; 
lean_inc(v_r_3651_);
lean_inc(v_l_3650_);
lean_inc(v_v_3649_);
lean_inc(v_k_3648_);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_r_3634_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; lean_object* v_unused_3685_; lean_object* v_unused_3686_; lean_object* v_unused_3687_; lean_object* v_unused_3688_; 
v_unused_3684_ = lean_ctor_get(v_r_3634_, 4);
lean_dec(v_unused_3684_);
v_unused_3685_ = lean_ctor_get(v_r_3634_, 3);
lean_dec(v_unused_3685_);
v_unused_3686_ = lean_ctor_get(v_r_3634_, 2);
lean_dec(v_unused_3686_);
v_unused_3687_ = lean_ctor_get(v_r_3634_, 1);
lean_dec(v_unused_3687_);
v_unused_3688_ = lean_ctor_get(v_r_3634_, 0);
lean_dec(v_unused_3688_);
v___x_3656_ = v_r_3634_;
v_isShared_3657_ = v_isSharedCheck_3683_;
goto v_resetjp_3655_;
}
else
{
lean_dec(v_r_3634_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3683_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___x_3671_; lean_object* v___y_3673_; 
v___x_3658_ = lean_nat_add(v___x_3628_, v_size_3630_);
lean_dec(v_size_3630_);
v___x_3659_ = lean_nat_add(v___x_3658_, v_size_3629_);
lean_dec(v___x_3658_);
v___x_3671_ = lean_nat_add(v___x_3628_, v_size_3646_);
if (lean_obj_tag(v_l_3650_) == 0)
{
lean_object* v_size_3681_; 
v_size_3681_ = lean_ctor_get(v_l_3650_, 0);
lean_inc(v_size_3681_);
v___y_3673_ = v_size_3681_;
goto v___jp_3672_;
}
else
{
lean_object* v___x_3682_; 
v___x_3682_ = lean_unsigned_to_nat(0u);
v___y_3673_ = v___x_3682_;
goto v___jp_3672_;
}
v___jp_3660_:
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3664_ = lean_nat_add(v___y_3662_, v___y_3663_);
lean_dec(v___y_3663_);
lean_dec(v___y_3662_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 4, v_r_3621_);
lean_ctor_set(v___x_3656_, 3, v_r_3651_);
lean_ctor_set(v___x_3656_, 2, v_v_3619_);
lean_ctor_set(v___x_3656_, 1, v_k_3618_);
lean_ctor_set(v___x_3656_, 0, v___x_3664_);
v___x_3666_ = v___x_3656_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3670_, 3, v_r_3651_);
lean_ctor_set(v_reuseFailAlloc_3670_, 4, v_r_3621_);
v___x_3666_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3668_; 
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 4, v___x_3666_);
lean_ctor_set(v___x_3644_, 3, v___y_3661_);
lean_ctor_set(v___x_3644_, 2, v_v_3649_);
lean_ctor_set(v___x_3644_, 1, v_k_3648_);
lean_ctor_set(v___x_3644_, 0, v___x_3659_);
v___x_3668_ = v___x_3644_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_k_3648_);
lean_ctor_set(v_reuseFailAlloc_3669_, 2, v_v_3649_);
lean_ctor_set(v_reuseFailAlloc_3669_, 3, v___y_3661_);
lean_ctor_set(v_reuseFailAlloc_3669_, 4, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
v___jp_3672_:
{
lean_object* v___x_3674_; lean_object* v___x_3676_; 
v___x_3674_ = lean_nat_add(v___x_3671_, v___y_3673_);
lean_dec(v___y_3673_);
lean_dec(v___x_3671_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v_l_3650_);
lean_ctor_set(v___x_3623_, 3, v_l_3633_);
lean_ctor_set(v___x_3623_, 2, v_v_3632_);
lean_ctor_set(v___x_3623_, 1, v_k_3631_);
lean_ctor_set(v___x_3623_, 0, v___x_3674_);
v___x_3676_ = v___x_3623_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3674_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_k_3631_);
lean_ctor_set(v_reuseFailAlloc_3680_, 2, v_v_3632_);
lean_ctor_set(v_reuseFailAlloc_3680_, 3, v_l_3633_);
lean_ctor_set(v_reuseFailAlloc_3680_, 4, v_l_3650_);
v___x_3676_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; 
v___x_3677_ = lean_nat_add(v___x_3628_, v_size_3629_);
if (lean_obj_tag(v_r_3651_) == 0)
{
lean_object* v_size_3678_; 
v_size_3678_ = lean_ctor_get(v_r_3651_, 0);
lean_inc(v_size_3678_);
v___y_3661_ = v___x_3676_;
v___y_3662_ = v___x_3677_;
v___y_3663_ = v_size_3678_;
goto v___jp_3660_;
}
else
{
lean_object* v___x_3679_; 
v___x_3679_ = lean_unsigned_to_nat(0u);
v___y_3661_ = v___x_3676_;
v___y_3662_ = v___x_3677_;
v___y_3663_ = v___x_3679_;
goto v___jp_3660_;
}
}
}
}
}
else
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
lean_del_object(v___x_3623_);
v___x_3689_ = lean_nat_add(v___x_3628_, v_size_3630_);
lean_dec(v_size_3630_);
v___x_3690_ = lean_nat_add(v___x_3689_, v_size_3629_);
lean_dec(v___x_3689_);
v___x_3691_ = lean_nat_add(v___x_3628_, v_size_3629_);
v___x_3692_ = lean_nat_add(v___x_3691_, v_size_3647_);
lean_dec(v___x_3691_);
lean_inc_ref(v_r_3621_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 4, v_r_3621_);
lean_ctor_set(v___x_3644_, 3, v_r_3634_);
lean_ctor_set(v___x_3644_, 2, v_v_3619_);
lean_ctor_set(v___x_3644_, 1, v_k_3618_);
lean_ctor_set(v___x_3644_, 0, v___x_3692_);
v___x_3694_ = v___x_3644_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3707_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3707_, 3, v_r_3634_);
lean_ctor_set(v_reuseFailAlloc_3707_, 4, v_r_3621_);
v___x_3694_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
v_isSharedCheck_3701_ = !lean_is_exclusive(v_r_3621_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; lean_object* v_unused_3703_; lean_object* v_unused_3704_; lean_object* v_unused_3705_; lean_object* v_unused_3706_; 
v_unused_3702_ = lean_ctor_get(v_r_3621_, 4);
lean_dec(v_unused_3702_);
v_unused_3703_ = lean_ctor_get(v_r_3621_, 3);
lean_dec(v_unused_3703_);
v_unused_3704_ = lean_ctor_get(v_r_3621_, 2);
lean_dec(v_unused_3704_);
v_unused_3705_ = lean_ctor_get(v_r_3621_, 1);
lean_dec(v_unused_3705_);
v_unused_3706_ = lean_ctor_get(v_r_3621_, 0);
lean_dec(v_unused_3706_);
v___x_3696_ = v_r_3621_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_dec(v_r_3621_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 4, v___x_3694_);
lean_ctor_set(v___x_3696_, 3, v_l_3633_);
lean_ctor_set(v___x_3696_, 2, v_v_3632_);
lean_ctor_set(v___x_3696_, 1, v_k_3631_);
lean_ctor_set(v___x_3696_, 0, v___x_3690_);
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_k_3631_);
lean_ctor_set(v_reuseFailAlloc_3700_, 2, v_v_3632_);
lean_ctor_set(v_reuseFailAlloc_3700_, 3, v_l_3633_);
lean_ctor_set(v_reuseFailAlloc_3700_, 4, v___x_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3714_; 
v_l_3714_ = lean_ctor_get(v_impl_3627_, 3);
lean_inc(v_l_3714_);
if (lean_obj_tag(v_l_3714_) == 0)
{
lean_object* v_r_3715_; lean_object* v_k_3716_; lean_object* v_v_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3728_; 
v_r_3715_ = lean_ctor_get(v_impl_3627_, 4);
v_k_3716_ = lean_ctor_get(v_impl_3627_, 1);
v_v_3717_ = lean_ctor_get(v_impl_3627_, 2);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_impl_3627_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; lean_object* v_unused_3730_; 
v_unused_3729_ = lean_ctor_get(v_impl_3627_, 3);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v_impl_3627_, 0);
lean_dec(v_unused_3730_);
v___x_3719_ = v_impl_3627_;
v_isShared_3720_ = v_isSharedCheck_3728_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_r_3715_);
lean_inc(v_v_3717_);
lean_inc(v_k_3716_);
lean_dec(v_impl_3627_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3728_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3721_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3715_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 3, v_r_3715_);
lean_ctor_set(v___x_3719_, 2, v_v_3619_);
lean_ctor_set(v___x_3719_, 1, v_k_3618_);
lean_ctor_set(v___x_3719_, 0, v___x_3628_);
v___x_3723_ = v___x_3719_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v_r_3715_);
lean_ctor_set(v_reuseFailAlloc_3727_, 4, v_r_3715_);
v___x_3723_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3725_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v___x_3723_);
lean_ctor_set(v___x_3623_, 3, v_l_3714_);
lean_ctor_set(v___x_3623_, 2, v_v_3717_);
lean_ctor_set(v___x_3623_, 1, v_k_3716_);
lean_ctor_set(v___x_3623_, 0, v___x_3721_);
v___x_3725_ = v___x_3623_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_k_3716_);
lean_ctor_set(v_reuseFailAlloc_3726_, 2, v_v_3717_);
lean_ctor_set(v_reuseFailAlloc_3726_, 3, v_l_3714_);
lean_ctor_set(v_reuseFailAlloc_3726_, 4, v___x_3723_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
else
{
lean_object* v_r_3731_; 
v_r_3731_ = lean_ctor_get(v_impl_3627_, 4);
lean_inc(v_r_3731_);
if (lean_obj_tag(v_r_3731_) == 0)
{
lean_object* v_k_3732_; lean_object* v_v_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3756_; 
v_k_3732_ = lean_ctor_get(v_impl_3627_, 1);
v_v_3733_ = lean_ctor_get(v_impl_3627_, 2);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_impl_3627_);
if (v_isSharedCheck_3756_ == 0)
{
lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; 
v_unused_3757_ = lean_ctor_get(v_impl_3627_, 4);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_impl_3627_, 3);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_impl_3627_, 0);
lean_dec(v_unused_3759_);
v___x_3735_ = v_impl_3627_;
v_isShared_3736_ = v_isSharedCheck_3756_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_v_3733_);
lean_inc(v_k_3732_);
lean_dec(v_impl_3627_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3756_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v_k_3737_; lean_object* v_v_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3752_; 
v_k_3737_ = lean_ctor_get(v_r_3731_, 1);
v_v_3738_ = lean_ctor_get(v_r_3731_, 2);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_r_3731_);
if (v_isSharedCheck_3752_ == 0)
{
lean_object* v_unused_3753_; lean_object* v_unused_3754_; lean_object* v_unused_3755_; 
v_unused_3753_ = lean_ctor_get(v_r_3731_, 4);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_r_3731_, 3);
lean_dec(v_unused_3754_);
v_unused_3755_ = lean_ctor_get(v_r_3731_, 0);
lean_dec(v_unused_3755_);
v___x_3740_ = v_r_3731_;
v_isShared_3741_ = v_isSharedCheck_3752_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_v_3738_);
lean_inc(v_k_3737_);
lean_dec(v_r_3731_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3752_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3742_; lean_object* v___x_3744_; 
v___x_3742_ = lean_unsigned_to_nat(3u);
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 4, v_l_3714_);
lean_ctor_set(v___x_3740_, 3, v_l_3714_);
lean_ctor_set(v___x_3740_, 2, v_v_3733_);
lean_ctor_set(v___x_3740_, 1, v_k_3732_);
lean_ctor_set(v___x_3740_, 0, v___x_3628_);
v___x_3744_ = v___x_3740_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v_k_3732_);
lean_ctor_set(v_reuseFailAlloc_3751_, 2, v_v_3733_);
lean_ctor_set(v_reuseFailAlloc_3751_, 3, v_l_3714_);
lean_ctor_set(v_reuseFailAlloc_3751_, 4, v_l_3714_);
v___x_3744_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
lean_object* v___x_3746_; 
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 4, v_l_3714_);
lean_ctor_set(v___x_3735_, 2, v_v_3619_);
lean_ctor_set(v___x_3735_, 1, v_k_3618_);
lean_ctor_set(v___x_3735_, 0, v___x_3628_);
v___x_3746_ = v___x_3735_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3750_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3750_, 3, v_l_3714_);
lean_ctor_set(v_reuseFailAlloc_3750_, 4, v_l_3714_);
v___x_3746_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3748_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v___x_3746_);
lean_ctor_set(v___x_3623_, 3, v___x_3744_);
lean_ctor_set(v___x_3623_, 2, v_v_3738_);
lean_ctor_set(v___x_3623_, 1, v_k_3737_);
lean_ctor_set(v___x_3623_, 0, v___x_3742_);
v___x_3748_ = v___x_3623_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3742_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_k_3737_);
lean_ctor_set(v_reuseFailAlloc_3749_, 2, v_v_3738_);
lean_ctor_set(v_reuseFailAlloc_3749_, 3, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3749_, 4, v___x_3746_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
}
}
else
{
lean_object* v___x_3760_; lean_object* v___x_3762_; 
v___x_3760_ = lean_unsigned_to_nat(2u);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v_r_3731_);
lean_ctor_set(v___x_3623_, 3, v_impl_3627_);
lean_ctor_set(v___x_3623_, 0, v___x_3760_);
v___x_3762_ = v___x_3623_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3760_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3763_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3763_, 3, v_impl_3627_);
lean_ctor_set(v_reuseFailAlloc_3763_, 4, v_r_3731_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3765_; 
lean_dec(v_v_3619_);
lean_dec(v_k_3618_);
lean_dec_ref(v_cmp_3613_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 2, v_v_3615_);
lean_ctor_set(v___x_3623_, 1, v_k_3614_);
v___x_3765_ = v___x_3623_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_size_3617_);
lean_ctor_set(v_reuseFailAlloc_3766_, 1, v_k_3614_);
lean_ctor_set(v_reuseFailAlloc_3766_, 2, v_v_3615_);
lean_ctor_set(v_reuseFailAlloc_3766_, 3, v_l_3620_);
lean_ctor_set(v_reuseFailAlloc_3766_, 4, v_r_3621_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
default: 
{
lean_object* v_impl_3767_; lean_object* v___x_3768_; 
lean_dec(v_size_3617_);
v_impl_3767_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3613_, v_k_3614_, v_v_3615_, v_r_3621_);
v___x_3768_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3620_) == 0)
{
lean_object* v_size_3769_; lean_object* v_size_3770_; lean_object* v_k_3771_; lean_object* v_v_3772_; lean_object* v_l_3773_; lean_object* v_r_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v_size_3769_ = lean_ctor_get(v_l_3620_, 0);
v_size_3770_ = lean_ctor_get(v_impl_3767_, 0);
lean_inc(v_size_3770_);
v_k_3771_ = lean_ctor_get(v_impl_3767_, 1);
lean_inc(v_k_3771_);
v_v_3772_ = lean_ctor_get(v_impl_3767_, 2);
lean_inc(v_v_3772_);
v_l_3773_ = lean_ctor_get(v_impl_3767_, 3);
lean_inc(v_l_3773_);
v_r_3774_ = lean_ctor_get(v_impl_3767_, 4);
lean_inc(v_r_3774_);
v___x_3775_ = lean_unsigned_to_nat(3u);
v___x_3776_ = lean_nat_mul(v___x_3775_, v_size_3769_);
v___x_3777_ = lean_nat_dec_lt(v___x_3776_, v_size_3770_);
lean_dec(v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3781_; 
lean_dec(v_r_3774_);
lean_dec(v_l_3773_);
lean_dec(v_v_3772_);
lean_dec(v_k_3771_);
v___x_3778_ = lean_nat_add(v___x_3768_, v_size_3769_);
v___x_3779_ = lean_nat_add(v___x_3778_, v_size_3770_);
lean_dec(v_size_3770_);
lean_dec(v___x_3778_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v_impl_3767_);
lean_ctor_set(v___x_3623_, 0, v___x_3779_);
v___x_3781_ = v___x_3623_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3779_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3782_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3782_, 3, v_l_3620_);
lean_ctor_set(v_reuseFailAlloc_3782_, 4, v_impl_3767_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
else
{
lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3846_; 
v_isSharedCheck_3846_ = !lean_is_exclusive(v_impl_3767_);
if (v_isSharedCheck_3846_ == 0)
{
lean_object* v_unused_3847_; lean_object* v_unused_3848_; lean_object* v_unused_3849_; lean_object* v_unused_3850_; lean_object* v_unused_3851_; 
v_unused_3847_ = lean_ctor_get(v_impl_3767_, 4);
lean_dec(v_unused_3847_);
v_unused_3848_ = lean_ctor_get(v_impl_3767_, 3);
lean_dec(v_unused_3848_);
v_unused_3849_ = lean_ctor_get(v_impl_3767_, 2);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_impl_3767_, 1);
lean_dec(v_unused_3850_);
v_unused_3851_ = lean_ctor_get(v_impl_3767_, 0);
lean_dec(v_unused_3851_);
v___x_3784_ = v_impl_3767_;
v_isShared_3785_ = v_isSharedCheck_3846_;
goto v_resetjp_3783_;
}
else
{
lean_dec(v_impl_3767_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3846_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v_size_3786_; lean_object* v_k_3787_; lean_object* v_v_3788_; lean_object* v_l_3789_; lean_object* v_r_3790_; lean_object* v_size_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; uint8_t v___x_3794_; 
v_size_3786_ = lean_ctor_get(v_l_3773_, 0);
v_k_3787_ = lean_ctor_get(v_l_3773_, 1);
v_v_3788_ = lean_ctor_get(v_l_3773_, 2);
v_l_3789_ = lean_ctor_get(v_l_3773_, 3);
v_r_3790_ = lean_ctor_get(v_l_3773_, 4);
v_size_3791_ = lean_ctor_get(v_r_3774_, 0);
v___x_3792_ = lean_unsigned_to_nat(2u);
v___x_3793_ = lean_nat_mul(v___x_3792_, v_size_3791_);
v___x_3794_ = lean_nat_dec_lt(v_size_3786_, v___x_3793_);
lean_dec(v___x_3793_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3822_; 
lean_inc(v_r_3790_);
lean_inc(v_l_3789_);
lean_inc(v_v_3788_);
lean_inc(v_k_3787_);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_l_3773_);
if (v_isSharedCheck_3822_ == 0)
{
lean_object* v_unused_3823_; lean_object* v_unused_3824_; lean_object* v_unused_3825_; lean_object* v_unused_3826_; lean_object* v_unused_3827_; 
v_unused_3823_ = lean_ctor_get(v_l_3773_, 4);
lean_dec(v_unused_3823_);
v_unused_3824_ = lean_ctor_get(v_l_3773_, 3);
lean_dec(v_unused_3824_);
v_unused_3825_ = lean_ctor_get(v_l_3773_, 2);
lean_dec(v_unused_3825_);
v_unused_3826_ = lean_ctor_get(v_l_3773_, 1);
lean_dec(v_unused_3826_);
v_unused_3827_ = lean_ctor_get(v_l_3773_, 0);
lean_dec(v_unused_3827_);
v___x_3796_ = v_l_3773_;
v_isShared_3797_ = v_isSharedCheck_3822_;
goto v_resetjp_3795_;
}
else
{
lean_dec(v_l_3773_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3822_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3812_; 
v___x_3798_ = lean_nat_add(v___x_3768_, v_size_3769_);
v___x_3799_ = lean_nat_add(v___x_3798_, v_size_3770_);
lean_dec(v_size_3770_);
if (lean_obj_tag(v_l_3789_) == 0)
{
lean_object* v_size_3820_; 
v_size_3820_ = lean_ctor_get(v_l_3789_, 0);
lean_inc(v_size_3820_);
v___y_3812_ = v_size_3820_;
goto v___jp_3811_;
}
else
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_unsigned_to_nat(0u);
v___y_3812_ = v___x_3821_;
goto v___jp_3811_;
}
v___jp_3800_:
{
lean_object* v___x_3804_; lean_object* v___x_3806_; 
v___x_3804_ = lean_nat_add(v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec(v___y_3802_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 4, v_r_3774_);
lean_ctor_set(v___x_3796_, 3, v_r_3790_);
lean_ctor_set(v___x_3796_, 2, v_v_3772_);
lean_ctor_set(v___x_3796_, 1, v_k_3771_);
lean_ctor_set(v___x_3796_, 0, v___x_3804_);
v___x_3806_ = v___x_3796_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3804_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v_k_3771_);
lean_ctor_set(v_reuseFailAlloc_3810_, 2, v_v_3772_);
lean_ctor_set(v_reuseFailAlloc_3810_, 3, v_r_3790_);
lean_ctor_set(v_reuseFailAlloc_3810_, 4, v_r_3774_);
v___x_3806_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
lean_object* v___x_3808_; 
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 4, v___x_3806_);
lean_ctor_set(v___x_3784_, 3, v___y_3801_);
lean_ctor_set(v___x_3784_, 2, v_v_3788_);
lean_ctor_set(v___x_3784_, 1, v_k_3787_);
lean_ctor_set(v___x_3784_, 0, v___x_3799_);
v___x_3808_ = v___x_3784_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_k_3787_);
lean_ctor_set(v_reuseFailAlloc_3809_, 2, v_v_3788_);
lean_ctor_set(v_reuseFailAlloc_3809_, 3, v___y_3801_);
lean_ctor_set(v_reuseFailAlloc_3809_, 4, v___x_3806_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
v___jp_3811_:
{
lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3813_ = lean_nat_add(v___x_3798_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec(v___x_3798_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v_l_3789_);
lean_ctor_set(v___x_3623_, 0, v___x_3813_);
v___x_3815_ = v___x_3623_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3819_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3819_, 3, v_l_3620_);
lean_ctor_set(v_reuseFailAlloc_3819_, 4, v_l_3789_);
v___x_3815_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
lean_object* v___x_3816_; 
v___x_3816_ = lean_nat_add(v___x_3768_, v_size_3791_);
if (lean_obj_tag(v_r_3790_) == 0)
{
lean_object* v_size_3817_; 
v_size_3817_ = lean_ctor_get(v_r_3790_, 0);
lean_inc(v_size_3817_);
v___y_3801_ = v___x_3815_;
v___y_3802_ = v___x_3816_;
v___y_3803_ = v_size_3817_;
goto v___jp_3800_;
}
else
{
lean_object* v___x_3818_; 
v___x_3818_ = lean_unsigned_to_nat(0u);
v___y_3801_ = v___x_3815_;
v___y_3802_ = v___x_3816_;
v___y_3803_ = v___x_3818_;
goto v___jp_3800_;
}
}
}
}
}
else
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3832_; 
lean_del_object(v___x_3623_);
v___x_3828_ = lean_nat_add(v___x_3768_, v_size_3769_);
v___x_3829_ = lean_nat_add(v___x_3828_, v_size_3770_);
lean_dec(v_size_3770_);
v___x_3830_ = lean_nat_add(v___x_3828_, v_size_3786_);
lean_dec(v___x_3828_);
lean_inc_ref(v_l_3620_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 4, v_l_3773_);
lean_ctor_set(v___x_3784_, 3, v_l_3620_);
lean_ctor_set(v___x_3784_, 2, v_v_3619_);
lean_ctor_set(v___x_3784_, 1, v_k_3618_);
lean_ctor_set(v___x_3784_, 0, v___x_3830_);
v___x_3832_ = v___x_3784_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3830_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3845_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3845_, 3, v_l_3620_);
lean_ctor_set(v_reuseFailAlloc_3845_, 4, v_l_3773_);
v___x_3832_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
v_isSharedCheck_3839_ = !lean_is_exclusive(v_l_3620_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; lean_object* v_unused_3841_; lean_object* v_unused_3842_; lean_object* v_unused_3843_; lean_object* v_unused_3844_; 
v_unused_3840_ = lean_ctor_get(v_l_3620_, 4);
lean_dec(v_unused_3840_);
v_unused_3841_ = lean_ctor_get(v_l_3620_, 3);
lean_dec(v_unused_3841_);
v_unused_3842_ = lean_ctor_get(v_l_3620_, 2);
lean_dec(v_unused_3842_);
v_unused_3843_ = lean_ctor_get(v_l_3620_, 1);
lean_dec(v_unused_3843_);
v_unused_3844_ = lean_ctor_get(v_l_3620_, 0);
lean_dec(v_unused_3844_);
v___x_3834_ = v_l_3620_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_dec(v_l_3620_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 4, v_r_3774_);
lean_ctor_set(v___x_3834_, 3, v___x_3832_);
lean_ctor_set(v___x_3834_, 2, v_v_3772_);
lean_ctor_set(v___x_3834_, 1, v_k_3771_);
lean_ctor_set(v___x_3834_, 0, v___x_3829_);
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3829_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_k_3771_);
lean_ctor_set(v_reuseFailAlloc_3838_, 2, v_v_3772_);
lean_ctor_set(v_reuseFailAlloc_3838_, 3, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3838_, 4, v_r_3774_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3852_; 
v_l_3852_ = lean_ctor_get(v_impl_3767_, 3);
lean_inc(v_l_3852_);
if (lean_obj_tag(v_l_3852_) == 0)
{
lean_object* v_r_3853_; lean_object* v_k_3854_; lean_object* v_v_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3878_; 
v_r_3853_ = lean_ctor_get(v_impl_3767_, 4);
v_k_3854_ = lean_ctor_get(v_impl_3767_, 1);
v_v_3855_ = lean_ctor_get(v_impl_3767_, 2);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_impl_3767_);
if (v_isSharedCheck_3878_ == 0)
{
lean_object* v_unused_3879_; lean_object* v_unused_3880_; 
v_unused_3879_ = lean_ctor_get(v_impl_3767_, 3);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_impl_3767_, 0);
lean_dec(v_unused_3880_);
v___x_3857_ = v_impl_3767_;
v_isShared_3858_ = v_isSharedCheck_3878_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_r_3853_);
lean_inc(v_v_3855_);
lean_inc(v_k_3854_);
lean_dec(v_impl_3767_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3878_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v_k_3859_; lean_object* v_v_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3874_; 
v_k_3859_ = lean_ctor_get(v_l_3852_, 1);
v_v_3860_ = lean_ctor_get(v_l_3852_, 2);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_l_3852_);
if (v_isSharedCheck_3874_ == 0)
{
lean_object* v_unused_3875_; lean_object* v_unused_3876_; lean_object* v_unused_3877_; 
v_unused_3875_ = lean_ctor_get(v_l_3852_, 4);
lean_dec(v_unused_3875_);
v_unused_3876_ = lean_ctor_get(v_l_3852_, 3);
lean_dec(v_unused_3876_);
v_unused_3877_ = lean_ctor_get(v_l_3852_, 0);
lean_dec(v_unused_3877_);
v___x_3862_ = v_l_3852_;
v_isShared_3863_ = v_isSharedCheck_3874_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_v_3860_);
lean_inc(v_k_3859_);
lean_dec(v_l_3852_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3874_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3864_; lean_object* v___x_3866_; 
v___x_3864_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3853_, 2);
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 4, v_r_3853_);
lean_ctor_set(v___x_3862_, 3, v_r_3853_);
lean_ctor_set(v___x_3862_, 2, v_v_3619_);
lean_ctor_set(v___x_3862_, 1, v_k_3618_);
lean_ctor_set(v___x_3862_, 0, v___x_3768_);
v___x_3866_ = v___x_3862_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3873_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3873_, 3, v_r_3853_);
lean_ctor_set(v_reuseFailAlloc_3873_, 4, v_r_3853_);
v___x_3866_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3868_; 
lean_inc(v_r_3853_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 3, v_r_3853_);
lean_ctor_set(v___x_3857_, 0, v___x_3768_);
v___x_3868_ = v___x_3857_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_r_3853_);
lean_ctor_set(v_reuseFailAlloc_3872_, 4, v_r_3853_);
v___x_3868_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3870_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v___x_3868_);
lean_ctor_set(v___x_3623_, 3, v___x_3866_);
lean_ctor_set(v___x_3623_, 2, v_v_3860_);
lean_ctor_set(v___x_3623_, 1, v_k_3859_);
lean_ctor_set(v___x_3623_, 0, v___x_3864_);
v___x_3870_ = v___x_3623_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_k_3859_);
lean_ctor_set(v_reuseFailAlloc_3871_, 2, v_v_3860_);
lean_ctor_set(v_reuseFailAlloc_3871_, 3, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3871_, 4, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
}
}
else
{
lean_object* v_r_3881_; 
v_r_3881_ = lean_ctor_get(v_impl_3767_, 4);
lean_inc(v_r_3881_);
if (lean_obj_tag(v_r_3881_) == 0)
{
lean_object* v_k_3882_; lean_object* v_v_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3894_; 
v_k_3882_ = lean_ctor_get(v_impl_3767_, 1);
v_v_3883_ = lean_ctor_get(v_impl_3767_, 2);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_impl_3767_);
if (v_isSharedCheck_3894_ == 0)
{
lean_object* v_unused_3895_; lean_object* v_unused_3896_; lean_object* v_unused_3897_; 
v_unused_3895_ = lean_ctor_get(v_impl_3767_, 4);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_impl_3767_, 3);
lean_dec(v_unused_3896_);
v_unused_3897_ = lean_ctor_get(v_impl_3767_, 0);
lean_dec(v_unused_3897_);
v___x_3885_ = v_impl_3767_;
v_isShared_3886_ = v_isSharedCheck_3894_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_v_3883_);
lean_inc(v_k_3882_);
lean_dec(v_impl_3767_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3894_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3887_ = lean_unsigned_to_nat(3u);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 4, v_l_3852_);
lean_ctor_set(v___x_3885_, 2, v_v_3619_);
lean_ctor_set(v___x_3885_, 1, v_k_3618_);
lean_ctor_set(v___x_3885_, 0, v___x_3768_);
v___x_3889_ = v___x_3885_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3893_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3893_, 3, v_l_3852_);
lean_ctor_set(v_reuseFailAlloc_3893_, 4, v_l_3852_);
v___x_3889_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3891_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v_r_3881_);
lean_ctor_set(v___x_3623_, 3, v___x_3889_);
lean_ctor_set(v___x_3623_, 2, v_v_3883_);
lean_ctor_set(v___x_3623_, 1, v_k_3882_);
lean_ctor_set(v___x_3623_, 0, v___x_3887_);
v___x_3891_ = v___x_3623_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3887_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_k_3882_);
lean_ctor_set(v_reuseFailAlloc_3892_, 2, v_v_3883_);
lean_ctor_set(v_reuseFailAlloc_3892_, 3, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3892_, 4, v_r_3881_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
else
{
lean_object* v___x_3898_; lean_object* v___x_3900_; 
v___x_3898_ = lean_unsigned_to_nat(2u);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v_impl_3767_);
lean_ctor_set(v___x_3623_, 3, v_r_3881_);
lean_ctor_set(v___x_3623_, 0, v___x_3898_);
v___x_3900_ = v___x_3623_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3898_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3901_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3901_, 3, v_r_3881_);
lean_ctor_set(v_reuseFailAlloc_3901_, 4, v_impl_3767_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
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
lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_dec_ref(v_cmp_3613_);
v___x_3903_ = lean_unsigned_to_nat(1u);
v___x_3904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
lean_ctor_set(v___x_3904_, 1, v_k_3614_);
lean_ctor_set(v___x_3904_, 2, v_v_3615_);
lean_ctor_set(v___x_3904_, 3, v_t_3616_);
lean_ctor_set(v___x_3904_, 4, v_t_3616_);
return v___x_3904_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_3905_, lean_object* v_t_3906_, lean_object* v_k_3907_){
_start:
{
if (lean_obj_tag(v_t_3906_) == 0)
{
lean_object* v_k_3908_; lean_object* v_v_3909_; lean_object* v_l_3910_; lean_object* v_r_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; 
v_k_3908_ = lean_ctor_get(v_t_3906_, 1);
lean_inc_n(v_k_3908_, 2);
v_v_3909_ = lean_ctor_get(v_t_3906_, 2);
lean_inc(v_v_3909_);
v_l_3910_ = lean_ctor_get(v_t_3906_, 3);
lean_inc(v_l_3910_);
v_r_3911_ = lean_ctor_get(v_t_3906_, 4);
lean_inc(v_r_3911_);
lean_dec_ref(v_t_3906_);
lean_inc_ref(v_cmp_3905_);
lean_inc(v_k_3907_);
v___x_3912_ = lean_apply_2(v_cmp_3905_, v_k_3907_, v_k_3908_);
v___x_3913_ = lean_unbox(v___x_3912_);
switch(v___x_3913_)
{
case 0:
{
lean_dec(v_r_3911_);
lean_dec(v_v_3909_);
lean_dec(v_k_3908_);
v_t_3906_ = v_l_3910_;
goto _start;
}
case 1:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
lean_dec(v_r_3911_);
lean_dec(v_l_3910_);
lean_dec(v_k_3907_);
lean_dec_ref(v_cmp_3905_);
v___x_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3915_, 0, v_k_3908_);
lean_ctor_set(v___x_3915_, 1, v_v_3909_);
v___x_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
return v___x_3916_;
}
default: 
{
lean_dec(v_l_3910_);
lean_dec(v_v_3909_);
lean_dec(v_k_3908_);
v_t_3906_ = v_r_3911_;
goto _start;
}
}
}
else
{
lean_object* v___x_3918_; 
lean_dec(v_k_3907_);
lean_dec_ref(v_cmp_3905_);
v___x_3918_ = lean_box(0);
return v___x_3918_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_cmp_3919_, lean_object* v_m_u2081_3920_, lean_object* v_init_3921_, lean_object* v_x_3922_){
_start:
{
if (lean_obj_tag(v_x_3922_) == 0)
{
lean_object* v_k_3923_; lean_object* v_l_3924_; lean_object* v_r_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_k_3923_ = lean_ctor_get(v_x_3922_, 1);
lean_inc(v_k_3923_);
v_l_3924_ = lean_ctor_get(v_x_3922_, 3);
lean_inc(v_l_3924_);
v_r_3925_ = lean_ctor_get(v_x_3922_, 4);
lean_inc(v_r_3925_);
lean_dec_ref(v_x_3922_);
lean_inc_n(v_m_u2081_3920_, 2);
lean_inc_ref_n(v_cmp_3919_, 2);
v___x_3926_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3919_, v_m_u2081_3920_, v_init_3921_, v_l_3924_);
v___x_3927_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3919_, v_m_u2081_3920_, v_k_3923_);
if (lean_obj_tag(v___x_3927_) == 0)
{
v_init_3921_ = v___x_3926_;
v_x_3922_ = v_r_3925_;
goto _start;
}
else
{
lean_object* v_val_3929_; lean_object* v_fst_3930_; lean_object* v_snd_3931_; lean_object* v_impl_3932_; 
v_val_3929_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_val_3929_);
lean_dec_ref(v___x_3927_);
v_fst_3930_ = lean_ctor_get(v_val_3929_, 0);
lean_inc(v_fst_3930_);
v_snd_3931_ = lean_ctor_get(v_val_3929_, 1);
lean_inc(v_snd_3931_);
lean_dec(v_val_3929_);
lean_inc_ref(v_cmp_3919_);
v_impl_3932_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3919_, v_fst_3930_, v_snd_3931_, v___x_3926_);
v_init_3921_ = v_impl_3932_;
v_x_3922_ = v_r_3925_;
goto _start;
}
}
else
{
lean_dec(v_m_u2081_3920_);
lean_dec_ref(v_cmp_3919_);
return v_init_3921_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(lean_object* v_cmp_3934_, lean_object* v_m_u2081_3935_, lean_object* v_m_u2082_3936_){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = lean_box(1);
v___x_3938_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3934_, v_m_u2081_3935_, v___x_3937_, v_m_u2082_3936_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(lean_object* v_cmp_3939_, lean_object* v_m_u2082_3940_, lean_object* v_t_3941_){
_start:
{
if (lean_obj_tag(v_t_3941_) == 0)
{
lean_object* v_k_3942_; lean_object* v_v_3943_; lean_object* v_l_3944_; lean_object* v_r_3945_; uint8_t v___x_3946_; 
v_k_3942_ = lean_ctor_get(v_t_3941_, 1);
lean_inc_n(v_k_3942_, 2);
v_v_3943_ = lean_ctor_get(v_t_3941_, 2);
lean_inc(v_v_3943_);
v_l_3944_ = lean_ctor_get(v_t_3941_, 3);
lean_inc(v_l_3944_);
v_r_3945_ = lean_ctor_get(v_t_3941_, 4);
lean_inc(v_r_3945_);
lean_dec_ref(v_t_3941_);
lean_inc(v_m_u2082_3940_);
lean_inc_ref(v_cmp_3939_);
v___x_3946_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3939_, v_k_3942_, v_m_u2082_3940_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
lean_dec(v_v_3943_);
lean_dec(v_k_3942_);
lean_inc(v_m_u2082_3940_);
lean_inc_ref(v_cmp_3939_);
v___x_3947_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3939_, v_m_u2082_3940_, v_l_3944_);
v___x_3948_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3939_, v_m_u2082_3940_, v_r_3945_);
v___x_3949_ = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(v___x_3947_, v___x_3948_);
return v___x_3949_;
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
lean_inc(v_m_u2082_3940_);
lean_inc_ref(v_cmp_3939_);
v___x_3950_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3939_, v_m_u2082_3940_, v_l_3944_);
v___x_3951_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3939_, v_m_u2082_3940_, v_r_3945_);
v___x_3952_ = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(v_k_3942_, v_v_3943_, v___x_3950_, v___x_3951_);
return v___x_3952_;
}
}
else
{
lean_dec(v_m_u2082_3940_);
lean_dec_ref(v_cmp_3939_);
return v_t_3941_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(lean_object* v_cmp_3953_, lean_object* v_m_u2081_3954_, lean_object* v_m_u2082_3955_){
_start:
{
lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3963_; 
if (lean_obj_tag(v_m_u2081_3954_) == 0)
{
lean_object* v_size_3966_; 
v_size_3966_ = lean_ctor_get(v_m_u2081_3954_, 0);
lean_inc(v_size_3966_);
v___y_3963_ = v_size_3966_;
goto v___jp_3962_;
}
else
{
lean_object* v___x_3967_; 
v___x_3967_ = lean_unsigned_to_nat(0u);
v___y_3963_ = v___x_3967_;
goto v___jp_3962_;
}
v___jp_3956_:
{
uint8_t v___x_3959_; 
v___x_3959_ = lean_nat_dec_le(v___y_3957_, v___y_3958_);
lean_dec(v___y_3958_);
lean_dec(v___y_3957_);
if (v___x_3959_ == 0)
{
lean_object* v___x_3960_; 
v___x_3960_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(v_cmp_3953_, v_m_u2081_3954_, v_m_u2082_3955_);
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; 
v___x_3961_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3953_, v_m_u2082_3955_, v_m_u2081_3954_);
return v___x_3961_;
}
}
v___jp_3962_:
{
if (lean_obj_tag(v_m_u2082_3955_) == 0)
{
lean_object* v_size_3964_; 
v_size_3964_ = lean_ctor_get(v_m_u2082_3955_, 0);
lean_inc(v_size_3964_);
v___y_3957_ = v___y_3963_;
v___y_3958_ = v_size_3964_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_3965_; 
v___x_3965_ = lean_unsigned_to_nat(0u);
v___y_3957_ = v___y_3963_;
v___y_3958_ = v___x_3965_;
goto v___jp_3956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter___redArg(lean_object* v_cmp_3968_, lean_object* v_t_u2081_3969_, lean_object* v_t_u2082_3970_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_3968_, v_t_u2081_3969_, v_t_u2082_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter(lean_object* v_00_u03b1_3972_, lean_object* v_00_u03b2_3973_, lean_object* v_cmp_3974_, lean_object* v_t_u2081_3975_, lean_object* v_t_u2082_3976_){
_start:
{
lean_object* v___x_3977_; 
v___x_3977_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_3974_, v_t_u2081_3975_, v_t_u2082_3976_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0(lean_object* v_00_u03b1_3978_, lean_object* v_cmp_3979_, lean_object* v_00_u03b2_3980_, lean_object* v_m_u2081_3981_, lean_object* v_m_u2082_3982_){
_start:
{
lean_object* v___x_3983_; 
v___x_3983_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_3979_, v_m_u2081_3981_, v_m_u2082_3982_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0(lean_object* v_00_u03b1_3984_, lean_object* v_cmp_3985_, lean_object* v_00_u03b2_3986_, lean_object* v_m_u2081_3987_, lean_object* v_m_u2082_3988_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(v_cmp_3985_, v_m_u2081_3987_, v_m_u2082_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1(lean_object* v_00_u03b1_3990_, lean_object* v_00_u03b2_3991_, lean_object* v_cmp_3992_, lean_object* v_m_u2082_3993_, lean_object* v_t_3994_){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3992_, v_m_u2082_3993_, v_t_3994_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3996_, lean_object* v_cmp_3997_, lean_object* v_00_u03b2_3998_, lean_object* v_t_3999_, lean_object* v_k_4000_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3997_, v_t_3999_, v_k_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_4002_, lean_object* v_cmp_4003_, lean_object* v_00_u03b2_4004_, lean_object* v_k_4005_, lean_object* v_v_4006_, lean_object* v_t_4007_, lean_object* v_hl_4008_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_4003_, v_k_4005_, v_v_4006_, v_t_4007_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3___redArg(lean_object* v_cmp_4010_, lean_object* v_m_u2081_4011_, lean_object* v_init_4012_, lean_object* v_t_4013_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4010_, v_m_u2081_4011_, v_init_4012_, v_t_4013_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4015_, lean_object* v_00_u03b2_4016_, lean_object* v_cmp_4017_, lean_object* v_m_u2081_4018_, lean_object* v_init_4019_, lean_object* v_t_4020_){
_start:
{
lean_object* v___x_4021_; 
v___x_4021_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4017_, v_m_u2081_4018_, v_init_4019_, v_t_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b1_4022_, lean_object* v_00_u03b2_4023_, lean_object* v_cmp_4024_, lean_object* v_m_u2081_4025_, lean_object* v_init_4026_, lean_object* v_x_4027_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4024_, v_m_u2081_4025_, v_init_4026_, v_x_4027_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter___redArg(lean_object* v_cmp_4029_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_4030_, 0, lean_box(0));
lean_closure_set(v___x_4030_, 1, lean_box(0));
lean_closure_set(v___x_4030_, 2, v_cmp_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter(lean_object* v_00_u03b1_4031_, lean_object* v_00_u03b2_4032_, lean_object* v_cmp_4033_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_4034_, 0, lean_box(0));
lean_closure_set(v___x_4034_, 1, lean_box(0));
lean_closure_set(v___x_4034_, 2, v_cmp_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_beq___redArg(lean_object* v_cmp_4035_, lean_object* v_inst_4036_, lean_object* v_t_u2081_4037_, lean_object* v_t_u2082_4038_){
_start:
{
uint8_t v___x_4039_; 
v___x_4039_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_4035_, v_inst_4036_, v_t_u2081_4037_, v_t_u2082_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___redArg___boxed(lean_object* v_cmp_4040_, lean_object* v_inst_4041_, lean_object* v_t_u2081_4042_, lean_object* v_t_u2082_4043_){
_start:
{
uint8_t v_res_4044_; lean_object* v_r_4045_; 
v_res_4044_ = l_Std_DTreeMap_Raw_beq___redArg(v_cmp_4040_, v_inst_4041_, v_t_u2081_4042_, v_t_u2082_4043_);
v_r_4045_ = lean_box(v_res_4044_);
return v_r_4045_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_beq(lean_object* v_00_u03b1_4046_, lean_object* v_00_u03b2_4047_, lean_object* v_cmp_4048_, lean_object* v_inst_4049_, lean_object* v_inst_4050_, lean_object* v_t_u2081_4051_, lean_object* v_t_u2082_4052_){
_start:
{
uint8_t v___x_4053_; 
v___x_4053_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_4048_, v_inst_4050_, v_t_u2081_4051_, v_t_u2082_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___boxed(lean_object* v_00_u03b1_4054_, lean_object* v_00_u03b2_4055_, lean_object* v_cmp_4056_, lean_object* v_inst_4057_, lean_object* v_inst_4058_, lean_object* v_t_u2081_4059_, lean_object* v_t_u2082_4060_){
_start:
{
uint8_t v_res_4061_; lean_object* v_r_4062_; 
v_res_4061_ = l_Std_DTreeMap_Raw_beq(v_00_u03b1_4054_, v_00_u03b2_4055_, v_cmp_4056_, v_inst_4057_, v_inst_4058_, v_t_u2081_4059_, v_t_u2082_4060_);
v_r_4062_ = lean_box(v_res_4061_);
return v_r_4062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp___redArg(lean_object* v_cmp_4063_, lean_object* v_inst_4064_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_4065_, 0, lean_box(0));
lean_closure_set(v___x_4065_, 1, lean_box(0));
lean_closure_set(v___x_4065_, 2, v_cmp_4063_);
lean_closure_set(v___x_4065_, 3, lean_box(0));
lean_closure_set(v___x_4065_, 4, v_inst_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp(lean_object* v_00_u03b1_4066_, lean_object* v_00_u03b2_4067_, lean_object* v_cmp_4068_, lean_object* v_inst_4069_, lean_object* v_inst_4070_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_4071_, 0, lean_box(0));
lean_closure_set(v___x_4071_, 1, lean_box(0));
lean_closure_set(v___x_4071_, 2, v_cmp_4068_);
lean_closure_set(v___x_4071_, 3, lean_box(0));
lean_closure_set(v___x_4071_, 4, v_inst_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___redArg(lean_object* v_cmp_4072_, lean_object* v_inst_4073_, lean_object* v_t_u2081_4074_, lean_object* v_t_u2082_4075_){
_start:
{
uint8_t v___x_4076_; 
v___x_4076_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_4072_, v_inst_4073_, v_t_u2081_4074_, v_t_u2082_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___redArg___boxed(lean_object* v_cmp_4077_, lean_object* v_inst_4078_, lean_object* v_t_u2081_4079_, lean_object* v_t_u2082_4080_){
_start:
{
uint8_t v_res_4081_; lean_object* v_r_4082_; 
v_res_4081_ = l_Std_DTreeMap_Raw_Const_beq___redArg(v_cmp_4077_, v_inst_4078_, v_t_u2081_4079_, v_t_u2082_4080_);
v_r_4082_ = lean_box(v_res_4081_);
return v_r_4082_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq(lean_object* v_00_u03b1_4083_, lean_object* v_cmp_4084_, lean_object* v_00_u03b2_4085_, lean_object* v_inst_4086_, lean_object* v_t_u2081_4087_, lean_object* v_t_u2082_4088_){
_start:
{
uint8_t v___x_4089_; 
v___x_4089_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_4084_, v_inst_4086_, v_t_u2081_4087_, v_t_u2082_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___boxed(lean_object* v_00_u03b1_4090_, lean_object* v_cmp_4091_, lean_object* v_00_u03b2_4092_, lean_object* v_inst_4093_, lean_object* v_t_u2081_4094_, lean_object* v_t_u2082_4095_){
_start:
{
uint8_t v_res_4096_; lean_object* v_r_4097_; 
v_res_4096_ = l_Std_DTreeMap_Raw_Const_beq(v_00_u03b1_4090_, v_cmp_4091_, v_00_u03b2_4092_, v_inst_4093_, v_t_u2081_4094_, v_t_u2082_4095_);
v_r_4097_ = lean_box(v_res_4096_);
return v_r_4097_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(lean_object* v_cmp_4098_, lean_object* v_t_u2082_4099_, lean_object* v_t_4100_){
_start:
{
if (lean_obj_tag(v_t_4100_) == 0)
{
lean_object* v_k_4101_; lean_object* v_v_4102_; lean_object* v_l_4103_; lean_object* v_r_4104_; uint8_t v___x_4105_; 
v_k_4101_ = lean_ctor_get(v_t_4100_, 1);
lean_inc_n(v_k_4101_, 2);
v_v_4102_ = lean_ctor_get(v_t_4100_, 2);
lean_inc(v_v_4102_);
v_l_4103_ = lean_ctor_get(v_t_4100_, 3);
lean_inc(v_l_4103_);
v_r_4104_ = lean_ctor_get(v_t_4100_, 4);
lean_inc(v_r_4104_);
lean_dec_ref(v_t_4100_);
lean_inc(v_t_u2082_4099_);
lean_inc_ref(v_cmp_4098_);
v___x_4105_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_4098_, v_k_4101_, v_t_u2082_4099_);
if (v___x_4105_ == 0)
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_inc(v_t_u2082_4099_);
lean_inc_ref(v_cmp_4098_);
v___x_4106_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4098_, v_t_u2082_4099_, v_l_4103_);
v___x_4107_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4098_, v_t_u2082_4099_, v_r_4104_);
v___x_4108_ = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(v_k_4101_, v_v_4102_, v___x_4106_, v___x_4107_);
return v___x_4108_;
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_dec(v_v_4102_);
lean_dec(v_k_4101_);
lean_inc(v_t_u2082_4099_);
lean_inc_ref(v_cmp_4098_);
v___x_4109_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4098_, v_t_u2082_4099_, v_l_4103_);
v___x_4110_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4098_, v_t_u2082_4099_, v_r_4104_);
v___x_4111_ = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(v___x_4109_, v___x_4110_);
return v___x_4111_;
}
}
else
{
lean_dec(v_t_u2082_4099_);
lean_dec_ref(v_cmp_4098_);
return v_t_4100_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(lean_object* v_cmp_4112_, lean_object* v_k_4113_, lean_object* v_t_4114_){
_start:
{
if (lean_obj_tag(v_t_4114_) == 0)
{
lean_object* v_k_4115_; lean_object* v_v_4116_; lean_object* v_l_4117_; lean_object* v_r_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4808_; 
v_k_4115_ = lean_ctor_get(v_t_4114_, 1);
v_v_4116_ = lean_ctor_get(v_t_4114_, 2);
v_l_4117_ = lean_ctor_get(v_t_4114_, 3);
v_r_4118_ = lean_ctor_get(v_t_4114_, 4);
v_isSharedCheck_4808_ = !lean_is_exclusive(v_t_4114_);
if (v_isSharedCheck_4808_ == 0)
{
lean_object* v_unused_4809_; 
v_unused_4809_ = lean_ctor_get(v_t_4114_, 0);
lean_dec(v_unused_4809_);
v___x_4120_ = v_t_4114_;
v_isShared_4121_ = v_isSharedCheck_4808_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_r_4118_);
lean_inc(v_l_4117_);
lean_inc(v_v_4116_);
lean_inc(v_k_4115_);
lean_dec(v_t_4114_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4808_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4122_; uint8_t v___x_4123_; 
lean_inc_ref(v_cmp_4112_);
lean_inc(v_k_4115_);
lean_inc(v_k_4113_);
v___x_4122_ = lean_apply_2(v_cmp_4112_, v_k_4113_, v_k_4115_);
v___x_4123_ = lean_unbox(v___x_4122_);
switch(v___x_4123_)
{
case 0:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4112_, v_k_4113_, v_l_4117_);
if (lean_obj_tag(v___x_4124_) == 0)
{
if (lean_obj_tag(v_r_4118_) == 0)
{
lean_object* v_size_4125_; lean_object* v_size_4126_; lean_object* v_k_4127_; lean_object* v_v_4128_; lean_object* v_l_4129_; lean_object* v_r_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; uint8_t v___x_4133_; 
v_size_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_size_4125_);
v_size_4126_ = lean_ctor_get(v_r_4118_, 0);
v_k_4127_ = lean_ctor_get(v_r_4118_, 1);
v_v_4128_ = lean_ctor_get(v_r_4118_, 2);
v_l_4129_ = lean_ctor_get(v_r_4118_, 3);
lean_inc(v_l_4129_);
v_r_4130_ = lean_ctor_get(v_r_4118_, 4);
v___x_4131_ = lean_unsigned_to_nat(3u);
v___x_4132_ = lean_nat_mul(v___x_4131_, v_size_4125_);
v___x_4133_ = lean_nat_dec_lt(v___x_4132_, v_size_4126_);
lean_dec(v___x_4132_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4138_; 
lean_dec(v_l_4129_);
v___x_4134_ = lean_unsigned_to_nat(1u);
v___x_4135_ = lean_nat_add(v___x_4134_, v_size_4125_);
lean_dec(v_size_4125_);
v___x_4136_ = lean_nat_add(v___x_4135_, v_size_4126_);
lean_dec(v___x_4135_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 3, v___x_4124_);
lean_ctor_set(v___x_4120_, 0, v___x_4136_);
v___x_4138_ = v___x_4120_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4139_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4139_, 3, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4139_, 4, v_r_4118_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
else
{
lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4209_; 
lean_inc(v_r_4130_);
lean_inc(v_v_4128_);
lean_inc(v_k_4127_);
lean_inc(v_size_4126_);
v_isSharedCheck_4209_ = !lean_is_exclusive(v_r_4118_);
if (v_isSharedCheck_4209_ == 0)
{
lean_object* v_unused_4210_; lean_object* v_unused_4211_; lean_object* v_unused_4212_; lean_object* v_unused_4213_; lean_object* v_unused_4214_; 
v_unused_4210_ = lean_ctor_get(v_r_4118_, 4);
lean_dec(v_unused_4210_);
v_unused_4211_ = lean_ctor_get(v_r_4118_, 3);
lean_dec(v_unused_4211_);
v_unused_4212_ = lean_ctor_get(v_r_4118_, 2);
lean_dec(v_unused_4212_);
v_unused_4213_ = lean_ctor_get(v_r_4118_, 1);
lean_dec(v_unused_4213_);
v_unused_4214_ = lean_ctor_get(v_r_4118_, 0);
lean_dec(v_unused_4214_);
v___x_4141_ = v_r_4118_;
v_isShared_4142_ = v_isSharedCheck_4209_;
goto v_resetjp_4140_;
}
else
{
lean_dec(v_r_4118_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4209_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
if (lean_obj_tag(v_l_4129_) == 0)
{
if (lean_obj_tag(v_r_4130_) == 0)
{
lean_object* v_size_4143_; lean_object* v_k_4144_; lean_object* v_v_4145_; lean_object* v_l_4146_; lean_object* v_r_4147_; lean_object* v_size_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; 
v_size_4143_ = lean_ctor_get(v_l_4129_, 0);
v_k_4144_ = lean_ctor_get(v_l_4129_, 1);
v_v_4145_ = lean_ctor_get(v_l_4129_, 2);
v_l_4146_ = lean_ctor_get(v_l_4129_, 3);
v_r_4147_ = lean_ctor_get(v_l_4129_, 4);
v_size_4148_ = lean_ctor_get(v_r_4130_, 0);
v___x_4149_ = lean_unsigned_to_nat(2u);
v___x_4150_ = lean_nat_mul(v___x_4149_, v_size_4148_);
v___x_4151_ = lean_nat_dec_lt(v_size_4143_, v___x_4150_);
lean_dec(v___x_4150_);
if (v___x_4151_ == 0)
{
lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4180_; 
lean_inc(v_r_4147_);
lean_inc(v_l_4146_);
lean_inc(v_v_4145_);
lean_inc(v_k_4144_);
v_isSharedCheck_4180_ = !lean_is_exclusive(v_l_4129_);
if (v_isSharedCheck_4180_ == 0)
{
lean_object* v_unused_4181_; lean_object* v_unused_4182_; lean_object* v_unused_4183_; lean_object* v_unused_4184_; lean_object* v_unused_4185_; 
v_unused_4181_ = lean_ctor_get(v_l_4129_, 4);
lean_dec(v_unused_4181_);
v_unused_4182_ = lean_ctor_get(v_l_4129_, 3);
lean_dec(v_unused_4182_);
v_unused_4183_ = lean_ctor_get(v_l_4129_, 2);
lean_dec(v_unused_4183_);
v_unused_4184_ = lean_ctor_get(v_l_4129_, 1);
lean_dec(v_unused_4184_);
v_unused_4185_ = lean_ctor_get(v_l_4129_, 0);
lean_dec(v_unused_4185_);
v___x_4153_ = v_l_4129_;
v_isShared_4154_ = v_isSharedCheck_4180_;
goto v_resetjp_4152_;
}
else
{
lean_dec(v_l_4129_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4180_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4170_; 
v___x_4155_ = lean_unsigned_to_nat(1u);
v___x_4156_ = lean_nat_add(v___x_4155_, v_size_4125_);
lean_dec(v_size_4125_);
v___x_4157_ = lean_nat_add(v___x_4156_, v_size_4126_);
lean_dec(v_size_4126_);
if (lean_obj_tag(v_l_4146_) == 0)
{
lean_object* v_size_4178_; 
v_size_4178_ = lean_ctor_get(v_l_4146_, 0);
lean_inc(v_size_4178_);
v___y_4170_ = v_size_4178_;
goto v___jp_4169_;
}
else
{
lean_object* v___x_4179_; 
v___x_4179_ = lean_unsigned_to_nat(0u);
v___y_4170_ = v___x_4179_;
goto v___jp_4169_;
}
v___jp_4158_:
{
lean_object* v___x_4162_; lean_object* v___x_4164_; 
v___x_4162_ = lean_nat_add(v___y_4159_, v___y_4161_);
lean_dec(v___y_4161_);
lean_dec(v___y_4159_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 4, v_r_4130_);
lean_ctor_set(v___x_4153_, 3, v_r_4147_);
lean_ctor_set(v___x_4153_, 2, v_v_4128_);
lean_ctor_set(v___x_4153_, 1, v_k_4127_);
lean_ctor_set(v___x_4153_, 0, v___x_4162_);
v___x_4164_ = v___x_4153_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4162_);
lean_ctor_set(v_reuseFailAlloc_4168_, 1, v_k_4127_);
lean_ctor_set(v_reuseFailAlloc_4168_, 2, v_v_4128_);
lean_ctor_set(v_reuseFailAlloc_4168_, 3, v_r_4147_);
lean_ctor_set(v_reuseFailAlloc_4168_, 4, v_r_4130_);
v___x_4164_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
lean_object* v___x_4166_; 
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 4, v___x_4164_);
lean_ctor_set(v___x_4141_, 3, v___y_4160_);
lean_ctor_set(v___x_4141_, 2, v_v_4145_);
lean_ctor_set(v___x_4141_, 1, v_k_4144_);
lean_ctor_set(v___x_4141_, 0, v___x_4157_);
v___x_4166_ = v___x_4141_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4157_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v_k_4144_);
lean_ctor_set(v_reuseFailAlloc_4167_, 2, v_v_4145_);
lean_ctor_set(v_reuseFailAlloc_4167_, 3, v___y_4160_);
lean_ctor_set(v_reuseFailAlloc_4167_, 4, v___x_4164_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
v___jp_4169_:
{
lean_object* v___x_4171_; lean_object* v___x_4173_; 
v___x_4171_ = lean_nat_add(v___x_4156_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec(v___x_4156_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v_l_4146_);
lean_ctor_set(v___x_4120_, 3, v___x_4124_);
lean_ctor_set(v___x_4120_, 0, v___x_4171_);
v___x_4173_ = v___x_4120_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4171_);
lean_ctor_set(v_reuseFailAlloc_4177_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4177_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4177_, 3, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4177_, 4, v_l_4146_);
v___x_4173_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
lean_object* v___x_4174_; 
v___x_4174_ = lean_nat_add(v___x_4155_, v_size_4148_);
if (lean_obj_tag(v_r_4147_) == 0)
{
lean_object* v_size_4175_; 
v_size_4175_ = lean_ctor_get(v_r_4147_, 0);
lean_inc(v_size_4175_);
v___y_4159_ = v___x_4174_;
v___y_4160_ = v___x_4173_;
v___y_4161_ = v_size_4175_;
goto v___jp_4158_;
}
else
{
lean_object* v___x_4176_; 
v___x_4176_ = lean_unsigned_to_nat(0u);
v___y_4159_ = v___x_4174_;
v___y_4160_ = v___x_4173_;
v___y_4161_ = v___x_4176_;
goto v___jp_4158_;
}
}
}
}
}
else
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4191_; 
lean_del_object(v___x_4120_);
v___x_4186_ = lean_unsigned_to_nat(1u);
v___x_4187_ = lean_nat_add(v___x_4186_, v_size_4125_);
lean_dec(v_size_4125_);
v___x_4188_ = lean_nat_add(v___x_4187_, v_size_4126_);
lean_dec(v_size_4126_);
v___x_4189_ = lean_nat_add(v___x_4187_, v_size_4143_);
lean_dec(v___x_4187_);
lean_inc_ref(v___x_4124_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 4, v_l_4129_);
lean_ctor_set(v___x_4141_, 3, v___x_4124_);
lean_ctor_set(v___x_4141_, 2, v_v_4116_);
lean_ctor_set(v___x_4141_, 1, v_k_4115_);
lean_ctor_set(v___x_4141_, 0, v___x_4189_);
v___x_4191_ = v___x_4141_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v___x_4189_);
lean_ctor_set(v_reuseFailAlloc_4204_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4204_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4204_, 3, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4204_, 4, v_l_4129_);
v___x_4191_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4198_ == 0)
{
lean_object* v_unused_4199_; lean_object* v_unused_4200_; lean_object* v_unused_4201_; lean_object* v_unused_4202_; lean_object* v_unused_4203_; 
v_unused_4199_ = lean_ctor_get(v___x_4124_, 4);
lean_dec(v_unused_4199_);
v_unused_4200_ = lean_ctor_get(v___x_4124_, 3);
lean_dec(v_unused_4200_);
v_unused_4201_ = lean_ctor_get(v___x_4124_, 2);
lean_dec(v_unused_4201_);
v_unused_4202_ = lean_ctor_get(v___x_4124_, 1);
lean_dec(v_unused_4202_);
v_unused_4203_ = lean_ctor_get(v___x_4124_, 0);
lean_dec(v_unused_4203_);
v___x_4193_ = v___x_4124_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_dec(v___x_4124_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 4, v_r_4130_);
lean_ctor_set(v___x_4193_, 3, v___x_4191_);
lean_ctor_set(v___x_4193_, 2, v_v_4128_);
lean_ctor_set(v___x_4193_, 1, v_k_4127_);
lean_ctor_set(v___x_4193_, 0, v___x_4188_);
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4197_, 1, v_k_4127_);
lean_ctor_set(v_reuseFailAlloc_4197_, 2, v_v_4128_);
lean_ctor_set(v_reuseFailAlloc_4197_, 3, v___x_4191_);
lean_ctor_set(v_reuseFailAlloc_4197_, 4, v_r_4130_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
}
else
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
lean_dec_ref(v_l_4129_);
lean_del_object(v___x_4141_);
lean_dec(v_v_4128_);
lean_dec(v_k_4127_);
lean_dec(v_size_4126_);
lean_dec(v_size_4125_);
lean_dec_ref(v___x_4124_);
lean_del_object(v___x_4120_);
lean_dec(v_v_4116_);
lean_dec(v_k_4115_);
v___x_4205_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7);
v___x_4206_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4205_);
return v___x_4206_;
}
}
else
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_del_object(v___x_4141_);
lean_dec(v_r_4130_);
lean_dec(v_v_4128_);
lean_dec(v_k_4127_);
lean_dec(v_size_4126_);
lean_dec(v_size_4125_);
lean_dec_ref(v___x_4124_);
lean_del_object(v___x_4120_);
lean_dec(v_v_4116_);
lean_dec(v_k_4115_);
v___x_4207_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8);
v___x_4208_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4207_);
return v___x_4208_;
}
}
}
}
else
{
lean_object* v_size_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4219_; 
v_size_4215_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_size_4215_);
v___x_4216_ = lean_unsigned_to_nat(1u);
v___x_4217_ = lean_nat_add(v___x_4216_, v_size_4215_);
lean_dec(v_size_4215_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 3, v___x_4124_);
lean_ctor_set(v___x_4120_, 0, v___x_4217_);
v___x_4219_ = v___x_4120_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4217_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4220_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4220_, 3, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4220_, 4, v_r_4118_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
else
{
if (lean_obj_tag(v_r_4118_) == 0)
{
lean_object* v_l_4221_; 
v_l_4221_ = lean_ctor_get(v_r_4118_, 3);
lean_inc(v_l_4221_);
if (lean_obj_tag(v_l_4221_) == 0)
{
lean_object* v_r_4222_; 
v_r_4222_ = lean_ctor_get(v_r_4118_, 4);
lean_inc(v_r_4222_);
if (lean_obj_tag(v_r_4222_) == 0)
{
lean_object* v_size_4223_; lean_object* v_k_4224_; lean_object* v_v_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4239_; 
v_size_4223_ = lean_ctor_get(v_r_4118_, 0);
v_k_4224_ = lean_ctor_get(v_r_4118_, 1);
v_v_4225_ = lean_ctor_get(v_r_4118_, 2);
v_isSharedCheck_4239_ = !lean_is_exclusive(v_r_4118_);
if (v_isSharedCheck_4239_ == 0)
{
lean_object* v_unused_4240_; lean_object* v_unused_4241_; 
v_unused_4240_ = lean_ctor_get(v_r_4118_, 4);
lean_dec(v_unused_4240_);
v_unused_4241_ = lean_ctor_get(v_r_4118_, 3);
lean_dec(v_unused_4241_);
v___x_4227_ = v_r_4118_;
v_isShared_4228_ = v_isSharedCheck_4239_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_v_4225_);
lean_inc(v_k_4224_);
lean_inc(v_size_4223_);
lean_dec(v_r_4118_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4239_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v_size_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4234_; 
v_size_4229_ = lean_ctor_get(v_l_4221_, 0);
v___x_4230_ = lean_unsigned_to_nat(1u);
v___x_4231_ = lean_nat_add(v___x_4230_, v_size_4223_);
lean_dec(v_size_4223_);
v___x_4232_ = lean_nat_add(v___x_4230_, v_size_4229_);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 4, v_l_4221_);
lean_ctor_set(v___x_4227_, 3, v___x_4124_);
lean_ctor_set(v___x_4227_, 2, v_v_4116_);
lean_ctor_set(v___x_4227_, 1, v_k_4115_);
lean_ctor_set(v___x_4227_, 0, v___x_4232_);
v___x_4234_ = v___x_4227_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4232_);
lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4238_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4238_, 3, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4238_, 4, v_l_4221_);
v___x_4234_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
lean_object* v___x_4236_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v_r_4222_);
lean_ctor_set(v___x_4120_, 3, v___x_4234_);
lean_ctor_set(v___x_4120_, 2, v_v_4225_);
lean_ctor_set(v___x_4120_, 1, v_k_4224_);
lean_ctor_set(v___x_4120_, 0, v___x_4231_);
v___x_4236_ = v___x_4120_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4231_);
lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_k_4224_);
lean_ctor_set(v_reuseFailAlloc_4237_, 2, v_v_4225_);
lean_ctor_set(v_reuseFailAlloc_4237_, 3, v___x_4234_);
lean_ctor_set(v_reuseFailAlloc_4237_, 4, v_r_4222_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
else
{
lean_object* v_k_4242_; lean_object* v_v_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4267_; 
v_k_4242_ = lean_ctor_get(v_r_4118_, 1);
v_v_4243_ = lean_ctor_get(v_r_4118_, 2);
v_isSharedCheck_4267_ = !lean_is_exclusive(v_r_4118_);
if (v_isSharedCheck_4267_ == 0)
{
lean_object* v_unused_4268_; lean_object* v_unused_4269_; lean_object* v_unused_4270_; 
v_unused_4268_ = lean_ctor_get(v_r_4118_, 4);
lean_dec(v_unused_4268_);
v_unused_4269_ = lean_ctor_get(v_r_4118_, 3);
lean_dec(v_unused_4269_);
v_unused_4270_ = lean_ctor_get(v_r_4118_, 0);
lean_dec(v_unused_4270_);
v___x_4245_ = v_r_4118_;
v_isShared_4246_ = v_isSharedCheck_4267_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_v_4243_);
lean_inc(v_k_4242_);
lean_dec(v_r_4118_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4267_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v_k_4247_; lean_object* v_v_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4263_; 
v_k_4247_ = lean_ctor_get(v_l_4221_, 1);
v_v_4248_ = lean_ctor_get(v_l_4221_, 2);
v_isSharedCheck_4263_ = !lean_is_exclusive(v_l_4221_);
if (v_isSharedCheck_4263_ == 0)
{
lean_object* v_unused_4264_; lean_object* v_unused_4265_; lean_object* v_unused_4266_; 
v_unused_4264_ = lean_ctor_get(v_l_4221_, 4);
lean_dec(v_unused_4264_);
v_unused_4265_ = lean_ctor_get(v_l_4221_, 3);
lean_dec(v_unused_4265_);
v_unused_4266_ = lean_ctor_get(v_l_4221_, 0);
lean_dec(v_unused_4266_);
v___x_4250_ = v_l_4221_;
v_isShared_4251_ = v_isSharedCheck_4263_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_v_4248_);
lean_inc(v_k_4247_);
lean_dec(v_l_4221_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4263_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4255_; 
v___x_4252_ = lean_unsigned_to_nat(3u);
v___x_4253_ = lean_unsigned_to_nat(1u);
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 4, v_r_4222_);
lean_ctor_set(v___x_4250_, 3, v_r_4222_);
lean_ctor_set(v___x_4250_, 2, v_v_4116_);
lean_ctor_set(v___x_4250_, 1, v_k_4115_);
lean_ctor_set(v___x_4250_, 0, v___x_4253_);
v___x_4255_ = v___x_4250_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4253_);
lean_ctor_set(v_reuseFailAlloc_4262_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4262_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4262_, 3, v_r_4222_);
lean_ctor_set(v_reuseFailAlloc_4262_, 4, v_r_4222_);
v___x_4255_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
lean_object* v___x_4257_; 
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 3, v_r_4222_);
lean_ctor_set(v___x_4245_, 0, v___x_4253_);
v___x_4257_ = v___x_4245_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4253_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v_k_4242_);
lean_ctor_set(v_reuseFailAlloc_4261_, 2, v_v_4243_);
lean_ctor_set(v_reuseFailAlloc_4261_, 3, v_r_4222_);
lean_ctor_set(v_reuseFailAlloc_4261_, 4, v_r_4222_);
v___x_4257_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
lean_object* v___x_4259_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v___x_4257_);
lean_ctor_set(v___x_4120_, 3, v___x_4255_);
lean_ctor_set(v___x_4120_, 2, v_v_4248_);
lean_ctor_set(v___x_4120_, 1, v_k_4247_);
lean_ctor_set(v___x_4120_, 0, v___x_4252_);
v___x_4259_ = v___x_4120_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v___x_4252_);
lean_ctor_set(v_reuseFailAlloc_4260_, 1, v_k_4247_);
lean_ctor_set(v_reuseFailAlloc_4260_, 2, v_v_4248_);
lean_ctor_set(v_reuseFailAlloc_4260_, 3, v___x_4255_);
lean_ctor_set(v_reuseFailAlloc_4260_, 4, v___x_4257_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_4271_; 
v_r_4271_ = lean_ctor_get(v_r_4118_, 4);
lean_inc(v_r_4271_);
if (lean_obj_tag(v_r_4271_) == 0)
{
lean_object* v_k_4272_; lean_object* v_v_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4285_; 
v_k_4272_ = lean_ctor_get(v_r_4118_, 1);
v_v_4273_ = lean_ctor_get(v_r_4118_, 2);
v_isSharedCheck_4285_ = !lean_is_exclusive(v_r_4118_);
if (v_isSharedCheck_4285_ == 0)
{
lean_object* v_unused_4286_; lean_object* v_unused_4287_; lean_object* v_unused_4288_; 
v_unused_4286_ = lean_ctor_get(v_r_4118_, 4);
lean_dec(v_unused_4286_);
v_unused_4287_ = lean_ctor_get(v_r_4118_, 3);
lean_dec(v_unused_4287_);
v_unused_4288_ = lean_ctor_get(v_r_4118_, 0);
lean_dec(v_unused_4288_);
v___x_4275_ = v_r_4118_;
v_isShared_4276_ = v_isSharedCheck_4285_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_v_4273_);
lean_inc(v_k_4272_);
lean_dec(v_r_4118_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4285_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4280_; 
v___x_4277_ = lean_unsigned_to_nat(3u);
v___x_4278_ = lean_unsigned_to_nat(1u);
if (v_isShared_4276_ == 0)
{
lean_ctor_set(v___x_4275_, 4, v_l_4221_);
lean_ctor_set(v___x_4275_, 2, v_v_4116_);
lean_ctor_set(v___x_4275_, 1, v_k_4115_);
lean_ctor_set(v___x_4275_, 0, v___x_4278_);
v___x_4280_ = v___x_4275_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4278_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4284_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4284_, 3, v_l_4221_);
lean_ctor_set(v_reuseFailAlloc_4284_, 4, v_l_4221_);
v___x_4280_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
lean_object* v___x_4282_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v_r_4271_);
lean_ctor_set(v___x_4120_, 3, v___x_4280_);
lean_ctor_set(v___x_4120_, 2, v_v_4273_);
lean_ctor_set(v___x_4120_, 1, v_k_4272_);
lean_ctor_set(v___x_4120_, 0, v___x_4277_);
v___x_4282_ = v___x_4120_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4277_);
lean_ctor_set(v_reuseFailAlloc_4283_, 1, v_k_4272_);
lean_ctor_set(v_reuseFailAlloc_4283_, 2, v_v_4273_);
lean_ctor_set(v_reuseFailAlloc_4283_, 3, v___x_4280_);
lean_ctor_set(v_reuseFailAlloc_4283_, 4, v_r_4271_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
else
{
lean_object* v___x_4289_; lean_object* v___x_4291_; 
v___x_4289_ = lean_unsigned_to_nat(2u);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 3, v_r_4271_);
lean_ctor_set(v___x_4120_, 0, v___x_4289_);
v___x_4291_ = v___x_4120_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v___x_4289_);
lean_ctor_set(v_reuseFailAlloc_4292_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4292_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4292_, 3, v_r_4271_);
lean_ctor_set(v_reuseFailAlloc_4292_, 4, v_r_4118_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
}
else
{
lean_object* v___x_4293_; lean_object* v___x_4295_; 
v___x_4293_ = lean_unsigned_to_nat(1u);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 3, v_r_4118_);
lean_ctor_set(v___x_4120_, 0, v___x_4293_);
v___x_4295_ = v___x_4120_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4293_);
lean_ctor_set(v_reuseFailAlloc_4296_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4296_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4296_, 3, v_r_4118_);
lean_ctor_set(v_reuseFailAlloc_4296_, 4, v_r_4118_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
case 1:
{
lean_del_object(v___x_4120_);
lean_dec(v_v_4116_);
lean_dec(v_k_4115_);
lean_dec(v_k_4113_);
lean_dec_ref(v_cmp_4112_);
if (lean_obj_tag(v_l_4117_) == 0)
{
if (lean_obj_tag(v_r_4118_) == 0)
{
lean_object* v_size_4297_; lean_object* v_k_4298_; lean_object* v_v_4299_; lean_object* v_l_4300_; lean_object* v_r_4301_; lean_object* v_size_4302_; lean_object* v_k_4303_; lean_object* v_v_4304_; lean_object* v_l_4305_; lean_object* v_r_4306_; uint8_t v___x_4307_; 
v_size_4297_ = lean_ctor_get(v_l_4117_, 0);
v_k_4298_ = lean_ctor_get(v_l_4117_, 1);
v_v_4299_ = lean_ctor_get(v_l_4117_, 2);
v_l_4300_ = lean_ctor_get(v_l_4117_, 3);
v_r_4301_ = lean_ctor_get(v_l_4117_, 4);
lean_inc(v_r_4301_);
v_size_4302_ = lean_ctor_get(v_r_4118_, 0);
v_k_4303_ = lean_ctor_get(v_r_4118_, 1);
v_v_4304_ = lean_ctor_get(v_r_4118_, 2);
v_l_4305_ = lean_ctor_get(v_r_4118_, 3);
lean_inc(v_l_4305_);
v_r_4306_ = lean_ctor_get(v_r_4118_, 4);
v___x_4307_ = lean_nat_dec_lt(v_size_4297_, v_size_4302_);
if (v___x_4307_ == 0)
{
lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4459_; 
lean_inc(v_l_4300_);
lean_inc(v_v_4299_);
lean_inc(v_k_4298_);
v_isSharedCheck_4459_ = !lean_is_exclusive(v_l_4117_);
if (v_isSharedCheck_4459_ == 0)
{
lean_object* v_unused_4460_; lean_object* v_unused_4461_; lean_object* v_unused_4462_; lean_object* v_unused_4463_; lean_object* v_unused_4464_; 
v_unused_4460_ = lean_ctor_get(v_l_4117_, 4);
lean_dec(v_unused_4460_);
v_unused_4461_ = lean_ctor_get(v_l_4117_, 3);
lean_dec(v_unused_4461_);
v_unused_4462_ = lean_ctor_get(v_l_4117_, 2);
lean_dec(v_unused_4462_);
v_unused_4463_ = lean_ctor_get(v_l_4117_, 1);
lean_dec(v_unused_4463_);
v_unused_4464_ = lean_ctor_get(v_l_4117_, 0);
lean_dec(v_unused_4464_);
v___x_4309_ = v_l_4117_;
v_isShared_4310_ = v_isSharedCheck_4459_;
goto v_resetjp_4308_;
}
else
{
lean_dec(v_l_4117_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4459_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v_d_4311_; lean_object* v_tree_4312_; 
v_d_4311_ = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(v_k_4298_, v_v_4299_, v_l_4300_, v_r_4301_);
v_tree_4312_ = lean_ctor_get(v_d_4311_, 2);
lean_inc(v_tree_4312_);
if (lean_obj_tag(v_tree_4312_) == 0)
{
lean_object* v_k_4313_; lean_object* v_v_4314_; lean_object* v_size_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; 
v_k_4313_ = lean_ctor_get(v_d_4311_, 0);
lean_inc(v_k_4313_);
v_v_4314_ = lean_ctor_get(v_d_4311_, 1);
lean_inc(v_v_4314_);
lean_dec_ref(v_d_4311_);
v_size_4315_ = lean_ctor_get(v_tree_4312_, 0);
v___x_4316_ = lean_unsigned_to_nat(3u);
v___x_4317_ = lean_nat_mul(v___x_4316_, v_size_4315_);
v___x_4318_ = lean_nat_dec_lt(v___x_4317_, v_size_4302_);
lean_dec(v___x_4317_);
if (v___x_4318_ == 0)
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4323_; 
lean_dec(v_l_4305_);
v___x_4319_ = lean_unsigned_to_nat(1u);
v___x_4320_ = lean_nat_add(v___x_4319_, v_size_4315_);
v___x_4321_ = lean_nat_add(v___x_4320_, v_size_4302_);
lean_dec(v___x_4320_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 4, v_r_4118_);
lean_ctor_set(v___x_4309_, 3, v_tree_4312_);
lean_ctor_set(v___x_4309_, 2, v_v_4314_);
lean_ctor_set(v___x_4309_, 1, v_k_4313_);
lean_ctor_set(v___x_4309_, 0, v___x_4321_);
v___x_4323_ = v___x_4309_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
lean_ctor_set(v_reuseFailAlloc_4324_, 1, v_k_4313_);
lean_ctor_set(v_reuseFailAlloc_4324_, 2, v_v_4314_);
lean_ctor_set(v_reuseFailAlloc_4324_, 3, v_tree_4312_);
lean_ctor_set(v_reuseFailAlloc_4324_, 4, v_r_4118_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
else
{
lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4385_; 
lean_inc(v_r_4306_);
lean_inc(v_v_4304_);
lean_inc(v_k_4303_);
lean_inc(v_size_4302_);
v_isSharedCheck_4385_ = !lean_is_exclusive(v_r_4118_);
if (v_isSharedCheck_4385_ == 0)
{
lean_object* v_unused_4386_; lean_object* v_unused_4387_; lean_object* v_unused_4388_; lean_object* v_unused_4389_; lean_object* v_unused_4390_; 
v_unused_4386_ = lean_ctor_get(v_r_4118_, 4);
lean_dec(v_unused_4386_);
v_unused_4387_ = lean_ctor_get(v_r_4118_, 3);
lean_dec(v_unused_4387_);
v_unused_4388_ = lean_ctor_get(v_r_4118_, 2);
lean_dec(v_unused_4388_);
v_unused_4389_ = lean_ctor_get(v_r_4118_, 1);
lean_dec(v_unused_4389_);
v_unused_4390_ = lean_ctor_get(v_r_4118_, 0);
lean_dec(v_unused_4390_);
v___x_4326_ = v_r_4118_;
v_isShared_4327_ = v_isSharedCheck_4385_;
goto v_resetjp_4325_;
}
else
{
lean_dec(v_r_4118_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4385_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
if (lean_obj_tag(v_l_4305_) == 0)
{
if (lean_obj_tag(v_r_4306_) == 0)
{
lean_object* v_size_4328_; lean_object* v_k_4329_; lean_object* v_v_4330_; lean_object* v_l_4331_; lean_object* v_r_4332_; lean_object* v_size_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; uint8_t v___x_4336_; 
v_size_4328_ = lean_ctor_get(v_l_4305_, 0);
v_k_4329_ = lean_ctor_get(v_l_4305_, 1);
v_v_4330_ = lean_ctor_get(v_l_4305_, 2);
v_l_4331_ = lean_ctor_get(v_l_4305_, 3);
v_r_4332_ = lean_ctor_get(v_l_4305_, 4);
v_size_4333_ = lean_ctor_get(v_r_4306_, 0);
v___x_4334_ = lean_unsigned_to_nat(2u);
v___x_4335_ = lean_nat_mul(v___x_4334_, v_size_4333_);
v___x_4336_ = lean_nat_dec_lt(v_size_4328_, v___x_4335_);
lean_dec(v___x_4335_);
if (v___x_4336_ == 0)
{
lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4365_; 
lean_inc(v_r_4332_);
lean_inc(v_l_4331_);
lean_inc(v_v_4330_);
lean_inc(v_k_4329_);
v_isSharedCheck_4365_ = !lean_is_exclusive(v_l_4305_);
if (v_isSharedCheck_4365_ == 0)
{
lean_object* v_unused_4366_; lean_object* v_unused_4367_; lean_object* v_unused_4368_; lean_object* v_unused_4369_; lean_object* v_unused_4370_; 
v_unused_4366_ = lean_ctor_get(v_l_4305_, 4);
lean_dec(v_unused_4366_);
v_unused_4367_ = lean_ctor_get(v_l_4305_, 3);
lean_dec(v_unused_4367_);
v_unused_4368_ = lean_ctor_get(v_l_4305_, 2);
lean_dec(v_unused_4368_);
v_unused_4369_ = lean_ctor_get(v_l_4305_, 1);
lean_dec(v_unused_4369_);
v_unused_4370_ = lean_ctor_get(v_l_4305_, 0);
lean_dec(v_unused_4370_);
v___x_4338_ = v_l_4305_;
v_isShared_4339_ = v_isSharedCheck_4365_;
goto v_resetjp_4337_;
}
else
{
lean_dec(v_l_4305_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4365_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4355_; 
v___x_4340_ = lean_unsigned_to_nat(1u);
v___x_4341_ = lean_nat_add(v___x_4340_, v_size_4315_);
v___x_4342_ = lean_nat_add(v___x_4341_, v_size_4302_);
lean_dec(v_size_4302_);
if (lean_obj_tag(v_l_4331_) == 0)
{
lean_object* v_size_4363_; 
v_size_4363_ = lean_ctor_get(v_l_4331_, 0);
lean_inc(v_size_4363_);
v___y_4355_ = v_size_4363_;
goto v___jp_4354_;
}
else
{
lean_object* v___x_4364_; 
v___x_4364_ = lean_unsigned_to_nat(0u);
v___y_4355_ = v___x_4364_;
goto v___jp_4354_;
}
v___jp_4343_:
{
lean_object* v___x_4347_; lean_object* v___x_4349_; 
v___x_4347_ = lean_nat_add(v___y_4345_, v___y_4346_);
lean_dec(v___y_4346_);
lean_dec(v___y_4345_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 4, v_r_4306_);
lean_ctor_set(v___x_4338_, 3, v_r_4332_);
lean_ctor_set(v___x_4338_, 2, v_v_4304_);
lean_ctor_set(v___x_4338_, 1, v_k_4303_);
lean_ctor_set(v___x_4338_, 0, v___x_4347_);
v___x_4349_ = v___x_4338_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4347_);
lean_ctor_set(v_reuseFailAlloc_4353_, 1, v_k_4303_);
lean_ctor_set(v_reuseFailAlloc_4353_, 2, v_v_4304_);
lean_ctor_set(v_reuseFailAlloc_4353_, 3, v_r_4332_);
lean_ctor_set(v_reuseFailAlloc_4353_, 4, v_r_4306_);
v___x_4349_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
lean_object* v___x_4351_; 
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 4, v___x_4349_);
lean_ctor_set(v___x_4326_, 3, v___y_4344_);
lean_ctor_set(v___x_4326_, 2, v_v_4330_);
lean_ctor_set(v___x_4326_, 1, v_k_4329_);
lean_ctor_set(v___x_4326_, 0, v___x_4342_);
v___x_4351_ = v___x_4326_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4342_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v_k_4329_);
lean_ctor_set(v_reuseFailAlloc_4352_, 2, v_v_4330_);
lean_ctor_set(v_reuseFailAlloc_4352_, 3, v___y_4344_);
lean_ctor_set(v_reuseFailAlloc_4352_, 4, v___x_4349_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
v___jp_4354_:
{
lean_object* v___x_4356_; lean_object* v___x_4358_; 
v___x_4356_ = lean_nat_add(v___x_4341_, v___y_4355_);
lean_dec(v___y_4355_);
lean_dec(v___x_4341_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 4, v_l_4331_);
lean_ctor_set(v___x_4309_, 3, v_tree_4312_);
lean_ctor_set(v___x_4309_, 2, v_v_4314_);
lean_ctor_set(v___x_4309_, 1, v_k_4313_);
lean_ctor_set(v___x_4309_, 0, v___x_4356_);
v___x_4358_ = v___x_4309_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v___x_4356_);
lean_ctor_set(v_reuseFailAlloc_4362_, 1, v_k_4313_);
lean_ctor_set(v_reuseFailAlloc_4362_, 2, v_v_4314_);
lean_ctor_set(v_reuseFailAlloc_4362_, 3, v_tree_4312_);
lean_ctor_set(v_reuseFailAlloc_4362_, 4, v_l_4331_);
v___x_4358_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
lean_object* v___x_4359_; 
v___x_4359_ = lean_nat_add(v___x_4340_, v_size_4333_);
if (lean_obj_tag(v_r_4332_) == 0)
{
lean_object* v_size_4360_; 
v_size_4360_ = lean_ctor_get(v_r_4332_, 0);
lean_inc(v_size_4360_);
v___y_4344_ = v___x_4358_;
v___y_4345_ = v___x_4359_;
v___y_4346_ = v_size_4360_;
goto v___jp_4343_;
}
else
{
lean_object* v___x_4361_; 
v___x_4361_ = lean_unsigned_to_nat(0u);
v___y_4344_ = v___x_4358_;
v___y_4345_ = v___x_4359_;
v___y_4346_ = v___x_4361_;
goto v___jp_4343_;
}
}
}
}
}
else
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4376_; 
v___x_4371_ = lean_unsigned_to_nat(1u);
v___x_4372_ = lean_nat_add(v___x_4371_, v_size_4315_);
v___x_4373_ = lean_nat_add(v___x_4372_, v_size_4302_);
lean_dec(v_size_4302_);
v___x_4374_ = lean_nat_add(v___x_4372_, v_size_4328_);
lean_dec(v___x_4372_);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 4, v_l_4305_);
lean_ctor_set(v___x_4326_, 3, v_tree_4312_);
lean_ctor_set(v___x_4326_, 2, v_v_4314_);
lean_ctor_set(v___x_4326_, 1, v_k_4313_);
lean_ctor_set(v___x_4326_, 0, v___x_4374_);
v___x_4376_ = v___x_4326_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4374_);
lean_ctor_set(v_reuseFailAlloc_4380_, 1, v_k_4313_);
lean_ctor_set(v_reuseFailAlloc_4380_, 2, v_v_4314_);
lean_ctor_set(v_reuseFailAlloc_4380_, 3, v_tree_4312_);
lean_ctor_set(v_reuseFailAlloc_4380_, 4, v_l_4305_);
v___x_4376_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
lean_object* v___x_4378_; 
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 4, v_r_4306_);
lean_ctor_set(v___x_4309_, 3, v___x_4376_);
lean_ctor_set(v___x_4309_, 2, v_v_4304_);
lean_ctor_set(v___x_4309_, 1, v_k_4303_);
lean_ctor_set(v___x_4309_, 0, v___x_4373_);
v___x_4378_ = v___x_4309_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v___x_4373_);
lean_ctor_set(v_reuseFailAlloc_4379_, 1, v_k_4303_);
lean_ctor_set(v_reuseFailAlloc_4379_, 2, v_v_4304_);
lean_ctor_set(v_reuseFailAlloc_4379_, 3, v___x_4376_);
lean_ctor_set(v_reuseFailAlloc_4379_, 4, v_r_4306_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
else
{
lean_object* v___x_4381_; lean_object* v___x_4382_; 
lean_dec_ref(v_l_4305_);
lean_del_object(v___x_4326_);
lean_dec(v_v_4314_);
lean_dec_ref(v_tree_4312_);
lean_dec(v_k_4313_);
lean_del_object(v___x_4309_);
lean_dec(v_v_4304_);
lean_dec(v_k_4303_);
lean_dec(v_size_4302_);
v___x_4381_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7);
v___x_4382_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4381_);
return v___x_4382_;
}
}
else
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
lean_del_object(v___x_4326_);
lean_dec(v_v_4314_);
lean_dec(v_k_4313_);
lean_dec_ref(v_tree_4312_);
lean_del_object(v___x_4309_);
lean_dec(v_r_4306_);
lean_dec(v_v_4304_);
lean_dec(v_k_4303_);
lean_dec(v_size_4302_);
v___x_4383_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8);
v___x_4384_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4383_);
return v___x_4384_;
}
}
}
}
else
{
lean_inc(v_r_4306_);
if (lean_obj_tag(v_l_4305_) == 0)
{
lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4428_; 
lean_inc(v_v_4304_);
lean_inc(v_k_4303_);
lean_inc(v_size_4302_);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_r_4118_);
if (v_isSharedCheck_4428_ == 0)
{
lean_object* v_unused_4429_; lean_object* v_unused_4430_; lean_object* v_unused_4431_; lean_object* v_unused_4432_; lean_object* v_unused_4433_; 
v_unused_4429_ = lean_ctor_get(v_r_4118_, 4);
lean_dec(v_unused_4429_);
v_unused_4430_ = lean_ctor_get(v_r_4118_, 3);
lean_dec(v_unused_4430_);
v_unused_4431_ = lean_ctor_get(v_r_4118_, 2);
lean_dec(v_unused_4431_);
v_unused_4432_ = lean_ctor_get(v_r_4118_, 1);
lean_dec(v_unused_4432_);
v_unused_4433_ = lean_ctor_get(v_r_4118_, 0);
lean_dec(v_unused_4433_);
v___x_4392_ = v_r_4118_;
v_isShared_4393_ = v_isSharedCheck_4428_;
goto v_resetjp_4391_;
}
else
{
lean_dec(v_r_4118_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4428_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
if (lean_obj_tag(v_r_4306_) == 0)
{
lean_object* v_k_4394_; lean_object* v_v_4395_; lean_object* v_size_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4401_; 
v_k_4394_ = lean_ctor_get(v_d_4311_, 0);
lean_inc(v_k_4394_);
v_v_4395_ = lean_ctor_get(v_d_4311_, 1);
lean_inc(v_v_4395_);
lean_dec_ref(v_d_4311_);
v_size_4396_ = lean_ctor_get(v_l_4305_, 0);
v___x_4397_ = lean_unsigned_to_nat(1u);
v___x_4398_ = lean_nat_add(v___x_4397_, v_size_4302_);
lean_dec(v_size_4302_);
v___x_4399_ = lean_nat_add(v___x_4397_, v_size_4396_);
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 4, v_l_4305_);
lean_ctor_set(v___x_4392_, 3, v_tree_4312_);
lean_ctor_set(v___x_4392_, 2, v_v_4395_);
lean_ctor_set(v___x_4392_, 1, v_k_4394_);
lean_ctor_set(v___x_4392_, 0, v___x_4399_);
v___x_4401_ = v___x_4392_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4399_);
lean_ctor_set(v_reuseFailAlloc_4405_, 1, v_k_4394_);
lean_ctor_set(v_reuseFailAlloc_4405_, 2, v_v_4395_);
lean_ctor_set(v_reuseFailAlloc_4405_, 3, v_tree_4312_);
lean_ctor_set(v_reuseFailAlloc_4405_, 4, v_l_4305_);
v___x_4401_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
lean_object* v___x_4403_; 
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 4, v_r_4306_);
lean_ctor_set(v___x_4309_, 3, v___x_4401_);
lean_ctor_set(v___x_4309_, 2, v_v_4304_);
lean_ctor_set(v___x_4309_, 1, v_k_4303_);
lean_ctor_set(v___x_4309_, 0, v___x_4398_);
v___x_4403_ = v___x_4309_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4398_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_k_4303_);
lean_ctor_set(v_reuseFailAlloc_4404_, 2, v_v_4304_);
lean_ctor_set(v_reuseFailAlloc_4404_, 3, v___x_4401_);
lean_ctor_set(v_reuseFailAlloc_4404_, 4, v_r_4306_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
else
{
lean_object* v_k_4406_; lean_object* v_v_4407_; lean_object* v_k_4408_; lean_object* v_v_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4424_; 
lean_dec(v_size_4302_);
v_k_4406_ = lean_ctor_get(v_d_4311_, 0);
lean_inc(v_k_4406_);
v_v_4407_ = lean_ctor_get(v_d_4311_, 1);
lean_inc(v_v_4407_);
lean_dec_ref(v_d_4311_);
v_k_4408_ = lean_ctor_get(v_l_4305_, 1);
v_v_4409_ = lean_ctor_get(v_l_4305_, 2);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_l_4305_);
if (v_isSharedCheck_4424_ == 0)
{
lean_object* v_unused_4425_; lean_object* v_unused_4426_; lean_object* v_unused_4427_; 
v_unused_4425_ = lean_ctor_get(v_l_4305_, 4);
lean_dec(v_unused_4425_);
v_unused_4426_ = lean_ctor_get(v_l_4305_, 3);
lean_dec(v_unused_4426_);
v_unused_4427_ = lean_ctor_get(v_l_4305_, 0);
lean_dec(v_unused_4427_);
v___x_4411_ = v_l_4305_;
v_isShared_4412_ = v_isSharedCheck_4424_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_v_4409_);
lean_inc(v_k_4408_);
lean_dec(v_l_4305_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4424_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4416_; 
v___x_4413_ = lean_unsigned_to_nat(3u);
v___x_4414_ = lean_unsigned_to_nat(1u);
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 4, v_r_4306_);
lean_ctor_set(v___x_4411_, 3, v_r_4306_);
lean_ctor_set(v___x_4411_, 2, v_v_4407_);
lean_ctor_set(v___x_4411_, 1, v_k_4406_);
lean_ctor_set(v___x_4411_, 0, v___x_4414_);
v___x_4416_ = v___x_4411_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4414_);
lean_ctor_set(v_reuseFailAlloc_4423_, 1, v_k_4406_);
lean_ctor_set(v_reuseFailAlloc_4423_, 2, v_v_4407_);
lean_ctor_set(v_reuseFailAlloc_4423_, 3, v_r_4306_);
lean_ctor_set(v_reuseFailAlloc_4423_, 4, v_r_4306_);
v___x_4416_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4418_; 
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 3, v_r_4306_);
lean_ctor_set(v___x_4392_, 0, v___x_4414_);
v___x_4418_ = v___x_4392_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4414_);
lean_ctor_set(v_reuseFailAlloc_4422_, 1, v_k_4303_);
lean_ctor_set(v_reuseFailAlloc_4422_, 2, v_v_4304_);
lean_ctor_set(v_reuseFailAlloc_4422_, 3, v_r_4306_);
lean_ctor_set(v_reuseFailAlloc_4422_, 4, v_r_4306_);
v___x_4418_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4420_; 
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 4, v___x_4418_);
lean_ctor_set(v___x_4309_, 3, v___x_4416_);
lean_ctor_set(v___x_4309_, 2, v_v_4409_);
lean_ctor_set(v___x_4309_, 1, v_k_4408_);
lean_ctor_set(v___x_4309_, 0, v___x_4413_);
v___x_4420_ = v___x_4309_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v___x_4413_);
lean_ctor_set(v_reuseFailAlloc_4421_, 1, v_k_4408_);
lean_ctor_set(v_reuseFailAlloc_4421_, 2, v_v_4409_);
lean_ctor_set(v_reuseFailAlloc_4421_, 3, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4421_, 4, v___x_4418_);
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
if (lean_obj_tag(v_r_4306_) == 0)
{
lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4447_; 
lean_inc(v_v_4304_);
lean_inc(v_k_4303_);
v_isSharedCheck_4447_ = !lean_is_exclusive(v_r_4118_);
if (v_isSharedCheck_4447_ == 0)
{
lean_object* v_unused_4448_; lean_object* v_unused_4449_; lean_object* v_unused_4450_; lean_object* v_unused_4451_; lean_object* v_unused_4452_; 
v_unused_4448_ = lean_ctor_get(v_r_4118_, 4);
lean_dec(v_unused_4448_);
v_unused_4449_ = lean_ctor_get(v_r_4118_, 3);
lean_dec(v_unused_4449_);
v_unused_4450_ = lean_ctor_get(v_r_4118_, 2);
lean_dec(v_unused_4450_);
v_unused_4451_ = lean_ctor_get(v_r_4118_, 1);
lean_dec(v_unused_4451_);
v_unused_4452_ = lean_ctor_get(v_r_4118_, 0);
lean_dec(v_unused_4452_);
v___x_4435_ = v_r_4118_;
v_isShared_4436_ = v_isSharedCheck_4447_;
goto v_resetjp_4434_;
}
else
{
lean_dec(v_r_4118_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4447_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v_k_4437_; lean_object* v_v_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4442_; 
v_k_4437_ = lean_ctor_get(v_d_4311_, 0);
lean_inc(v_k_4437_);
v_v_4438_ = lean_ctor_get(v_d_4311_, 1);
lean_inc(v_v_4438_);
lean_dec_ref(v_d_4311_);
v___x_4439_ = lean_unsigned_to_nat(3u);
v___x_4440_ = lean_unsigned_to_nat(1u);
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 4, v_l_4305_);
lean_ctor_set(v___x_4435_, 2, v_v_4438_);
lean_ctor_set(v___x_4435_, 1, v_k_4437_);
lean_ctor_set(v___x_4435_, 0, v___x_4440_);
v___x_4442_ = v___x_4435_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4440_);
lean_ctor_set(v_reuseFailAlloc_4446_, 1, v_k_4437_);
lean_ctor_set(v_reuseFailAlloc_4446_, 2, v_v_4438_);
lean_ctor_set(v_reuseFailAlloc_4446_, 3, v_l_4305_);
lean_ctor_set(v_reuseFailAlloc_4446_, 4, v_l_4305_);
v___x_4442_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
lean_object* v___x_4444_; 
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 4, v_r_4306_);
lean_ctor_set(v___x_4309_, 3, v___x_4442_);
lean_ctor_set(v___x_4309_, 2, v_v_4304_);
lean_ctor_set(v___x_4309_, 1, v_k_4303_);
lean_ctor_set(v___x_4309_, 0, v___x_4439_);
v___x_4444_ = v___x_4309_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v___x_4439_);
lean_ctor_set(v_reuseFailAlloc_4445_, 1, v_k_4303_);
lean_ctor_set(v_reuseFailAlloc_4445_, 2, v_v_4304_);
lean_ctor_set(v_reuseFailAlloc_4445_, 3, v___x_4442_);
lean_ctor_set(v_reuseFailAlloc_4445_, 4, v_r_4306_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
else
{
lean_object* v_k_4453_; lean_object* v_v_4454_; lean_object* v___x_4455_; lean_object* v___x_4457_; 
v_k_4453_ = lean_ctor_get(v_d_4311_, 0);
lean_inc(v_k_4453_);
v_v_4454_ = lean_ctor_get(v_d_4311_, 1);
lean_inc(v_v_4454_);
lean_dec_ref(v_d_4311_);
v___x_4455_ = lean_unsigned_to_nat(2u);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 4, v_r_4118_);
lean_ctor_set(v___x_4309_, 3, v_r_4306_);
lean_ctor_set(v___x_4309_, 2, v_v_4454_);
lean_ctor_set(v___x_4309_, 1, v_k_4453_);
lean_ctor_set(v___x_4309_, 0, v___x_4455_);
v___x_4457_ = v___x_4309_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4455_);
lean_ctor_set(v_reuseFailAlloc_4458_, 1, v_k_4453_);
lean_ctor_set(v_reuseFailAlloc_4458_, 2, v_v_4454_);
lean_ctor_set(v_reuseFailAlloc_4458_, 3, v_r_4306_);
lean_ctor_set(v_reuseFailAlloc_4458_, 4, v_r_4118_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
}
}
else
{
lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4627_; 
lean_inc(v_r_4306_);
lean_inc(v_v_4304_);
lean_inc(v_k_4303_);
v_isSharedCheck_4627_ = !lean_is_exclusive(v_r_4118_);
if (v_isSharedCheck_4627_ == 0)
{
lean_object* v_unused_4628_; lean_object* v_unused_4629_; lean_object* v_unused_4630_; lean_object* v_unused_4631_; lean_object* v_unused_4632_; 
v_unused_4628_ = lean_ctor_get(v_r_4118_, 4);
lean_dec(v_unused_4628_);
v_unused_4629_ = lean_ctor_get(v_r_4118_, 3);
lean_dec(v_unused_4629_);
v_unused_4630_ = lean_ctor_get(v_r_4118_, 2);
lean_dec(v_unused_4630_);
v_unused_4631_ = lean_ctor_get(v_r_4118_, 1);
lean_dec(v_unused_4631_);
v_unused_4632_ = lean_ctor_get(v_r_4118_, 0);
lean_dec(v_unused_4632_);
v___x_4466_ = v_r_4118_;
v_isShared_4467_ = v_isSharedCheck_4627_;
goto v_resetjp_4465_;
}
else
{
lean_dec(v_r_4118_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4627_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v_d_4468_; lean_object* v_tree_4469_; 
v_d_4468_ = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(v_k_4303_, v_v_4304_, v_l_4305_, v_r_4306_);
v_tree_4469_ = lean_ctor_get(v_d_4468_, 2);
lean_inc(v_tree_4469_);
if (lean_obj_tag(v_tree_4469_) == 0)
{
lean_object* v_k_4470_; lean_object* v_v_4471_; lean_object* v_size_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; uint8_t v___x_4475_; 
v_k_4470_ = lean_ctor_get(v_d_4468_, 0);
lean_inc(v_k_4470_);
v_v_4471_ = lean_ctor_get(v_d_4468_, 1);
lean_inc(v_v_4471_);
lean_dec_ref(v_d_4468_);
v_size_4472_ = lean_ctor_get(v_tree_4469_, 0);
v___x_4473_ = lean_unsigned_to_nat(3u);
v___x_4474_ = lean_nat_mul(v___x_4473_, v_size_4472_);
v___x_4475_ = lean_nat_dec_lt(v___x_4474_, v_size_4297_);
lean_dec(v___x_4474_);
if (v___x_4475_ == 0)
{
lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4480_; 
lean_dec(v_r_4301_);
v___x_4476_ = lean_unsigned_to_nat(1u);
v___x_4477_ = lean_nat_add(v___x_4476_, v_size_4297_);
v___x_4478_ = lean_nat_add(v___x_4477_, v_size_4472_);
lean_dec(v___x_4477_);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 4, v_tree_4469_);
lean_ctor_set(v___x_4466_, 3, v_l_4117_);
lean_ctor_set(v___x_4466_, 2, v_v_4471_);
lean_ctor_set(v___x_4466_, 1, v_k_4470_);
lean_ctor_set(v___x_4466_, 0, v___x_4478_);
v___x_4480_ = v___x_4466_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4478_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v_k_4470_);
lean_ctor_set(v_reuseFailAlloc_4481_, 2, v_v_4471_);
lean_ctor_set(v_reuseFailAlloc_4481_, 3, v_l_4117_);
lean_ctor_set(v_reuseFailAlloc_4481_, 4, v_tree_4469_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
else
{
lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4553_; 
lean_inc(v_l_4300_);
lean_inc(v_v_4299_);
lean_inc(v_k_4298_);
lean_inc(v_size_4297_);
v_isSharedCheck_4553_ = !lean_is_exclusive(v_l_4117_);
if (v_isSharedCheck_4553_ == 0)
{
lean_object* v_unused_4554_; lean_object* v_unused_4555_; lean_object* v_unused_4556_; lean_object* v_unused_4557_; lean_object* v_unused_4558_; 
v_unused_4554_ = lean_ctor_get(v_l_4117_, 4);
lean_dec(v_unused_4554_);
v_unused_4555_ = lean_ctor_get(v_l_4117_, 3);
lean_dec(v_unused_4555_);
v_unused_4556_ = lean_ctor_get(v_l_4117_, 2);
lean_dec(v_unused_4556_);
v_unused_4557_ = lean_ctor_get(v_l_4117_, 1);
lean_dec(v_unused_4557_);
v_unused_4558_ = lean_ctor_get(v_l_4117_, 0);
lean_dec(v_unused_4558_);
v___x_4483_ = v_l_4117_;
v_isShared_4484_ = v_isSharedCheck_4553_;
goto v_resetjp_4482_;
}
else
{
lean_dec(v_l_4117_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4553_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
if (lean_obj_tag(v_l_4300_) == 0)
{
if (lean_obj_tag(v_r_4301_) == 0)
{
lean_object* v_size_4485_; lean_object* v_size_4486_; lean_object* v_k_4487_; lean_object* v_v_4488_; lean_object* v_l_4489_; lean_object* v_r_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; uint8_t v___x_4493_; 
v_size_4485_ = lean_ctor_get(v_l_4300_, 0);
v_size_4486_ = lean_ctor_get(v_r_4301_, 0);
v_k_4487_ = lean_ctor_get(v_r_4301_, 1);
v_v_4488_ = lean_ctor_get(v_r_4301_, 2);
v_l_4489_ = lean_ctor_get(v_r_4301_, 3);
v_r_4490_ = lean_ctor_get(v_r_4301_, 4);
v___x_4491_ = lean_unsigned_to_nat(2u);
v___x_4492_ = lean_nat_mul(v___x_4491_, v_size_4485_);
v___x_4493_ = lean_nat_dec_lt(v_size_4486_, v___x_4492_);
lean_dec(v___x_4492_);
if (v___x_4493_ == 0)
{
lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4532_; 
lean_inc(v_r_4490_);
lean_inc(v_l_4489_);
lean_inc(v_v_4488_);
lean_inc(v_k_4487_);
lean_del_object(v___x_4483_);
v_isSharedCheck_4532_ = !lean_is_exclusive(v_r_4301_);
if (v_isSharedCheck_4532_ == 0)
{
lean_object* v_unused_4533_; lean_object* v_unused_4534_; lean_object* v_unused_4535_; lean_object* v_unused_4536_; lean_object* v_unused_4537_; 
v_unused_4533_ = lean_ctor_get(v_r_4301_, 4);
lean_dec(v_unused_4533_);
v_unused_4534_ = lean_ctor_get(v_r_4301_, 3);
lean_dec(v_unused_4534_);
v_unused_4535_ = lean_ctor_get(v_r_4301_, 2);
lean_dec(v_unused_4535_);
v_unused_4536_ = lean_ctor_get(v_r_4301_, 1);
lean_dec(v_unused_4536_);
v_unused_4537_ = lean_ctor_get(v_r_4301_, 0);
lean_dec(v_unused_4537_);
v___x_4495_ = v_r_4301_;
v_isShared_4496_ = v_isSharedCheck_4532_;
goto v_resetjp_4494_;
}
else
{
lean_dec(v_r_4301_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4532_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___x_4520_; lean_object* v___y_4522_; 
v___x_4497_ = lean_unsigned_to_nat(1u);
v___x_4498_ = lean_nat_add(v___x_4497_, v_size_4297_);
lean_dec(v_size_4297_);
v___x_4499_ = lean_nat_add(v___x_4498_, v_size_4472_);
lean_dec(v___x_4498_);
v___x_4520_ = lean_nat_add(v___x_4497_, v_size_4485_);
if (lean_obj_tag(v_l_4489_) == 0)
{
lean_object* v_size_4530_; 
v_size_4530_ = lean_ctor_get(v_l_4489_, 0);
lean_inc(v_size_4530_);
v___y_4522_ = v_size_4530_;
goto v___jp_4521_;
}
else
{
lean_object* v___x_4531_; 
v___x_4531_ = lean_unsigned_to_nat(0u);
v___y_4522_ = v___x_4531_;
goto v___jp_4521_;
}
v___jp_4500_:
{
lean_object* v___x_4504_; lean_object* v___x_4506_; 
v___x_4504_ = lean_nat_add(v___y_4501_, v___y_4503_);
lean_dec(v___y_4503_);
lean_dec(v___y_4501_);
lean_inc_ref(v_tree_4469_);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 4, v_tree_4469_);
lean_ctor_set(v___x_4495_, 3, v_r_4490_);
lean_ctor_set(v___x_4495_, 2, v_v_4471_);
lean_ctor_set(v___x_4495_, 1, v_k_4470_);
lean_ctor_set(v___x_4495_, 0, v___x_4504_);
v___x_4506_ = v___x_4495_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v___x_4504_);
lean_ctor_set(v_reuseFailAlloc_4519_, 1, v_k_4470_);
lean_ctor_set(v_reuseFailAlloc_4519_, 2, v_v_4471_);
lean_ctor_set(v_reuseFailAlloc_4519_, 3, v_r_4490_);
lean_ctor_set(v_reuseFailAlloc_4519_, 4, v_tree_4469_);
v___x_4506_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
v_isSharedCheck_4513_ = !lean_is_exclusive(v_tree_4469_);
if (v_isSharedCheck_4513_ == 0)
{
lean_object* v_unused_4514_; lean_object* v_unused_4515_; lean_object* v_unused_4516_; lean_object* v_unused_4517_; lean_object* v_unused_4518_; 
v_unused_4514_ = lean_ctor_get(v_tree_4469_, 4);
lean_dec(v_unused_4514_);
v_unused_4515_ = lean_ctor_get(v_tree_4469_, 3);
lean_dec(v_unused_4515_);
v_unused_4516_ = lean_ctor_get(v_tree_4469_, 2);
lean_dec(v_unused_4516_);
v_unused_4517_ = lean_ctor_get(v_tree_4469_, 1);
lean_dec(v_unused_4517_);
v_unused_4518_ = lean_ctor_get(v_tree_4469_, 0);
lean_dec(v_unused_4518_);
v___x_4508_ = v_tree_4469_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_dec(v_tree_4469_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 4, v___x_4506_);
lean_ctor_set(v___x_4508_, 3, v___y_4502_);
lean_ctor_set(v___x_4508_, 2, v_v_4488_);
lean_ctor_set(v___x_4508_, 1, v_k_4487_);
lean_ctor_set(v___x_4508_, 0, v___x_4499_);
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4499_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_k_4487_);
lean_ctor_set(v_reuseFailAlloc_4512_, 2, v_v_4488_);
lean_ctor_set(v_reuseFailAlloc_4512_, 3, v___y_4502_);
lean_ctor_set(v_reuseFailAlloc_4512_, 4, v___x_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
v___jp_4521_:
{
lean_object* v___x_4523_; lean_object* v___x_4525_; 
v___x_4523_ = lean_nat_add(v___x_4520_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec(v___x_4520_);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 4, v_l_4489_);
lean_ctor_set(v___x_4466_, 3, v_l_4300_);
lean_ctor_set(v___x_4466_, 2, v_v_4299_);
lean_ctor_set(v___x_4466_, 1, v_k_4298_);
lean_ctor_set(v___x_4466_, 0, v___x_4523_);
v___x_4525_ = v___x_4466_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4523_);
lean_ctor_set(v_reuseFailAlloc_4529_, 1, v_k_4298_);
lean_ctor_set(v_reuseFailAlloc_4529_, 2, v_v_4299_);
lean_ctor_set(v_reuseFailAlloc_4529_, 3, v_l_4300_);
lean_ctor_set(v_reuseFailAlloc_4529_, 4, v_l_4489_);
v___x_4525_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
lean_object* v___x_4526_; 
v___x_4526_ = lean_nat_add(v___x_4497_, v_size_4472_);
if (lean_obj_tag(v_r_4490_) == 0)
{
lean_object* v_size_4527_; 
v_size_4527_ = lean_ctor_get(v_r_4490_, 0);
lean_inc(v_size_4527_);
v___y_4501_ = v___x_4526_;
v___y_4502_ = v___x_4525_;
v___y_4503_ = v_size_4527_;
goto v___jp_4500_;
}
else
{
lean_object* v___x_4528_; 
v___x_4528_ = lean_unsigned_to_nat(0u);
v___y_4501_ = v___x_4526_;
v___y_4502_ = v___x_4525_;
v___y_4503_ = v___x_4528_;
goto v___jp_4500_;
}
}
}
}
}
else
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4544_; 
v___x_4538_ = lean_unsigned_to_nat(1u);
v___x_4539_ = lean_nat_add(v___x_4538_, v_size_4297_);
lean_dec(v_size_4297_);
v___x_4540_ = lean_nat_add(v___x_4539_, v_size_4472_);
lean_dec(v___x_4539_);
v___x_4541_ = lean_nat_add(v___x_4538_, v_size_4472_);
v___x_4542_ = lean_nat_add(v___x_4541_, v_size_4486_);
lean_dec(v___x_4541_);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 4, v_tree_4469_);
lean_ctor_set(v___x_4466_, 3, v_r_4301_);
lean_ctor_set(v___x_4466_, 2, v_v_4471_);
lean_ctor_set(v___x_4466_, 1, v_k_4470_);
lean_ctor_set(v___x_4466_, 0, v___x_4542_);
v___x_4544_ = v___x_4466_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4542_);
lean_ctor_set(v_reuseFailAlloc_4548_, 1, v_k_4470_);
lean_ctor_set(v_reuseFailAlloc_4548_, 2, v_v_4471_);
lean_ctor_set(v_reuseFailAlloc_4548_, 3, v_r_4301_);
lean_ctor_set(v_reuseFailAlloc_4548_, 4, v_tree_4469_);
v___x_4544_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
lean_object* v___x_4546_; 
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 4, v___x_4544_);
lean_ctor_set(v___x_4483_, 0, v___x_4540_);
v___x_4546_ = v___x_4483_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v___x_4540_);
lean_ctor_set(v_reuseFailAlloc_4547_, 1, v_k_4298_);
lean_ctor_set(v_reuseFailAlloc_4547_, 2, v_v_4299_);
lean_ctor_set(v_reuseFailAlloc_4547_, 3, v_l_4300_);
lean_ctor_set(v_reuseFailAlloc_4547_, 4, v___x_4544_);
v___x_4546_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
return v___x_4546_;
}
}
}
}
else
{
lean_object* v___x_4549_; lean_object* v___x_4550_; 
lean_dec_ref(v_l_4300_);
lean_del_object(v___x_4483_);
lean_dec(v_v_4471_);
lean_dec(v_k_4470_);
lean_dec_ref(v_tree_4469_);
lean_del_object(v___x_4466_);
lean_dec(v_v_4299_);
lean_dec(v_k_4298_);
lean_dec(v_size_4297_);
v___x_4549_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3);
v___x_4550_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4549_);
return v___x_4550_;
}
}
else
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
lean_del_object(v___x_4483_);
lean_dec(v_v_4471_);
lean_dec(v_k_4470_);
lean_dec_ref(v_tree_4469_);
lean_del_object(v___x_4466_);
lean_dec(v_r_4301_);
lean_dec(v_v_4299_);
lean_dec(v_k_4298_);
lean_dec(v_size_4297_);
v___x_4551_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4);
v___x_4552_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4551_);
return v___x_4552_;
}
}
}
}
else
{
if (lean_obj_tag(v_l_4300_) == 0)
{
lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4584_; 
lean_inc_ref(v_l_4300_);
lean_inc(v_v_4299_);
lean_inc(v_k_4298_);
lean_inc(v_size_4297_);
v_isSharedCheck_4584_ = !lean_is_exclusive(v_l_4117_);
if (v_isSharedCheck_4584_ == 0)
{
lean_object* v_unused_4585_; lean_object* v_unused_4586_; lean_object* v_unused_4587_; lean_object* v_unused_4588_; lean_object* v_unused_4589_; 
v_unused_4585_ = lean_ctor_get(v_l_4117_, 4);
lean_dec(v_unused_4585_);
v_unused_4586_ = lean_ctor_get(v_l_4117_, 3);
lean_dec(v_unused_4586_);
v_unused_4587_ = lean_ctor_get(v_l_4117_, 2);
lean_dec(v_unused_4587_);
v_unused_4588_ = lean_ctor_get(v_l_4117_, 1);
lean_dec(v_unused_4588_);
v_unused_4589_ = lean_ctor_get(v_l_4117_, 0);
lean_dec(v_unused_4589_);
v___x_4560_ = v_l_4117_;
v_isShared_4561_ = v_isSharedCheck_4584_;
goto v_resetjp_4559_;
}
else
{
lean_dec(v_l_4117_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4584_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
if (lean_obj_tag(v_r_4301_) == 0)
{
lean_object* v_k_4562_; lean_object* v_v_4563_; lean_object* v_size_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4569_; 
v_k_4562_ = lean_ctor_get(v_d_4468_, 0);
lean_inc(v_k_4562_);
v_v_4563_ = lean_ctor_get(v_d_4468_, 1);
lean_inc(v_v_4563_);
lean_dec_ref(v_d_4468_);
v_size_4564_ = lean_ctor_get(v_r_4301_, 0);
v___x_4565_ = lean_unsigned_to_nat(1u);
v___x_4566_ = lean_nat_add(v___x_4565_, v_size_4297_);
lean_dec(v_size_4297_);
v___x_4567_ = lean_nat_add(v___x_4565_, v_size_4564_);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 4, v_tree_4469_);
lean_ctor_set(v___x_4466_, 3, v_r_4301_);
lean_ctor_set(v___x_4466_, 2, v_v_4563_);
lean_ctor_set(v___x_4466_, 1, v_k_4562_);
lean_ctor_set(v___x_4466_, 0, v___x_4567_);
v___x_4569_ = v___x_4466_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4567_);
lean_ctor_set(v_reuseFailAlloc_4573_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4573_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4573_, 3, v_r_4301_);
lean_ctor_set(v_reuseFailAlloc_4573_, 4, v_tree_4469_);
v___x_4569_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
lean_object* v___x_4571_; 
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 4, v___x_4569_);
lean_ctor_set(v___x_4560_, 0, v___x_4566_);
v___x_4571_ = v___x_4560_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4566_);
lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_k_4298_);
lean_ctor_set(v_reuseFailAlloc_4572_, 2, v_v_4299_);
lean_ctor_set(v_reuseFailAlloc_4572_, 3, v_l_4300_);
lean_ctor_set(v_reuseFailAlloc_4572_, 4, v___x_4569_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
else
{
lean_object* v_k_4574_; lean_object* v_v_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4579_; 
lean_dec(v_size_4297_);
v_k_4574_ = lean_ctor_get(v_d_4468_, 0);
lean_inc(v_k_4574_);
v_v_4575_ = lean_ctor_get(v_d_4468_, 1);
lean_inc(v_v_4575_);
lean_dec_ref(v_d_4468_);
v___x_4576_ = lean_unsigned_to_nat(3u);
v___x_4577_ = lean_unsigned_to_nat(1u);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 4, v_r_4301_);
lean_ctor_set(v___x_4466_, 3, v_r_4301_);
lean_ctor_set(v___x_4466_, 2, v_v_4575_);
lean_ctor_set(v___x_4466_, 1, v_k_4574_);
lean_ctor_set(v___x_4466_, 0, v___x_4577_);
v___x_4579_ = v___x_4466_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4577_);
lean_ctor_set(v_reuseFailAlloc_4583_, 1, v_k_4574_);
lean_ctor_set(v_reuseFailAlloc_4583_, 2, v_v_4575_);
lean_ctor_set(v_reuseFailAlloc_4583_, 3, v_r_4301_);
lean_ctor_set(v_reuseFailAlloc_4583_, 4, v_r_4301_);
v___x_4579_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
lean_object* v___x_4581_; 
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 4, v___x_4579_);
lean_ctor_set(v___x_4560_, 0, v___x_4576_);
v___x_4581_ = v___x_4560_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4576_);
lean_ctor_set(v_reuseFailAlloc_4582_, 1, v_k_4298_);
lean_ctor_set(v_reuseFailAlloc_4582_, 2, v_v_4299_);
lean_ctor_set(v_reuseFailAlloc_4582_, 3, v_l_4300_);
lean_ctor_set(v_reuseFailAlloc_4582_, 4, v___x_4579_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4301_) == 0)
{
lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4615_; 
lean_inc(v_l_4300_);
lean_inc(v_v_4299_);
lean_inc(v_k_4298_);
v_isSharedCheck_4615_ = !lean_is_exclusive(v_l_4117_);
if (v_isSharedCheck_4615_ == 0)
{
lean_object* v_unused_4616_; lean_object* v_unused_4617_; lean_object* v_unused_4618_; lean_object* v_unused_4619_; lean_object* v_unused_4620_; 
v_unused_4616_ = lean_ctor_get(v_l_4117_, 4);
lean_dec(v_unused_4616_);
v_unused_4617_ = lean_ctor_get(v_l_4117_, 3);
lean_dec(v_unused_4617_);
v_unused_4618_ = lean_ctor_get(v_l_4117_, 2);
lean_dec(v_unused_4618_);
v_unused_4619_ = lean_ctor_get(v_l_4117_, 1);
lean_dec(v_unused_4619_);
v_unused_4620_ = lean_ctor_get(v_l_4117_, 0);
lean_dec(v_unused_4620_);
v___x_4591_ = v_l_4117_;
v_isShared_4592_ = v_isSharedCheck_4615_;
goto v_resetjp_4590_;
}
else
{
lean_dec(v_l_4117_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4615_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v_k_4593_; lean_object* v_v_4594_; lean_object* v_k_4595_; lean_object* v_v_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4611_; 
v_k_4593_ = lean_ctor_get(v_d_4468_, 0);
lean_inc(v_k_4593_);
v_v_4594_ = lean_ctor_get(v_d_4468_, 1);
lean_inc(v_v_4594_);
lean_dec_ref(v_d_4468_);
v_k_4595_ = lean_ctor_get(v_r_4301_, 1);
v_v_4596_ = lean_ctor_get(v_r_4301_, 2);
v_isSharedCheck_4611_ = !lean_is_exclusive(v_r_4301_);
if (v_isSharedCheck_4611_ == 0)
{
lean_object* v_unused_4612_; lean_object* v_unused_4613_; lean_object* v_unused_4614_; 
v_unused_4612_ = lean_ctor_get(v_r_4301_, 4);
lean_dec(v_unused_4612_);
v_unused_4613_ = lean_ctor_get(v_r_4301_, 3);
lean_dec(v_unused_4613_);
v_unused_4614_ = lean_ctor_get(v_r_4301_, 0);
lean_dec(v_unused_4614_);
v___x_4598_ = v_r_4301_;
v_isShared_4599_ = v_isSharedCheck_4611_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_v_4596_);
lean_inc(v_k_4595_);
lean_dec(v_r_4301_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4611_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4603_; 
v___x_4600_ = lean_unsigned_to_nat(3u);
v___x_4601_ = lean_unsigned_to_nat(1u);
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 4, v_l_4300_);
lean_ctor_set(v___x_4598_, 3, v_l_4300_);
lean_ctor_set(v___x_4598_, 2, v_v_4299_);
lean_ctor_set(v___x_4598_, 1, v_k_4298_);
lean_ctor_set(v___x_4598_, 0, v___x_4601_);
v___x_4603_ = v___x_4598_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4601_);
lean_ctor_set(v_reuseFailAlloc_4610_, 1, v_k_4298_);
lean_ctor_set(v_reuseFailAlloc_4610_, 2, v_v_4299_);
lean_ctor_set(v_reuseFailAlloc_4610_, 3, v_l_4300_);
lean_ctor_set(v_reuseFailAlloc_4610_, 4, v_l_4300_);
v___x_4603_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
lean_object* v___x_4605_; 
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 4, v_l_4300_);
lean_ctor_set(v___x_4466_, 3, v_l_4300_);
lean_ctor_set(v___x_4466_, 2, v_v_4594_);
lean_ctor_set(v___x_4466_, 1, v_k_4593_);
lean_ctor_set(v___x_4466_, 0, v___x_4601_);
v___x_4605_ = v___x_4466_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4601_);
lean_ctor_set(v_reuseFailAlloc_4609_, 1, v_k_4593_);
lean_ctor_set(v_reuseFailAlloc_4609_, 2, v_v_4594_);
lean_ctor_set(v_reuseFailAlloc_4609_, 3, v_l_4300_);
lean_ctor_set(v_reuseFailAlloc_4609_, 4, v_l_4300_);
v___x_4605_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
lean_object* v___x_4607_; 
if (v_isShared_4592_ == 0)
{
lean_ctor_set(v___x_4591_, 4, v___x_4605_);
lean_ctor_set(v___x_4591_, 3, v___x_4603_);
lean_ctor_set(v___x_4591_, 2, v_v_4596_);
lean_ctor_set(v___x_4591_, 1, v_k_4595_);
lean_ctor_set(v___x_4591_, 0, v___x_4600_);
v___x_4607_ = v___x_4591_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4600_);
lean_ctor_set(v_reuseFailAlloc_4608_, 1, v_k_4595_);
lean_ctor_set(v_reuseFailAlloc_4608_, 2, v_v_4596_);
lean_ctor_set(v_reuseFailAlloc_4608_, 3, v___x_4603_);
lean_ctor_set(v_reuseFailAlloc_4608_, 4, v___x_4605_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
}
}
}
else
{
lean_object* v_k_4621_; lean_object* v_v_4622_; lean_object* v___x_4623_; lean_object* v___x_4625_; 
v_k_4621_ = lean_ctor_get(v_d_4468_, 0);
lean_inc(v_k_4621_);
v_v_4622_ = lean_ctor_get(v_d_4468_, 1);
lean_inc(v_v_4622_);
lean_dec_ref(v_d_4468_);
v___x_4623_ = lean_unsigned_to_nat(2u);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 4, v_r_4301_);
lean_ctor_set(v___x_4466_, 3, v_l_4117_);
lean_ctor_set(v___x_4466_, 2, v_v_4622_);
lean_ctor_set(v___x_4466_, 1, v_k_4621_);
lean_ctor_set(v___x_4466_, 0, v___x_4623_);
v___x_4625_ = v___x_4466_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
lean_ctor_set(v_reuseFailAlloc_4626_, 1, v_k_4621_);
lean_ctor_set(v_reuseFailAlloc_4626_, 2, v_v_4622_);
lean_ctor_set(v_reuseFailAlloc_4626_, 3, v_l_4117_);
lean_ctor_set(v_reuseFailAlloc_4626_, 4, v_r_4301_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
}
}
}
}
else
{
return v_l_4117_;
}
}
else
{
return v_r_4118_;
}
}
default: 
{
lean_object* v___x_4633_; 
v___x_4633_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4112_, v_k_4113_, v_r_4118_);
if (lean_obj_tag(v___x_4633_) == 0)
{
if (lean_obj_tag(v_l_4117_) == 0)
{
lean_object* v_size_4634_; lean_object* v_size_4635_; lean_object* v_k_4636_; lean_object* v_v_4637_; lean_object* v_l_4638_; lean_object* v_r_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; uint8_t v___x_4642_; 
v_size_4634_ = lean_ctor_get(v___x_4633_, 0);
lean_inc(v_size_4634_);
v_size_4635_ = lean_ctor_get(v_l_4117_, 0);
v_k_4636_ = lean_ctor_get(v_l_4117_, 1);
v_v_4637_ = lean_ctor_get(v_l_4117_, 2);
v_l_4638_ = lean_ctor_get(v_l_4117_, 3);
v_r_4639_ = lean_ctor_get(v_l_4117_, 4);
lean_inc(v_r_4639_);
v___x_4640_ = lean_unsigned_to_nat(3u);
v___x_4641_ = lean_nat_mul(v___x_4640_, v_size_4634_);
v___x_4642_ = lean_nat_dec_lt(v___x_4641_, v_size_4635_);
lean_dec(v___x_4641_);
if (v___x_4642_ == 0)
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4647_; 
lean_dec(v_r_4639_);
v___x_4643_ = lean_unsigned_to_nat(1u);
v___x_4644_ = lean_nat_add(v___x_4643_, v_size_4635_);
v___x_4645_ = lean_nat_add(v___x_4644_, v_size_4634_);
lean_dec(v_size_4634_);
lean_dec(v___x_4644_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v___x_4633_);
lean_ctor_set(v___x_4120_, 0, v___x_4645_);
v___x_4647_ = v___x_4120_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4645_);
lean_ctor_set(v_reuseFailAlloc_4648_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4648_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4648_, 3, v_l_4117_);
lean_ctor_set(v_reuseFailAlloc_4648_, 4, v___x_4633_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
else
{
lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4720_; 
lean_inc(v_l_4638_);
lean_inc(v_v_4637_);
lean_inc(v_k_4636_);
lean_inc(v_size_4635_);
v_isSharedCheck_4720_ = !lean_is_exclusive(v_l_4117_);
if (v_isSharedCheck_4720_ == 0)
{
lean_object* v_unused_4721_; lean_object* v_unused_4722_; lean_object* v_unused_4723_; lean_object* v_unused_4724_; lean_object* v_unused_4725_; 
v_unused_4721_ = lean_ctor_get(v_l_4117_, 4);
lean_dec(v_unused_4721_);
v_unused_4722_ = lean_ctor_get(v_l_4117_, 3);
lean_dec(v_unused_4722_);
v_unused_4723_ = lean_ctor_get(v_l_4117_, 2);
lean_dec(v_unused_4723_);
v_unused_4724_ = lean_ctor_get(v_l_4117_, 1);
lean_dec(v_unused_4724_);
v_unused_4725_ = lean_ctor_get(v_l_4117_, 0);
lean_dec(v_unused_4725_);
v___x_4650_ = v_l_4117_;
v_isShared_4651_ = v_isSharedCheck_4720_;
goto v_resetjp_4649_;
}
else
{
lean_dec(v_l_4117_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4720_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
if (lean_obj_tag(v_l_4638_) == 0)
{
if (lean_obj_tag(v_r_4639_) == 0)
{
lean_object* v_size_4652_; lean_object* v_size_4653_; lean_object* v_k_4654_; lean_object* v_v_4655_; lean_object* v_l_4656_; lean_object* v_r_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; uint8_t v___x_4660_; 
v_size_4652_ = lean_ctor_get(v_l_4638_, 0);
v_size_4653_ = lean_ctor_get(v_r_4639_, 0);
v_k_4654_ = lean_ctor_get(v_r_4639_, 1);
v_v_4655_ = lean_ctor_get(v_r_4639_, 2);
v_l_4656_ = lean_ctor_get(v_r_4639_, 3);
v_r_4657_ = lean_ctor_get(v_r_4639_, 4);
v___x_4658_ = lean_unsigned_to_nat(2u);
v___x_4659_ = lean_nat_mul(v___x_4658_, v_size_4652_);
v___x_4660_ = lean_nat_dec_lt(v_size_4653_, v___x_4659_);
lean_dec(v___x_4659_);
if (v___x_4660_ == 0)
{
lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4690_; 
lean_inc(v_r_4657_);
lean_inc(v_l_4656_);
lean_inc(v_v_4655_);
lean_inc(v_k_4654_);
v_isSharedCheck_4690_ = !lean_is_exclusive(v_r_4639_);
if (v_isSharedCheck_4690_ == 0)
{
lean_object* v_unused_4691_; lean_object* v_unused_4692_; lean_object* v_unused_4693_; lean_object* v_unused_4694_; lean_object* v_unused_4695_; 
v_unused_4691_ = lean_ctor_get(v_r_4639_, 4);
lean_dec(v_unused_4691_);
v_unused_4692_ = lean_ctor_get(v_r_4639_, 3);
lean_dec(v_unused_4692_);
v_unused_4693_ = lean_ctor_get(v_r_4639_, 2);
lean_dec(v_unused_4693_);
v_unused_4694_ = lean_ctor_get(v_r_4639_, 1);
lean_dec(v_unused_4694_);
v_unused_4695_ = lean_ctor_get(v_r_4639_, 0);
lean_dec(v_unused_4695_);
v___x_4662_ = v_r_4639_;
v_isShared_4663_ = v_isSharedCheck_4690_;
goto v_resetjp_4661_;
}
else
{
lean_dec(v_r_4639_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4690_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; lean_object* v___x_4678_; lean_object* v___y_4680_; 
v___x_4664_ = lean_unsigned_to_nat(1u);
v___x_4665_ = lean_nat_add(v___x_4664_, v_size_4635_);
lean_dec(v_size_4635_);
v___x_4666_ = lean_nat_add(v___x_4665_, v_size_4634_);
lean_dec(v___x_4665_);
v___x_4678_ = lean_nat_add(v___x_4664_, v_size_4652_);
if (lean_obj_tag(v_l_4656_) == 0)
{
lean_object* v_size_4688_; 
v_size_4688_ = lean_ctor_get(v_l_4656_, 0);
lean_inc(v_size_4688_);
v___y_4680_ = v_size_4688_;
goto v___jp_4679_;
}
else
{
lean_object* v___x_4689_; 
v___x_4689_ = lean_unsigned_to_nat(0u);
v___y_4680_ = v___x_4689_;
goto v___jp_4679_;
}
v___jp_4667_:
{
lean_object* v___x_4671_; lean_object* v___x_4673_; 
v___x_4671_ = lean_nat_add(v___y_4669_, v___y_4670_);
lean_dec(v___y_4670_);
lean_dec(v___y_4669_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 4, v___x_4633_);
lean_ctor_set(v___x_4662_, 3, v_r_4657_);
lean_ctor_set(v___x_4662_, 2, v_v_4116_);
lean_ctor_set(v___x_4662_, 1, v_k_4115_);
lean_ctor_set(v___x_4662_, 0, v___x_4671_);
v___x_4673_ = v___x_4662_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v___x_4671_);
lean_ctor_set(v_reuseFailAlloc_4677_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4677_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4677_, 3, v_r_4657_);
lean_ctor_set(v_reuseFailAlloc_4677_, 4, v___x_4633_);
v___x_4673_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
lean_object* v___x_4675_; 
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 4, v___x_4673_);
lean_ctor_set(v___x_4650_, 3, v___y_4668_);
lean_ctor_set(v___x_4650_, 2, v_v_4655_);
lean_ctor_set(v___x_4650_, 1, v_k_4654_);
lean_ctor_set(v___x_4650_, 0, v___x_4666_);
v___x_4675_ = v___x_4650_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4666_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_k_4654_);
lean_ctor_set(v_reuseFailAlloc_4676_, 2, v_v_4655_);
lean_ctor_set(v_reuseFailAlloc_4676_, 3, v___y_4668_);
lean_ctor_set(v_reuseFailAlloc_4676_, 4, v___x_4673_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
v___jp_4679_:
{
lean_object* v___x_4681_; lean_object* v___x_4683_; 
v___x_4681_ = lean_nat_add(v___x_4678_, v___y_4680_);
lean_dec(v___y_4680_);
lean_dec(v___x_4678_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v_l_4656_);
lean_ctor_set(v___x_4120_, 3, v_l_4638_);
lean_ctor_set(v___x_4120_, 2, v_v_4637_);
lean_ctor_set(v___x_4120_, 1, v_k_4636_);
lean_ctor_set(v___x_4120_, 0, v___x_4681_);
v___x_4683_ = v___x_4120_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4681_);
lean_ctor_set(v_reuseFailAlloc_4687_, 1, v_k_4636_);
lean_ctor_set(v_reuseFailAlloc_4687_, 2, v_v_4637_);
lean_ctor_set(v_reuseFailAlloc_4687_, 3, v_l_4638_);
lean_ctor_set(v_reuseFailAlloc_4687_, 4, v_l_4656_);
v___x_4683_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
lean_object* v___x_4684_; 
v___x_4684_ = lean_nat_add(v___x_4664_, v_size_4634_);
lean_dec(v_size_4634_);
if (lean_obj_tag(v_r_4657_) == 0)
{
lean_object* v_size_4685_; 
v_size_4685_ = lean_ctor_get(v_r_4657_, 0);
lean_inc(v_size_4685_);
v___y_4668_ = v___x_4683_;
v___y_4669_ = v___x_4684_;
v___y_4670_ = v_size_4685_;
goto v___jp_4667_;
}
else
{
lean_object* v___x_4686_; 
v___x_4686_ = lean_unsigned_to_nat(0u);
v___y_4668_ = v___x_4683_;
v___y_4669_ = v___x_4684_;
v___y_4670_ = v___x_4686_;
goto v___jp_4667_;
}
}
}
}
}
else
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4702_; 
lean_del_object(v___x_4120_);
v___x_4696_ = lean_unsigned_to_nat(1u);
v___x_4697_ = lean_nat_add(v___x_4696_, v_size_4635_);
lean_dec(v_size_4635_);
v___x_4698_ = lean_nat_add(v___x_4697_, v_size_4634_);
lean_dec(v___x_4697_);
v___x_4699_ = lean_nat_add(v___x_4696_, v_size_4634_);
lean_dec(v_size_4634_);
v___x_4700_ = lean_nat_add(v___x_4699_, v_size_4653_);
lean_dec(v___x_4699_);
lean_inc_ref(v___x_4633_);
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 4, v___x_4633_);
lean_ctor_set(v___x_4650_, 3, v_r_4639_);
lean_ctor_set(v___x_4650_, 2, v_v_4116_);
lean_ctor_set(v___x_4650_, 1, v_k_4115_);
lean_ctor_set(v___x_4650_, 0, v___x_4700_);
v___x_4702_ = v___x_4650_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4700_);
lean_ctor_set(v_reuseFailAlloc_4715_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4715_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4715_, 3, v_r_4639_);
lean_ctor_set(v_reuseFailAlloc_4715_, 4, v___x_4633_);
v___x_4702_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4709_ == 0)
{
lean_object* v_unused_4710_; lean_object* v_unused_4711_; lean_object* v_unused_4712_; lean_object* v_unused_4713_; lean_object* v_unused_4714_; 
v_unused_4710_ = lean_ctor_get(v___x_4633_, 4);
lean_dec(v_unused_4710_);
v_unused_4711_ = lean_ctor_get(v___x_4633_, 3);
lean_dec(v_unused_4711_);
v_unused_4712_ = lean_ctor_get(v___x_4633_, 2);
lean_dec(v_unused_4712_);
v_unused_4713_ = lean_ctor_get(v___x_4633_, 1);
lean_dec(v_unused_4713_);
v_unused_4714_ = lean_ctor_get(v___x_4633_, 0);
lean_dec(v_unused_4714_);
v___x_4704_ = v___x_4633_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_dec(v___x_4633_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 4, v___x_4702_);
lean_ctor_set(v___x_4704_, 3, v_l_4638_);
lean_ctor_set(v___x_4704_, 2, v_v_4637_);
lean_ctor_set(v___x_4704_, 1, v_k_4636_);
lean_ctor_set(v___x_4704_, 0, v___x_4698_);
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4698_);
lean_ctor_set(v_reuseFailAlloc_4708_, 1, v_k_4636_);
lean_ctor_set(v_reuseFailAlloc_4708_, 2, v_v_4637_);
lean_ctor_set(v_reuseFailAlloc_4708_, 3, v_l_4638_);
lean_ctor_set(v_reuseFailAlloc_4708_, 4, v___x_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
}
else
{
lean_object* v___x_4716_; lean_object* v___x_4717_; 
lean_dec_ref(v_l_4638_);
lean_del_object(v___x_4650_);
lean_dec(v_v_4637_);
lean_dec(v_k_4636_);
lean_dec(v_size_4635_);
lean_dec(v_size_4634_);
lean_dec_ref(v___x_4633_);
lean_del_object(v___x_4120_);
lean_dec(v_v_4116_);
lean_dec(v_k_4115_);
v___x_4716_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3);
v___x_4717_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4716_);
return v___x_4717_;
}
}
else
{
lean_object* v___x_4718_; lean_object* v___x_4719_; 
lean_del_object(v___x_4650_);
lean_dec(v_r_4639_);
lean_dec(v_v_4637_);
lean_dec(v_k_4636_);
lean_dec(v_size_4635_);
lean_dec(v_size_4634_);
lean_dec_ref(v___x_4633_);
lean_del_object(v___x_4120_);
lean_dec(v_v_4116_);
lean_dec(v_k_4115_);
v___x_4718_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4);
v___x_4719_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4718_);
return v___x_4719_;
}
}
}
}
else
{
lean_object* v_size_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4730_; 
v_size_4726_ = lean_ctor_get(v___x_4633_, 0);
lean_inc(v_size_4726_);
v___x_4727_ = lean_unsigned_to_nat(1u);
v___x_4728_ = lean_nat_add(v___x_4727_, v_size_4726_);
lean_dec(v_size_4726_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v___x_4633_);
lean_ctor_set(v___x_4120_, 0, v___x_4728_);
v___x_4730_ = v___x_4120_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v___x_4728_);
lean_ctor_set(v_reuseFailAlloc_4731_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4731_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4731_, 3, v_l_4117_);
lean_ctor_set(v_reuseFailAlloc_4731_, 4, v___x_4633_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
else
{
if (lean_obj_tag(v_l_4117_) == 0)
{
lean_object* v_l_4732_; 
v_l_4732_ = lean_ctor_get(v_l_4117_, 3);
if (lean_obj_tag(v_l_4732_) == 0)
{
lean_object* v_r_4733_; 
lean_inc_ref(v_l_4732_);
v_r_4733_ = lean_ctor_get(v_l_4117_, 4);
lean_inc(v_r_4733_);
if (lean_obj_tag(v_r_4733_) == 0)
{
lean_object* v_size_4734_; lean_object* v_k_4735_; lean_object* v_v_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4750_; 
v_size_4734_ = lean_ctor_get(v_l_4117_, 0);
v_k_4735_ = lean_ctor_get(v_l_4117_, 1);
v_v_4736_ = lean_ctor_get(v_l_4117_, 2);
v_isSharedCheck_4750_ = !lean_is_exclusive(v_l_4117_);
if (v_isSharedCheck_4750_ == 0)
{
lean_object* v_unused_4751_; lean_object* v_unused_4752_; 
v_unused_4751_ = lean_ctor_get(v_l_4117_, 4);
lean_dec(v_unused_4751_);
v_unused_4752_ = lean_ctor_get(v_l_4117_, 3);
lean_dec(v_unused_4752_);
v___x_4738_ = v_l_4117_;
v_isShared_4739_ = v_isSharedCheck_4750_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_v_4736_);
lean_inc(v_k_4735_);
lean_inc(v_size_4734_);
lean_dec(v_l_4117_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4750_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v_size_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4745_; 
v_size_4740_ = lean_ctor_get(v_r_4733_, 0);
v___x_4741_ = lean_unsigned_to_nat(1u);
v___x_4742_ = lean_nat_add(v___x_4741_, v_size_4734_);
lean_dec(v_size_4734_);
v___x_4743_ = lean_nat_add(v___x_4741_, v_size_4740_);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 4, v___x_4633_);
lean_ctor_set(v___x_4738_, 3, v_r_4733_);
lean_ctor_set(v___x_4738_, 2, v_v_4116_);
lean_ctor_set(v___x_4738_, 1, v_k_4115_);
lean_ctor_set(v___x_4738_, 0, v___x_4743_);
v___x_4745_ = v___x_4738_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4743_);
lean_ctor_set(v_reuseFailAlloc_4749_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4749_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4749_, 3, v_r_4733_);
lean_ctor_set(v_reuseFailAlloc_4749_, 4, v___x_4633_);
v___x_4745_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
lean_object* v___x_4747_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v___x_4745_);
lean_ctor_set(v___x_4120_, 3, v_l_4732_);
lean_ctor_set(v___x_4120_, 2, v_v_4736_);
lean_ctor_set(v___x_4120_, 1, v_k_4735_);
lean_ctor_set(v___x_4120_, 0, v___x_4742_);
v___x_4747_ = v___x_4120_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v___x_4742_);
lean_ctor_set(v_reuseFailAlloc_4748_, 1, v_k_4735_);
lean_ctor_set(v_reuseFailAlloc_4748_, 2, v_v_4736_);
lean_ctor_set(v_reuseFailAlloc_4748_, 3, v_l_4732_);
lean_ctor_set(v_reuseFailAlloc_4748_, 4, v___x_4745_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
else
{
lean_object* v_k_4753_; lean_object* v_v_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4766_; 
v_k_4753_ = lean_ctor_get(v_l_4117_, 1);
v_v_4754_ = lean_ctor_get(v_l_4117_, 2);
v_isSharedCheck_4766_ = !lean_is_exclusive(v_l_4117_);
if (v_isSharedCheck_4766_ == 0)
{
lean_object* v_unused_4767_; lean_object* v_unused_4768_; lean_object* v_unused_4769_; 
v_unused_4767_ = lean_ctor_get(v_l_4117_, 4);
lean_dec(v_unused_4767_);
v_unused_4768_ = lean_ctor_get(v_l_4117_, 3);
lean_dec(v_unused_4768_);
v_unused_4769_ = lean_ctor_get(v_l_4117_, 0);
lean_dec(v_unused_4769_);
v___x_4756_ = v_l_4117_;
v_isShared_4757_ = v_isSharedCheck_4766_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_v_4754_);
lean_inc(v_k_4753_);
lean_dec(v_l_4117_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4766_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4761_; 
v___x_4758_ = lean_unsigned_to_nat(3u);
v___x_4759_ = lean_unsigned_to_nat(1u);
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 3, v_r_4733_);
lean_ctor_set(v___x_4756_, 2, v_v_4116_);
lean_ctor_set(v___x_4756_, 1, v_k_4115_);
lean_ctor_set(v___x_4756_, 0, v___x_4759_);
v___x_4761_ = v___x_4756_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4759_);
lean_ctor_set(v_reuseFailAlloc_4765_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4765_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4765_, 3, v_r_4733_);
lean_ctor_set(v_reuseFailAlloc_4765_, 4, v_r_4733_);
v___x_4761_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
lean_object* v___x_4763_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v___x_4761_);
lean_ctor_set(v___x_4120_, 3, v_l_4732_);
lean_ctor_set(v___x_4120_, 2, v_v_4754_);
lean_ctor_set(v___x_4120_, 1, v_k_4753_);
lean_ctor_set(v___x_4120_, 0, v___x_4758_);
v___x_4763_ = v___x_4120_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v___x_4758_);
lean_ctor_set(v_reuseFailAlloc_4764_, 1, v_k_4753_);
lean_ctor_set(v_reuseFailAlloc_4764_, 2, v_v_4754_);
lean_ctor_set(v_reuseFailAlloc_4764_, 3, v_l_4732_);
lean_ctor_set(v_reuseFailAlloc_4764_, 4, v___x_4761_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
}
else
{
lean_object* v_r_4770_; 
v_r_4770_ = lean_ctor_get(v_l_4117_, 4);
lean_inc(v_r_4770_);
if (lean_obj_tag(v_r_4770_) == 0)
{
lean_object* v_k_4771_; lean_object* v_v_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4796_; 
lean_inc(v_l_4732_);
v_k_4771_ = lean_ctor_get(v_l_4117_, 1);
v_v_4772_ = lean_ctor_get(v_l_4117_, 2);
v_isSharedCheck_4796_ = !lean_is_exclusive(v_l_4117_);
if (v_isSharedCheck_4796_ == 0)
{
lean_object* v_unused_4797_; lean_object* v_unused_4798_; lean_object* v_unused_4799_; 
v_unused_4797_ = lean_ctor_get(v_l_4117_, 4);
lean_dec(v_unused_4797_);
v_unused_4798_ = lean_ctor_get(v_l_4117_, 3);
lean_dec(v_unused_4798_);
v_unused_4799_ = lean_ctor_get(v_l_4117_, 0);
lean_dec(v_unused_4799_);
v___x_4774_ = v_l_4117_;
v_isShared_4775_ = v_isSharedCheck_4796_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_v_4772_);
lean_inc(v_k_4771_);
lean_dec(v_l_4117_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4796_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v_k_4776_; lean_object* v_v_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4792_; 
v_k_4776_ = lean_ctor_get(v_r_4770_, 1);
v_v_4777_ = lean_ctor_get(v_r_4770_, 2);
v_isSharedCheck_4792_ = !lean_is_exclusive(v_r_4770_);
if (v_isSharedCheck_4792_ == 0)
{
lean_object* v_unused_4793_; lean_object* v_unused_4794_; lean_object* v_unused_4795_; 
v_unused_4793_ = lean_ctor_get(v_r_4770_, 4);
lean_dec(v_unused_4793_);
v_unused_4794_ = lean_ctor_get(v_r_4770_, 3);
lean_dec(v_unused_4794_);
v_unused_4795_ = lean_ctor_get(v_r_4770_, 0);
lean_dec(v_unused_4795_);
v___x_4779_ = v_r_4770_;
v_isShared_4780_ = v_isSharedCheck_4792_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_v_4777_);
lean_inc(v_k_4776_);
lean_dec(v_r_4770_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4792_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4784_; 
v___x_4781_ = lean_unsigned_to_nat(3u);
v___x_4782_ = lean_unsigned_to_nat(1u);
if (v_isShared_4780_ == 0)
{
lean_ctor_set(v___x_4779_, 4, v_l_4732_);
lean_ctor_set(v___x_4779_, 3, v_l_4732_);
lean_ctor_set(v___x_4779_, 2, v_v_4772_);
lean_ctor_set(v___x_4779_, 1, v_k_4771_);
lean_ctor_set(v___x_4779_, 0, v___x_4782_);
v___x_4784_ = v___x_4779_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4782_);
lean_ctor_set(v_reuseFailAlloc_4791_, 1, v_k_4771_);
lean_ctor_set(v_reuseFailAlloc_4791_, 2, v_v_4772_);
lean_ctor_set(v_reuseFailAlloc_4791_, 3, v_l_4732_);
lean_ctor_set(v_reuseFailAlloc_4791_, 4, v_l_4732_);
v___x_4784_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
lean_object* v___x_4786_; 
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 4, v_l_4732_);
lean_ctor_set(v___x_4774_, 2, v_v_4116_);
lean_ctor_set(v___x_4774_, 1, v_k_4115_);
lean_ctor_set(v___x_4774_, 0, v___x_4782_);
v___x_4786_ = v___x_4774_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v___x_4782_);
lean_ctor_set(v_reuseFailAlloc_4790_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4790_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4790_, 3, v_l_4732_);
lean_ctor_set(v_reuseFailAlloc_4790_, 4, v_l_4732_);
v___x_4786_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
lean_object* v___x_4788_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v___x_4786_);
lean_ctor_set(v___x_4120_, 3, v___x_4784_);
lean_ctor_set(v___x_4120_, 2, v_v_4777_);
lean_ctor_set(v___x_4120_, 1, v_k_4776_);
lean_ctor_set(v___x_4120_, 0, v___x_4781_);
v___x_4788_ = v___x_4120_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4781_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_k_4776_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v_v_4777_);
lean_ctor_set(v_reuseFailAlloc_4789_, 3, v___x_4784_);
lean_ctor_set(v_reuseFailAlloc_4789_, 4, v___x_4786_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
}
}
else
{
lean_object* v___x_4800_; lean_object* v___x_4802_; 
v___x_4800_ = lean_unsigned_to_nat(2u);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v_r_4770_);
lean_ctor_set(v___x_4120_, 0, v___x_4800_);
v___x_4802_ = v___x_4120_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4800_);
lean_ctor_set(v_reuseFailAlloc_4803_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4803_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4803_, 3, v_l_4117_);
lean_ctor_set(v_reuseFailAlloc_4803_, 4, v_r_4770_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
}
else
{
lean_object* v___x_4804_; lean_object* v___x_4806_; 
v___x_4804_ = lean_unsigned_to_nat(1u);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v_l_4117_);
lean_ctor_set(v___x_4120_, 0, v___x_4804_);
v___x_4806_ = v___x_4120_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4804_);
lean_ctor_set(v_reuseFailAlloc_4807_, 1, v_k_4115_);
lean_ctor_set(v_reuseFailAlloc_4807_, 2, v_v_4116_);
lean_ctor_set(v_reuseFailAlloc_4807_, 3, v_l_4117_);
lean_ctor_set(v_reuseFailAlloc_4807_, 4, v_l_4117_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_4113_);
lean_dec_ref(v_cmp_4112_);
return v_t_4114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(lean_object* v_cmp_4810_, lean_object* v_init_4811_, lean_object* v_x_4812_){
_start:
{
if (lean_obj_tag(v_x_4812_) == 0)
{
lean_object* v_k_4813_; lean_object* v_l_4814_; lean_object* v_r_4815_; lean_object* v___x_4816_; lean_object* v_a_4817_; lean_object* v_r_4818_; 
v_k_4813_ = lean_ctor_get(v_x_4812_, 1);
lean_inc(v_k_4813_);
v_l_4814_ = lean_ctor_get(v_x_4812_, 3);
lean_inc(v_l_4814_);
v_r_4815_ = lean_ctor_get(v_x_4812_, 4);
lean_inc(v_r_4815_);
lean_dec_ref(v_x_4812_);
lean_inc_ref_n(v_cmp_4810_, 2);
v___x_4816_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4810_, v_init_4811_, v_l_4814_);
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
lean_inc(v_a_4817_);
lean_dec_ref(v___x_4816_);
v_r_4818_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4810_, v_k_4813_, v_a_4817_);
v_init_4811_ = v_r_4818_;
v_x_4812_ = v_r_4815_;
goto _start;
}
else
{
lean_object* v___x_4820_; 
lean_dec_ref(v_cmp_4810_);
v___x_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4820_, 0, v_init_4811_);
return v___x_4820_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(lean_object* v_cmp_4821_, lean_object* v_t_u2081_4822_, lean_object* v_t_u2082_4823_){
_start:
{
lean_object* v___y_4825_; lean_object* v___y_4826_; lean_object* v___y_4832_; 
if (lean_obj_tag(v_t_u2081_4822_) == 0)
{
lean_object* v_size_4835_; 
v_size_4835_ = lean_ctor_get(v_t_u2081_4822_, 0);
lean_inc(v_size_4835_);
v___y_4832_ = v_size_4835_;
goto v___jp_4831_;
}
else
{
lean_object* v___x_4836_; 
v___x_4836_ = lean_unsigned_to_nat(0u);
v___y_4832_ = v___x_4836_;
goto v___jp_4831_;
}
v___jp_4824_:
{
uint8_t v___x_4827_; 
v___x_4827_ = lean_nat_dec_le(v___y_4825_, v___y_4826_);
lean_dec(v___y_4826_);
lean_dec(v___y_4825_);
if (v___x_4827_ == 0)
{
lean_object* v___x_4828_; lean_object* v_a_4829_; 
v___x_4828_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4821_, v_t_u2081_4822_, v_t_u2082_4823_);
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4829_);
lean_dec_ref(v___x_4828_);
return v_a_4829_;
}
else
{
lean_object* v___x_4830_; 
v___x_4830_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4821_, v_t_u2082_4823_, v_t_u2081_4822_);
return v___x_4830_;
}
}
v___jp_4831_:
{
if (lean_obj_tag(v_t_u2082_4823_) == 0)
{
lean_object* v_size_4833_; 
v_size_4833_ = lean_ctor_get(v_t_u2082_4823_, 0);
lean_inc(v_size_4833_);
v___y_4825_ = v___y_4832_;
v___y_4826_ = v_size_4833_;
goto v___jp_4824_;
}
else
{
lean_object* v___x_4834_; 
v___x_4834_ = lean_unsigned_to_nat(0u);
v___y_4825_ = v___y_4832_;
v___y_4826_ = v___x_4834_;
goto v___jp_4824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff___redArg(lean_object* v_cmp_4837_, lean_object* v_t_u2081_4838_, lean_object* v_t_u2082_4839_){
_start:
{
lean_object* v___x_4840_; 
v___x_4840_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4837_, v_t_u2081_4838_, v_t_u2082_4839_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff(lean_object* v_00_u03b1_4841_, lean_object* v_00_u03b2_4842_, lean_object* v_cmp_4843_, lean_object* v_t_u2081_4844_, lean_object* v_t_u2082_4845_){
_start:
{
lean_object* v___x_4846_; 
v___x_4846_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4843_, v_t_u2081_4844_, v_t_u2082_4845_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0(lean_object* v_00_u03b1_4847_, lean_object* v_cmp_4848_, lean_object* v_00_u03b2_4849_, lean_object* v_t_u2081_4850_, lean_object* v_t_u2082_4851_){
_start:
{
lean_object* v___x_4852_; 
v___x_4852_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4848_, v_t_u2081_4850_, v_t_u2082_4851_);
return v___x_4852_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0(lean_object* v_00_u03b1_4853_, lean_object* v_cmp_4854_, lean_object* v_00_u03b2_4855_, lean_object* v_k_4856_, lean_object* v_t_4857_){
_start:
{
lean_object* v___x_4858_; 
v___x_4858_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4854_, v_k_4856_, v_t_4857_);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1(lean_object* v_00_u03b1_4859_, lean_object* v_00_u03b2_4860_, lean_object* v_cmp_4861_, lean_object* v_init_4862_, lean_object* v_x_4863_){
_start:
{
lean_object* v___x_4864_; 
v___x_4864_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4861_, v_init_4862_, v_x_4863_);
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2(lean_object* v_00_u03b1_4865_, lean_object* v_00_u03b2_4866_, lean_object* v_cmp_4867_, lean_object* v_t_u2082_4868_, lean_object* v_t_4869_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4867_, v_t_u2082_4868_, v_t_4869_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff___redArg(lean_object* v_cmp_4871_){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_4872_, 0, lean_box(0));
lean_closure_set(v___x_4872_, 1, lean_box(0));
lean_closure_set(v___x_4872_, 2, v_cmp_4871_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff(lean_object* v_00_u03b1_4873_, lean_object* v_00_u03b2_4874_, lean_object* v_cmp_4875_){
_start:
{
lean_object* v___x_4876_; 
v___x_4876_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_4876_, 0, lean_box(0));
lean_closure_set(v___x_4876_, 1, lean_box(0));
lean_closure_set(v___x_4876_, 2, v_cmp_4875_);
return v___x_4876_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_4877_, lean_object* v_a_4878_, lean_object* v_____s_4879_){
_start:
{
lean_object* v_r_4880_; lean_object* v___x_4881_; 
v_r_4880_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_4877_, v_a_4878_, v_____s_4879_);
v___x_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4881_, 0, v_r_4880_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg(lean_object* v_cmp_4882_, lean_object* v_inst_4883_, lean_object* v_t_4884_, lean_object* v_l_4885_){
_start:
{
lean_object* v___f_4886_; lean_object* v___x_4887_; 
v___f_4886_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4886_, 0, v_cmp_4882_);
v___x_4887_ = lean_apply_4(v_inst_4883_, lean_box(0), v_l_4885_, v_t_4884_, v___f_4886_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany(lean_object* v_00_u03b1_4888_, lean_object* v_00_u03b2_4889_, lean_object* v_cmp_4890_, lean_object* v_00_u03c1_4891_, lean_object* v_inst_4892_, lean_object* v_t_4893_, lean_object* v_l_4894_){
_start:
{
lean_object* v___f_4895_; lean_object* v___x_4896_; 
v___f_4895_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4895_, 0, v_cmp_4890_);
v___x_4896_ = lean_apply_4(v_inst_4892_, lean_box(0), v_l_4894_, v_t_4893_, v___f_4895_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0(lean_object* v_cmp_4897_, lean_object* v_x_4898_, lean_object* v_____s_4899_){
_start:
{
lean_object* v_fst_4900_; lean_object* v_snd_4901_; lean_object* v_r_4902_; lean_object* v___x_4903_; 
v_fst_4900_ = lean_ctor_get(v_x_4898_, 0);
lean_inc(v_fst_4900_);
v_snd_4901_ = lean_ctor_get(v_x_4898_, 1);
lean_inc(v_snd_4901_);
lean_dec_ref(v_x_4898_);
v_r_4902_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_4897_, v_fst_4900_, v_snd_4901_, v_____s_4899_);
v___x_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4903_, 0, v_r_4902_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg(lean_object* v_cmp_4904_, lean_object* v_inst_4905_, lean_object* v_t_4906_, lean_object* v_l_4907_){
_start:
{
lean_object* v___f_4908_; lean_object* v___x_4909_; 
v___f_4908_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4908_, 0, v_cmp_4904_);
v___x_4909_ = lean_apply_4(v_inst_4905_, lean_box(0), v_l_4907_, v_t_4906_, v___f_4908_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany(lean_object* v_00_u03b1_4910_, lean_object* v_cmp_4911_, lean_object* v_00_u03b2_4912_, lean_object* v_00_u03c1_4913_, lean_object* v_inst_4914_, lean_object* v_t_4915_, lean_object* v_l_4916_){
_start:
{
lean_object* v___f_4917_; lean_object* v___x_4918_; 
v___f_4917_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4917_, 0, v_cmp_4911_);
v___x_4918_ = lean_apply_4(v_inst_4914_, lean_box(0), v_l_4916_, v_t_4915_, v___f_4917_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_4919_, lean_object* v_a_4920_, lean_object* v_____s_4921_){
_start:
{
uint8_t v___x_4922_; 
lean_inc(v_____s_4921_);
lean_inc(v_a_4920_);
lean_inc_ref(v_cmp_4919_);
v___x_4922_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4919_, v_a_4920_, v_____s_4921_);
if (v___x_4922_ == 0)
{
lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4923_ = lean_box(0);
v___x_4924_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_4919_, v_a_4920_, v___x_4923_, v_____s_4921_);
v___x_4925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4924_);
return v___x_4925_;
}
else
{
lean_object* v___x_4926_; 
lean_dec(v_a_4920_);
lean_dec_ref(v_cmp_4919_);
v___x_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4926_, 0, v_____s_4921_);
return v___x_4926_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_4927_, lean_object* v_inst_4928_, lean_object* v_t_4929_, lean_object* v_l_4930_){
_start:
{
lean_object* v___f_4931_; lean_object* v___x_4932_; 
v___f_4931_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4931_, 0, v_cmp_4927_);
v___x_4932_ = lean_apply_4(v_inst_4928_, lean_box(0), v_l_4930_, v_t_4929_, v___f_4931_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_4933_, lean_object* v_cmp_4934_, lean_object* v_00_u03c1_4935_, lean_object* v_inst_4936_, lean_object* v_t_4937_, lean_object* v_l_4938_){
_start:
{
lean_object* v___f_4939_; lean_object* v___x_4940_; 
v___f_4939_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4939_, 0, v_cmp_4934_);
v___x_4940_ = lean_apply_4(v_inst_4936_, lean_box(0), v_l_4938_, v_t_4937_, v___f_4939_);
return v___x_4940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(lean_object* v___f_4944_, lean_object* v___x_4945_, lean_object* v_m_4946_, lean_object* v_prec_4947_){
_start:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4948_ = ((lean_object*)(l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__1));
v___x_4949_ = lean_box(0);
v___x_4950_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_4951_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_4950_, v___f_4944_, v___x_4949_, v_m_4946_);
v___x_4952_ = l_List_repr___redArg(v___x_4945_, v___x_4951_);
v___x_4953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4953_, 0, v___x_4948_);
lean_ctor_set(v___x_4953_, 1, v___x_4952_);
v___x_4954_ = l_Repr_addAppParen(v___x_4953_, v_prec_4947_);
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_4955_, lean_object* v___x_4956_, lean_object* v_m_4957_, lean_object* v_prec_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(v___f_4955_, v___x_4956_, v_m_4957_, v_prec_4958_);
lean_dec(v_prec_4958_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg(lean_object* v_inst_4960_, lean_object* v_inst_4961_){
_start:
{
lean_object* v___f_4962_; lean_object* v___x_4963_; lean_object* v___f_4964_; 
v___f_4962_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_4963_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_4963_, 0, lean_box(0));
lean_closure_set(v___x_4963_, 1, lean_box(0));
lean_closure_set(v___x_4963_, 2, v_inst_4960_);
lean_closure_set(v___x_4963_, 3, v_inst_4961_);
v___f_4964_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4964_, 0, v___f_4962_);
lean_closure_set(v___f_4964_, 1, v___x_4963_);
return v___f_4964_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr(lean_object* v_00_u03b1_4965_, lean_object* v_00_u03b2_4966_, lean_object* v_cmp_4967_, lean_object* v_inst_4968_, lean_object* v_inst_4969_){
_start:
{
lean_object* v___x_4970_; 
v___x_4970_ = l_Std_DTreeMap_Raw_instRepr___redArg(v_inst_4968_, v_inst_4969_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___boxed(lean_object* v_00_u03b1_4971_, lean_object* v_00_u03b2_4972_, lean_object* v_cmp_4973_, lean_object* v_inst_4974_, lean_object* v_inst_4975_){
_start:
{
lean_object* v_res_4976_; 
v_res_4976_ = l_Std_DTreeMap_Raw_instRepr(v_00_u03b1_4971_, v_00_u03b2_4972_, v_cmp_4973_, v_inst_4974_, v_inst_4975_);
lean_dec_ref(v_cmp_4973_);
return v_res_4976_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_DTreeMap_Raw___auto__1 = _init_l_Std_DTreeMap_Raw___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw___auto__1);
l_Std_DTreeMap_Raw_ofList___auto__1 = _init_l_Std_DTreeMap_Raw_ofList___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_ofList___auto__1);
l_Std_DTreeMap_Raw_ofArray___auto__1 = _init_l_Std_DTreeMap_Raw_ofArray___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_ofArray___auto__1);
l_Std_DTreeMap_Raw_Const_ofList___auto__1 = _init_l_Std_DTreeMap_Raw_Const_ofList___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_Const_ofList___auto__1);
l_Std_DTreeMap_Raw_Const_unitOfList___auto__1 = _init_l_Std_DTreeMap_Raw_Const_unitOfList___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_Const_unitOfList___auto__1);
l_Std_DTreeMap_Raw_Const_ofArray___auto__1 = _init_l_Std_DTreeMap_Raw_Const_ofArray___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_Const_ofArray___auto__1);
l_Std_DTreeMap_Raw_Const_unitOfArray___auto__1 = _init_l_Std_DTreeMap_Raw_Const_unitOfArray___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_Const_unitOfArray___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
