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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg___boxed(lean_object* v_l_2772_, lean_object* v_cmp_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Std_DTreeMap_Raw_ofList___redArg(v_l_2772_, v_cmp_2773_);
lean_dec(v_l_2772_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList(lean_object* v_00_u03b1_2775_, lean_object* v_00_u03b2_2776_, lean_object* v_l_2777_, lean_object* v_cmp_2778_){
_start:
{
lean_object* v___f_2779_; lean_object* v___x_2780_; lean_object* v_r_2781_; lean_object* v___x_2782_; 
v___f_2779_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2779_, 0, v_cmp_2778_);
v___x_2780_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2781_ = lean_box(1);
v___x_2782_ = l_List_forIn_x27_loop___redArg(v___x_2780_, v___f_2779_, v_l_2777_, v_r_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___boxed(lean_object* v_00_u03b1_2783_, lean_object* v_00_u03b2_2784_, lean_object* v_l_2785_, lean_object* v_cmp_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Std_DTreeMap_Raw_ofList(v_00_u03b1_2783_, v_00_u03b2_2784_, v_l_2785_, v_cmp_2786_);
lean_dec(v_l_2785_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg___lam__0(lean_object* v_l_2788_, lean_object* v_k_2789_, lean_object* v_v_2790_){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v_k_2789_);
lean_ctor_set(v___x_2791_, 1, v_v_2790_);
v___x_2792_ = lean_array_push(v_l_2788_, v___x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg(lean_object* v_t_2794_){
_start:
{
lean_object* v___f_2795_; lean_object* v___y_2797_; 
v___f_2795_ = ((lean_object*)(l_Std_DTreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2794_) == 0)
{
lean_object* v_size_2800_; 
v_size_2800_ = lean_ctor_get(v_t_2794_, 0);
lean_inc(v_size_2800_);
v___y_2797_ = v_size_2800_;
goto v___jp_2796_;
}
else
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_unsigned_to_nat(0u);
v___y_2797_ = v___x_2801_;
goto v___jp_2796_;
}
v___jp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = lean_mk_empty_array_with_capacity(v___y_2797_);
lean_dec(v___y_2797_);
v___x_2799_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2795_, v___x_2798_, v_t_2794_);
return v___x_2799_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray(lean_object* v_00_u03b1_2802_, lean_object* v_00_u03b2_2803_, lean_object* v_cmp_2804_, lean_object* v_t_2805_){
_start:
{
lean_object* v___f_2806_; lean_object* v___y_2808_; 
v___f_2806_ = ((lean_object*)(l_Std_DTreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2805_) == 0)
{
lean_object* v_size_2811_; 
v_size_2811_ = lean_ctor_get(v_t_2805_, 0);
lean_inc(v_size_2811_);
v___y_2808_ = v_size_2811_;
goto v___jp_2807_;
}
else
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_unsigned_to_nat(0u);
v___y_2808_ = v___x_2812_;
goto v___jp_2807_;
}
v___jp_2807_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_mk_empty_array_with_capacity(v___y_2808_);
lean_dec(v___y_2808_);
v___x_2810_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2806_, v___x_2809_, v_t_2805_);
return v___x_2810_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___boxed(lean_object* v_00_u03b1_2813_, lean_object* v_00_u03b2_2814_, lean_object* v_cmp_2815_, lean_object* v_t_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Std_DTreeMap_Raw_toArray(v_00_u03b1_2813_, v_00_u03b2_2814_, v_cmp_2815_, v_t_2816_);
lean_dec_ref(v_cmp_2815_);
return v_res_2817_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray___redArg(lean_object* v_a_2819_, lean_object* v_cmp_2820_){
_start:
{
lean_object* v___f_2821_; lean_object* v___x_2822_; lean_object* v_r_2823_; size_t v_sz_2824_; size_t v___x_2825_; lean_object* v___x_2826_; 
v___f_2821_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2821_, 0, v_cmp_2820_);
v___x_2822_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2823_ = lean_box(1);
v_sz_2824_ = lean_array_size(v_a_2819_);
v___x_2825_ = ((size_t)0ULL);
v___x_2826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2822_, v_a_2819_, v___f_2821_, v_sz_2824_, v___x_2825_, v_r_2823_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray(lean_object* v_00_u03b1_2827_, lean_object* v_00_u03b2_2828_, lean_object* v_a_2829_, lean_object* v_cmp_2830_){
_start:
{
lean_object* v___f_2831_; lean_object* v___x_2832_; lean_object* v_r_2833_; size_t v_sz_2834_; size_t v___x_2835_; lean_object* v___x_2836_; 
v___f_2831_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2831_, 0, v_cmp_2830_);
v___x_2832_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2833_ = lean_box(1);
v_sz_2834_ = lean_array_size(v_a_2829_);
v___x_2835_ = ((size_t)0ULL);
v___x_2836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2832_, v_a_2829_, v___f_2831_, v_sz_2834_, v___x_2835_, v_r_2833_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify___redArg(lean_object* v_cmp_2837_, lean_object* v_t_2838_, lean_object* v_a_2839_, lean_object* v_f_2840_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2837_, v_a_2839_, v_f_2840_, v_t_2838_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify(lean_object* v_00_u03b1_2842_, lean_object* v_00_u03b2_2843_, lean_object* v_cmp_2844_, lean_object* v_inst_2845_, lean_object* v_t_2846_, lean_object* v_a_2847_, lean_object* v_f_2848_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2844_, v_a_2847_, v_f_2848_, v_t_2846_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter___redArg(lean_object* v_cmp_2850_, lean_object* v_t_2851_, lean_object* v_a_2852_, lean_object* v_f_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2850_, v_a_2852_, v_f_2853_, v_t_2851_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter(lean_object* v_00_u03b1_2855_, lean_object* v_00_u03b2_2856_, lean_object* v_cmp_2857_, lean_object* v_inst_2858_, lean_object* v_t_2859_, lean_object* v_a_2860_, lean_object* v_f_2861_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2857_, v_a_2860_, v_f_2861_, v_t_2859_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2863_, lean_object* v_mergeFn_2864_, lean_object* v_a_2865_, lean_object* v_x_2866_){
_start:
{
if (lean_obj_tag(v_x_2866_) == 0)
{
lean_object* v___x_2867_; 
lean_dec(v_a_2865_);
lean_dec(v_mergeFn_2864_);
v___x_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2867_, 0, v_b_u2082_2863_);
return v___x_2867_;
}
else
{
lean_object* v_val_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2876_; 
v_val_2868_ = lean_ctor_get(v_x_2866_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_x_2866_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2870_ = v_x_2866_;
v_isShared_2871_ = v_isSharedCheck_2876_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_val_2868_);
lean_dec(v_x_2866_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2876_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2872_ = lean_apply_3(v_mergeFn_2864_, v_a_2865_, v_val_2868_, v_b_u2082_2863_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v___x_2872_);
v___x_2874_ = v___x_2870_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2877_, lean_object* v_cmp_2878_, lean_object* v_t_2879_, lean_object* v_a_2880_, lean_object* v_b_u2082_2881_){
_start:
{
lean_object* v___f_2882_; lean_object* v___x_2883_; 
lean_inc(v_a_2880_);
v___f_2882_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2882_, 0, v_b_u2082_2881_);
lean_closure_set(v___f_2882_, 1, v_mergeFn_2877_);
lean_closure_set(v___f_2882_, 2, v_a_2880_);
v___x_2883_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2878_, v_a_2880_, v___f_2882_, v_t_2879_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg(lean_object* v_cmp_2884_, lean_object* v_mergeFn_2885_, lean_object* v_t_u2081_2886_, lean_object* v_t_u2082_2887_){
_start:
{
lean_object* v___f_2888_; lean_object* v___x_2889_; 
v___f_2888_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2888_, 0, v_mergeFn_2885_);
lean_closure_set(v___f_2888_, 1, v_cmp_2884_);
v___x_2889_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2888_, v_t_u2081_2886_, v_t_u2082_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith(lean_object* v_00_u03b1_2890_, lean_object* v_00_u03b2_2891_, lean_object* v_cmp_2892_, lean_object* v_inst_2893_, lean_object* v_mergeFn_2894_, lean_object* v_t_u2081_2895_, lean_object* v_t_u2082_2896_){
_start:
{
lean_object* v___f_2897_; lean_object* v___x_2898_; 
v___f_2897_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2897_, 0, v_mergeFn_2894_);
lean_closure_set(v___f_2897_, 1, v_cmp_2892_);
v___x_2898_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2897_, v_t_u2081_2895_, v_t_u2082_2896_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg___lam__0(lean_object* v_x1_2899_, lean_object* v_x2_2900_, lean_object* v_x3_2901_){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2902_, 0, v_x1_2899_);
lean_ctor_set(v___x_2902_, 1, v_x2_2900_);
v___x_2903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
lean_ctor_set(v___x_2903_, 1, v_x3_2901_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg(lean_object* v_t_2905_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList(lean_object* v_00_u03b1_2910_, lean_object* v_cmp_2911_, lean_object* v_00_u03b2_2912_, lean_object* v_t_2913_){
_start:
{
lean_object* v___f_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___f_2914_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0));
v___x_2915_ = lean_box(0);
v___x_2916_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2917_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2916_, v___f_2914_, v___x_2915_, v_t_2913_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___boxed(lean_object* v_00_u03b1_2918_, lean_object* v_cmp_2919_, lean_object* v_00_u03b2_2920_, lean_object* v_t_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_Std_DTreeMap_Raw_Const_toList(v_00_u03b1_2918_, v_cmp_2919_, v_00_u03b2_2920_, v_t_2921_);
lean_dec_ref(v_cmp_2919_);
return v_res_2922_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0(lean_object* v_cmp_2924_, lean_object* v_a_2925_, lean_object* v_x_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_fst_2928_; lean_object* v_snd_2929_; lean_object* v_r_2930_; lean_object* v___x_2931_; 
v_fst_2928_ = lean_ctor_get(v_a_2925_, 0);
lean_inc(v_fst_2928_);
v_snd_2929_ = lean_ctor_get(v_a_2925_, 1);
lean_inc(v_snd_2929_);
lean_dec_ref(v_a_2925_);
v_r_2930_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2924_, v_fst_2928_, v_snd_2929_, v___y_2927_);
v___x_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2931_, 0, v_r_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg(lean_object* v_l_2932_, lean_object* v_cmp_2933_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg___boxed(lean_object* v_l_2938_, lean_object* v_cmp_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Std_DTreeMap_Raw_Const_ofList___redArg(v_l_2938_, v_cmp_2939_);
lean_dec(v_l_2938_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList(lean_object* v_00_u03b1_2941_, lean_object* v_00_u03b2_2942_, lean_object* v_l_2943_, lean_object* v_cmp_2944_){
_start:
{
lean_object* v___f_2945_; lean_object* v___x_2946_; lean_object* v_r_2947_; lean_object* v___x_2948_; 
v___f_2945_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2945_, 0, v_cmp_2944_);
v___x_2946_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2947_ = lean_box(1);
v___x_2948_ = l_List_forIn_x27_loop___redArg(v___x_2946_, v___f_2945_, v_l_2943_, v_r_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_00_u03b2_2950_, lean_object* v_l_2951_, lean_object* v_cmp_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Std_DTreeMap_Raw_Const_ofList(v_00_u03b1_2949_, v_00_u03b2_2950_, v_l_2951_, v_cmp_2952_);
lean_dec(v_l_2951_);
return v_res_2953_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_2955_, lean_object* v_a_2956_, lean_object* v_x_2957_, lean_object* v___y_2958_){
_start:
{
uint8_t v___x_2959_; 
lean_inc(v___y_2958_);
lean_inc(v_a_2956_);
lean_inc_ref(v_cmp_2955_);
v___x_2959_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2955_, v_a_2956_, v___y_2958_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = lean_box(0);
v___x_2961_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2955_, v_a_2956_, v___x_2960_, v___y_2958_);
v___x_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
else
{
lean_object* v___x_2963_; 
lean_dec(v_a_2956_);
lean_dec_ref(v_cmp_2955_);
v___x_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___y_2958_);
return v___x_2963_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg(lean_object* v_l_2964_, lean_object* v_cmp_2965_){
_start:
{
lean_object* v___f_2966_; lean_object* v___x_2967_; lean_object* v_r_2968_; lean_object* v___x_2969_; 
v___f_2966_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2966_, 0, v_cmp_2965_);
v___x_2967_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2968_ = lean_box(1);
v___x_2969_ = l_List_forIn_x27_loop___redArg(v___x_2967_, v___f_2966_, v_l_2964_, v_r_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___boxed(lean_object* v_l_2970_, lean_object* v_cmp_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Std_DTreeMap_Raw_Const_unitOfList___redArg(v_l_2970_, v_cmp_2971_);
lean_dec(v_l_2970_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList(lean_object* v_00_u03b1_2973_, lean_object* v_l_2974_, lean_object* v_cmp_2975_){
_start:
{
lean_object* v___f_2976_; lean_object* v___x_2977_; lean_object* v_r_2978_; lean_object* v___x_2979_; 
v___f_2976_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2976_, 0, v_cmp_2975_);
v___x_2977_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2978_ = lean_box(1);
v___x_2979_ = l_List_forIn_x27_loop___redArg(v___x_2977_, v___f_2976_, v_l_2974_, v_r_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___boxed(lean_object* v_00_u03b1_2980_, lean_object* v_l_2981_, lean_object* v_cmp_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Std_DTreeMap_Raw_Const_unitOfList(v_00_u03b1_2980_, v_l_2981_, v_cmp_2982_);
lean_dec(v_l_2981_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg___lam__0(lean_object* v_l_2984_, lean_object* v_k_2985_, lean_object* v_v_2986_){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v_k_2985_);
lean_ctor_set(v___x_2987_, 1, v_v_2986_);
v___x_2988_ = lean_array_push(v_l_2984_, v___x_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg(lean_object* v_t_2990_){
_start:
{
lean_object* v___f_2991_; lean_object* v___y_2993_; 
v___f_2991_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2990_) == 0)
{
lean_object* v_size_2996_; 
v_size_2996_ = lean_ctor_get(v_t_2990_, 0);
lean_inc(v_size_2996_);
v___y_2993_ = v_size_2996_;
goto v___jp_2992_;
}
else
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_unsigned_to_nat(0u);
v___y_2993_ = v___x_2997_;
goto v___jp_2992_;
}
v___jp_2992_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_mk_empty_array_with_capacity(v___y_2993_);
lean_dec(v___y_2993_);
v___x_2995_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2991_, v___x_2994_, v_t_2990_);
return v___x_2995_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray(lean_object* v_00_u03b1_2998_, lean_object* v_cmp_2999_, lean_object* v_00_u03b2_3000_, lean_object* v_t_3001_){
_start:
{
lean_object* v___f_3002_; lean_object* v___y_3004_; 
v___f_3002_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3001_) == 0)
{
lean_object* v_size_3007_; 
v_size_3007_ = lean_ctor_get(v_t_3001_, 0);
lean_inc(v_size_3007_);
v___y_3004_ = v_size_3007_;
goto v___jp_3003_;
}
else
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_unsigned_to_nat(0u);
v___y_3004_ = v___x_3008_;
goto v___jp_3003_;
}
v___jp_3003_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = lean_mk_empty_array_with_capacity(v___y_3004_);
lean_dec(v___y_3004_);
v___x_3006_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3002_, v___x_3005_, v_t_3001_);
return v___x_3006_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___boxed(lean_object* v_00_u03b1_3009_, lean_object* v_cmp_3010_, lean_object* v_00_u03b2_3011_, lean_object* v_t_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Std_DTreeMap_Raw_Const_toArray(v_00_u03b1_3009_, v_cmp_3010_, v_00_u03b2_3011_, v_t_3012_);
lean_dec_ref(v_cmp_3010_);
return v_res_3013_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray___redArg(lean_object* v_a_3015_, lean_object* v_cmp_3016_){
_start:
{
lean_object* v___f_3017_; lean_object* v___x_3018_; lean_object* v_r_3019_; size_t v_sz_3020_; size_t v___x_3021_; lean_object* v___x_3022_; 
v___f_3017_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3017_, 0, v_cmp_3016_);
v___x_3018_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3019_ = lean_box(1);
v_sz_3020_ = lean_array_size(v_a_3015_);
v___x_3021_ = ((size_t)0ULL);
v___x_3022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3018_, v_a_3015_, v___f_3017_, v_sz_3020_, v___x_3021_, v_r_3019_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray(lean_object* v_00_u03b1_3023_, lean_object* v_00_u03b2_3024_, lean_object* v_a_3025_, lean_object* v_cmp_3026_){
_start:
{
lean_object* v___f_3027_; lean_object* v___x_3028_; lean_object* v_r_3029_; size_t v_sz_3030_; size_t v___x_3031_; lean_object* v___x_3032_; 
v___f_3027_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3027_, 0, v_cmp_3026_);
v___x_3028_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3029_ = lean_box(1);
v_sz_3030_ = lean_array_size(v_a_3025_);
v___x_3031_ = ((size_t)0ULL);
v___x_3032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3028_, v_a_3025_, v___f_3027_, v_sz_3030_, v___x_3031_, v_r_3029_);
return v___x_3032_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray___redArg(lean_object* v_a_3034_, lean_object* v_cmp_3035_){
_start:
{
lean_object* v___f_3036_; lean_object* v___x_3037_; lean_object* v_r_3038_; size_t v_sz_3039_; size_t v___x_3040_; lean_object* v___x_3041_; 
v___f_3036_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3036_, 0, v_cmp_3035_);
v___x_3037_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3038_ = lean_box(1);
v_sz_3039_ = lean_array_size(v_a_3034_);
v___x_3040_ = ((size_t)0ULL);
v___x_3041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3037_, v_a_3034_, v___f_3036_, v_sz_3039_, v___x_3040_, v_r_3038_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray(lean_object* v_00_u03b1_3042_, lean_object* v_a_3043_, lean_object* v_cmp_3044_){
_start:
{
lean_object* v___f_3045_; lean_object* v___x_3046_; lean_object* v_r_3047_; size_t v_sz_3048_; size_t v___x_3049_; lean_object* v___x_3050_; 
v___f_3045_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3045_, 0, v_cmp_3044_);
v___x_3046_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3047_ = lean_box(1);
v_sz_3048_ = lean_array_size(v_a_3043_);
v___x_3049_ = ((size_t)0ULL);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3046_, v_a_3043_, v___f_3045_, v_sz_3048_, v___x_3049_, v_r_3047_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify___redArg(lean_object* v_cmp_3051_, lean_object* v_t_3052_, lean_object* v_a_3053_, lean_object* v_f_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3051_, v_a_3053_, v_f_3054_, v_t_3052_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify(lean_object* v_00_u03b1_3056_, lean_object* v_cmp_3057_, lean_object* v_00_u03b2_3058_, lean_object* v_t_3059_, lean_object* v_a_3060_, lean_object* v_f_3061_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3057_, v_a_3060_, v_f_3061_, v_t_3059_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter___redArg(lean_object* v_cmp_3063_, lean_object* v_t_3064_, lean_object* v_a_3065_, lean_object* v_f_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3063_, v_a_3065_, v_f_3066_, v_t_3064_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter(lean_object* v_00_u03b1_3068_, lean_object* v_cmp_3069_, lean_object* v_00_u03b2_3070_, lean_object* v_t_3071_, lean_object* v_a_3072_, lean_object* v_f_3073_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3069_, v_a_3072_, v_f_3073_, v_t_3071_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3075_, lean_object* v_cmp_3076_, lean_object* v_t_3077_, lean_object* v_a_3078_, lean_object* v_b_u2082_3079_){
_start:
{
lean_object* v___f_3080_; lean_object* v___x_3081_; 
lean_inc(v_a_3078_);
v___f_3080_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3080_, 0, v_b_u2082_3079_);
lean_closure_set(v___f_3080_, 1, v_mergeFn_3075_);
lean_closure_set(v___f_3080_, 2, v_a_3078_);
v___x_3081_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3076_, v_a_3078_, v___f_3080_, v_t_3077_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg(lean_object* v_cmp_3082_, lean_object* v_mergeFn_3083_, lean_object* v_t_u2081_3084_, lean_object* v_t_u2082_3085_){
_start:
{
lean_object* v___f_3086_; lean_object* v___x_3087_; 
v___f_3086_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3086_, 0, v_mergeFn_3083_);
lean_closure_set(v___f_3086_, 1, v_cmp_3082_);
v___x_3087_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3086_, v_t_u2081_3084_, v_t_u2082_3085_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith(lean_object* v_00_u03b1_3088_, lean_object* v_cmp_3089_, lean_object* v_00_u03b2_3090_, lean_object* v_mergeFn_3091_, lean_object* v_t_u2081_3092_, lean_object* v_t_u2082_3093_){
_start:
{
lean_object* v___f_3094_; lean_object* v___x_3095_; 
v___f_3094_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3094_, 0, v_mergeFn_3091_);
lean_closure_set(v___f_3094_, 1, v_cmp_3089_);
v___x_3095_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3094_, v_t_u2081_3092_, v_t_u2082_3093_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_3096_, lean_object* v_x_3097_, lean_object* v_____s_3098_){
_start:
{
lean_object* v_fst_3099_; lean_object* v_snd_3100_; lean_object* v_r_3101_; lean_object* v___x_3102_; 
v_fst_3099_ = lean_ctor_get(v_x_3097_, 0);
lean_inc(v_fst_3099_);
v_snd_3100_ = lean_ctor_get(v_x_3097_, 1);
lean_inc(v_snd_3100_);
lean_dec_ref(v_x_3097_);
v_r_3101_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_3096_, v_fst_3099_, v_snd_3100_, v_____s_3098_);
v___x_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3102_, 0, v_r_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg(lean_object* v_cmp_3103_, lean_object* v_inst_3104_, lean_object* v_t_3105_, lean_object* v_l_3106_){
_start:
{
lean_object* v___f_3107_; lean_object* v___x_3108_; 
v___f_3107_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3107_, 0, v_cmp_3103_);
v___x_3108_ = lean_apply_4(v_inst_3104_, lean_box(0), v_l_3106_, v_t_3105_, v___f_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany(lean_object* v_00_u03b1_3109_, lean_object* v_00_u03b2_3110_, lean_object* v_cmp_3111_, lean_object* v_00_u03c1_3112_, lean_object* v_inst_3113_, lean_object* v_t_3114_, lean_object* v_l_3115_){
_start:
{
lean_object* v___f_3116_; lean_object* v___x_3117_; 
v___f_3116_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3116_, 0, v_cmp_3111_);
v___x_3117_ = lean_apply_4(v_inst_3113_, lean_box(0), v_l_3115_, v_t_3114_, v___f_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_3118_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_box(1);
v___x_3120_ = lean_panic_fn_borrowed(v___x_3119_, v_msg_3118_);
return v___x_3120_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3124_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__2));
v___x_3125_ = lean_unsigned_to_nat(35u);
v___x_3126_ = lean_unsigned_to_nat(182u);
v___x_3127_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__1));
v___x_3128_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0));
v___x_3129_ = l_mkPanicMessageWithDecl(v___x_3128_, v___x_3127_, v___x_3126_, v___x_3125_, v___x_3124_);
return v___x_3129_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3130_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__2));
v___x_3131_ = lean_unsigned_to_nat(21u);
v___x_3132_ = lean_unsigned_to_nat(183u);
v___x_3133_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__1));
v___x_3134_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0));
v___x_3135_ = l_mkPanicMessageWithDecl(v___x_3134_, v___x_3133_, v___x_3132_, v___x_3131_, v___x_3130_);
return v___x_3135_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3138_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__6));
v___x_3139_ = lean_unsigned_to_nat(35u);
v___x_3140_ = lean_unsigned_to_nat(276u);
v___x_3141_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__5));
v___x_3142_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0));
v___x_3143_ = l_mkPanicMessageWithDecl(v___x_3142_, v___x_3141_, v___x_3140_, v___x_3139_, v___x_3138_);
return v___x_3143_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3144_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__6));
v___x_3145_ = lean_unsigned_to_nat(21u);
v___x_3146_ = lean_unsigned_to_nat(277u);
v___x_3147_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__5));
v___x_3148_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0));
v___x_3149_ = l_mkPanicMessageWithDecl(v___x_3148_, v___x_3147_, v___x_3146_, v___x_3145_, v___x_3144_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(lean_object* v_cmp_3150_, lean_object* v_k_3151_, lean_object* v_v_3152_, lean_object* v_t_3153_){
_start:
{
if (lean_obj_tag(v_t_3153_) == 0)
{
lean_object* v_size_3154_; lean_object* v_k_3155_; lean_object* v_v_3156_; lean_object* v_l_3157_; lean_object* v_r_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3515_; 
v_size_3154_ = lean_ctor_get(v_t_3153_, 0);
v_k_3155_ = lean_ctor_get(v_t_3153_, 1);
v_v_3156_ = lean_ctor_get(v_t_3153_, 2);
v_l_3157_ = lean_ctor_get(v_t_3153_, 3);
v_r_3158_ = lean_ctor_get(v_t_3153_, 4);
v_isSharedCheck_3515_ = !lean_is_exclusive(v_t_3153_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3160_ = v_t_3153_;
v_isShared_3161_ = v_isSharedCheck_3515_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_r_3158_);
lean_inc(v_l_3157_);
lean_inc(v_v_3156_);
lean_inc(v_k_3155_);
lean_inc(v_size_3154_);
lean_dec(v_t_3153_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3515_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3162_; uint8_t v___x_3163_; 
lean_inc_ref(v_cmp_3150_);
lean_inc(v_k_3155_);
lean_inc(v_k_3151_);
v___x_3162_ = lean_apply_2(v_cmp_3150_, v_k_3151_, v_k_3155_);
v___x_3163_ = lean_unbox(v___x_3162_);
switch(v___x_3163_)
{
case 0:
{
lean_object* v___x_3164_; 
lean_dec(v_size_3154_);
v___x_3164_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3150_, v_k_3151_, v_v_3152_, v_l_3157_);
if (lean_obj_tag(v_r_3158_) == 0)
{
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_size_3165_; lean_object* v_size_3166_; lean_object* v_k_3167_; lean_object* v_v_3168_; lean_object* v_l_3169_; lean_object* v_r_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; 
v_size_3165_ = lean_ctor_get(v_r_3158_, 0);
v_size_3166_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_size_3166_);
v_k_3167_ = lean_ctor_get(v___x_3164_, 1);
lean_inc(v_k_3167_);
v_v_3168_ = lean_ctor_get(v___x_3164_, 2);
lean_inc(v_v_3168_);
v_l_3169_ = lean_ctor_get(v___x_3164_, 3);
lean_inc(v_l_3169_);
v_r_3170_ = lean_ctor_get(v___x_3164_, 4);
lean_inc(v_r_3170_);
v___x_3171_ = lean_unsigned_to_nat(3u);
v___x_3172_ = lean_nat_mul(v___x_3171_, v_size_3165_);
v___x_3173_ = lean_nat_dec_lt(v___x_3172_, v_size_3166_);
lean_dec(v___x_3172_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
lean_dec(v_r_3170_);
lean_dec(v_l_3169_);
lean_dec(v_v_3168_);
lean_dec(v_k_3167_);
v___x_3174_ = lean_unsigned_to_nat(1u);
v___x_3175_ = lean_nat_add(v___x_3174_, v_size_3166_);
lean_dec(v_size_3166_);
v___x_3176_ = lean_nat_add(v___x_3175_, v_size_3165_);
lean_dec(v___x_3175_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 3, v___x_3164_);
lean_ctor_set(v___x_3160_, 0, v___x_3176_);
v___x_3178_ = v___x_3160_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3179_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3179_, 3, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3179_, 4, v_r_3158_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
else
{
lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3251_; 
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; lean_object* v_unused_3253_; lean_object* v_unused_3254_; lean_object* v_unused_3255_; lean_object* v_unused_3256_; 
v_unused_3252_ = lean_ctor_get(v___x_3164_, 4);
lean_dec(v_unused_3252_);
v_unused_3253_ = lean_ctor_get(v___x_3164_, 3);
lean_dec(v_unused_3253_);
v_unused_3254_ = lean_ctor_get(v___x_3164_, 2);
lean_dec(v_unused_3254_);
v_unused_3255_ = lean_ctor_get(v___x_3164_, 1);
lean_dec(v_unused_3255_);
v_unused_3256_ = lean_ctor_get(v___x_3164_, 0);
lean_dec(v_unused_3256_);
v___x_3181_ = v___x_3164_;
v_isShared_3182_ = v_isSharedCheck_3251_;
goto v_resetjp_3180_;
}
else
{
lean_dec(v___x_3164_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3251_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
if (lean_obj_tag(v_l_3169_) == 0)
{
if (lean_obj_tag(v_r_3170_) == 0)
{
lean_object* v_size_3183_; lean_object* v_size_3184_; lean_object* v_k_3185_; lean_object* v_v_3186_; lean_object* v_l_3187_; lean_object* v_r_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; uint8_t v___x_3191_; 
v_size_3183_ = lean_ctor_get(v_l_3169_, 0);
v_size_3184_ = lean_ctor_get(v_r_3170_, 0);
v_k_3185_ = lean_ctor_get(v_r_3170_, 1);
v_v_3186_ = lean_ctor_get(v_r_3170_, 2);
v_l_3187_ = lean_ctor_get(v_r_3170_, 3);
v_r_3188_ = lean_ctor_get(v_r_3170_, 4);
v___x_3189_ = lean_unsigned_to_nat(2u);
v___x_3190_ = lean_nat_mul(v___x_3189_, v_size_3183_);
v___x_3191_ = lean_nat_dec_lt(v_size_3184_, v___x_3190_);
lean_dec(v___x_3190_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3221_; 
lean_inc(v_r_3188_);
lean_inc(v_l_3187_);
lean_inc(v_v_3186_);
lean_inc(v_k_3185_);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_r_3170_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; lean_object* v_unused_3223_; lean_object* v_unused_3224_; lean_object* v_unused_3225_; lean_object* v_unused_3226_; 
v_unused_3222_ = lean_ctor_get(v_r_3170_, 4);
lean_dec(v_unused_3222_);
v_unused_3223_ = lean_ctor_get(v_r_3170_, 3);
lean_dec(v_unused_3223_);
v_unused_3224_ = lean_ctor_get(v_r_3170_, 2);
lean_dec(v_unused_3224_);
v_unused_3225_ = lean_ctor_get(v_r_3170_, 1);
lean_dec(v_unused_3225_);
v_unused_3226_ = lean_ctor_get(v_r_3170_, 0);
lean_dec(v_unused_3226_);
v___x_3193_ = v_r_3170_;
v_isShared_3194_ = v_isSharedCheck_3221_;
goto v_resetjp_3192_;
}
else
{
lean_dec(v_r_3170_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3221_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___x_3209_; lean_object* v___y_3211_; 
v___x_3195_ = lean_unsigned_to_nat(1u);
v___x_3196_ = lean_nat_add(v___x_3195_, v_size_3166_);
lean_dec(v_size_3166_);
v___x_3197_ = lean_nat_add(v___x_3196_, v_size_3165_);
lean_dec(v___x_3196_);
v___x_3209_ = lean_nat_add(v___x_3195_, v_size_3183_);
if (lean_obj_tag(v_l_3187_) == 0)
{
lean_object* v_size_3219_; 
v_size_3219_ = lean_ctor_get(v_l_3187_, 0);
lean_inc(v_size_3219_);
v___y_3211_ = v_size_3219_;
goto v___jp_3210_;
}
else
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_unsigned_to_nat(0u);
v___y_3211_ = v___x_3220_;
goto v___jp_3210_;
}
v___jp_3198_:
{
lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3202_ = lean_nat_add(v___y_3200_, v___y_3201_);
lean_dec(v___y_3201_);
lean_dec(v___y_3200_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 4, v_r_3158_);
lean_ctor_set(v___x_3193_, 3, v_r_3188_);
lean_ctor_set(v___x_3193_, 2, v_v_3156_);
lean_ctor_set(v___x_3193_, 1, v_k_3155_);
lean_ctor_set(v___x_3193_, 0, v___x_3202_);
v___x_3204_ = v___x_3193_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3208_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3208_, 3, v_r_3188_);
lean_ctor_set(v_reuseFailAlloc_3208_, 4, v_r_3158_);
v___x_3204_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3206_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 4, v___x_3204_);
lean_ctor_set(v___x_3181_, 3, v___y_3199_);
lean_ctor_set(v___x_3181_, 2, v_v_3186_);
lean_ctor_set(v___x_3181_, 1, v_k_3185_);
lean_ctor_set(v___x_3181_, 0, v___x_3197_);
v___x_3206_ = v___x_3181_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_k_3185_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v_v_3186_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v___y_3199_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
v___jp_3210_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = lean_nat_add(v___x_3209_, v___y_3211_);
lean_dec(v___y_3211_);
lean_dec(v___x_3209_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v_l_3187_);
lean_ctor_set(v___x_3160_, 3, v_l_3169_);
lean_ctor_set(v___x_3160_, 2, v_v_3168_);
lean_ctor_set(v___x_3160_, 1, v_k_3167_);
lean_ctor_set(v___x_3160_, 0, v___x_3212_);
v___x_3214_ = v___x_3160_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3212_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v_l_3169_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v_l_3187_);
v___x_3214_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_nat_add(v___x_3195_, v_size_3165_);
if (lean_obj_tag(v_r_3188_) == 0)
{
lean_object* v_size_3216_; 
v_size_3216_ = lean_ctor_get(v_r_3188_, 0);
lean_inc(v_size_3216_);
v___y_3199_ = v___x_3214_;
v___y_3200_ = v___x_3215_;
v___y_3201_ = v_size_3216_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_unsigned_to_nat(0u);
v___y_3199_ = v___x_3214_;
v___y_3200_ = v___x_3215_;
v___y_3201_ = v___x_3217_;
goto v___jp_3198_;
}
}
}
}
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3233_; 
lean_del_object(v___x_3160_);
v___x_3227_ = lean_unsigned_to_nat(1u);
v___x_3228_ = lean_nat_add(v___x_3227_, v_size_3166_);
lean_dec(v_size_3166_);
v___x_3229_ = lean_nat_add(v___x_3228_, v_size_3165_);
lean_dec(v___x_3228_);
v___x_3230_ = lean_nat_add(v___x_3227_, v_size_3165_);
v___x_3231_ = lean_nat_add(v___x_3230_, v_size_3184_);
lean_dec(v___x_3230_);
lean_inc_ref(v_r_3158_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 4, v_r_3158_);
lean_ctor_set(v___x_3181_, 3, v_r_3170_);
lean_ctor_set(v___x_3181_, 2, v_v_3156_);
lean_ctor_set(v___x_3181_, 1, v_k_3155_);
lean_ctor_set(v___x_3181_, 0, v___x_3231_);
v___x_3233_ = v___x_3181_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3231_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v_r_3170_);
lean_ctor_set(v_reuseFailAlloc_3246_, 4, v_r_3158_);
v___x_3233_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
v_isSharedCheck_3240_ = !lean_is_exclusive(v_r_3158_);
if (v_isSharedCheck_3240_ == 0)
{
lean_object* v_unused_3241_; lean_object* v_unused_3242_; lean_object* v_unused_3243_; lean_object* v_unused_3244_; lean_object* v_unused_3245_; 
v_unused_3241_ = lean_ctor_get(v_r_3158_, 4);
lean_dec(v_unused_3241_);
v_unused_3242_ = lean_ctor_get(v_r_3158_, 3);
lean_dec(v_unused_3242_);
v_unused_3243_ = lean_ctor_get(v_r_3158_, 2);
lean_dec(v_unused_3243_);
v_unused_3244_ = lean_ctor_get(v_r_3158_, 1);
lean_dec(v_unused_3244_);
v_unused_3245_ = lean_ctor_get(v_r_3158_, 0);
lean_dec(v_unused_3245_);
v___x_3235_ = v_r_3158_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_dec(v_r_3158_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 4, v___x_3233_);
lean_ctor_set(v___x_3235_, 3, v_l_3169_);
lean_ctor_set(v___x_3235_, 2, v_v_3168_);
lean_ctor_set(v___x_3235_, 1, v_k_3167_);
lean_ctor_set(v___x_3235_, 0, v___x_3229_);
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3239_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3239_, 3, v_l_3169_);
lean_ctor_set(v_reuseFailAlloc_3239_, 4, v___x_3233_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
}
else
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_dec_ref(v_l_3169_);
lean_del_object(v___x_3181_);
lean_dec(v_v_3168_);
lean_dec(v_k_3167_);
lean_dec(v_size_3166_);
lean_dec_ref(v_r_3158_);
lean_del_object(v___x_3160_);
lean_dec(v_v_3156_);
lean_dec(v_k_3155_);
v___x_3247_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3);
v___x_3248_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_3247_);
return v___x_3248_;
}
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
lean_del_object(v___x_3181_);
lean_dec(v_r_3170_);
lean_dec(v_v_3168_);
lean_dec(v_k_3167_);
lean_dec(v_size_3166_);
lean_dec_ref(v_r_3158_);
lean_del_object(v___x_3160_);
lean_dec(v_v_3156_);
lean_dec(v_k_3155_);
v___x_3249_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4);
v___x_3250_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_3249_);
return v___x_3250_;
}
}
}
}
else
{
lean_object* v_size_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3261_; 
v_size_3257_ = lean_ctor_get(v_r_3158_, 0);
v___x_3258_ = lean_unsigned_to_nat(1u);
v___x_3259_ = lean_nat_add(v___x_3258_, v_size_3257_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 3, v___x_3164_);
lean_ctor_set(v___x_3160_, 0, v___x_3259_);
v___x_3261_ = v___x_3160_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3262_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3262_, 3, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3262_, 4, v_r_3158_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
else
{
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_l_3263_; 
v_l_3263_ = lean_ctor_get(v___x_3164_, 3);
lean_inc(v_l_3263_);
if (lean_obj_tag(v_l_3263_) == 0)
{
lean_object* v_r_3264_; 
v_r_3264_ = lean_ctor_get(v___x_3164_, 4);
lean_inc(v_r_3264_);
if (lean_obj_tag(v_r_3264_) == 0)
{
lean_object* v_size_3265_; lean_object* v_k_3266_; lean_object* v_v_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3281_; 
v_size_3265_ = lean_ctor_get(v___x_3164_, 0);
v_k_3266_ = lean_ctor_get(v___x_3164_, 1);
v_v_3267_ = lean_ctor_get(v___x_3164_, 2);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; lean_object* v_unused_3283_; 
v_unused_3282_ = lean_ctor_get(v___x_3164_, 4);
lean_dec(v_unused_3282_);
v_unused_3283_ = lean_ctor_get(v___x_3164_, 3);
lean_dec(v_unused_3283_);
v___x_3269_ = v___x_3164_;
v_isShared_3270_ = v_isSharedCheck_3281_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_v_3267_);
lean_inc(v_k_3266_);
lean_inc(v_size_3265_);
lean_dec(v___x_3164_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3281_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v_size_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
v_size_3271_ = lean_ctor_get(v_r_3264_, 0);
v___x_3272_ = lean_unsigned_to_nat(1u);
v___x_3273_ = lean_nat_add(v___x_3272_, v_size_3265_);
lean_dec(v_size_3265_);
v___x_3274_ = lean_nat_add(v___x_3272_, v_size_3271_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 4, v_r_3158_);
lean_ctor_set(v___x_3269_, 3, v_r_3264_);
lean_ctor_set(v___x_3269_, 2, v_v_3156_);
lean_ctor_set(v___x_3269_, 1, v_k_3155_);
lean_ctor_set(v___x_3269_, 0, v___x_3274_);
v___x_3276_ = v___x_3269_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3274_);
lean_ctor_set(v_reuseFailAlloc_3280_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3280_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3280_, 3, v_r_3264_);
lean_ctor_set(v_reuseFailAlloc_3280_, 4, v_r_3158_);
v___x_3276_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
lean_object* v___x_3278_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v___x_3276_);
lean_ctor_set(v___x_3160_, 3, v_l_3263_);
lean_ctor_set(v___x_3160_, 2, v_v_3267_);
lean_ctor_set(v___x_3160_, 1, v_k_3266_);
lean_ctor_set(v___x_3160_, 0, v___x_3273_);
v___x_3278_ = v___x_3160_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3273_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_k_3266_);
lean_ctor_set(v_reuseFailAlloc_3279_, 2, v_v_3267_);
lean_ctor_set(v_reuseFailAlloc_3279_, 3, v_l_3263_);
lean_ctor_set(v_reuseFailAlloc_3279_, 4, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
else
{
lean_object* v_k_3284_; lean_object* v_v_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3297_; 
v_k_3284_ = lean_ctor_get(v___x_3164_, 1);
v_v_3285_ = lean_ctor_get(v___x_3164_, 2);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; lean_object* v_unused_3299_; lean_object* v_unused_3300_; 
v_unused_3298_ = lean_ctor_get(v___x_3164_, 4);
lean_dec(v_unused_3298_);
v_unused_3299_ = lean_ctor_get(v___x_3164_, 3);
lean_dec(v_unused_3299_);
v_unused_3300_ = lean_ctor_get(v___x_3164_, 0);
lean_dec(v_unused_3300_);
v___x_3287_ = v___x_3164_;
v_isShared_3288_ = v_isSharedCheck_3297_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_v_3285_);
lean_inc(v_k_3284_);
lean_dec(v___x_3164_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3297_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3292_; 
v___x_3289_ = lean_unsigned_to_nat(3u);
v___x_3290_ = lean_unsigned_to_nat(1u);
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 3, v_r_3264_);
lean_ctor_set(v___x_3287_, 2, v_v_3156_);
lean_ctor_set(v___x_3287_, 1, v_k_3155_);
lean_ctor_set(v___x_3287_, 0, v___x_3290_);
v___x_3292_ = v___x_3287_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3290_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3296_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3296_, 3, v_r_3264_);
lean_ctor_set(v_reuseFailAlloc_3296_, 4, v_r_3264_);
v___x_3292_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
lean_object* v___x_3294_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v___x_3292_);
lean_ctor_set(v___x_3160_, 3, v_l_3263_);
lean_ctor_set(v___x_3160_, 2, v_v_3285_);
lean_ctor_set(v___x_3160_, 1, v_k_3284_);
lean_ctor_set(v___x_3160_, 0, v___x_3289_);
v___x_3294_ = v___x_3160_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3289_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_k_3284_);
lean_ctor_set(v_reuseFailAlloc_3295_, 2, v_v_3285_);
lean_ctor_set(v_reuseFailAlloc_3295_, 3, v_l_3263_);
lean_ctor_set(v_reuseFailAlloc_3295_, 4, v___x_3292_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
else
{
lean_object* v_r_3301_; 
v_r_3301_ = lean_ctor_get(v___x_3164_, 4);
lean_inc(v_r_3301_);
if (lean_obj_tag(v_r_3301_) == 0)
{
lean_object* v_k_3302_; lean_object* v_v_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3327_; 
v_k_3302_ = lean_ctor_get(v___x_3164_, 1);
v_v_3303_ = lean_ctor_get(v___x_3164_, 2);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3327_ == 0)
{
lean_object* v_unused_3328_; lean_object* v_unused_3329_; lean_object* v_unused_3330_; 
v_unused_3328_ = lean_ctor_get(v___x_3164_, 4);
lean_dec(v_unused_3328_);
v_unused_3329_ = lean_ctor_get(v___x_3164_, 3);
lean_dec(v_unused_3329_);
v_unused_3330_ = lean_ctor_get(v___x_3164_, 0);
lean_dec(v_unused_3330_);
v___x_3305_ = v___x_3164_;
v_isShared_3306_ = v_isSharedCheck_3327_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_v_3303_);
lean_inc(v_k_3302_);
lean_dec(v___x_3164_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3327_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v_k_3307_; lean_object* v_v_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3323_; 
v_k_3307_ = lean_ctor_get(v_r_3301_, 1);
v_v_3308_ = lean_ctor_get(v_r_3301_, 2);
v_isSharedCheck_3323_ = !lean_is_exclusive(v_r_3301_);
if (v_isSharedCheck_3323_ == 0)
{
lean_object* v_unused_3324_; lean_object* v_unused_3325_; lean_object* v_unused_3326_; 
v_unused_3324_ = lean_ctor_get(v_r_3301_, 4);
lean_dec(v_unused_3324_);
v_unused_3325_ = lean_ctor_get(v_r_3301_, 3);
lean_dec(v_unused_3325_);
v_unused_3326_ = lean_ctor_get(v_r_3301_, 0);
lean_dec(v_unused_3326_);
v___x_3310_ = v_r_3301_;
v_isShared_3311_ = v_isSharedCheck_3323_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_v_3308_);
lean_inc(v_k_3307_);
lean_dec(v_r_3301_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3323_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3312_ = lean_unsigned_to_nat(3u);
v___x_3313_ = lean_unsigned_to_nat(1u);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 4, v_l_3263_);
lean_ctor_set(v___x_3310_, 3, v_l_3263_);
lean_ctor_set(v___x_3310_, 2, v_v_3303_);
lean_ctor_set(v___x_3310_, 1, v_k_3302_);
lean_ctor_set(v___x_3310_, 0, v___x_3313_);
v___x_3315_ = v___x_3310_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v_k_3302_);
lean_ctor_set(v_reuseFailAlloc_3322_, 2, v_v_3303_);
lean_ctor_set(v_reuseFailAlloc_3322_, 3, v_l_3263_);
lean_ctor_set(v_reuseFailAlloc_3322_, 4, v_l_3263_);
v___x_3315_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
lean_object* v___x_3317_; 
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 4, v_l_3263_);
lean_ctor_set(v___x_3305_, 2, v_v_3156_);
lean_ctor_set(v___x_3305_, 1, v_k_3155_);
lean_ctor_set(v___x_3305_, 0, v___x_3313_);
v___x_3317_ = v___x_3305_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3321_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3321_, 3, v_l_3263_);
lean_ctor_set(v_reuseFailAlloc_3321_, 4, v_l_3263_);
v___x_3317_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
lean_object* v___x_3319_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v___x_3317_);
lean_ctor_set(v___x_3160_, 3, v___x_3315_);
lean_ctor_set(v___x_3160_, 2, v_v_3308_);
lean_ctor_set(v___x_3160_, 1, v_k_3307_);
lean_ctor_set(v___x_3160_, 0, v___x_3312_);
v___x_3319_ = v___x_3160_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3312_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_k_3307_);
lean_ctor_set(v_reuseFailAlloc_3320_, 2, v_v_3308_);
lean_ctor_set(v_reuseFailAlloc_3320_, 3, v___x_3315_);
lean_ctor_set(v_reuseFailAlloc_3320_, 4, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3333_; 
v___x_3331_ = lean_unsigned_to_nat(2u);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v_r_3301_);
lean_ctor_set(v___x_3160_, 3, v___x_3164_);
lean_ctor_set(v___x_3160_, 0, v___x_3331_);
v___x_3333_ = v___x_3160_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3331_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_r_3301_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3335_ = lean_unsigned_to_nat(1u);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v___x_3164_);
lean_ctor_set(v___x_3160_, 3, v___x_3164_);
lean_ctor_set(v___x_3160_, 0, v___x_3335_);
v___x_3337_ = v___x_3160_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3338_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3338_, 3, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3338_, 4, v___x_3164_);
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
case 1:
{
lean_object* v___x_3340_; 
lean_dec(v_v_3156_);
lean_dec(v_k_3155_);
lean_dec_ref(v_cmp_3150_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 2, v_v_3152_);
lean_ctor_set(v___x_3160_, 1, v_k_3151_);
v___x_3340_ = v___x_3160_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_size_3154_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_k_3151_);
lean_ctor_set(v_reuseFailAlloc_3341_, 2, v_v_3152_);
lean_ctor_set(v_reuseFailAlloc_3341_, 3, v_l_3157_);
lean_ctor_set(v_reuseFailAlloc_3341_, 4, v_r_3158_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
default: 
{
lean_object* v___x_3342_; 
lean_dec(v_size_3154_);
v___x_3342_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3150_, v_k_3151_, v_v_3152_, v_r_3158_);
if (lean_obj_tag(v_l_3157_) == 0)
{
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_size_3343_; lean_object* v_size_3344_; lean_object* v_k_3345_; lean_object* v_v_3346_; lean_object* v_l_3347_; lean_object* v_r_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v_size_3343_ = lean_ctor_get(v_l_3157_, 0);
v_size_3344_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_size_3344_);
v_k_3345_ = lean_ctor_get(v___x_3342_, 1);
lean_inc(v_k_3345_);
v_v_3346_ = lean_ctor_get(v___x_3342_, 2);
lean_inc(v_v_3346_);
v_l_3347_ = lean_ctor_get(v___x_3342_, 3);
lean_inc(v_l_3347_);
v_r_3348_ = lean_ctor_get(v___x_3342_, 4);
lean_inc(v_r_3348_);
v___x_3349_ = lean_unsigned_to_nat(3u);
v___x_3350_ = lean_nat_mul(v___x_3349_, v_size_3343_);
v___x_3351_ = lean_nat_dec_lt(v___x_3350_, v_size_3344_);
lean_dec(v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
lean_dec(v_r_3348_);
lean_dec(v_l_3347_);
lean_dec(v_v_3346_);
lean_dec(v_k_3345_);
v___x_3352_ = lean_unsigned_to_nat(1u);
v___x_3353_ = lean_nat_add(v___x_3352_, v_size_3343_);
v___x_3354_ = lean_nat_add(v___x_3353_, v_size_3344_);
lean_dec(v_size_3344_);
lean_dec(v___x_3353_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v___x_3342_);
lean_ctor_set(v___x_3160_, 0, v___x_3354_);
v___x_3356_ = v___x_3160_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3357_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3357_, 3, v_l_3157_);
lean_ctor_set(v_reuseFailAlloc_3357_, 4, v___x_3342_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
else
{
lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3427_; 
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; lean_object* v_unused_3429_; lean_object* v_unused_3430_; lean_object* v_unused_3431_; lean_object* v_unused_3432_; 
v_unused_3428_ = lean_ctor_get(v___x_3342_, 4);
lean_dec(v_unused_3428_);
v_unused_3429_ = lean_ctor_get(v___x_3342_, 3);
lean_dec(v_unused_3429_);
v_unused_3430_ = lean_ctor_get(v___x_3342_, 2);
lean_dec(v_unused_3430_);
v_unused_3431_ = lean_ctor_get(v___x_3342_, 1);
lean_dec(v_unused_3431_);
v_unused_3432_ = lean_ctor_get(v___x_3342_, 0);
lean_dec(v_unused_3432_);
v___x_3359_ = v___x_3342_;
v_isShared_3360_ = v_isSharedCheck_3427_;
goto v_resetjp_3358_;
}
else
{
lean_dec(v___x_3342_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3427_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
if (lean_obj_tag(v_l_3347_) == 0)
{
if (lean_obj_tag(v_r_3348_) == 0)
{
lean_object* v_size_3361_; lean_object* v_k_3362_; lean_object* v_v_3363_; lean_object* v_l_3364_; lean_object* v_r_3365_; lean_object* v_size_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v_size_3361_ = lean_ctor_get(v_l_3347_, 0);
v_k_3362_ = lean_ctor_get(v_l_3347_, 1);
v_v_3363_ = lean_ctor_get(v_l_3347_, 2);
v_l_3364_ = lean_ctor_get(v_l_3347_, 3);
v_r_3365_ = lean_ctor_get(v_l_3347_, 4);
v_size_3366_ = lean_ctor_get(v_r_3348_, 0);
v___x_3367_ = lean_unsigned_to_nat(2u);
v___x_3368_ = lean_nat_mul(v___x_3367_, v_size_3366_);
v___x_3369_ = lean_nat_dec_lt(v_size_3361_, v___x_3368_);
lean_dec(v___x_3368_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3398_; 
lean_inc(v_r_3365_);
lean_inc(v_l_3364_);
lean_inc(v_v_3363_);
lean_inc(v_k_3362_);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_l_3347_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; lean_object* v_unused_3400_; lean_object* v_unused_3401_; lean_object* v_unused_3402_; lean_object* v_unused_3403_; 
v_unused_3399_ = lean_ctor_get(v_l_3347_, 4);
lean_dec(v_unused_3399_);
v_unused_3400_ = lean_ctor_get(v_l_3347_, 3);
lean_dec(v_unused_3400_);
v_unused_3401_ = lean_ctor_get(v_l_3347_, 2);
lean_dec(v_unused_3401_);
v_unused_3402_ = lean_ctor_get(v_l_3347_, 1);
lean_dec(v_unused_3402_);
v_unused_3403_ = lean_ctor_get(v_l_3347_, 0);
lean_dec(v_unused_3403_);
v___x_3371_ = v_l_3347_;
v_isShared_3372_ = v_isSharedCheck_3398_;
goto v_resetjp_3370_;
}
else
{
lean_dec(v_l_3347_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3398_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3388_; 
v___x_3373_ = lean_unsigned_to_nat(1u);
v___x_3374_ = lean_nat_add(v___x_3373_, v_size_3343_);
v___x_3375_ = lean_nat_add(v___x_3374_, v_size_3344_);
lean_dec(v_size_3344_);
if (lean_obj_tag(v_l_3364_) == 0)
{
lean_object* v_size_3396_; 
v_size_3396_ = lean_ctor_get(v_l_3364_, 0);
lean_inc(v_size_3396_);
v___y_3388_ = v_size_3396_;
goto v___jp_3387_;
}
else
{
lean_object* v___x_3397_; 
v___x_3397_ = lean_unsigned_to_nat(0u);
v___y_3388_ = v___x_3397_;
goto v___jp_3387_;
}
v___jp_3376_:
{
lean_object* v___x_3380_; lean_object* v___x_3382_; 
v___x_3380_ = lean_nat_add(v___y_3377_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec(v___y_3377_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 4, v_r_3348_);
lean_ctor_set(v___x_3371_, 3, v_r_3365_);
lean_ctor_set(v___x_3371_, 2, v_v_3346_);
lean_ctor_set(v___x_3371_, 1, v_k_3345_);
lean_ctor_set(v___x_3371_, 0, v___x_3380_);
v___x_3382_ = v___x_3371_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3380_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_k_3345_);
lean_ctor_set(v_reuseFailAlloc_3386_, 2, v_v_3346_);
lean_ctor_set(v_reuseFailAlloc_3386_, 3, v_r_3365_);
lean_ctor_set(v_reuseFailAlloc_3386_, 4, v_r_3348_);
v___x_3382_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
lean_object* v___x_3384_; 
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 4, v___x_3382_);
lean_ctor_set(v___x_3359_, 3, v___y_3378_);
lean_ctor_set(v___x_3359_, 2, v_v_3363_);
lean_ctor_set(v___x_3359_, 1, v_k_3362_);
lean_ctor_set(v___x_3359_, 0, v___x_3375_);
v___x_3384_ = v___x_3359_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_k_3362_);
lean_ctor_set(v_reuseFailAlloc_3385_, 2, v_v_3363_);
lean_ctor_set(v_reuseFailAlloc_3385_, 3, v___y_3378_);
lean_ctor_set(v_reuseFailAlloc_3385_, 4, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
v___jp_3387_:
{
lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3389_ = lean_nat_add(v___x_3374_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec(v___x_3374_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v_l_3364_);
lean_ctor_set(v___x_3160_, 0, v___x_3389_);
v___x_3391_ = v___x_3160_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3395_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3395_, 3, v_l_3157_);
lean_ctor_set(v_reuseFailAlloc_3395_, 4, v_l_3364_);
v___x_3391_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_nat_add(v___x_3373_, v_size_3366_);
if (lean_obj_tag(v_r_3365_) == 0)
{
lean_object* v_size_3393_; 
v_size_3393_ = lean_ctor_get(v_r_3365_, 0);
lean_inc(v_size_3393_);
v___y_3377_ = v___x_3392_;
v___y_3378_ = v___x_3391_;
v___y_3379_ = v_size_3393_;
goto v___jp_3376_;
}
else
{
lean_object* v___x_3394_; 
v___x_3394_ = lean_unsigned_to_nat(0u);
v___y_3377_ = v___x_3392_;
v___y_3378_ = v___x_3391_;
v___y_3379_ = v___x_3394_;
goto v___jp_3376_;
}
}
}
}
}
else
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3409_; 
lean_del_object(v___x_3160_);
v___x_3404_ = lean_unsigned_to_nat(1u);
v___x_3405_ = lean_nat_add(v___x_3404_, v_size_3343_);
v___x_3406_ = lean_nat_add(v___x_3405_, v_size_3344_);
lean_dec(v_size_3344_);
v___x_3407_ = lean_nat_add(v___x_3405_, v_size_3361_);
lean_dec(v___x_3405_);
lean_inc_ref(v_l_3157_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 4, v_l_3347_);
lean_ctor_set(v___x_3359_, 3, v_l_3157_);
lean_ctor_set(v___x_3359_, 2, v_v_3156_);
lean_ctor_set(v___x_3359_, 1, v_k_3155_);
lean_ctor_set(v___x_3359_, 0, v___x_3407_);
v___x_3409_ = v___x_3359_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3407_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3422_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3422_, 3, v_l_3157_);
lean_ctor_set(v_reuseFailAlloc_3422_, 4, v_l_3347_);
v___x_3409_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
v_isSharedCheck_3416_ = !lean_is_exclusive(v_l_3157_);
if (v_isSharedCheck_3416_ == 0)
{
lean_object* v_unused_3417_; lean_object* v_unused_3418_; lean_object* v_unused_3419_; lean_object* v_unused_3420_; lean_object* v_unused_3421_; 
v_unused_3417_ = lean_ctor_get(v_l_3157_, 4);
lean_dec(v_unused_3417_);
v_unused_3418_ = lean_ctor_get(v_l_3157_, 3);
lean_dec(v_unused_3418_);
v_unused_3419_ = lean_ctor_get(v_l_3157_, 2);
lean_dec(v_unused_3419_);
v_unused_3420_ = lean_ctor_get(v_l_3157_, 1);
lean_dec(v_unused_3420_);
v_unused_3421_ = lean_ctor_get(v_l_3157_, 0);
lean_dec(v_unused_3421_);
v___x_3411_ = v_l_3157_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_dec(v_l_3157_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 4, v_r_3348_);
lean_ctor_set(v___x_3411_, 3, v___x_3409_);
lean_ctor_set(v___x_3411_, 2, v_v_3346_);
lean_ctor_set(v___x_3411_, 1, v_k_3345_);
lean_ctor_set(v___x_3411_, 0, v___x_3406_);
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3406_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_k_3345_);
lean_ctor_set(v_reuseFailAlloc_3415_, 2, v_v_3346_);
lean_ctor_set(v_reuseFailAlloc_3415_, 3, v___x_3409_);
lean_ctor_set(v_reuseFailAlloc_3415_, 4, v_r_3348_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_dec_ref(v_l_3347_);
lean_del_object(v___x_3359_);
lean_dec(v_v_3346_);
lean_dec(v_k_3345_);
lean_dec(v_size_3344_);
lean_dec_ref(v_l_3157_);
lean_del_object(v___x_3160_);
lean_dec(v_v_3156_);
lean_dec(v_k_3155_);
v___x_3423_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7);
v___x_3424_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_3423_);
return v___x_3424_;
}
}
else
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
lean_del_object(v___x_3359_);
lean_dec(v_r_3348_);
lean_dec(v_v_3346_);
lean_dec(v_k_3345_);
lean_dec(v_size_3344_);
lean_dec_ref(v_l_3157_);
lean_del_object(v___x_3160_);
lean_dec(v_v_3156_);
lean_dec(v_k_3155_);
v___x_3425_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8);
v___x_3426_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_3425_);
return v___x_3426_;
}
}
}
}
else
{
lean_object* v_size_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3437_; 
v_size_3433_ = lean_ctor_get(v_l_3157_, 0);
v___x_3434_ = lean_unsigned_to_nat(1u);
v___x_3435_ = lean_nat_add(v___x_3434_, v_size_3433_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v___x_3342_);
lean_ctor_set(v___x_3160_, 0, v___x_3435_);
v___x_3437_ = v___x_3160_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3438_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3438_, 3, v_l_3157_);
lean_ctor_set(v_reuseFailAlloc_3438_, 4, v___x_3342_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
else
{
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_l_3439_; 
v_l_3439_ = lean_ctor_get(v___x_3342_, 3);
lean_inc(v_l_3439_);
if (lean_obj_tag(v_l_3439_) == 0)
{
lean_object* v_r_3440_; 
v_r_3440_ = lean_ctor_get(v___x_3342_, 4);
lean_inc(v_r_3440_);
if (lean_obj_tag(v_r_3440_) == 0)
{
lean_object* v_size_3441_; lean_object* v_k_3442_; lean_object* v_v_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3457_; 
v_size_3441_ = lean_ctor_get(v___x_3342_, 0);
v_k_3442_ = lean_ctor_get(v___x_3342_, 1);
v_v_3443_ = lean_ctor_get(v___x_3342_, 2);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3457_ == 0)
{
lean_object* v_unused_3458_; lean_object* v_unused_3459_; 
v_unused_3458_ = lean_ctor_get(v___x_3342_, 4);
lean_dec(v_unused_3458_);
v_unused_3459_ = lean_ctor_get(v___x_3342_, 3);
lean_dec(v_unused_3459_);
v___x_3445_ = v___x_3342_;
v_isShared_3446_ = v_isSharedCheck_3457_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_v_3443_);
lean_inc(v_k_3442_);
lean_inc(v_size_3441_);
lean_dec(v___x_3342_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3457_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v_size_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3452_; 
v_size_3447_ = lean_ctor_get(v_l_3439_, 0);
v___x_3448_ = lean_unsigned_to_nat(1u);
v___x_3449_ = lean_nat_add(v___x_3448_, v_size_3441_);
lean_dec(v_size_3441_);
v___x_3450_ = lean_nat_add(v___x_3448_, v_size_3447_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 4, v_l_3439_);
lean_ctor_set(v___x_3445_, 3, v_l_3157_);
lean_ctor_set(v___x_3445_, 2, v_v_3156_);
lean_ctor_set(v___x_3445_, 1, v_k_3155_);
lean_ctor_set(v___x_3445_, 0, v___x_3450_);
v___x_3452_ = v___x_3445_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3456_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3456_, 3, v_l_3157_);
lean_ctor_set(v_reuseFailAlloc_3456_, 4, v_l_3439_);
v___x_3452_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3454_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v_r_3440_);
lean_ctor_set(v___x_3160_, 3, v___x_3452_);
lean_ctor_set(v___x_3160_, 2, v_v_3443_);
lean_ctor_set(v___x_3160_, 1, v_k_3442_);
lean_ctor_set(v___x_3160_, 0, v___x_3449_);
v___x_3454_ = v___x_3160_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_k_3442_);
lean_ctor_set(v_reuseFailAlloc_3455_, 2, v_v_3443_);
lean_ctor_set(v_reuseFailAlloc_3455_, 3, v___x_3452_);
lean_ctor_set(v_reuseFailAlloc_3455_, 4, v_r_3440_);
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
else
{
lean_object* v_k_3460_; lean_object* v_v_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3485_; 
v_k_3460_ = lean_ctor_get(v___x_3342_, 1);
v_v_3461_ = lean_ctor_get(v___x_3342_, 2);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3485_ == 0)
{
lean_object* v_unused_3486_; lean_object* v_unused_3487_; lean_object* v_unused_3488_; 
v_unused_3486_ = lean_ctor_get(v___x_3342_, 4);
lean_dec(v_unused_3486_);
v_unused_3487_ = lean_ctor_get(v___x_3342_, 3);
lean_dec(v_unused_3487_);
v_unused_3488_ = lean_ctor_get(v___x_3342_, 0);
lean_dec(v_unused_3488_);
v___x_3463_ = v___x_3342_;
v_isShared_3464_ = v_isSharedCheck_3485_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_v_3461_);
lean_inc(v_k_3460_);
lean_dec(v___x_3342_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3485_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v_k_3465_; lean_object* v_v_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3481_; 
v_k_3465_ = lean_ctor_get(v_l_3439_, 1);
v_v_3466_ = lean_ctor_get(v_l_3439_, 2);
v_isSharedCheck_3481_ = !lean_is_exclusive(v_l_3439_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; lean_object* v_unused_3483_; lean_object* v_unused_3484_; 
v_unused_3482_ = lean_ctor_get(v_l_3439_, 4);
lean_dec(v_unused_3482_);
v_unused_3483_ = lean_ctor_get(v_l_3439_, 3);
lean_dec(v_unused_3483_);
v_unused_3484_ = lean_ctor_get(v_l_3439_, 0);
lean_dec(v_unused_3484_);
v___x_3468_ = v_l_3439_;
v_isShared_3469_ = v_isSharedCheck_3481_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_v_3466_);
lean_inc(v_k_3465_);
lean_dec(v_l_3439_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3481_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3470_ = lean_unsigned_to_nat(3u);
v___x_3471_ = lean_unsigned_to_nat(1u);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 4, v_r_3440_);
lean_ctor_set(v___x_3468_, 3, v_r_3440_);
lean_ctor_set(v___x_3468_, 2, v_v_3156_);
lean_ctor_set(v___x_3468_, 1, v_k_3155_);
lean_ctor_set(v___x_3468_, 0, v___x_3471_);
v___x_3473_ = v___x_3468_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3480_, 3, v_r_3440_);
lean_ctor_set(v_reuseFailAlloc_3480_, 4, v_r_3440_);
v___x_3473_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3475_; 
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 3, v_r_3440_);
lean_ctor_set(v___x_3463_, 0, v___x_3471_);
v___x_3475_ = v___x_3463_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_k_3460_);
lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_v_3461_);
lean_ctor_set(v_reuseFailAlloc_3479_, 3, v_r_3440_);
lean_ctor_set(v_reuseFailAlloc_3479_, 4, v_r_3440_);
v___x_3475_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3477_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v___x_3475_);
lean_ctor_set(v___x_3160_, 3, v___x_3473_);
lean_ctor_set(v___x_3160_, 2, v_v_3466_);
lean_ctor_set(v___x_3160_, 1, v_k_3465_);
lean_ctor_set(v___x_3160_, 0, v___x_3470_);
v___x_3477_ = v___x_3160_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_k_3465_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_v_3466_);
lean_ctor_set(v_reuseFailAlloc_3478_, 3, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3478_, 4, v___x_3475_);
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
}
}
}
else
{
lean_object* v_r_3489_; 
v_r_3489_ = lean_ctor_get(v___x_3342_, 4);
lean_inc(v_r_3489_);
if (lean_obj_tag(v_r_3489_) == 0)
{
lean_object* v_k_3490_; lean_object* v_v_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3503_; 
v_k_3490_ = lean_ctor_get(v___x_3342_, 1);
v_v_3491_ = lean_ctor_get(v___x_3342_, 2);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3503_ == 0)
{
lean_object* v_unused_3504_; lean_object* v_unused_3505_; lean_object* v_unused_3506_; 
v_unused_3504_ = lean_ctor_get(v___x_3342_, 4);
lean_dec(v_unused_3504_);
v_unused_3505_ = lean_ctor_get(v___x_3342_, 3);
lean_dec(v_unused_3505_);
v_unused_3506_ = lean_ctor_get(v___x_3342_, 0);
lean_dec(v_unused_3506_);
v___x_3493_ = v___x_3342_;
v_isShared_3494_ = v_isSharedCheck_3503_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_v_3491_);
lean_inc(v_k_3490_);
lean_dec(v___x_3342_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3503_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3495_ = lean_unsigned_to_nat(3u);
v___x_3496_ = lean_unsigned_to_nat(1u);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 4, v_l_3439_);
lean_ctor_set(v___x_3493_, 2, v_v_3156_);
lean_ctor_set(v___x_3493_, 1, v_k_3155_);
lean_ctor_set(v___x_3493_, 0, v___x_3496_);
v___x_3498_ = v___x_3493_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3496_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3502_, 3, v_l_3439_);
lean_ctor_set(v_reuseFailAlloc_3502_, 4, v_l_3439_);
v___x_3498_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3500_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v_r_3489_);
lean_ctor_set(v___x_3160_, 3, v___x_3498_);
lean_ctor_set(v___x_3160_, 2, v_v_3491_);
lean_ctor_set(v___x_3160_, 1, v_k_3490_);
lean_ctor_set(v___x_3160_, 0, v___x_3495_);
v___x_3500_ = v___x_3160_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3501_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3501_, 3, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3501_, 4, v_r_3489_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3509_; 
v___x_3507_ = lean_unsigned_to_nat(2u);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v___x_3342_);
lean_ctor_set(v___x_3160_, 3, v_r_3489_);
lean_ctor_set(v___x_3160_, 0, v___x_3507_);
v___x_3509_ = v___x_3160_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3507_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3510_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3510_, 3, v_r_3489_);
lean_ctor_set(v_reuseFailAlloc_3510_, 4, v___x_3342_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
v___x_3511_ = lean_unsigned_to_nat(1u);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 4, v___x_3342_);
lean_ctor_set(v___x_3160_, 3, v___x_3342_);
lean_ctor_set(v___x_3160_, 0, v___x_3511_);
v___x_3513_ = v___x_3160_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3514_, 2, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3514_, 3, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3514_, 4, v___x_3342_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
lean_dec_ref(v_cmp_3150_);
v___x_3516_ = lean_unsigned_to_nat(1u);
v___x_3517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
lean_ctor_set(v___x_3517_, 1, v_k_3151_);
lean_ctor_set(v___x_3517_, 2, v_v_3152_);
lean_ctor_set(v___x_3517_, 3, v_t_3153_);
lean_ctor_set(v___x_3517_, 4, v_t_3153_);
return v___x_3517_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(lean_object* v_cmp_3518_, lean_object* v_init_3519_, lean_object* v_x_3520_){
_start:
{
if (lean_obj_tag(v_x_3520_) == 0)
{
lean_object* v_k_3521_; lean_object* v_v_3522_; lean_object* v_l_3523_; lean_object* v_r_3524_; lean_object* v___x_3525_; lean_object* v_a_3526_; lean_object* v_r_3527_; 
v_k_3521_ = lean_ctor_get(v_x_3520_, 1);
lean_inc(v_k_3521_);
v_v_3522_ = lean_ctor_get(v_x_3520_, 2);
lean_inc(v_v_3522_);
v_l_3523_ = lean_ctor_get(v_x_3520_, 3);
lean_inc(v_l_3523_);
v_r_3524_ = lean_ctor_get(v_x_3520_, 4);
lean_inc(v_r_3524_);
lean_dec_ref(v_x_3520_);
lean_inc_ref_n(v_cmp_3518_, 2);
v___x_3525_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3518_, v_init_3519_, v_l_3523_);
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3526_);
lean_dec_ref(v___x_3525_);
v_r_3527_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3518_, v_k_3521_, v_v_3522_, v_a_3526_);
v_init_3519_ = v_r_3527_;
v_x_3520_ = v_r_3524_;
goto _start;
}
else
{
lean_object* v___x_3529_; 
lean_dec_ref(v_cmp_3518_);
v___x_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3529_, 0, v_init_3519_);
return v___x_3529_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(lean_object* v_cmp_3530_, lean_object* v_k_3531_, lean_object* v_t_3532_){
_start:
{
if (lean_obj_tag(v_t_3532_) == 0)
{
lean_object* v_k_3533_; lean_object* v_l_3534_; lean_object* v_r_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v_k_3533_ = lean_ctor_get(v_t_3532_, 1);
lean_inc(v_k_3533_);
v_l_3534_ = lean_ctor_get(v_t_3532_, 3);
lean_inc(v_l_3534_);
v_r_3535_ = lean_ctor_get(v_t_3532_, 4);
lean_inc(v_r_3535_);
lean_dec_ref(v_t_3532_);
lean_inc_ref(v_cmp_3530_);
lean_inc(v_k_3531_);
v___x_3536_ = lean_apply_2(v_cmp_3530_, v_k_3531_, v_k_3533_);
v___x_3537_ = lean_unbox(v___x_3536_);
switch(v___x_3537_)
{
case 0:
{
lean_dec(v_r_3535_);
v_t_3532_ = v_l_3534_;
goto _start;
}
case 1:
{
uint8_t v___x_3539_; 
lean_dec(v_r_3535_);
lean_dec(v_l_3534_);
lean_dec(v_k_3531_);
lean_dec_ref(v_cmp_3530_);
v___x_3539_ = 1;
return v___x_3539_;
}
default: 
{
lean_dec(v_l_3534_);
v_t_3532_ = v_r_3535_;
goto _start;
}
}
}
else
{
uint8_t v___x_3541_; 
lean_dec(v_k_3531_);
lean_dec_ref(v_cmp_3530_);
v___x_3541_ = 0;
return v___x_3541_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_3542_, lean_object* v_k_3543_, lean_object* v_t_3544_){
_start:
{
uint8_t v_res_3545_; lean_object* v_r_3546_; 
v_res_3545_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3542_, v_k_3543_, v_t_3544_);
v_r_3546_ = lean_box(v_res_3545_);
return v_r_3546_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(lean_object* v_cmp_3547_, lean_object* v_init_3548_, lean_object* v_x_3549_){
_start:
{
if (lean_obj_tag(v_x_3549_) == 0)
{
lean_object* v_k_3550_; lean_object* v_v_3551_; lean_object* v_l_3552_; lean_object* v_r_3553_; lean_object* v___x_3554_; lean_object* v_a_3555_; uint8_t v___x_3556_; 
v_k_3550_ = lean_ctor_get(v_x_3549_, 1);
lean_inc_n(v_k_3550_, 2);
v_v_3551_ = lean_ctor_get(v_x_3549_, 2);
lean_inc(v_v_3551_);
v_l_3552_ = lean_ctor_get(v_x_3549_, 3);
lean_inc(v_l_3552_);
v_r_3553_ = lean_ctor_get(v_x_3549_, 4);
lean_inc(v_r_3553_);
lean_dec_ref(v_x_3549_);
lean_inc_ref_n(v_cmp_3547_, 2);
v___x_3554_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3547_, v_init_3548_, v_l_3552_);
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc_n(v_a_3555_, 2);
lean_dec_ref(v___x_3554_);
v___x_3556_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3547_, v_k_3550_, v_a_3555_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; 
lean_inc_ref(v_cmp_3547_);
v___x_3557_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3547_, v_k_3550_, v_v_3551_, v_a_3555_);
v_init_3548_ = v___x_3557_;
v_x_3549_ = v_r_3553_;
goto _start;
}
else
{
lean_dec(v_v_3551_);
lean_dec(v_k_3550_);
v_init_3548_ = v_a_3555_;
v_x_3549_ = v_r_3553_;
goto _start;
}
}
else
{
lean_object* v___x_3560_; 
lean_dec_ref(v_cmp_3547_);
v___x_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3560_, 0, v_init_3548_);
return v___x_3560_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(lean_object* v_cmp_3561_, lean_object* v_t_u2081_3562_, lean_object* v_t_u2082_3563_){
_start:
{
lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3573_; 
if (lean_obj_tag(v_t_u2081_3562_) == 0)
{
lean_object* v_size_3576_; 
v_size_3576_ = lean_ctor_get(v_t_u2081_3562_, 0);
lean_inc(v_size_3576_);
v___y_3573_ = v_size_3576_;
goto v___jp_3572_;
}
else
{
lean_object* v___x_3577_; 
v___x_3577_ = lean_unsigned_to_nat(0u);
v___y_3573_ = v___x_3577_;
goto v___jp_3572_;
}
v___jp_3564_:
{
uint8_t v___x_3567_; 
v___x_3567_ = lean_nat_dec_le(v___y_3565_, v___y_3566_);
lean_dec(v___y_3566_);
lean_dec(v___y_3565_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; lean_object* v_a_3569_; 
v___x_3568_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3561_, v_t_u2081_3562_, v_t_u2082_3563_);
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref(v___x_3568_);
return v_a_3569_;
}
else
{
lean_object* v___x_3570_; lean_object* v_a_3571_; 
v___x_3570_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3561_, v_t_u2082_3563_, v_t_u2081_3562_);
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref(v___x_3570_);
return v_a_3571_;
}
}
v___jp_3572_:
{
if (lean_obj_tag(v_t_u2082_3563_) == 0)
{
lean_object* v_size_3574_; 
v_size_3574_ = lean_ctor_get(v_t_u2082_3563_, 0);
lean_inc(v_size_3574_);
v___y_3565_ = v___y_3573_;
v___y_3566_ = v_size_3574_;
goto v___jp_3564_;
}
else
{
lean_object* v___x_3575_; 
v___x_3575_ = lean_unsigned_to_nat(0u);
v___y_3565_ = v___y_3573_;
v___y_3566_ = v___x_3575_;
goto v___jp_3564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union___redArg(lean_object* v_cmp_3578_, lean_object* v_t_u2081_3579_, lean_object* v_t_u2082_3580_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3578_, v_t_u2081_3579_, v_t_u2082_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union(lean_object* v_00_u03b1_3582_, lean_object* v_00_u03b2_3583_, lean_object* v_cmp_3584_, lean_object* v_t_u2081_3585_, lean_object* v_t_u2082_3586_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3584_, v_t_u2081_3585_, v_t_u2082_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0(lean_object* v_00_u03b1_3588_, lean_object* v_cmp_3589_, lean_object* v_00_u03b2_3590_, lean_object* v_t_u2081_3591_, lean_object* v_t_u2082_3592_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3589_, v_t_u2081_3591_, v_t_u2082_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0(lean_object* v_00_u03b1_3594_, lean_object* v_cmp_3595_, lean_object* v_00_u03b2_3596_, lean_object* v_k_3597_, lean_object* v_t_3598_){
_start:
{
uint8_t v___x_3599_; 
v___x_3599_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3595_, v_k_3597_, v_t_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3600_, lean_object* v_cmp_3601_, lean_object* v_00_u03b2_3602_, lean_object* v_k_3603_, lean_object* v_t_3604_){
_start:
{
uint8_t v_res_3605_; lean_object* v_r_3606_; 
v_res_3605_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0(v_00_u03b1_3600_, v_cmp_3601_, v_00_u03b2_3602_, v_k_3603_, v_t_3604_);
v_r_3606_ = lean_box(v_res_3605_);
return v_r_3606_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3607_, lean_object* v_00_u03b2_3608_, lean_object* v_msg_3609_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v_msg_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1(lean_object* v_00_u03b1_3611_, lean_object* v_cmp_3612_, lean_object* v_00_u03b2_3613_, lean_object* v_k_3614_, lean_object* v_v_3615_, lean_object* v_t_3616_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3612_, v_k_3614_, v_v_3615_, v_t_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2(lean_object* v_00_u03b1_3618_, lean_object* v_00_u03b2_3619_, lean_object* v_cmp_3620_, lean_object* v_init_3621_, lean_object* v_x_3622_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3620_, v_init_3621_, v_x_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3(lean_object* v_00_u03b1_3624_, lean_object* v_00_u03b2_3625_, lean_object* v_cmp_3626_, lean_object* v_init_3627_, lean_object* v_x_3628_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3626_, v_init_3627_, v_x_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion___redArg(lean_object* v_cmp_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_3631_, 0, lean_box(0));
lean_closure_set(v___x_3631_, 1, lean_box(0));
lean_closure_set(v___x_3631_, 2, v_cmp_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion(lean_object* v_00_u03b1_3632_, lean_object* v_00_u03b2_3633_, lean_object* v_cmp_3634_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_3635_, 0, lean_box(0));
lean_closure_set(v___x_3635_, 1, lean_box(0));
lean_closure_set(v___x_3635_, 2, v_cmp_3634_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(lean_object* v_cmp_3636_, lean_object* v_k_3637_, lean_object* v_v_3638_, lean_object* v_t_3639_){
_start:
{
if (lean_obj_tag(v_t_3639_) == 0)
{
lean_object* v_size_3640_; lean_object* v_k_3641_; lean_object* v_v_3642_; lean_object* v_l_3643_; lean_object* v_r_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3925_; 
v_size_3640_ = lean_ctor_get(v_t_3639_, 0);
v_k_3641_ = lean_ctor_get(v_t_3639_, 1);
v_v_3642_ = lean_ctor_get(v_t_3639_, 2);
v_l_3643_ = lean_ctor_get(v_t_3639_, 3);
v_r_3644_ = lean_ctor_get(v_t_3639_, 4);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_t_3639_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3646_ = v_t_3639_;
v_isShared_3647_ = v_isSharedCheck_3925_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_r_3644_);
lean_inc(v_l_3643_);
lean_inc(v_v_3642_);
lean_inc(v_k_3641_);
lean_inc(v_size_3640_);
lean_dec(v_t_3639_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3925_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3648_; uint8_t v___x_3649_; 
lean_inc_ref(v_cmp_3636_);
lean_inc(v_k_3641_);
lean_inc(v_k_3637_);
v___x_3648_ = lean_apply_2(v_cmp_3636_, v_k_3637_, v_k_3641_);
v___x_3649_ = lean_unbox(v___x_3648_);
switch(v___x_3649_)
{
case 0:
{
lean_object* v_impl_3650_; lean_object* v___x_3651_; 
lean_dec(v_size_3640_);
v_impl_3650_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3636_, v_k_3637_, v_v_3638_, v_l_3643_);
v___x_3651_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3644_) == 0)
{
lean_object* v_size_3652_; lean_object* v_size_3653_; lean_object* v_k_3654_; lean_object* v_v_3655_; lean_object* v_l_3656_; lean_object* v_r_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; 
v_size_3652_ = lean_ctor_get(v_r_3644_, 0);
v_size_3653_ = lean_ctor_get(v_impl_3650_, 0);
lean_inc(v_size_3653_);
v_k_3654_ = lean_ctor_get(v_impl_3650_, 1);
lean_inc(v_k_3654_);
v_v_3655_ = lean_ctor_get(v_impl_3650_, 2);
lean_inc(v_v_3655_);
v_l_3656_ = lean_ctor_get(v_impl_3650_, 3);
lean_inc(v_l_3656_);
v_r_3657_ = lean_ctor_get(v_impl_3650_, 4);
lean_inc(v_r_3657_);
v___x_3658_ = lean_unsigned_to_nat(3u);
v___x_3659_ = lean_nat_mul(v___x_3658_, v_size_3652_);
v___x_3660_ = lean_nat_dec_lt(v___x_3659_, v_size_3653_);
lean_dec(v___x_3659_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3664_; 
lean_dec(v_r_3657_);
lean_dec(v_l_3656_);
lean_dec(v_v_3655_);
lean_dec(v_k_3654_);
v___x_3661_ = lean_nat_add(v___x_3651_, v_size_3653_);
lean_dec(v_size_3653_);
v___x_3662_ = lean_nat_add(v___x_3661_, v_size_3652_);
lean_dec(v___x_3661_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 3, v_impl_3650_);
lean_ctor_set(v___x_3646_, 0, v___x_3662_);
v___x_3664_ = v___x_3646_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3665_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3665_, 3, v_impl_3650_);
lean_ctor_set(v_reuseFailAlloc_3665_, 4, v_r_3644_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
else
{
lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3731_; 
v_isSharedCheck_3731_ = !lean_is_exclusive(v_impl_3650_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; lean_object* v_unused_3736_; 
v_unused_3732_ = lean_ctor_get(v_impl_3650_, 4);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_impl_3650_, 3);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_impl_3650_, 2);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_impl_3650_, 1);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_impl_3650_, 0);
lean_dec(v_unused_3736_);
v___x_3667_ = v_impl_3650_;
v_isShared_3668_ = v_isSharedCheck_3731_;
goto v_resetjp_3666_;
}
else
{
lean_dec(v_impl_3650_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3731_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_size_3669_; lean_object* v_size_3670_; lean_object* v_k_3671_; lean_object* v_v_3672_; lean_object* v_l_3673_; lean_object* v_r_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; uint8_t v___x_3677_; 
v_size_3669_ = lean_ctor_get(v_l_3656_, 0);
v_size_3670_ = lean_ctor_get(v_r_3657_, 0);
v_k_3671_ = lean_ctor_get(v_r_3657_, 1);
v_v_3672_ = lean_ctor_get(v_r_3657_, 2);
v_l_3673_ = lean_ctor_get(v_r_3657_, 3);
v_r_3674_ = lean_ctor_get(v_r_3657_, 4);
v___x_3675_ = lean_unsigned_to_nat(2u);
v___x_3676_ = lean_nat_mul(v___x_3675_, v_size_3669_);
v___x_3677_ = lean_nat_dec_lt(v_size_3670_, v___x_3676_);
lean_dec(v___x_3676_);
if (v___x_3677_ == 0)
{
lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3706_; 
lean_inc(v_r_3674_);
lean_inc(v_l_3673_);
lean_inc(v_v_3672_);
lean_inc(v_k_3671_);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_r_3657_);
if (v_isSharedCheck_3706_ == 0)
{
lean_object* v_unused_3707_; lean_object* v_unused_3708_; lean_object* v_unused_3709_; lean_object* v_unused_3710_; lean_object* v_unused_3711_; 
v_unused_3707_ = lean_ctor_get(v_r_3657_, 4);
lean_dec(v_unused_3707_);
v_unused_3708_ = lean_ctor_get(v_r_3657_, 3);
lean_dec(v_unused_3708_);
v_unused_3709_ = lean_ctor_get(v_r_3657_, 2);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_r_3657_, 1);
lean_dec(v_unused_3710_);
v_unused_3711_ = lean_ctor_get(v_r_3657_, 0);
lean_dec(v_unused_3711_);
v___x_3679_ = v_r_3657_;
v_isShared_3680_ = v_isSharedCheck_3706_;
goto v_resetjp_3678_;
}
else
{
lean_dec(v_r_3657_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3706_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___x_3694_; lean_object* v___y_3696_; 
v___x_3681_ = lean_nat_add(v___x_3651_, v_size_3653_);
lean_dec(v_size_3653_);
v___x_3682_ = lean_nat_add(v___x_3681_, v_size_3652_);
lean_dec(v___x_3681_);
v___x_3694_ = lean_nat_add(v___x_3651_, v_size_3669_);
if (lean_obj_tag(v_l_3673_) == 0)
{
lean_object* v_size_3704_; 
v_size_3704_ = lean_ctor_get(v_l_3673_, 0);
lean_inc(v_size_3704_);
v___y_3696_ = v_size_3704_;
goto v___jp_3695_;
}
else
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_unsigned_to_nat(0u);
v___y_3696_ = v___x_3705_;
goto v___jp_3695_;
}
v___jp_3683_:
{
lean_object* v___x_3687_; lean_object* v___x_3689_; 
v___x_3687_ = lean_nat_add(v___y_3685_, v___y_3686_);
lean_dec(v___y_3686_);
lean_dec(v___y_3685_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 4, v_r_3644_);
lean_ctor_set(v___x_3679_, 3, v_r_3674_);
lean_ctor_set(v___x_3679_, 2, v_v_3642_);
lean_ctor_set(v___x_3679_, 1, v_k_3641_);
lean_ctor_set(v___x_3679_, 0, v___x_3687_);
v___x_3689_ = v___x_3679_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3687_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3693_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3693_, 3, v_r_3674_);
lean_ctor_set(v_reuseFailAlloc_3693_, 4, v_r_3644_);
v___x_3689_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
lean_object* v___x_3691_; 
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 4, v___x_3689_);
lean_ctor_set(v___x_3667_, 3, v___y_3684_);
lean_ctor_set(v___x_3667_, 2, v_v_3672_);
lean_ctor_set(v___x_3667_, 1, v_k_3671_);
lean_ctor_set(v___x_3667_, 0, v___x_3682_);
v___x_3691_ = v___x_3667_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_k_3671_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v_v_3672_);
lean_ctor_set(v_reuseFailAlloc_3692_, 3, v___y_3684_);
lean_ctor_set(v_reuseFailAlloc_3692_, 4, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
v___jp_3695_:
{
lean_object* v___x_3697_; lean_object* v___x_3699_; 
v___x_3697_ = lean_nat_add(v___x_3694_, v___y_3696_);
lean_dec(v___y_3696_);
lean_dec(v___x_3694_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 4, v_l_3673_);
lean_ctor_set(v___x_3646_, 3, v_l_3656_);
lean_ctor_set(v___x_3646_, 2, v_v_3655_);
lean_ctor_set(v___x_3646_, 1, v_k_3654_);
lean_ctor_set(v___x_3646_, 0, v___x_3697_);
v___x_3699_ = v___x_3646_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3697_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_k_3654_);
lean_ctor_set(v_reuseFailAlloc_3703_, 2, v_v_3655_);
lean_ctor_set(v_reuseFailAlloc_3703_, 3, v_l_3656_);
lean_ctor_set(v_reuseFailAlloc_3703_, 4, v_l_3673_);
v___x_3699_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_nat_add(v___x_3651_, v_size_3652_);
if (lean_obj_tag(v_r_3674_) == 0)
{
lean_object* v_size_3701_; 
v_size_3701_ = lean_ctor_get(v_r_3674_, 0);
lean_inc(v_size_3701_);
v___y_3684_ = v___x_3699_;
v___y_3685_ = v___x_3700_;
v___y_3686_ = v_size_3701_;
goto v___jp_3683_;
}
else
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_unsigned_to_nat(0u);
v___y_3684_ = v___x_3699_;
v___y_3685_ = v___x_3700_;
v___y_3686_ = v___x_3702_;
goto v___jp_3683_;
}
}
}
}
}
else
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3717_; 
lean_del_object(v___x_3646_);
v___x_3712_ = lean_nat_add(v___x_3651_, v_size_3653_);
lean_dec(v_size_3653_);
v___x_3713_ = lean_nat_add(v___x_3712_, v_size_3652_);
lean_dec(v___x_3712_);
v___x_3714_ = lean_nat_add(v___x_3651_, v_size_3652_);
v___x_3715_ = lean_nat_add(v___x_3714_, v_size_3670_);
lean_dec(v___x_3714_);
lean_inc_ref(v_r_3644_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 4, v_r_3644_);
lean_ctor_set(v___x_3667_, 3, v_r_3657_);
lean_ctor_set(v___x_3667_, 2, v_v_3642_);
lean_ctor_set(v___x_3667_, 1, v_k_3641_);
lean_ctor_set(v___x_3667_, 0, v___x_3715_);
v___x_3717_ = v___x_3667_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3715_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v_r_3657_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v_r_3644_);
v___x_3717_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
v_isSharedCheck_3724_ = !lean_is_exclusive(v_r_3644_);
if (v_isSharedCheck_3724_ == 0)
{
lean_object* v_unused_3725_; lean_object* v_unused_3726_; lean_object* v_unused_3727_; lean_object* v_unused_3728_; lean_object* v_unused_3729_; 
v_unused_3725_ = lean_ctor_get(v_r_3644_, 4);
lean_dec(v_unused_3725_);
v_unused_3726_ = lean_ctor_get(v_r_3644_, 3);
lean_dec(v_unused_3726_);
v_unused_3727_ = lean_ctor_get(v_r_3644_, 2);
lean_dec(v_unused_3727_);
v_unused_3728_ = lean_ctor_get(v_r_3644_, 1);
lean_dec(v_unused_3728_);
v_unused_3729_ = lean_ctor_get(v_r_3644_, 0);
lean_dec(v_unused_3729_);
v___x_3719_ = v_r_3644_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_dec(v_r_3644_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 4, v___x_3717_);
lean_ctor_set(v___x_3719_, 3, v_l_3656_);
lean_ctor_set(v___x_3719_, 2, v_v_3655_);
lean_ctor_set(v___x_3719_, 1, v_k_3654_);
lean_ctor_set(v___x_3719_, 0, v___x_3713_);
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3713_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_k_3654_);
lean_ctor_set(v_reuseFailAlloc_3723_, 2, v_v_3655_);
lean_ctor_set(v_reuseFailAlloc_3723_, 3, v_l_3656_);
lean_ctor_set(v_reuseFailAlloc_3723_, 4, v___x_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3737_; 
v_l_3737_ = lean_ctor_get(v_impl_3650_, 3);
lean_inc(v_l_3737_);
if (lean_obj_tag(v_l_3737_) == 0)
{
lean_object* v_r_3738_; lean_object* v_k_3739_; lean_object* v_v_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3751_; 
v_r_3738_ = lean_ctor_get(v_impl_3650_, 4);
v_k_3739_ = lean_ctor_get(v_impl_3650_, 1);
v_v_3740_ = lean_ctor_get(v_impl_3650_, 2);
v_isSharedCheck_3751_ = !lean_is_exclusive(v_impl_3650_);
if (v_isSharedCheck_3751_ == 0)
{
lean_object* v_unused_3752_; lean_object* v_unused_3753_; 
v_unused_3752_ = lean_ctor_get(v_impl_3650_, 3);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_impl_3650_, 0);
lean_dec(v_unused_3753_);
v___x_3742_ = v_impl_3650_;
v_isShared_3743_ = v_isSharedCheck_3751_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_r_3738_);
lean_inc(v_v_3740_);
lean_inc(v_k_3739_);
lean_dec(v_impl_3650_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3751_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; lean_object* v___x_3746_; 
v___x_3744_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3738_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 3, v_r_3738_);
lean_ctor_set(v___x_3742_, 2, v_v_3642_);
lean_ctor_set(v___x_3742_, 1, v_k_3641_);
lean_ctor_set(v___x_3742_, 0, v___x_3651_);
v___x_3746_ = v___x_3742_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3651_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3750_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3750_, 3, v_r_3738_);
lean_ctor_set(v_reuseFailAlloc_3750_, 4, v_r_3738_);
v___x_3746_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3748_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 4, v___x_3746_);
lean_ctor_set(v___x_3646_, 3, v_l_3737_);
lean_ctor_set(v___x_3646_, 2, v_v_3740_);
lean_ctor_set(v___x_3646_, 1, v_k_3739_);
lean_ctor_set(v___x_3646_, 0, v___x_3744_);
v___x_3748_ = v___x_3646_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_k_3739_);
lean_ctor_set(v_reuseFailAlloc_3749_, 2, v_v_3740_);
lean_ctor_set(v_reuseFailAlloc_3749_, 3, v_l_3737_);
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
else
{
lean_object* v_r_3754_; 
v_r_3754_ = lean_ctor_get(v_impl_3650_, 4);
lean_inc(v_r_3754_);
if (lean_obj_tag(v_r_3754_) == 0)
{
lean_object* v_k_3755_; lean_object* v_v_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3779_; 
v_k_3755_ = lean_ctor_get(v_impl_3650_, 1);
v_v_3756_ = lean_ctor_get(v_impl_3650_, 2);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_impl_3650_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; lean_object* v_unused_3781_; lean_object* v_unused_3782_; 
v_unused_3780_ = lean_ctor_get(v_impl_3650_, 4);
lean_dec(v_unused_3780_);
v_unused_3781_ = lean_ctor_get(v_impl_3650_, 3);
lean_dec(v_unused_3781_);
v_unused_3782_ = lean_ctor_get(v_impl_3650_, 0);
lean_dec(v_unused_3782_);
v___x_3758_ = v_impl_3650_;
v_isShared_3759_ = v_isSharedCheck_3779_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_v_3756_);
lean_inc(v_k_3755_);
lean_dec(v_impl_3650_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3779_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v_k_3760_; lean_object* v_v_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3775_; 
v_k_3760_ = lean_ctor_get(v_r_3754_, 1);
v_v_3761_ = lean_ctor_get(v_r_3754_, 2);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_r_3754_);
if (v_isSharedCheck_3775_ == 0)
{
lean_object* v_unused_3776_; lean_object* v_unused_3777_; lean_object* v_unused_3778_; 
v_unused_3776_ = lean_ctor_get(v_r_3754_, 4);
lean_dec(v_unused_3776_);
v_unused_3777_ = lean_ctor_get(v_r_3754_, 3);
lean_dec(v_unused_3777_);
v_unused_3778_ = lean_ctor_get(v_r_3754_, 0);
lean_dec(v_unused_3778_);
v___x_3763_ = v_r_3754_;
v_isShared_3764_ = v_isSharedCheck_3775_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_v_3761_);
lean_inc(v_k_3760_);
lean_dec(v_r_3754_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3775_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
v___x_3765_ = lean_unsigned_to_nat(3u);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 4, v_l_3737_);
lean_ctor_set(v___x_3763_, 3, v_l_3737_);
lean_ctor_set(v___x_3763_, 2, v_v_3756_);
lean_ctor_set(v___x_3763_, 1, v_k_3755_);
lean_ctor_set(v___x_3763_, 0, v___x_3651_);
v___x_3767_ = v___x_3763_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3651_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_k_3755_);
lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_v_3756_);
lean_ctor_set(v_reuseFailAlloc_3774_, 3, v_l_3737_);
lean_ctor_set(v_reuseFailAlloc_3774_, 4, v_l_3737_);
v___x_3767_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
lean_object* v___x_3769_; 
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 4, v_l_3737_);
lean_ctor_set(v___x_3758_, 2, v_v_3642_);
lean_ctor_set(v___x_3758_, 1, v_k_3641_);
lean_ctor_set(v___x_3758_, 0, v___x_3651_);
v___x_3769_ = v___x_3758_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3651_);
lean_ctor_set(v_reuseFailAlloc_3773_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3773_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3773_, 3, v_l_3737_);
lean_ctor_set(v_reuseFailAlloc_3773_, 4, v_l_3737_);
v___x_3769_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3771_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 4, v___x_3769_);
lean_ctor_set(v___x_3646_, 3, v___x_3767_);
lean_ctor_set(v___x_3646_, 2, v_v_3761_);
lean_ctor_set(v___x_3646_, 1, v_k_3760_);
lean_ctor_set(v___x_3646_, 0, v___x_3765_);
v___x_3771_ = v___x_3646_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_k_3760_);
lean_ctor_set(v_reuseFailAlloc_3772_, 2, v_v_3761_);
lean_ctor_set(v_reuseFailAlloc_3772_, 3, v___x_3767_);
lean_ctor_set(v_reuseFailAlloc_3772_, 4, v___x_3769_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
}
else
{
lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___x_3783_ = lean_unsigned_to_nat(2u);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 4, v_r_3754_);
lean_ctor_set(v___x_3646_, 3, v_impl_3650_);
lean_ctor_set(v___x_3646_, 0, v___x_3783_);
v___x_3785_ = v___x_3646_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3786_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3786_, 3, v_impl_3650_);
lean_ctor_set(v_reuseFailAlloc_3786_, 4, v_r_3754_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3788_; 
lean_dec(v_v_3642_);
lean_dec(v_k_3641_);
lean_dec_ref(v_cmp_3636_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 2, v_v_3638_);
lean_ctor_set(v___x_3646_, 1, v_k_3637_);
v___x_3788_ = v___x_3646_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_size_3640_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_k_3637_);
lean_ctor_set(v_reuseFailAlloc_3789_, 2, v_v_3638_);
lean_ctor_set(v_reuseFailAlloc_3789_, 3, v_l_3643_);
lean_ctor_set(v_reuseFailAlloc_3789_, 4, v_r_3644_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
default: 
{
lean_object* v_impl_3790_; lean_object* v___x_3791_; 
lean_dec(v_size_3640_);
v_impl_3790_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3636_, v_k_3637_, v_v_3638_, v_r_3644_);
v___x_3791_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3643_) == 0)
{
lean_object* v_size_3792_; lean_object* v_size_3793_; lean_object* v_k_3794_; lean_object* v_v_3795_; lean_object* v_l_3796_; lean_object* v_r_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; 
v_size_3792_ = lean_ctor_get(v_l_3643_, 0);
v_size_3793_ = lean_ctor_get(v_impl_3790_, 0);
lean_inc(v_size_3793_);
v_k_3794_ = lean_ctor_get(v_impl_3790_, 1);
lean_inc(v_k_3794_);
v_v_3795_ = lean_ctor_get(v_impl_3790_, 2);
lean_inc(v_v_3795_);
v_l_3796_ = lean_ctor_get(v_impl_3790_, 3);
lean_inc(v_l_3796_);
v_r_3797_ = lean_ctor_get(v_impl_3790_, 4);
lean_inc(v_r_3797_);
v___x_3798_ = lean_unsigned_to_nat(3u);
v___x_3799_ = lean_nat_mul(v___x_3798_, v_size_3792_);
v___x_3800_ = lean_nat_dec_lt(v___x_3799_, v_size_3793_);
lean_dec(v___x_3799_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3804_; 
lean_dec(v_r_3797_);
lean_dec(v_l_3796_);
lean_dec(v_v_3795_);
lean_dec(v_k_3794_);
v___x_3801_ = lean_nat_add(v___x_3791_, v_size_3792_);
v___x_3802_ = lean_nat_add(v___x_3801_, v_size_3793_);
lean_dec(v_size_3793_);
lean_dec(v___x_3801_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 4, v_impl_3790_);
lean_ctor_set(v___x_3646_, 0, v___x_3802_);
v___x_3804_ = v___x_3646_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3802_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3805_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3805_, 3, v_l_3643_);
lean_ctor_set(v_reuseFailAlloc_3805_, 4, v_impl_3790_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
else
{
lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3869_; 
v_isSharedCheck_3869_ = !lean_is_exclusive(v_impl_3790_);
if (v_isSharedCheck_3869_ == 0)
{
lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; lean_object* v_unused_3873_; lean_object* v_unused_3874_; 
v_unused_3870_ = lean_ctor_get(v_impl_3790_, 4);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_impl_3790_, 3);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_impl_3790_, 2);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_impl_3790_, 1);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_impl_3790_, 0);
lean_dec(v_unused_3874_);
v___x_3807_ = v_impl_3790_;
v_isShared_3808_ = v_isSharedCheck_3869_;
goto v_resetjp_3806_;
}
else
{
lean_dec(v_impl_3790_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3869_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v_size_3809_; lean_object* v_k_3810_; lean_object* v_v_3811_; lean_object* v_l_3812_; lean_object* v_r_3813_; lean_object* v_size_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v_size_3809_ = lean_ctor_get(v_l_3796_, 0);
v_k_3810_ = lean_ctor_get(v_l_3796_, 1);
v_v_3811_ = lean_ctor_get(v_l_3796_, 2);
v_l_3812_ = lean_ctor_get(v_l_3796_, 3);
v_r_3813_ = lean_ctor_get(v_l_3796_, 4);
v_size_3814_ = lean_ctor_get(v_r_3797_, 0);
v___x_3815_ = lean_unsigned_to_nat(2u);
v___x_3816_ = lean_nat_mul(v___x_3815_, v_size_3814_);
v___x_3817_ = lean_nat_dec_lt(v_size_3809_, v___x_3816_);
lean_dec(v___x_3816_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3845_; 
lean_inc(v_r_3813_);
lean_inc(v_l_3812_);
lean_inc(v_v_3811_);
lean_inc(v_k_3810_);
v_isSharedCheck_3845_ = !lean_is_exclusive(v_l_3796_);
if (v_isSharedCheck_3845_ == 0)
{
lean_object* v_unused_3846_; lean_object* v_unused_3847_; lean_object* v_unused_3848_; lean_object* v_unused_3849_; lean_object* v_unused_3850_; 
v_unused_3846_ = lean_ctor_get(v_l_3796_, 4);
lean_dec(v_unused_3846_);
v_unused_3847_ = lean_ctor_get(v_l_3796_, 3);
lean_dec(v_unused_3847_);
v_unused_3848_ = lean_ctor_get(v_l_3796_, 2);
lean_dec(v_unused_3848_);
v_unused_3849_ = lean_ctor_get(v_l_3796_, 1);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_l_3796_, 0);
lean_dec(v_unused_3850_);
v___x_3819_ = v_l_3796_;
v_isShared_3820_ = v_isSharedCheck_3845_;
goto v_resetjp_3818_;
}
else
{
lean_dec(v_l_3796_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3845_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3835_; 
v___x_3821_ = lean_nat_add(v___x_3791_, v_size_3792_);
v___x_3822_ = lean_nat_add(v___x_3821_, v_size_3793_);
lean_dec(v_size_3793_);
if (lean_obj_tag(v_l_3812_) == 0)
{
lean_object* v_size_3843_; 
v_size_3843_ = lean_ctor_get(v_l_3812_, 0);
lean_inc(v_size_3843_);
v___y_3835_ = v_size_3843_;
goto v___jp_3834_;
}
else
{
lean_object* v___x_3844_; 
v___x_3844_ = lean_unsigned_to_nat(0u);
v___y_3835_ = v___x_3844_;
goto v___jp_3834_;
}
v___jp_3823_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = lean_nat_add(v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec(v___y_3825_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 4, v_r_3797_);
lean_ctor_set(v___x_3819_, 3, v_r_3813_);
lean_ctor_set(v___x_3819_, 2, v_v_3795_);
lean_ctor_set(v___x_3819_, 1, v_k_3794_);
lean_ctor_set(v___x_3819_, 0, v___x_3827_);
v___x_3829_ = v___x_3819_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3827_);
lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_k_3794_);
lean_ctor_set(v_reuseFailAlloc_3833_, 2, v_v_3795_);
lean_ctor_set(v_reuseFailAlloc_3833_, 3, v_r_3813_);
lean_ctor_set(v_reuseFailAlloc_3833_, 4, v_r_3797_);
v___x_3829_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3831_; 
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 4, v___x_3829_);
lean_ctor_set(v___x_3807_, 3, v___y_3824_);
lean_ctor_set(v___x_3807_, 2, v_v_3811_);
lean_ctor_set(v___x_3807_, 1, v_k_3810_);
lean_ctor_set(v___x_3807_, 0, v___x_3822_);
v___x_3831_ = v___x_3807_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_k_3810_);
lean_ctor_set(v_reuseFailAlloc_3832_, 2, v_v_3811_);
lean_ctor_set(v_reuseFailAlloc_3832_, 3, v___y_3824_);
lean_ctor_set(v_reuseFailAlloc_3832_, 4, v___x_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
v___jp_3834_:
{
lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3836_ = lean_nat_add(v___x_3821_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec(v___x_3821_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 4, v_l_3812_);
lean_ctor_set(v___x_3646_, 0, v___x_3836_);
v___x_3838_ = v___x_3646_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3836_);
lean_ctor_set(v_reuseFailAlloc_3842_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3842_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3842_, 3, v_l_3643_);
lean_ctor_set(v_reuseFailAlloc_3842_, 4, v_l_3812_);
v___x_3838_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3839_; 
v___x_3839_ = lean_nat_add(v___x_3791_, v_size_3814_);
if (lean_obj_tag(v_r_3813_) == 0)
{
lean_object* v_size_3840_; 
v_size_3840_ = lean_ctor_get(v_r_3813_, 0);
lean_inc(v_size_3840_);
v___y_3824_ = v___x_3838_;
v___y_3825_ = v___x_3839_;
v___y_3826_ = v_size_3840_;
goto v___jp_3823_;
}
else
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_unsigned_to_nat(0u);
v___y_3824_ = v___x_3838_;
v___y_3825_ = v___x_3839_;
v___y_3826_ = v___x_3841_;
goto v___jp_3823_;
}
}
}
}
}
else
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3855_; 
lean_del_object(v___x_3646_);
v___x_3851_ = lean_nat_add(v___x_3791_, v_size_3792_);
v___x_3852_ = lean_nat_add(v___x_3851_, v_size_3793_);
lean_dec(v_size_3793_);
v___x_3853_ = lean_nat_add(v___x_3851_, v_size_3809_);
lean_dec(v___x_3851_);
lean_inc_ref(v_l_3643_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 4, v_l_3796_);
lean_ctor_set(v___x_3807_, 3, v_l_3643_);
lean_ctor_set(v___x_3807_, 2, v_v_3642_);
lean_ctor_set(v___x_3807_, 1, v_k_3641_);
lean_ctor_set(v___x_3807_, 0, v___x_3853_);
v___x_3855_ = v___x_3807_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3868_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3868_, 3, v_l_3643_);
lean_ctor_set(v_reuseFailAlloc_3868_, 4, v_l_3796_);
v___x_3855_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
v_isSharedCheck_3862_ = !lean_is_exclusive(v_l_3643_);
if (v_isSharedCheck_3862_ == 0)
{
lean_object* v_unused_3863_; lean_object* v_unused_3864_; lean_object* v_unused_3865_; lean_object* v_unused_3866_; lean_object* v_unused_3867_; 
v_unused_3863_ = lean_ctor_get(v_l_3643_, 4);
lean_dec(v_unused_3863_);
v_unused_3864_ = lean_ctor_get(v_l_3643_, 3);
lean_dec(v_unused_3864_);
v_unused_3865_ = lean_ctor_get(v_l_3643_, 2);
lean_dec(v_unused_3865_);
v_unused_3866_ = lean_ctor_get(v_l_3643_, 1);
lean_dec(v_unused_3866_);
v_unused_3867_ = lean_ctor_get(v_l_3643_, 0);
lean_dec(v_unused_3867_);
v___x_3857_ = v_l_3643_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_dec(v_l_3643_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 4, v_r_3797_);
lean_ctor_set(v___x_3857_, 3, v___x_3855_);
lean_ctor_set(v___x_3857_, 2, v_v_3795_);
lean_ctor_set(v___x_3857_, 1, v_k_3794_);
lean_ctor_set(v___x_3857_, 0, v___x_3852_);
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3861_, 1, v_k_3794_);
lean_ctor_set(v_reuseFailAlloc_3861_, 2, v_v_3795_);
lean_ctor_set(v_reuseFailAlloc_3861_, 3, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_3861_, 4, v_r_3797_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3875_; 
v_l_3875_ = lean_ctor_get(v_impl_3790_, 3);
lean_inc(v_l_3875_);
if (lean_obj_tag(v_l_3875_) == 0)
{
lean_object* v_r_3876_; lean_object* v_k_3877_; lean_object* v_v_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3901_; 
v_r_3876_ = lean_ctor_get(v_impl_3790_, 4);
v_k_3877_ = lean_ctor_get(v_impl_3790_, 1);
v_v_3878_ = lean_ctor_get(v_impl_3790_, 2);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_impl_3790_);
if (v_isSharedCheck_3901_ == 0)
{
lean_object* v_unused_3902_; lean_object* v_unused_3903_; 
v_unused_3902_ = lean_ctor_get(v_impl_3790_, 3);
lean_dec(v_unused_3902_);
v_unused_3903_ = lean_ctor_get(v_impl_3790_, 0);
lean_dec(v_unused_3903_);
v___x_3880_ = v_impl_3790_;
v_isShared_3881_ = v_isSharedCheck_3901_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_r_3876_);
lean_inc(v_v_3878_);
lean_inc(v_k_3877_);
lean_dec(v_impl_3790_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3901_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v_k_3882_; lean_object* v_v_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3897_; 
v_k_3882_ = lean_ctor_get(v_l_3875_, 1);
v_v_3883_ = lean_ctor_get(v_l_3875_, 2);
v_isSharedCheck_3897_ = !lean_is_exclusive(v_l_3875_);
if (v_isSharedCheck_3897_ == 0)
{
lean_object* v_unused_3898_; lean_object* v_unused_3899_; lean_object* v_unused_3900_; 
v_unused_3898_ = lean_ctor_get(v_l_3875_, 4);
lean_dec(v_unused_3898_);
v_unused_3899_ = lean_ctor_get(v_l_3875_, 3);
lean_dec(v_unused_3899_);
v_unused_3900_ = lean_ctor_get(v_l_3875_, 0);
lean_dec(v_unused_3900_);
v___x_3885_ = v_l_3875_;
v_isShared_3886_ = v_isSharedCheck_3897_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_v_3883_);
lean_inc(v_k_3882_);
lean_dec(v_l_3875_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3897_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3887_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3876_, 2);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 4, v_r_3876_);
lean_ctor_set(v___x_3885_, 3, v_r_3876_);
lean_ctor_set(v___x_3885_, 2, v_v_3642_);
lean_ctor_set(v___x_3885_, 1, v_k_3641_);
lean_ctor_set(v___x_3885_, 0, v___x_3791_);
v___x_3889_ = v___x_3885_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3791_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3896_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3896_, 3, v_r_3876_);
lean_ctor_set(v_reuseFailAlloc_3896_, 4, v_r_3876_);
v___x_3889_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3891_; 
lean_inc(v_r_3876_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 3, v_r_3876_);
lean_ctor_set(v___x_3880_, 0, v___x_3791_);
v___x_3891_ = v___x_3880_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3791_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v_k_3877_);
lean_ctor_set(v_reuseFailAlloc_3895_, 2, v_v_3878_);
lean_ctor_set(v_reuseFailAlloc_3895_, 3, v_r_3876_);
lean_ctor_set(v_reuseFailAlloc_3895_, 4, v_r_3876_);
v___x_3891_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
lean_object* v___x_3893_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 4, v___x_3891_);
lean_ctor_set(v___x_3646_, 3, v___x_3889_);
lean_ctor_set(v___x_3646_, 2, v_v_3883_);
lean_ctor_set(v___x_3646_, 1, v_k_3882_);
lean_ctor_set(v___x_3646_, 0, v___x_3887_);
v___x_3893_ = v___x_3646_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3887_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_k_3882_);
lean_ctor_set(v_reuseFailAlloc_3894_, 2, v_v_3883_);
lean_ctor_set(v_reuseFailAlloc_3894_, 3, v___x_3889_);
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
}
}
}
else
{
lean_object* v_r_3904_; 
v_r_3904_ = lean_ctor_get(v_impl_3790_, 4);
lean_inc(v_r_3904_);
if (lean_obj_tag(v_r_3904_) == 0)
{
lean_object* v_k_3905_; lean_object* v_v_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3917_; 
v_k_3905_ = lean_ctor_get(v_impl_3790_, 1);
v_v_3906_ = lean_ctor_get(v_impl_3790_, 2);
v_isSharedCheck_3917_ = !lean_is_exclusive(v_impl_3790_);
if (v_isSharedCheck_3917_ == 0)
{
lean_object* v_unused_3918_; lean_object* v_unused_3919_; lean_object* v_unused_3920_; 
v_unused_3918_ = lean_ctor_get(v_impl_3790_, 4);
lean_dec(v_unused_3918_);
v_unused_3919_ = lean_ctor_get(v_impl_3790_, 3);
lean_dec(v_unused_3919_);
v_unused_3920_ = lean_ctor_get(v_impl_3790_, 0);
lean_dec(v_unused_3920_);
v___x_3908_ = v_impl_3790_;
v_isShared_3909_ = v_isSharedCheck_3917_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_v_3906_);
lean_inc(v_k_3905_);
lean_dec(v_impl_3790_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3917_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3910_ = lean_unsigned_to_nat(3u);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 4, v_l_3875_);
lean_ctor_set(v___x_3908_, 2, v_v_3642_);
lean_ctor_set(v___x_3908_, 1, v_k_3641_);
lean_ctor_set(v___x_3908_, 0, v___x_3791_);
v___x_3912_ = v___x_3908_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3791_);
lean_ctor_set(v_reuseFailAlloc_3916_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3916_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3916_, 3, v_l_3875_);
lean_ctor_set(v_reuseFailAlloc_3916_, 4, v_l_3875_);
v___x_3912_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3914_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 4, v_r_3904_);
lean_ctor_set(v___x_3646_, 3, v___x_3912_);
lean_ctor_set(v___x_3646_, 2, v_v_3906_);
lean_ctor_set(v___x_3646_, 1, v_k_3905_);
lean_ctor_set(v___x_3646_, 0, v___x_3910_);
v___x_3914_ = v___x_3646_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_k_3905_);
lean_ctor_set(v_reuseFailAlloc_3915_, 2, v_v_3906_);
lean_ctor_set(v_reuseFailAlloc_3915_, 3, v___x_3912_);
lean_ctor_set(v_reuseFailAlloc_3915_, 4, v_r_3904_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
else
{
lean_object* v___x_3921_; lean_object* v___x_3923_; 
v___x_3921_ = lean_unsigned_to_nat(2u);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 4, v_impl_3790_);
lean_ctor_set(v___x_3646_, 3, v_r_3904_);
lean_ctor_set(v___x_3646_, 0, v___x_3921_);
v___x_3923_ = v___x_3646_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_3924_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3924_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3924_, 3, v_r_3904_);
lean_ctor_set(v_reuseFailAlloc_3924_, 4, v_impl_3790_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
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
lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_dec_ref(v_cmp_3636_);
v___x_3926_ = lean_unsigned_to_nat(1u);
v___x_3927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
lean_ctor_set(v___x_3927_, 1, v_k_3637_);
lean_ctor_set(v___x_3927_, 2, v_v_3638_);
lean_ctor_set(v___x_3927_, 3, v_t_3639_);
lean_ctor_set(v___x_3927_, 4, v_t_3639_);
return v___x_3927_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_3928_, lean_object* v_t_3929_, lean_object* v_k_3930_){
_start:
{
if (lean_obj_tag(v_t_3929_) == 0)
{
lean_object* v_k_3931_; lean_object* v_v_3932_; lean_object* v_l_3933_; lean_object* v_r_3934_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
v_k_3931_ = lean_ctor_get(v_t_3929_, 1);
lean_inc_n(v_k_3931_, 2);
v_v_3932_ = lean_ctor_get(v_t_3929_, 2);
lean_inc(v_v_3932_);
v_l_3933_ = lean_ctor_get(v_t_3929_, 3);
lean_inc(v_l_3933_);
v_r_3934_ = lean_ctor_get(v_t_3929_, 4);
lean_inc(v_r_3934_);
lean_dec_ref(v_t_3929_);
lean_inc_ref(v_cmp_3928_);
lean_inc(v_k_3930_);
v___x_3935_ = lean_apply_2(v_cmp_3928_, v_k_3930_, v_k_3931_);
v___x_3936_ = lean_unbox(v___x_3935_);
switch(v___x_3936_)
{
case 0:
{
lean_dec(v_r_3934_);
lean_dec(v_v_3932_);
lean_dec(v_k_3931_);
v_t_3929_ = v_l_3933_;
goto _start;
}
case 1:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_dec(v_r_3934_);
lean_dec(v_l_3933_);
lean_dec(v_k_3930_);
lean_dec_ref(v_cmp_3928_);
v___x_3938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3938_, 0, v_k_3931_);
lean_ctor_set(v___x_3938_, 1, v_v_3932_);
v___x_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
return v___x_3939_;
}
default: 
{
lean_dec(v_l_3933_);
lean_dec(v_v_3932_);
lean_dec(v_k_3931_);
v_t_3929_ = v_r_3934_;
goto _start;
}
}
}
else
{
lean_object* v___x_3941_; 
lean_dec(v_k_3930_);
lean_dec_ref(v_cmp_3928_);
v___x_3941_ = lean_box(0);
return v___x_3941_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_cmp_3942_, lean_object* v_m_u2081_3943_, lean_object* v_init_3944_, lean_object* v_x_3945_){
_start:
{
if (lean_obj_tag(v_x_3945_) == 0)
{
lean_object* v_k_3946_; lean_object* v_l_3947_; lean_object* v_r_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v_k_3946_ = lean_ctor_get(v_x_3945_, 1);
lean_inc(v_k_3946_);
v_l_3947_ = lean_ctor_get(v_x_3945_, 3);
lean_inc(v_l_3947_);
v_r_3948_ = lean_ctor_get(v_x_3945_, 4);
lean_inc(v_r_3948_);
lean_dec_ref(v_x_3945_);
lean_inc_n(v_m_u2081_3943_, 2);
lean_inc_ref_n(v_cmp_3942_, 2);
v___x_3949_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3942_, v_m_u2081_3943_, v_init_3944_, v_l_3947_);
v___x_3950_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3942_, v_m_u2081_3943_, v_k_3946_);
if (lean_obj_tag(v___x_3950_) == 0)
{
v_init_3944_ = v___x_3949_;
v_x_3945_ = v_r_3948_;
goto _start;
}
else
{
lean_object* v_val_3952_; lean_object* v_fst_3953_; lean_object* v_snd_3954_; lean_object* v_impl_3955_; 
v_val_3952_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_val_3952_);
lean_dec_ref(v___x_3950_);
v_fst_3953_ = lean_ctor_get(v_val_3952_, 0);
lean_inc(v_fst_3953_);
v_snd_3954_ = lean_ctor_get(v_val_3952_, 1);
lean_inc(v_snd_3954_);
lean_dec(v_val_3952_);
lean_inc_ref(v_cmp_3942_);
v_impl_3955_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3942_, v_fst_3953_, v_snd_3954_, v___x_3949_);
v_init_3944_ = v_impl_3955_;
v_x_3945_ = v_r_3948_;
goto _start;
}
}
else
{
lean_dec(v_m_u2081_3943_);
lean_dec_ref(v_cmp_3942_);
return v_init_3944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(lean_object* v_cmp_3957_, lean_object* v_m_u2081_3958_, lean_object* v_m_u2082_3959_){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = lean_box(1);
v___x_3961_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3957_, v_m_u2081_3958_, v___x_3960_, v_m_u2082_3959_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(lean_object* v_cmp_3962_, lean_object* v_m_u2082_3963_, lean_object* v_t_3964_){
_start:
{
if (lean_obj_tag(v_t_3964_) == 0)
{
lean_object* v_k_3965_; lean_object* v_v_3966_; lean_object* v_l_3967_; lean_object* v_r_3968_; uint8_t v___x_3969_; 
v_k_3965_ = lean_ctor_get(v_t_3964_, 1);
lean_inc_n(v_k_3965_, 2);
v_v_3966_ = lean_ctor_get(v_t_3964_, 2);
lean_inc(v_v_3966_);
v_l_3967_ = lean_ctor_get(v_t_3964_, 3);
lean_inc(v_l_3967_);
v_r_3968_ = lean_ctor_get(v_t_3964_, 4);
lean_inc(v_r_3968_);
lean_dec_ref(v_t_3964_);
lean_inc(v_m_u2082_3963_);
lean_inc_ref(v_cmp_3962_);
v___x_3969_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3962_, v_k_3965_, v_m_u2082_3963_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
lean_dec(v_v_3966_);
lean_dec(v_k_3965_);
lean_inc(v_m_u2082_3963_);
lean_inc_ref(v_cmp_3962_);
v___x_3970_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3962_, v_m_u2082_3963_, v_l_3967_);
v___x_3971_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3962_, v_m_u2082_3963_, v_r_3968_);
v___x_3972_ = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(v___x_3970_, v___x_3971_);
return v___x_3972_;
}
else
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
lean_inc(v_m_u2082_3963_);
lean_inc_ref(v_cmp_3962_);
v___x_3973_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3962_, v_m_u2082_3963_, v_l_3967_);
v___x_3974_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3962_, v_m_u2082_3963_, v_r_3968_);
v___x_3975_ = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(v_k_3965_, v_v_3966_, v___x_3973_, v___x_3974_);
return v___x_3975_;
}
}
else
{
lean_dec(v_m_u2082_3963_);
lean_dec_ref(v_cmp_3962_);
return v_t_3964_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(lean_object* v_cmp_3976_, lean_object* v_m_u2081_3977_, lean_object* v_m_u2082_3978_){
_start:
{
lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3986_; 
if (lean_obj_tag(v_m_u2081_3977_) == 0)
{
lean_object* v_size_3989_; 
v_size_3989_ = lean_ctor_get(v_m_u2081_3977_, 0);
lean_inc(v_size_3989_);
v___y_3986_ = v_size_3989_;
goto v___jp_3985_;
}
else
{
lean_object* v___x_3990_; 
v___x_3990_ = lean_unsigned_to_nat(0u);
v___y_3986_ = v___x_3990_;
goto v___jp_3985_;
}
v___jp_3979_:
{
uint8_t v___x_3982_; 
v___x_3982_ = lean_nat_dec_le(v___y_3980_, v___y_3981_);
lean_dec(v___y_3981_);
lean_dec(v___y_3980_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; 
v___x_3983_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(v_cmp_3976_, v_m_u2081_3977_, v_m_u2082_3978_);
return v___x_3983_;
}
else
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3976_, v_m_u2082_3978_, v_m_u2081_3977_);
return v___x_3984_;
}
}
v___jp_3985_:
{
if (lean_obj_tag(v_m_u2082_3978_) == 0)
{
lean_object* v_size_3987_; 
v_size_3987_ = lean_ctor_get(v_m_u2082_3978_, 0);
lean_inc(v_size_3987_);
v___y_3980_ = v___y_3986_;
v___y_3981_ = v_size_3987_;
goto v___jp_3979_;
}
else
{
lean_object* v___x_3988_; 
v___x_3988_ = lean_unsigned_to_nat(0u);
v___y_3980_ = v___y_3986_;
v___y_3981_ = v___x_3988_;
goto v___jp_3979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter___redArg(lean_object* v_cmp_3991_, lean_object* v_t_u2081_3992_, lean_object* v_t_u2082_3993_){
_start:
{
lean_object* v___x_3994_; 
v___x_3994_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_3991_, v_t_u2081_3992_, v_t_u2082_3993_);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter(lean_object* v_00_u03b1_3995_, lean_object* v_00_u03b2_3996_, lean_object* v_cmp_3997_, lean_object* v_t_u2081_3998_, lean_object* v_t_u2082_3999_){
_start:
{
lean_object* v___x_4000_; 
v___x_4000_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_3997_, v_t_u2081_3998_, v_t_u2082_3999_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0(lean_object* v_00_u03b1_4001_, lean_object* v_cmp_4002_, lean_object* v_00_u03b2_4003_, lean_object* v_m_u2081_4004_, lean_object* v_m_u2082_4005_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_4002_, v_m_u2081_4004_, v_m_u2082_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0(lean_object* v_00_u03b1_4007_, lean_object* v_cmp_4008_, lean_object* v_00_u03b2_4009_, lean_object* v_m_u2081_4010_, lean_object* v_m_u2082_4011_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(v_cmp_4008_, v_m_u2081_4010_, v_m_u2082_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1(lean_object* v_00_u03b1_4013_, lean_object* v_00_u03b2_4014_, lean_object* v_cmp_4015_, lean_object* v_m_u2082_4016_, lean_object* v_t_4017_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_4015_, v_m_u2082_4016_, v_t_4017_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4019_, lean_object* v_cmp_4020_, lean_object* v_00_u03b2_4021_, lean_object* v_t_4022_, lean_object* v_k_4023_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(v_cmp_4020_, v_t_4022_, v_k_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_4025_, lean_object* v_cmp_4026_, lean_object* v_00_u03b2_4027_, lean_object* v_k_4028_, lean_object* v_v_4029_, lean_object* v_t_4030_, lean_object* v_hl_4031_){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_4026_, v_k_4028_, v_v_4029_, v_t_4030_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3___redArg(lean_object* v_cmp_4033_, lean_object* v_m_u2081_4034_, lean_object* v_init_4035_, lean_object* v_t_4036_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4033_, v_m_u2081_4034_, v_init_4035_, v_t_4036_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4038_, lean_object* v_00_u03b2_4039_, lean_object* v_cmp_4040_, lean_object* v_m_u2081_4041_, lean_object* v_init_4042_, lean_object* v_t_4043_){
_start:
{
lean_object* v___x_4044_; 
v___x_4044_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4040_, v_m_u2081_4041_, v_init_4042_, v_t_4043_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b1_4045_, lean_object* v_00_u03b2_4046_, lean_object* v_cmp_4047_, lean_object* v_m_u2081_4048_, lean_object* v_init_4049_, lean_object* v_x_4050_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4047_, v_m_u2081_4048_, v_init_4049_, v_x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter___redArg(lean_object* v_cmp_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_4053_, 0, lean_box(0));
lean_closure_set(v___x_4053_, 1, lean_box(0));
lean_closure_set(v___x_4053_, 2, v_cmp_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter(lean_object* v_00_u03b1_4054_, lean_object* v_00_u03b2_4055_, lean_object* v_cmp_4056_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_4057_, 0, lean_box(0));
lean_closure_set(v___x_4057_, 1, lean_box(0));
lean_closure_set(v___x_4057_, 2, v_cmp_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_beq___redArg(lean_object* v_cmp_4058_, lean_object* v_inst_4059_, lean_object* v_t_u2081_4060_, lean_object* v_t_u2082_4061_){
_start:
{
uint8_t v___x_4062_; 
v___x_4062_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_4058_, v_inst_4059_, v_t_u2081_4060_, v_t_u2082_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___redArg___boxed(lean_object* v_cmp_4063_, lean_object* v_inst_4064_, lean_object* v_t_u2081_4065_, lean_object* v_t_u2082_4066_){
_start:
{
uint8_t v_res_4067_; lean_object* v_r_4068_; 
v_res_4067_ = l_Std_DTreeMap_Raw_beq___redArg(v_cmp_4063_, v_inst_4064_, v_t_u2081_4065_, v_t_u2082_4066_);
v_r_4068_ = lean_box(v_res_4067_);
return v_r_4068_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_beq(lean_object* v_00_u03b1_4069_, lean_object* v_00_u03b2_4070_, lean_object* v_cmp_4071_, lean_object* v_inst_4072_, lean_object* v_inst_4073_, lean_object* v_t_u2081_4074_, lean_object* v_t_u2082_4075_){
_start:
{
uint8_t v___x_4076_; 
v___x_4076_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_4071_, v_inst_4073_, v_t_u2081_4074_, v_t_u2082_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___boxed(lean_object* v_00_u03b1_4077_, lean_object* v_00_u03b2_4078_, lean_object* v_cmp_4079_, lean_object* v_inst_4080_, lean_object* v_inst_4081_, lean_object* v_t_u2081_4082_, lean_object* v_t_u2082_4083_){
_start:
{
uint8_t v_res_4084_; lean_object* v_r_4085_; 
v_res_4084_ = l_Std_DTreeMap_Raw_beq(v_00_u03b1_4077_, v_00_u03b2_4078_, v_cmp_4079_, v_inst_4080_, v_inst_4081_, v_t_u2081_4082_, v_t_u2082_4083_);
v_r_4085_ = lean_box(v_res_4084_);
return v_r_4085_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp___redArg(lean_object* v_cmp_4086_, lean_object* v_inst_4087_){
_start:
{
lean_object* v___x_4088_; 
v___x_4088_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_4088_, 0, lean_box(0));
lean_closure_set(v___x_4088_, 1, lean_box(0));
lean_closure_set(v___x_4088_, 2, v_cmp_4086_);
lean_closure_set(v___x_4088_, 3, lean_box(0));
lean_closure_set(v___x_4088_, 4, v_inst_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp(lean_object* v_00_u03b1_4089_, lean_object* v_00_u03b2_4090_, lean_object* v_cmp_4091_, lean_object* v_inst_4092_, lean_object* v_inst_4093_){
_start:
{
lean_object* v___x_4094_; 
v___x_4094_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_4094_, 0, lean_box(0));
lean_closure_set(v___x_4094_, 1, lean_box(0));
lean_closure_set(v___x_4094_, 2, v_cmp_4091_);
lean_closure_set(v___x_4094_, 3, lean_box(0));
lean_closure_set(v___x_4094_, 4, v_inst_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___redArg(lean_object* v_cmp_4095_, lean_object* v_inst_4096_, lean_object* v_t_u2081_4097_, lean_object* v_t_u2082_4098_){
_start:
{
uint8_t v___x_4099_; 
v___x_4099_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_4095_, v_inst_4096_, v_t_u2081_4097_, v_t_u2082_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___redArg___boxed(lean_object* v_cmp_4100_, lean_object* v_inst_4101_, lean_object* v_t_u2081_4102_, lean_object* v_t_u2082_4103_){
_start:
{
uint8_t v_res_4104_; lean_object* v_r_4105_; 
v_res_4104_ = l_Std_DTreeMap_Raw_Const_beq___redArg(v_cmp_4100_, v_inst_4101_, v_t_u2081_4102_, v_t_u2082_4103_);
v_r_4105_ = lean_box(v_res_4104_);
return v_r_4105_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq(lean_object* v_00_u03b1_4106_, lean_object* v_cmp_4107_, lean_object* v_00_u03b2_4108_, lean_object* v_inst_4109_, lean_object* v_t_u2081_4110_, lean_object* v_t_u2082_4111_){
_start:
{
uint8_t v___x_4112_; 
v___x_4112_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_4107_, v_inst_4109_, v_t_u2081_4110_, v_t_u2082_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___boxed(lean_object* v_00_u03b1_4113_, lean_object* v_cmp_4114_, lean_object* v_00_u03b2_4115_, lean_object* v_inst_4116_, lean_object* v_t_u2081_4117_, lean_object* v_t_u2082_4118_){
_start:
{
uint8_t v_res_4119_; lean_object* v_r_4120_; 
v_res_4119_ = l_Std_DTreeMap_Raw_Const_beq(v_00_u03b1_4113_, v_cmp_4114_, v_00_u03b2_4115_, v_inst_4116_, v_t_u2081_4117_, v_t_u2082_4118_);
v_r_4120_ = lean_box(v_res_4119_);
return v_r_4120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(lean_object* v_cmp_4121_, lean_object* v_t_u2082_4122_, lean_object* v_t_4123_){
_start:
{
if (lean_obj_tag(v_t_4123_) == 0)
{
lean_object* v_k_4124_; lean_object* v_v_4125_; lean_object* v_l_4126_; lean_object* v_r_4127_; uint8_t v___x_4128_; 
v_k_4124_ = lean_ctor_get(v_t_4123_, 1);
lean_inc_n(v_k_4124_, 2);
v_v_4125_ = lean_ctor_get(v_t_4123_, 2);
lean_inc(v_v_4125_);
v_l_4126_ = lean_ctor_get(v_t_4123_, 3);
lean_inc(v_l_4126_);
v_r_4127_ = lean_ctor_get(v_t_4123_, 4);
lean_inc(v_r_4127_);
lean_dec_ref(v_t_4123_);
lean_inc(v_t_u2082_4122_);
lean_inc_ref(v_cmp_4121_);
v___x_4128_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_4121_, v_k_4124_, v_t_u2082_4122_);
if (v___x_4128_ == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
lean_inc(v_t_u2082_4122_);
lean_inc_ref(v_cmp_4121_);
v___x_4129_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4121_, v_t_u2082_4122_, v_l_4126_);
v___x_4130_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4121_, v_t_u2082_4122_, v_r_4127_);
v___x_4131_ = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(v_k_4124_, v_v_4125_, v___x_4129_, v___x_4130_);
return v___x_4131_;
}
else
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
lean_dec(v_v_4125_);
lean_dec(v_k_4124_);
lean_inc(v_t_u2082_4122_);
lean_inc_ref(v_cmp_4121_);
v___x_4132_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4121_, v_t_u2082_4122_, v_l_4126_);
v___x_4133_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4121_, v_t_u2082_4122_, v_r_4127_);
v___x_4134_ = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(v___x_4132_, v___x_4133_);
return v___x_4134_;
}
}
else
{
lean_dec(v_t_u2082_4122_);
lean_dec_ref(v_cmp_4121_);
return v_t_4123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(lean_object* v_cmp_4135_, lean_object* v_k_4136_, lean_object* v_t_4137_){
_start:
{
if (lean_obj_tag(v_t_4137_) == 0)
{
lean_object* v_k_4138_; lean_object* v_v_4139_; lean_object* v_l_4140_; lean_object* v_r_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4831_; 
v_k_4138_ = lean_ctor_get(v_t_4137_, 1);
v_v_4139_ = lean_ctor_get(v_t_4137_, 2);
v_l_4140_ = lean_ctor_get(v_t_4137_, 3);
v_r_4141_ = lean_ctor_get(v_t_4137_, 4);
v_isSharedCheck_4831_ = !lean_is_exclusive(v_t_4137_);
if (v_isSharedCheck_4831_ == 0)
{
lean_object* v_unused_4832_; 
v_unused_4832_ = lean_ctor_get(v_t_4137_, 0);
lean_dec(v_unused_4832_);
v___x_4143_ = v_t_4137_;
v_isShared_4144_ = v_isSharedCheck_4831_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_r_4141_);
lean_inc(v_l_4140_);
lean_inc(v_v_4139_);
lean_inc(v_k_4138_);
lean_dec(v_t_4137_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4831_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4145_; uint8_t v___x_4146_; 
lean_inc_ref(v_cmp_4135_);
lean_inc(v_k_4138_);
lean_inc(v_k_4136_);
v___x_4145_ = lean_apply_2(v_cmp_4135_, v_k_4136_, v_k_4138_);
v___x_4146_ = lean_unbox(v___x_4145_);
switch(v___x_4146_)
{
case 0:
{
lean_object* v___x_4147_; 
v___x_4147_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4135_, v_k_4136_, v_l_4140_);
if (lean_obj_tag(v___x_4147_) == 0)
{
if (lean_obj_tag(v_r_4141_) == 0)
{
lean_object* v_size_4148_; lean_object* v_size_4149_; lean_object* v_k_4150_; lean_object* v_v_4151_; lean_object* v_l_4152_; lean_object* v_r_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; 
v_size_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_size_4148_);
v_size_4149_ = lean_ctor_get(v_r_4141_, 0);
v_k_4150_ = lean_ctor_get(v_r_4141_, 1);
v_v_4151_ = lean_ctor_get(v_r_4141_, 2);
v_l_4152_ = lean_ctor_get(v_r_4141_, 3);
lean_inc(v_l_4152_);
v_r_4153_ = lean_ctor_get(v_r_4141_, 4);
v___x_4154_ = lean_unsigned_to_nat(3u);
v___x_4155_ = lean_nat_mul(v___x_4154_, v_size_4148_);
v___x_4156_ = lean_nat_dec_lt(v___x_4155_, v_size_4149_);
lean_dec(v___x_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4161_; 
lean_dec(v_l_4152_);
v___x_4157_ = lean_unsigned_to_nat(1u);
v___x_4158_ = lean_nat_add(v___x_4157_, v_size_4148_);
lean_dec(v_size_4148_);
v___x_4159_ = lean_nat_add(v___x_4158_, v_size_4149_);
lean_dec(v___x_4158_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 3, v___x_4147_);
lean_ctor_set(v___x_4143_, 0, v___x_4159_);
v___x_4161_ = v___x_4143_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4159_);
lean_ctor_set(v_reuseFailAlloc_4162_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4162_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4162_, 3, v___x_4147_);
lean_ctor_set(v_reuseFailAlloc_4162_, 4, v_r_4141_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
else
{
lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4232_; 
lean_inc(v_r_4153_);
lean_inc(v_v_4151_);
lean_inc(v_k_4150_);
lean_inc(v_size_4149_);
v_isSharedCheck_4232_ = !lean_is_exclusive(v_r_4141_);
if (v_isSharedCheck_4232_ == 0)
{
lean_object* v_unused_4233_; lean_object* v_unused_4234_; lean_object* v_unused_4235_; lean_object* v_unused_4236_; lean_object* v_unused_4237_; 
v_unused_4233_ = lean_ctor_get(v_r_4141_, 4);
lean_dec(v_unused_4233_);
v_unused_4234_ = lean_ctor_get(v_r_4141_, 3);
lean_dec(v_unused_4234_);
v_unused_4235_ = lean_ctor_get(v_r_4141_, 2);
lean_dec(v_unused_4235_);
v_unused_4236_ = lean_ctor_get(v_r_4141_, 1);
lean_dec(v_unused_4236_);
v_unused_4237_ = lean_ctor_get(v_r_4141_, 0);
lean_dec(v_unused_4237_);
v___x_4164_ = v_r_4141_;
v_isShared_4165_ = v_isSharedCheck_4232_;
goto v_resetjp_4163_;
}
else
{
lean_dec(v_r_4141_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4232_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
if (lean_obj_tag(v_l_4152_) == 0)
{
if (lean_obj_tag(v_r_4153_) == 0)
{
lean_object* v_size_4166_; lean_object* v_k_4167_; lean_object* v_v_4168_; lean_object* v_l_4169_; lean_object* v_r_4170_; lean_object* v_size_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; uint8_t v___x_4174_; 
v_size_4166_ = lean_ctor_get(v_l_4152_, 0);
v_k_4167_ = lean_ctor_get(v_l_4152_, 1);
v_v_4168_ = lean_ctor_get(v_l_4152_, 2);
v_l_4169_ = lean_ctor_get(v_l_4152_, 3);
v_r_4170_ = lean_ctor_get(v_l_4152_, 4);
v_size_4171_ = lean_ctor_get(v_r_4153_, 0);
v___x_4172_ = lean_unsigned_to_nat(2u);
v___x_4173_ = lean_nat_mul(v___x_4172_, v_size_4171_);
v___x_4174_ = lean_nat_dec_lt(v_size_4166_, v___x_4173_);
lean_dec(v___x_4173_);
if (v___x_4174_ == 0)
{
lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4203_; 
lean_inc(v_r_4170_);
lean_inc(v_l_4169_);
lean_inc(v_v_4168_);
lean_inc(v_k_4167_);
v_isSharedCheck_4203_ = !lean_is_exclusive(v_l_4152_);
if (v_isSharedCheck_4203_ == 0)
{
lean_object* v_unused_4204_; lean_object* v_unused_4205_; lean_object* v_unused_4206_; lean_object* v_unused_4207_; lean_object* v_unused_4208_; 
v_unused_4204_ = lean_ctor_get(v_l_4152_, 4);
lean_dec(v_unused_4204_);
v_unused_4205_ = lean_ctor_get(v_l_4152_, 3);
lean_dec(v_unused_4205_);
v_unused_4206_ = lean_ctor_get(v_l_4152_, 2);
lean_dec(v_unused_4206_);
v_unused_4207_ = lean_ctor_get(v_l_4152_, 1);
lean_dec(v_unused_4207_);
v_unused_4208_ = lean_ctor_get(v_l_4152_, 0);
lean_dec(v_unused_4208_);
v___x_4176_ = v_l_4152_;
v_isShared_4177_ = v_isSharedCheck_4203_;
goto v_resetjp_4175_;
}
else
{
lean_dec(v_l_4152_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4203_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4193_; 
v___x_4178_ = lean_unsigned_to_nat(1u);
v___x_4179_ = lean_nat_add(v___x_4178_, v_size_4148_);
lean_dec(v_size_4148_);
v___x_4180_ = lean_nat_add(v___x_4179_, v_size_4149_);
lean_dec(v_size_4149_);
if (lean_obj_tag(v_l_4169_) == 0)
{
lean_object* v_size_4201_; 
v_size_4201_ = lean_ctor_get(v_l_4169_, 0);
lean_inc(v_size_4201_);
v___y_4193_ = v_size_4201_;
goto v___jp_4192_;
}
else
{
lean_object* v___x_4202_; 
v___x_4202_ = lean_unsigned_to_nat(0u);
v___y_4193_ = v___x_4202_;
goto v___jp_4192_;
}
v___jp_4181_:
{
lean_object* v___x_4185_; lean_object* v___x_4187_; 
v___x_4185_ = lean_nat_add(v___y_4182_, v___y_4184_);
lean_dec(v___y_4184_);
lean_dec(v___y_4182_);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 4, v_r_4153_);
lean_ctor_set(v___x_4176_, 3, v_r_4170_);
lean_ctor_set(v___x_4176_, 2, v_v_4151_);
lean_ctor_set(v___x_4176_, 1, v_k_4150_);
lean_ctor_set(v___x_4176_, 0, v___x_4185_);
v___x_4187_ = v___x_4176_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4185_);
lean_ctor_set(v_reuseFailAlloc_4191_, 1, v_k_4150_);
lean_ctor_set(v_reuseFailAlloc_4191_, 2, v_v_4151_);
lean_ctor_set(v_reuseFailAlloc_4191_, 3, v_r_4170_);
lean_ctor_set(v_reuseFailAlloc_4191_, 4, v_r_4153_);
v___x_4187_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
lean_object* v___x_4189_; 
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 4, v___x_4187_);
lean_ctor_set(v___x_4164_, 3, v___y_4183_);
lean_ctor_set(v___x_4164_, 2, v_v_4168_);
lean_ctor_set(v___x_4164_, 1, v_k_4167_);
lean_ctor_set(v___x_4164_, 0, v___x_4180_);
v___x_4189_ = v___x_4164_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4180_);
lean_ctor_set(v_reuseFailAlloc_4190_, 1, v_k_4167_);
lean_ctor_set(v_reuseFailAlloc_4190_, 2, v_v_4168_);
lean_ctor_set(v_reuseFailAlloc_4190_, 3, v___y_4183_);
lean_ctor_set(v_reuseFailAlloc_4190_, 4, v___x_4187_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
v___jp_4192_:
{
lean_object* v___x_4194_; lean_object* v___x_4196_; 
v___x_4194_ = lean_nat_add(v___x_4179_, v___y_4193_);
lean_dec(v___y_4193_);
lean_dec(v___x_4179_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 4, v_l_4169_);
lean_ctor_set(v___x_4143_, 3, v___x_4147_);
lean_ctor_set(v___x_4143_, 0, v___x_4194_);
v___x_4196_ = v___x_4143_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4194_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4200_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4200_, 3, v___x_4147_);
lean_ctor_set(v_reuseFailAlloc_4200_, 4, v_l_4169_);
v___x_4196_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
lean_object* v___x_4197_; 
v___x_4197_ = lean_nat_add(v___x_4178_, v_size_4171_);
if (lean_obj_tag(v_r_4170_) == 0)
{
lean_object* v_size_4198_; 
v_size_4198_ = lean_ctor_get(v_r_4170_, 0);
lean_inc(v_size_4198_);
v___y_4182_ = v___x_4197_;
v___y_4183_ = v___x_4196_;
v___y_4184_ = v_size_4198_;
goto v___jp_4181_;
}
else
{
lean_object* v___x_4199_; 
v___x_4199_ = lean_unsigned_to_nat(0u);
v___y_4182_ = v___x_4197_;
v___y_4183_ = v___x_4196_;
v___y_4184_ = v___x_4199_;
goto v___jp_4181_;
}
}
}
}
}
else
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4214_; 
lean_del_object(v___x_4143_);
v___x_4209_ = lean_unsigned_to_nat(1u);
v___x_4210_ = lean_nat_add(v___x_4209_, v_size_4148_);
lean_dec(v_size_4148_);
v___x_4211_ = lean_nat_add(v___x_4210_, v_size_4149_);
lean_dec(v_size_4149_);
v___x_4212_ = lean_nat_add(v___x_4210_, v_size_4166_);
lean_dec(v___x_4210_);
lean_inc_ref(v___x_4147_);
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 4, v_l_4152_);
lean_ctor_set(v___x_4164_, 3, v___x_4147_);
lean_ctor_set(v___x_4164_, 2, v_v_4139_);
lean_ctor_set(v___x_4164_, 1, v_k_4138_);
lean_ctor_set(v___x_4164_, 0, v___x_4212_);
v___x_4214_ = v___x_4164_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4212_);
lean_ctor_set(v_reuseFailAlloc_4227_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4227_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4227_, 3, v___x_4147_);
lean_ctor_set(v_reuseFailAlloc_4227_, 4, v_l_4152_);
v___x_4214_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4221_ == 0)
{
lean_object* v_unused_4222_; lean_object* v_unused_4223_; lean_object* v_unused_4224_; lean_object* v_unused_4225_; lean_object* v_unused_4226_; 
v_unused_4222_ = lean_ctor_get(v___x_4147_, 4);
lean_dec(v_unused_4222_);
v_unused_4223_ = lean_ctor_get(v___x_4147_, 3);
lean_dec(v_unused_4223_);
v_unused_4224_ = lean_ctor_get(v___x_4147_, 2);
lean_dec(v_unused_4224_);
v_unused_4225_ = lean_ctor_get(v___x_4147_, 1);
lean_dec(v_unused_4225_);
v_unused_4226_ = lean_ctor_get(v___x_4147_, 0);
lean_dec(v_unused_4226_);
v___x_4216_ = v___x_4147_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_dec(v___x_4147_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 4, v_r_4153_);
lean_ctor_set(v___x_4216_, 3, v___x_4214_);
lean_ctor_set(v___x_4216_, 2, v_v_4151_);
lean_ctor_set(v___x_4216_, 1, v_k_4150_);
lean_ctor_set(v___x_4216_, 0, v___x_4211_);
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4211_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_k_4150_);
lean_ctor_set(v_reuseFailAlloc_4220_, 2, v_v_4151_);
lean_ctor_set(v_reuseFailAlloc_4220_, 3, v___x_4214_);
lean_ctor_set(v_reuseFailAlloc_4220_, 4, v_r_4153_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
}
else
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
lean_dec_ref(v_l_4152_);
lean_del_object(v___x_4164_);
lean_dec(v_v_4151_);
lean_dec(v_k_4150_);
lean_dec(v_size_4149_);
lean_dec(v_size_4148_);
lean_dec_ref(v___x_4147_);
lean_del_object(v___x_4143_);
lean_dec(v_v_4139_);
lean_dec(v_k_4138_);
v___x_4228_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7);
v___x_4229_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4228_);
return v___x_4229_;
}
}
else
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_del_object(v___x_4164_);
lean_dec(v_r_4153_);
lean_dec(v_v_4151_);
lean_dec(v_k_4150_);
lean_dec(v_size_4149_);
lean_dec(v_size_4148_);
lean_dec_ref(v___x_4147_);
lean_del_object(v___x_4143_);
lean_dec(v_v_4139_);
lean_dec(v_k_4138_);
v___x_4230_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8);
v___x_4231_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4230_);
return v___x_4231_;
}
}
}
}
else
{
lean_object* v_size_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4242_; 
v_size_4238_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_size_4238_);
v___x_4239_ = lean_unsigned_to_nat(1u);
v___x_4240_ = lean_nat_add(v___x_4239_, v_size_4238_);
lean_dec(v_size_4238_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 3, v___x_4147_);
lean_ctor_set(v___x_4143_, 0, v___x_4240_);
v___x_4242_ = v___x_4143_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4240_);
lean_ctor_set(v_reuseFailAlloc_4243_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4243_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4243_, 3, v___x_4147_);
lean_ctor_set(v_reuseFailAlloc_4243_, 4, v_r_4141_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
else
{
if (lean_obj_tag(v_r_4141_) == 0)
{
lean_object* v_l_4244_; 
v_l_4244_ = lean_ctor_get(v_r_4141_, 3);
lean_inc(v_l_4244_);
if (lean_obj_tag(v_l_4244_) == 0)
{
lean_object* v_r_4245_; 
v_r_4245_ = lean_ctor_get(v_r_4141_, 4);
lean_inc(v_r_4245_);
if (lean_obj_tag(v_r_4245_) == 0)
{
lean_object* v_size_4246_; lean_object* v_k_4247_; lean_object* v_v_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4262_; 
v_size_4246_ = lean_ctor_get(v_r_4141_, 0);
v_k_4247_ = lean_ctor_get(v_r_4141_, 1);
v_v_4248_ = lean_ctor_get(v_r_4141_, 2);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_r_4141_);
if (v_isSharedCheck_4262_ == 0)
{
lean_object* v_unused_4263_; lean_object* v_unused_4264_; 
v_unused_4263_ = lean_ctor_get(v_r_4141_, 4);
lean_dec(v_unused_4263_);
v_unused_4264_ = lean_ctor_get(v_r_4141_, 3);
lean_dec(v_unused_4264_);
v___x_4250_ = v_r_4141_;
v_isShared_4251_ = v_isSharedCheck_4262_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_v_4248_);
lean_inc(v_k_4247_);
lean_inc(v_size_4246_);
lean_dec(v_r_4141_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4262_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v_size_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4257_; 
v_size_4252_ = lean_ctor_get(v_l_4244_, 0);
v___x_4253_ = lean_unsigned_to_nat(1u);
v___x_4254_ = lean_nat_add(v___x_4253_, v_size_4246_);
lean_dec(v_size_4246_);
v___x_4255_ = lean_nat_add(v___x_4253_, v_size_4252_);
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 4, v_l_4244_);
lean_ctor_set(v___x_4250_, 3, v___x_4147_);
lean_ctor_set(v___x_4250_, 2, v_v_4139_);
lean_ctor_set(v___x_4250_, 1, v_k_4138_);
lean_ctor_set(v___x_4250_, 0, v___x_4255_);
v___x_4257_ = v___x_4250_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4255_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4261_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4261_, 3, v___x_4147_);
lean_ctor_set(v_reuseFailAlloc_4261_, 4, v_l_4244_);
v___x_4257_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
lean_object* v___x_4259_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 4, v_r_4245_);
lean_ctor_set(v___x_4143_, 3, v___x_4257_);
lean_ctor_set(v___x_4143_, 2, v_v_4248_);
lean_ctor_set(v___x_4143_, 1, v_k_4247_);
lean_ctor_set(v___x_4143_, 0, v___x_4254_);
v___x_4259_ = v___x_4143_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v___x_4254_);
lean_ctor_set(v_reuseFailAlloc_4260_, 1, v_k_4247_);
lean_ctor_set(v_reuseFailAlloc_4260_, 2, v_v_4248_);
lean_ctor_set(v_reuseFailAlloc_4260_, 3, v___x_4257_);
lean_ctor_set(v_reuseFailAlloc_4260_, 4, v_r_4245_);
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
else
{
lean_object* v_k_4265_; lean_object* v_v_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4290_; 
v_k_4265_ = lean_ctor_get(v_r_4141_, 1);
v_v_4266_ = lean_ctor_get(v_r_4141_, 2);
v_isSharedCheck_4290_ = !lean_is_exclusive(v_r_4141_);
if (v_isSharedCheck_4290_ == 0)
{
lean_object* v_unused_4291_; lean_object* v_unused_4292_; lean_object* v_unused_4293_; 
v_unused_4291_ = lean_ctor_get(v_r_4141_, 4);
lean_dec(v_unused_4291_);
v_unused_4292_ = lean_ctor_get(v_r_4141_, 3);
lean_dec(v_unused_4292_);
v_unused_4293_ = lean_ctor_get(v_r_4141_, 0);
lean_dec(v_unused_4293_);
v___x_4268_ = v_r_4141_;
v_isShared_4269_ = v_isSharedCheck_4290_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_v_4266_);
lean_inc(v_k_4265_);
lean_dec(v_r_4141_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4290_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v_k_4270_; lean_object* v_v_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4286_; 
v_k_4270_ = lean_ctor_get(v_l_4244_, 1);
v_v_4271_ = lean_ctor_get(v_l_4244_, 2);
v_isSharedCheck_4286_ = !lean_is_exclusive(v_l_4244_);
if (v_isSharedCheck_4286_ == 0)
{
lean_object* v_unused_4287_; lean_object* v_unused_4288_; lean_object* v_unused_4289_; 
v_unused_4287_ = lean_ctor_get(v_l_4244_, 4);
lean_dec(v_unused_4287_);
v_unused_4288_ = lean_ctor_get(v_l_4244_, 3);
lean_dec(v_unused_4288_);
v_unused_4289_ = lean_ctor_get(v_l_4244_, 0);
lean_dec(v_unused_4289_);
v___x_4273_ = v_l_4244_;
v_isShared_4274_ = v_isSharedCheck_4286_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_v_4271_);
lean_inc(v_k_4270_);
lean_dec(v_l_4244_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4286_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4278_; 
v___x_4275_ = lean_unsigned_to_nat(3u);
v___x_4276_ = lean_unsigned_to_nat(1u);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 4, v_r_4245_);
lean_ctor_set(v___x_4273_, 3, v_r_4245_);
lean_ctor_set(v___x_4273_, 2, v_v_4139_);
lean_ctor_set(v___x_4273_, 1, v_k_4138_);
lean_ctor_set(v___x_4273_, 0, v___x_4276_);
v___x_4278_ = v___x_4273_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v___x_4276_);
lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4285_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4285_, 3, v_r_4245_);
lean_ctor_set(v_reuseFailAlloc_4285_, 4, v_r_4245_);
v___x_4278_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
lean_object* v___x_4280_; 
if (v_isShared_4269_ == 0)
{
lean_ctor_set(v___x_4268_, 3, v_r_4245_);
lean_ctor_set(v___x_4268_, 0, v___x_4276_);
v___x_4280_ = v___x_4268_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4276_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_k_4265_);
lean_ctor_set(v_reuseFailAlloc_4284_, 2, v_v_4266_);
lean_ctor_set(v_reuseFailAlloc_4284_, 3, v_r_4245_);
lean_ctor_set(v_reuseFailAlloc_4284_, 4, v_r_4245_);
v___x_4280_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
lean_object* v___x_4282_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 4, v___x_4280_);
lean_ctor_set(v___x_4143_, 3, v___x_4278_);
lean_ctor_set(v___x_4143_, 2, v_v_4271_);
lean_ctor_set(v___x_4143_, 1, v_k_4270_);
lean_ctor_set(v___x_4143_, 0, v___x_4275_);
v___x_4282_ = v___x_4143_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4275_);
lean_ctor_set(v_reuseFailAlloc_4283_, 1, v_k_4270_);
lean_ctor_set(v_reuseFailAlloc_4283_, 2, v_v_4271_);
lean_ctor_set(v_reuseFailAlloc_4283_, 3, v___x_4278_);
lean_ctor_set(v_reuseFailAlloc_4283_, 4, v___x_4280_);
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
}
}
}
else
{
lean_object* v_r_4294_; 
v_r_4294_ = lean_ctor_get(v_r_4141_, 4);
lean_inc(v_r_4294_);
if (lean_obj_tag(v_r_4294_) == 0)
{
lean_object* v_k_4295_; lean_object* v_v_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4308_; 
v_k_4295_ = lean_ctor_get(v_r_4141_, 1);
v_v_4296_ = lean_ctor_get(v_r_4141_, 2);
v_isSharedCheck_4308_ = !lean_is_exclusive(v_r_4141_);
if (v_isSharedCheck_4308_ == 0)
{
lean_object* v_unused_4309_; lean_object* v_unused_4310_; lean_object* v_unused_4311_; 
v_unused_4309_ = lean_ctor_get(v_r_4141_, 4);
lean_dec(v_unused_4309_);
v_unused_4310_ = lean_ctor_get(v_r_4141_, 3);
lean_dec(v_unused_4310_);
v_unused_4311_ = lean_ctor_get(v_r_4141_, 0);
lean_dec(v_unused_4311_);
v___x_4298_ = v_r_4141_;
v_isShared_4299_ = v_isSharedCheck_4308_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_v_4296_);
lean_inc(v_k_4295_);
lean_dec(v_r_4141_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4308_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4303_; 
v___x_4300_ = lean_unsigned_to_nat(3u);
v___x_4301_ = lean_unsigned_to_nat(1u);
if (v_isShared_4299_ == 0)
{
lean_ctor_set(v___x_4298_, 4, v_l_4244_);
lean_ctor_set(v___x_4298_, 2, v_v_4139_);
lean_ctor_set(v___x_4298_, 1, v_k_4138_);
lean_ctor_set(v___x_4298_, 0, v___x_4301_);
v___x_4303_ = v___x_4298_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4301_);
lean_ctor_set(v_reuseFailAlloc_4307_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4307_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4307_, 3, v_l_4244_);
lean_ctor_set(v_reuseFailAlloc_4307_, 4, v_l_4244_);
v___x_4303_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
lean_object* v___x_4305_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 4, v_r_4294_);
lean_ctor_set(v___x_4143_, 3, v___x_4303_);
lean_ctor_set(v___x_4143_, 2, v_v_4296_);
lean_ctor_set(v___x_4143_, 1, v_k_4295_);
lean_ctor_set(v___x_4143_, 0, v___x_4300_);
v___x_4305_ = v___x_4143_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v___x_4300_);
lean_ctor_set(v_reuseFailAlloc_4306_, 1, v_k_4295_);
lean_ctor_set(v_reuseFailAlloc_4306_, 2, v_v_4296_);
lean_ctor_set(v_reuseFailAlloc_4306_, 3, v___x_4303_);
lean_ctor_set(v_reuseFailAlloc_4306_, 4, v_r_4294_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
else
{
lean_object* v___x_4312_; lean_object* v___x_4314_; 
v___x_4312_ = lean_unsigned_to_nat(2u);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 3, v_r_4294_);
lean_ctor_set(v___x_4143_, 0, v___x_4312_);
v___x_4314_ = v___x_4143_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4312_);
lean_ctor_set(v_reuseFailAlloc_4315_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4315_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4315_, 3, v_r_4294_);
lean_ctor_set(v_reuseFailAlloc_4315_, 4, v_r_4141_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
else
{
lean_object* v___x_4316_; lean_object* v___x_4318_; 
v___x_4316_ = lean_unsigned_to_nat(1u);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 3, v_r_4141_);
lean_ctor_set(v___x_4143_, 0, v___x_4316_);
v___x_4318_ = v___x_4143_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4316_);
lean_ctor_set(v_reuseFailAlloc_4319_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4319_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4319_, 3, v_r_4141_);
lean_ctor_set(v_reuseFailAlloc_4319_, 4, v_r_4141_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
case 1:
{
lean_del_object(v___x_4143_);
lean_dec(v_v_4139_);
lean_dec(v_k_4138_);
lean_dec(v_k_4136_);
lean_dec_ref(v_cmp_4135_);
if (lean_obj_tag(v_l_4140_) == 0)
{
if (lean_obj_tag(v_r_4141_) == 0)
{
lean_object* v_size_4320_; lean_object* v_k_4321_; lean_object* v_v_4322_; lean_object* v_l_4323_; lean_object* v_r_4324_; lean_object* v_size_4325_; lean_object* v_k_4326_; lean_object* v_v_4327_; lean_object* v_l_4328_; lean_object* v_r_4329_; uint8_t v___x_4330_; 
v_size_4320_ = lean_ctor_get(v_l_4140_, 0);
v_k_4321_ = lean_ctor_get(v_l_4140_, 1);
v_v_4322_ = lean_ctor_get(v_l_4140_, 2);
v_l_4323_ = lean_ctor_get(v_l_4140_, 3);
v_r_4324_ = lean_ctor_get(v_l_4140_, 4);
lean_inc(v_r_4324_);
v_size_4325_ = lean_ctor_get(v_r_4141_, 0);
v_k_4326_ = lean_ctor_get(v_r_4141_, 1);
v_v_4327_ = lean_ctor_get(v_r_4141_, 2);
v_l_4328_ = lean_ctor_get(v_r_4141_, 3);
lean_inc(v_l_4328_);
v_r_4329_ = lean_ctor_get(v_r_4141_, 4);
v___x_4330_ = lean_nat_dec_lt(v_size_4320_, v_size_4325_);
if (v___x_4330_ == 0)
{
lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4482_; 
lean_inc(v_l_4323_);
lean_inc(v_v_4322_);
lean_inc(v_k_4321_);
v_isSharedCheck_4482_ = !lean_is_exclusive(v_l_4140_);
if (v_isSharedCheck_4482_ == 0)
{
lean_object* v_unused_4483_; lean_object* v_unused_4484_; lean_object* v_unused_4485_; lean_object* v_unused_4486_; lean_object* v_unused_4487_; 
v_unused_4483_ = lean_ctor_get(v_l_4140_, 4);
lean_dec(v_unused_4483_);
v_unused_4484_ = lean_ctor_get(v_l_4140_, 3);
lean_dec(v_unused_4484_);
v_unused_4485_ = lean_ctor_get(v_l_4140_, 2);
lean_dec(v_unused_4485_);
v_unused_4486_ = lean_ctor_get(v_l_4140_, 1);
lean_dec(v_unused_4486_);
v_unused_4487_ = lean_ctor_get(v_l_4140_, 0);
lean_dec(v_unused_4487_);
v___x_4332_ = v_l_4140_;
v_isShared_4333_ = v_isSharedCheck_4482_;
goto v_resetjp_4331_;
}
else
{
lean_dec(v_l_4140_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4482_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v_d_4334_; lean_object* v_tree_4335_; 
v_d_4334_ = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(v_k_4321_, v_v_4322_, v_l_4323_, v_r_4324_);
v_tree_4335_ = lean_ctor_get(v_d_4334_, 2);
lean_inc(v_tree_4335_);
if (lean_obj_tag(v_tree_4335_) == 0)
{
lean_object* v_k_4336_; lean_object* v_v_4337_; lean_object* v_size_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; 
v_k_4336_ = lean_ctor_get(v_d_4334_, 0);
lean_inc(v_k_4336_);
v_v_4337_ = lean_ctor_get(v_d_4334_, 1);
lean_inc(v_v_4337_);
lean_dec_ref(v_d_4334_);
v_size_4338_ = lean_ctor_get(v_tree_4335_, 0);
v___x_4339_ = lean_unsigned_to_nat(3u);
v___x_4340_ = lean_nat_mul(v___x_4339_, v_size_4338_);
v___x_4341_ = lean_nat_dec_lt(v___x_4340_, v_size_4325_);
lean_dec(v___x_4340_);
if (v___x_4341_ == 0)
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4346_; 
lean_dec(v_l_4328_);
v___x_4342_ = lean_unsigned_to_nat(1u);
v___x_4343_ = lean_nat_add(v___x_4342_, v_size_4338_);
v___x_4344_ = lean_nat_add(v___x_4343_, v_size_4325_);
lean_dec(v___x_4343_);
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 4, v_r_4141_);
lean_ctor_set(v___x_4332_, 3, v_tree_4335_);
lean_ctor_set(v___x_4332_, 2, v_v_4337_);
lean_ctor_set(v___x_4332_, 1, v_k_4336_);
lean_ctor_set(v___x_4332_, 0, v___x_4344_);
v___x_4346_ = v___x_4332_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v___x_4344_);
lean_ctor_set(v_reuseFailAlloc_4347_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4347_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4347_, 3, v_tree_4335_);
lean_ctor_set(v_reuseFailAlloc_4347_, 4, v_r_4141_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
else
{
lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4408_; 
lean_inc(v_r_4329_);
lean_inc(v_v_4327_);
lean_inc(v_k_4326_);
lean_inc(v_size_4325_);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_r_4141_);
if (v_isSharedCheck_4408_ == 0)
{
lean_object* v_unused_4409_; lean_object* v_unused_4410_; lean_object* v_unused_4411_; lean_object* v_unused_4412_; lean_object* v_unused_4413_; 
v_unused_4409_ = lean_ctor_get(v_r_4141_, 4);
lean_dec(v_unused_4409_);
v_unused_4410_ = lean_ctor_get(v_r_4141_, 3);
lean_dec(v_unused_4410_);
v_unused_4411_ = lean_ctor_get(v_r_4141_, 2);
lean_dec(v_unused_4411_);
v_unused_4412_ = lean_ctor_get(v_r_4141_, 1);
lean_dec(v_unused_4412_);
v_unused_4413_ = lean_ctor_get(v_r_4141_, 0);
lean_dec(v_unused_4413_);
v___x_4349_ = v_r_4141_;
v_isShared_4350_ = v_isSharedCheck_4408_;
goto v_resetjp_4348_;
}
else
{
lean_dec(v_r_4141_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4408_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
if (lean_obj_tag(v_l_4328_) == 0)
{
if (lean_obj_tag(v_r_4329_) == 0)
{
lean_object* v_size_4351_; lean_object* v_k_4352_; lean_object* v_v_4353_; lean_object* v_l_4354_; lean_object* v_r_4355_; lean_object* v_size_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v_size_4351_ = lean_ctor_get(v_l_4328_, 0);
v_k_4352_ = lean_ctor_get(v_l_4328_, 1);
v_v_4353_ = lean_ctor_get(v_l_4328_, 2);
v_l_4354_ = lean_ctor_get(v_l_4328_, 3);
v_r_4355_ = lean_ctor_get(v_l_4328_, 4);
v_size_4356_ = lean_ctor_get(v_r_4329_, 0);
v___x_4357_ = lean_unsigned_to_nat(2u);
v___x_4358_ = lean_nat_mul(v___x_4357_, v_size_4356_);
v___x_4359_ = lean_nat_dec_lt(v_size_4351_, v___x_4358_);
lean_dec(v___x_4358_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4388_; 
lean_inc(v_r_4355_);
lean_inc(v_l_4354_);
lean_inc(v_v_4353_);
lean_inc(v_k_4352_);
v_isSharedCheck_4388_ = !lean_is_exclusive(v_l_4328_);
if (v_isSharedCheck_4388_ == 0)
{
lean_object* v_unused_4389_; lean_object* v_unused_4390_; lean_object* v_unused_4391_; lean_object* v_unused_4392_; lean_object* v_unused_4393_; 
v_unused_4389_ = lean_ctor_get(v_l_4328_, 4);
lean_dec(v_unused_4389_);
v_unused_4390_ = lean_ctor_get(v_l_4328_, 3);
lean_dec(v_unused_4390_);
v_unused_4391_ = lean_ctor_get(v_l_4328_, 2);
lean_dec(v_unused_4391_);
v_unused_4392_ = lean_ctor_get(v_l_4328_, 1);
lean_dec(v_unused_4392_);
v_unused_4393_ = lean_ctor_get(v_l_4328_, 0);
lean_dec(v_unused_4393_);
v___x_4361_ = v_l_4328_;
v_isShared_4362_ = v_isSharedCheck_4388_;
goto v_resetjp_4360_;
}
else
{
lean_dec(v_l_4328_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4388_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4378_; 
v___x_4363_ = lean_unsigned_to_nat(1u);
v___x_4364_ = lean_nat_add(v___x_4363_, v_size_4338_);
v___x_4365_ = lean_nat_add(v___x_4364_, v_size_4325_);
lean_dec(v_size_4325_);
if (lean_obj_tag(v_l_4354_) == 0)
{
lean_object* v_size_4386_; 
v_size_4386_ = lean_ctor_get(v_l_4354_, 0);
lean_inc(v_size_4386_);
v___y_4378_ = v_size_4386_;
goto v___jp_4377_;
}
else
{
lean_object* v___x_4387_; 
v___x_4387_ = lean_unsigned_to_nat(0u);
v___y_4378_ = v___x_4387_;
goto v___jp_4377_;
}
v___jp_4366_:
{
lean_object* v___x_4370_; lean_object* v___x_4372_; 
v___x_4370_ = lean_nat_add(v___y_4368_, v___y_4369_);
lean_dec(v___y_4369_);
lean_dec(v___y_4368_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 4, v_r_4329_);
lean_ctor_set(v___x_4361_, 3, v_r_4355_);
lean_ctor_set(v___x_4361_, 2, v_v_4327_);
lean_ctor_set(v___x_4361_, 1, v_k_4326_);
lean_ctor_set(v___x_4361_, 0, v___x_4370_);
v___x_4372_ = v___x_4361_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___x_4370_);
lean_ctor_set(v_reuseFailAlloc_4376_, 1, v_k_4326_);
lean_ctor_set(v_reuseFailAlloc_4376_, 2, v_v_4327_);
lean_ctor_set(v_reuseFailAlloc_4376_, 3, v_r_4355_);
lean_ctor_set(v_reuseFailAlloc_4376_, 4, v_r_4329_);
v___x_4372_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
lean_object* v___x_4374_; 
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 4, v___x_4372_);
lean_ctor_set(v___x_4349_, 3, v___y_4367_);
lean_ctor_set(v___x_4349_, 2, v_v_4353_);
lean_ctor_set(v___x_4349_, 1, v_k_4352_);
lean_ctor_set(v___x_4349_, 0, v___x_4365_);
v___x_4374_ = v___x_4349_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4365_);
lean_ctor_set(v_reuseFailAlloc_4375_, 1, v_k_4352_);
lean_ctor_set(v_reuseFailAlloc_4375_, 2, v_v_4353_);
lean_ctor_set(v_reuseFailAlloc_4375_, 3, v___y_4367_);
lean_ctor_set(v_reuseFailAlloc_4375_, 4, v___x_4372_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
}
v___jp_4377_:
{
lean_object* v___x_4379_; lean_object* v___x_4381_; 
v___x_4379_ = lean_nat_add(v___x_4364_, v___y_4378_);
lean_dec(v___y_4378_);
lean_dec(v___x_4364_);
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 4, v_l_4354_);
lean_ctor_set(v___x_4332_, 3, v_tree_4335_);
lean_ctor_set(v___x_4332_, 2, v_v_4337_);
lean_ctor_set(v___x_4332_, 1, v_k_4336_);
lean_ctor_set(v___x_4332_, 0, v___x_4379_);
v___x_4381_ = v___x_4332_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4379_);
lean_ctor_set(v_reuseFailAlloc_4385_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4385_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4385_, 3, v_tree_4335_);
lean_ctor_set(v_reuseFailAlloc_4385_, 4, v_l_4354_);
v___x_4381_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
lean_object* v___x_4382_; 
v___x_4382_ = lean_nat_add(v___x_4363_, v_size_4356_);
if (lean_obj_tag(v_r_4355_) == 0)
{
lean_object* v_size_4383_; 
v_size_4383_ = lean_ctor_get(v_r_4355_, 0);
lean_inc(v_size_4383_);
v___y_4367_ = v___x_4381_;
v___y_4368_ = v___x_4382_;
v___y_4369_ = v_size_4383_;
goto v___jp_4366_;
}
else
{
lean_object* v___x_4384_; 
v___x_4384_ = lean_unsigned_to_nat(0u);
v___y_4367_ = v___x_4381_;
v___y_4368_ = v___x_4382_;
v___y_4369_ = v___x_4384_;
goto v___jp_4366_;
}
}
}
}
}
else
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4399_; 
v___x_4394_ = lean_unsigned_to_nat(1u);
v___x_4395_ = lean_nat_add(v___x_4394_, v_size_4338_);
v___x_4396_ = lean_nat_add(v___x_4395_, v_size_4325_);
lean_dec(v_size_4325_);
v___x_4397_ = lean_nat_add(v___x_4395_, v_size_4351_);
lean_dec(v___x_4395_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 4, v_l_4328_);
lean_ctor_set(v___x_4349_, 3, v_tree_4335_);
lean_ctor_set(v___x_4349_, 2, v_v_4337_);
lean_ctor_set(v___x_4349_, 1, v_k_4336_);
lean_ctor_set(v___x_4349_, 0, v___x_4397_);
v___x_4399_ = v___x_4349_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4397_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4403_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4403_, 3, v_tree_4335_);
lean_ctor_set(v_reuseFailAlloc_4403_, 4, v_l_4328_);
v___x_4399_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
lean_object* v___x_4401_; 
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 4, v_r_4329_);
lean_ctor_set(v___x_4332_, 3, v___x_4399_);
lean_ctor_set(v___x_4332_, 2, v_v_4327_);
lean_ctor_set(v___x_4332_, 1, v_k_4326_);
lean_ctor_set(v___x_4332_, 0, v___x_4396_);
v___x_4401_ = v___x_4332_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v___x_4396_);
lean_ctor_set(v_reuseFailAlloc_4402_, 1, v_k_4326_);
lean_ctor_set(v_reuseFailAlloc_4402_, 2, v_v_4327_);
lean_ctor_set(v_reuseFailAlloc_4402_, 3, v___x_4399_);
lean_ctor_set(v_reuseFailAlloc_4402_, 4, v_r_4329_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
else
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
lean_dec_ref(v_l_4328_);
lean_del_object(v___x_4349_);
lean_dec(v_v_4337_);
lean_dec_ref(v_tree_4335_);
lean_dec(v_k_4336_);
lean_del_object(v___x_4332_);
lean_dec(v_v_4327_);
lean_dec(v_k_4326_);
lean_dec(v_size_4325_);
v___x_4404_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7);
v___x_4405_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4404_);
return v___x_4405_;
}
}
else
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
lean_del_object(v___x_4349_);
lean_dec(v_v_4337_);
lean_dec(v_k_4336_);
lean_dec_ref(v_tree_4335_);
lean_del_object(v___x_4332_);
lean_dec(v_r_4329_);
lean_dec(v_v_4327_);
lean_dec(v_k_4326_);
lean_dec(v_size_4325_);
v___x_4406_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8);
v___x_4407_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4406_);
return v___x_4407_;
}
}
}
}
else
{
lean_inc(v_r_4329_);
if (lean_obj_tag(v_l_4328_) == 0)
{
lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4451_; 
lean_inc(v_v_4327_);
lean_inc(v_k_4326_);
lean_inc(v_size_4325_);
v_isSharedCheck_4451_ = !lean_is_exclusive(v_r_4141_);
if (v_isSharedCheck_4451_ == 0)
{
lean_object* v_unused_4452_; lean_object* v_unused_4453_; lean_object* v_unused_4454_; lean_object* v_unused_4455_; lean_object* v_unused_4456_; 
v_unused_4452_ = lean_ctor_get(v_r_4141_, 4);
lean_dec(v_unused_4452_);
v_unused_4453_ = lean_ctor_get(v_r_4141_, 3);
lean_dec(v_unused_4453_);
v_unused_4454_ = lean_ctor_get(v_r_4141_, 2);
lean_dec(v_unused_4454_);
v_unused_4455_ = lean_ctor_get(v_r_4141_, 1);
lean_dec(v_unused_4455_);
v_unused_4456_ = lean_ctor_get(v_r_4141_, 0);
lean_dec(v_unused_4456_);
v___x_4415_ = v_r_4141_;
v_isShared_4416_ = v_isSharedCheck_4451_;
goto v_resetjp_4414_;
}
else
{
lean_dec(v_r_4141_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4451_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
if (lean_obj_tag(v_r_4329_) == 0)
{
lean_object* v_k_4417_; lean_object* v_v_4418_; lean_object* v_size_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4424_; 
v_k_4417_ = lean_ctor_get(v_d_4334_, 0);
lean_inc(v_k_4417_);
v_v_4418_ = lean_ctor_get(v_d_4334_, 1);
lean_inc(v_v_4418_);
lean_dec_ref(v_d_4334_);
v_size_4419_ = lean_ctor_get(v_l_4328_, 0);
v___x_4420_ = lean_unsigned_to_nat(1u);
v___x_4421_ = lean_nat_add(v___x_4420_, v_size_4325_);
lean_dec(v_size_4325_);
v___x_4422_ = lean_nat_add(v___x_4420_, v_size_4419_);
if (v_isShared_4416_ == 0)
{
lean_ctor_set(v___x_4415_, 4, v_l_4328_);
lean_ctor_set(v___x_4415_, 3, v_tree_4335_);
lean_ctor_set(v___x_4415_, 2, v_v_4418_);
lean_ctor_set(v___x_4415_, 1, v_k_4417_);
lean_ctor_set(v___x_4415_, 0, v___x_4422_);
v___x_4424_ = v___x_4415_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v___x_4422_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v_k_4417_);
lean_ctor_set(v_reuseFailAlloc_4428_, 2, v_v_4418_);
lean_ctor_set(v_reuseFailAlloc_4428_, 3, v_tree_4335_);
lean_ctor_set(v_reuseFailAlloc_4428_, 4, v_l_4328_);
v___x_4424_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
lean_object* v___x_4426_; 
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 4, v_r_4329_);
lean_ctor_set(v___x_4332_, 3, v___x_4424_);
lean_ctor_set(v___x_4332_, 2, v_v_4327_);
lean_ctor_set(v___x_4332_, 1, v_k_4326_);
lean_ctor_set(v___x_4332_, 0, v___x_4421_);
v___x_4426_ = v___x_4332_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4421_);
lean_ctor_set(v_reuseFailAlloc_4427_, 1, v_k_4326_);
lean_ctor_set(v_reuseFailAlloc_4427_, 2, v_v_4327_);
lean_ctor_set(v_reuseFailAlloc_4427_, 3, v___x_4424_);
lean_ctor_set(v_reuseFailAlloc_4427_, 4, v_r_4329_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
else
{
lean_object* v_k_4429_; lean_object* v_v_4430_; lean_object* v_k_4431_; lean_object* v_v_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4447_; 
lean_dec(v_size_4325_);
v_k_4429_ = lean_ctor_get(v_d_4334_, 0);
lean_inc(v_k_4429_);
v_v_4430_ = lean_ctor_get(v_d_4334_, 1);
lean_inc(v_v_4430_);
lean_dec_ref(v_d_4334_);
v_k_4431_ = lean_ctor_get(v_l_4328_, 1);
v_v_4432_ = lean_ctor_get(v_l_4328_, 2);
v_isSharedCheck_4447_ = !lean_is_exclusive(v_l_4328_);
if (v_isSharedCheck_4447_ == 0)
{
lean_object* v_unused_4448_; lean_object* v_unused_4449_; lean_object* v_unused_4450_; 
v_unused_4448_ = lean_ctor_get(v_l_4328_, 4);
lean_dec(v_unused_4448_);
v_unused_4449_ = lean_ctor_get(v_l_4328_, 3);
lean_dec(v_unused_4449_);
v_unused_4450_ = lean_ctor_get(v_l_4328_, 0);
lean_dec(v_unused_4450_);
v___x_4434_ = v_l_4328_;
v_isShared_4435_ = v_isSharedCheck_4447_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_v_4432_);
lean_inc(v_k_4431_);
lean_dec(v_l_4328_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4447_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4439_; 
v___x_4436_ = lean_unsigned_to_nat(3u);
v___x_4437_ = lean_unsigned_to_nat(1u);
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 4, v_r_4329_);
lean_ctor_set(v___x_4434_, 3, v_r_4329_);
lean_ctor_set(v___x_4434_, 2, v_v_4430_);
lean_ctor_set(v___x_4434_, 1, v_k_4429_);
lean_ctor_set(v___x_4434_, 0, v___x_4437_);
v___x_4439_ = v___x_4434_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4437_);
lean_ctor_set(v_reuseFailAlloc_4446_, 1, v_k_4429_);
lean_ctor_set(v_reuseFailAlloc_4446_, 2, v_v_4430_);
lean_ctor_set(v_reuseFailAlloc_4446_, 3, v_r_4329_);
lean_ctor_set(v_reuseFailAlloc_4446_, 4, v_r_4329_);
v___x_4439_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
lean_object* v___x_4441_; 
if (v_isShared_4416_ == 0)
{
lean_ctor_set(v___x_4415_, 3, v_r_4329_);
lean_ctor_set(v___x_4415_, 0, v___x_4437_);
v___x_4441_ = v___x_4415_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v___x_4437_);
lean_ctor_set(v_reuseFailAlloc_4445_, 1, v_k_4326_);
lean_ctor_set(v_reuseFailAlloc_4445_, 2, v_v_4327_);
lean_ctor_set(v_reuseFailAlloc_4445_, 3, v_r_4329_);
lean_ctor_set(v_reuseFailAlloc_4445_, 4, v_r_4329_);
v___x_4441_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
lean_object* v___x_4443_; 
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 4, v___x_4441_);
lean_ctor_set(v___x_4332_, 3, v___x_4439_);
lean_ctor_set(v___x_4332_, 2, v_v_4432_);
lean_ctor_set(v___x_4332_, 1, v_k_4431_);
lean_ctor_set(v___x_4332_, 0, v___x_4436_);
v___x_4443_ = v___x_4332_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4436_);
lean_ctor_set(v_reuseFailAlloc_4444_, 1, v_k_4431_);
lean_ctor_set(v_reuseFailAlloc_4444_, 2, v_v_4432_);
lean_ctor_set(v_reuseFailAlloc_4444_, 3, v___x_4439_);
lean_ctor_set(v_reuseFailAlloc_4444_, 4, v___x_4441_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4329_) == 0)
{
lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4470_; 
lean_inc(v_v_4327_);
lean_inc(v_k_4326_);
v_isSharedCheck_4470_ = !lean_is_exclusive(v_r_4141_);
if (v_isSharedCheck_4470_ == 0)
{
lean_object* v_unused_4471_; lean_object* v_unused_4472_; lean_object* v_unused_4473_; lean_object* v_unused_4474_; lean_object* v_unused_4475_; 
v_unused_4471_ = lean_ctor_get(v_r_4141_, 4);
lean_dec(v_unused_4471_);
v_unused_4472_ = lean_ctor_get(v_r_4141_, 3);
lean_dec(v_unused_4472_);
v_unused_4473_ = lean_ctor_get(v_r_4141_, 2);
lean_dec(v_unused_4473_);
v_unused_4474_ = lean_ctor_get(v_r_4141_, 1);
lean_dec(v_unused_4474_);
v_unused_4475_ = lean_ctor_get(v_r_4141_, 0);
lean_dec(v_unused_4475_);
v___x_4458_ = v_r_4141_;
v_isShared_4459_ = v_isSharedCheck_4470_;
goto v_resetjp_4457_;
}
else
{
lean_dec(v_r_4141_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4470_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v_k_4460_; lean_object* v_v_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4465_; 
v_k_4460_ = lean_ctor_get(v_d_4334_, 0);
lean_inc(v_k_4460_);
v_v_4461_ = lean_ctor_get(v_d_4334_, 1);
lean_inc(v_v_4461_);
lean_dec_ref(v_d_4334_);
v___x_4462_ = lean_unsigned_to_nat(3u);
v___x_4463_ = lean_unsigned_to_nat(1u);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 4, v_l_4328_);
lean_ctor_set(v___x_4458_, 2, v_v_4461_);
lean_ctor_set(v___x_4458_, 1, v_k_4460_);
lean_ctor_set(v___x_4458_, 0, v___x_4463_);
v___x_4465_ = v___x_4458_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4463_);
lean_ctor_set(v_reuseFailAlloc_4469_, 1, v_k_4460_);
lean_ctor_set(v_reuseFailAlloc_4469_, 2, v_v_4461_);
lean_ctor_set(v_reuseFailAlloc_4469_, 3, v_l_4328_);
lean_ctor_set(v_reuseFailAlloc_4469_, 4, v_l_4328_);
v___x_4465_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
lean_object* v___x_4467_; 
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 4, v_r_4329_);
lean_ctor_set(v___x_4332_, 3, v___x_4465_);
lean_ctor_set(v___x_4332_, 2, v_v_4327_);
lean_ctor_set(v___x_4332_, 1, v_k_4326_);
lean_ctor_set(v___x_4332_, 0, v___x_4462_);
v___x_4467_ = v___x_4332_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4462_);
lean_ctor_set(v_reuseFailAlloc_4468_, 1, v_k_4326_);
lean_ctor_set(v_reuseFailAlloc_4468_, 2, v_v_4327_);
lean_ctor_set(v_reuseFailAlloc_4468_, 3, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4468_, 4, v_r_4329_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
}
else
{
lean_object* v_k_4476_; lean_object* v_v_4477_; lean_object* v___x_4478_; lean_object* v___x_4480_; 
v_k_4476_ = lean_ctor_get(v_d_4334_, 0);
lean_inc(v_k_4476_);
v_v_4477_ = lean_ctor_get(v_d_4334_, 1);
lean_inc(v_v_4477_);
lean_dec_ref(v_d_4334_);
v___x_4478_ = lean_unsigned_to_nat(2u);
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 4, v_r_4141_);
lean_ctor_set(v___x_4332_, 3, v_r_4329_);
lean_ctor_set(v___x_4332_, 2, v_v_4477_);
lean_ctor_set(v___x_4332_, 1, v_k_4476_);
lean_ctor_set(v___x_4332_, 0, v___x_4478_);
v___x_4480_ = v___x_4332_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4478_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4481_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4481_, 3, v_r_4329_);
lean_ctor_set(v_reuseFailAlloc_4481_, 4, v_r_4141_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
}
}
else
{
lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4650_; 
lean_inc(v_r_4329_);
lean_inc(v_v_4327_);
lean_inc(v_k_4326_);
v_isSharedCheck_4650_ = !lean_is_exclusive(v_r_4141_);
if (v_isSharedCheck_4650_ == 0)
{
lean_object* v_unused_4651_; lean_object* v_unused_4652_; lean_object* v_unused_4653_; lean_object* v_unused_4654_; lean_object* v_unused_4655_; 
v_unused_4651_ = lean_ctor_get(v_r_4141_, 4);
lean_dec(v_unused_4651_);
v_unused_4652_ = lean_ctor_get(v_r_4141_, 3);
lean_dec(v_unused_4652_);
v_unused_4653_ = lean_ctor_get(v_r_4141_, 2);
lean_dec(v_unused_4653_);
v_unused_4654_ = lean_ctor_get(v_r_4141_, 1);
lean_dec(v_unused_4654_);
v_unused_4655_ = lean_ctor_get(v_r_4141_, 0);
lean_dec(v_unused_4655_);
v___x_4489_ = v_r_4141_;
v_isShared_4490_ = v_isSharedCheck_4650_;
goto v_resetjp_4488_;
}
else
{
lean_dec(v_r_4141_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4650_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v_d_4491_; lean_object* v_tree_4492_; 
v_d_4491_ = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(v_k_4326_, v_v_4327_, v_l_4328_, v_r_4329_);
v_tree_4492_ = lean_ctor_get(v_d_4491_, 2);
lean_inc(v_tree_4492_);
if (lean_obj_tag(v_tree_4492_) == 0)
{
lean_object* v_k_4493_; lean_object* v_v_4494_; lean_object* v_size_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; uint8_t v___x_4498_; 
v_k_4493_ = lean_ctor_get(v_d_4491_, 0);
lean_inc(v_k_4493_);
v_v_4494_ = lean_ctor_get(v_d_4491_, 1);
lean_inc(v_v_4494_);
lean_dec_ref(v_d_4491_);
v_size_4495_ = lean_ctor_get(v_tree_4492_, 0);
v___x_4496_ = lean_unsigned_to_nat(3u);
v___x_4497_ = lean_nat_mul(v___x_4496_, v_size_4495_);
v___x_4498_ = lean_nat_dec_lt(v___x_4497_, v_size_4320_);
lean_dec(v___x_4497_);
if (v___x_4498_ == 0)
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4503_; 
lean_dec(v_r_4324_);
v___x_4499_ = lean_unsigned_to_nat(1u);
v___x_4500_ = lean_nat_add(v___x_4499_, v_size_4320_);
v___x_4501_ = lean_nat_add(v___x_4500_, v_size_4495_);
lean_dec(v___x_4500_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 4, v_tree_4492_);
lean_ctor_set(v___x_4489_, 3, v_l_4140_);
lean_ctor_set(v___x_4489_, 2, v_v_4494_);
lean_ctor_set(v___x_4489_, 1, v_k_4493_);
lean_ctor_set(v___x_4489_, 0, v___x_4501_);
v___x_4503_ = v___x_4489_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4501_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v_k_4493_);
lean_ctor_set(v_reuseFailAlloc_4504_, 2, v_v_4494_);
lean_ctor_set(v_reuseFailAlloc_4504_, 3, v_l_4140_);
lean_ctor_set(v_reuseFailAlloc_4504_, 4, v_tree_4492_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
else
{
lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4576_; 
lean_inc(v_l_4323_);
lean_inc(v_v_4322_);
lean_inc(v_k_4321_);
lean_inc(v_size_4320_);
v_isSharedCheck_4576_ = !lean_is_exclusive(v_l_4140_);
if (v_isSharedCheck_4576_ == 0)
{
lean_object* v_unused_4577_; lean_object* v_unused_4578_; lean_object* v_unused_4579_; lean_object* v_unused_4580_; lean_object* v_unused_4581_; 
v_unused_4577_ = lean_ctor_get(v_l_4140_, 4);
lean_dec(v_unused_4577_);
v_unused_4578_ = lean_ctor_get(v_l_4140_, 3);
lean_dec(v_unused_4578_);
v_unused_4579_ = lean_ctor_get(v_l_4140_, 2);
lean_dec(v_unused_4579_);
v_unused_4580_ = lean_ctor_get(v_l_4140_, 1);
lean_dec(v_unused_4580_);
v_unused_4581_ = lean_ctor_get(v_l_4140_, 0);
lean_dec(v_unused_4581_);
v___x_4506_ = v_l_4140_;
v_isShared_4507_ = v_isSharedCheck_4576_;
goto v_resetjp_4505_;
}
else
{
lean_dec(v_l_4140_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4576_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
if (lean_obj_tag(v_l_4323_) == 0)
{
if (lean_obj_tag(v_r_4324_) == 0)
{
lean_object* v_size_4508_; lean_object* v_size_4509_; lean_object* v_k_4510_; lean_object* v_v_4511_; lean_object* v_l_4512_; lean_object* v_r_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; uint8_t v___x_4516_; 
v_size_4508_ = lean_ctor_get(v_l_4323_, 0);
v_size_4509_ = lean_ctor_get(v_r_4324_, 0);
v_k_4510_ = lean_ctor_get(v_r_4324_, 1);
v_v_4511_ = lean_ctor_get(v_r_4324_, 2);
v_l_4512_ = lean_ctor_get(v_r_4324_, 3);
v_r_4513_ = lean_ctor_get(v_r_4324_, 4);
v___x_4514_ = lean_unsigned_to_nat(2u);
v___x_4515_ = lean_nat_mul(v___x_4514_, v_size_4508_);
v___x_4516_ = lean_nat_dec_lt(v_size_4509_, v___x_4515_);
lean_dec(v___x_4515_);
if (v___x_4516_ == 0)
{
lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4555_; 
lean_inc(v_r_4513_);
lean_inc(v_l_4512_);
lean_inc(v_v_4511_);
lean_inc(v_k_4510_);
lean_del_object(v___x_4506_);
v_isSharedCheck_4555_ = !lean_is_exclusive(v_r_4324_);
if (v_isSharedCheck_4555_ == 0)
{
lean_object* v_unused_4556_; lean_object* v_unused_4557_; lean_object* v_unused_4558_; lean_object* v_unused_4559_; lean_object* v_unused_4560_; 
v_unused_4556_ = lean_ctor_get(v_r_4324_, 4);
lean_dec(v_unused_4556_);
v_unused_4557_ = lean_ctor_get(v_r_4324_, 3);
lean_dec(v_unused_4557_);
v_unused_4558_ = lean_ctor_get(v_r_4324_, 2);
lean_dec(v_unused_4558_);
v_unused_4559_ = lean_ctor_get(v_r_4324_, 1);
lean_dec(v_unused_4559_);
v_unused_4560_ = lean_ctor_get(v_r_4324_, 0);
lean_dec(v_unused_4560_);
v___x_4518_ = v_r_4324_;
v_isShared_4519_ = v_isSharedCheck_4555_;
goto v_resetjp_4517_;
}
else
{
lean_dec(v_r_4324_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4555_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___x_4543_; lean_object* v___y_4545_; 
v___x_4520_ = lean_unsigned_to_nat(1u);
v___x_4521_ = lean_nat_add(v___x_4520_, v_size_4320_);
lean_dec(v_size_4320_);
v___x_4522_ = lean_nat_add(v___x_4521_, v_size_4495_);
lean_dec(v___x_4521_);
v___x_4543_ = lean_nat_add(v___x_4520_, v_size_4508_);
if (lean_obj_tag(v_l_4512_) == 0)
{
lean_object* v_size_4553_; 
v_size_4553_ = lean_ctor_get(v_l_4512_, 0);
lean_inc(v_size_4553_);
v___y_4545_ = v_size_4553_;
goto v___jp_4544_;
}
else
{
lean_object* v___x_4554_; 
v___x_4554_ = lean_unsigned_to_nat(0u);
v___y_4545_ = v___x_4554_;
goto v___jp_4544_;
}
v___jp_4523_:
{
lean_object* v___x_4527_; lean_object* v___x_4529_; 
v___x_4527_ = lean_nat_add(v___y_4524_, v___y_4526_);
lean_dec(v___y_4526_);
lean_dec(v___y_4524_);
lean_inc_ref(v_tree_4492_);
if (v_isShared_4519_ == 0)
{
lean_ctor_set(v___x_4518_, 4, v_tree_4492_);
lean_ctor_set(v___x_4518_, 3, v_r_4513_);
lean_ctor_set(v___x_4518_, 2, v_v_4494_);
lean_ctor_set(v___x_4518_, 1, v_k_4493_);
lean_ctor_set(v___x_4518_, 0, v___x_4527_);
v___x_4529_ = v___x_4518_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4527_);
lean_ctor_set(v_reuseFailAlloc_4542_, 1, v_k_4493_);
lean_ctor_set(v_reuseFailAlloc_4542_, 2, v_v_4494_);
lean_ctor_set(v_reuseFailAlloc_4542_, 3, v_r_4513_);
lean_ctor_set(v_reuseFailAlloc_4542_, 4, v_tree_4492_);
v___x_4529_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
v_isSharedCheck_4536_ = !lean_is_exclusive(v_tree_4492_);
if (v_isSharedCheck_4536_ == 0)
{
lean_object* v_unused_4537_; lean_object* v_unused_4538_; lean_object* v_unused_4539_; lean_object* v_unused_4540_; lean_object* v_unused_4541_; 
v_unused_4537_ = lean_ctor_get(v_tree_4492_, 4);
lean_dec(v_unused_4537_);
v_unused_4538_ = lean_ctor_get(v_tree_4492_, 3);
lean_dec(v_unused_4538_);
v_unused_4539_ = lean_ctor_get(v_tree_4492_, 2);
lean_dec(v_unused_4539_);
v_unused_4540_ = lean_ctor_get(v_tree_4492_, 1);
lean_dec(v_unused_4540_);
v_unused_4541_ = lean_ctor_get(v_tree_4492_, 0);
lean_dec(v_unused_4541_);
v___x_4531_ = v_tree_4492_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_dec(v_tree_4492_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
lean_ctor_set(v___x_4531_, 4, v___x_4529_);
lean_ctor_set(v___x_4531_, 3, v___y_4525_);
lean_ctor_set(v___x_4531_, 2, v_v_4511_);
lean_ctor_set(v___x_4531_, 1, v_k_4510_);
lean_ctor_set(v___x_4531_, 0, v___x_4522_);
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4522_);
lean_ctor_set(v_reuseFailAlloc_4535_, 1, v_k_4510_);
lean_ctor_set(v_reuseFailAlloc_4535_, 2, v_v_4511_);
lean_ctor_set(v_reuseFailAlloc_4535_, 3, v___y_4525_);
lean_ctor_set(v_reuseFailAlloc_4535_, 4, v___x_4529_);
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
v___jp_4544_:
{
lean_object* v___x_4546_; lean_object* v___x_4548_; 
v___x_4546_ = lean_nat_add(v___x_4543_, v___y_4545_);
lean_dec(v___y_4545_);
lean_dec(v___x_4543_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 4, v_l_4512_);
lean_ctor_set(v___x_4489_, 3, v_l_4323_);
lean_ctor_set(v___x_4489_, 2, v_v_4322_);
lean_ctor_set(v___x_4489_, 1, v_k_4321_);
lean_ctor_set(v___x_4489_, 0, v___x_4546_);
v___x_4548_ = v___x_4489_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4546_);
lean_ctor_set(v_reuseFailAlloc_4552_, 1, v_k_4321_);
lean_ctor_set(v_reuseFailAlloc_4552_, 2, v_v_4322_);
lean_ctor_set(v_reuseFailAlloc_4552_, 3, v_l_4323_);
lean_ctor_set(v_reuseFailAlloc_4552_, 4, v_l_4512_);
v___x_4548_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
lean_object* v___x_4549_; 
v___x_4549_ = lean_nat_add(v___x_4520_, v_size_4495_);
if (lean_obj_tag(v_r_4513_) == 0)
{
lean_object* v_size_4550_; 
v_size_4550_ = lean_ctor_get(v_r_4513_, 0);
lean_inc(v_size_4550_);
v___y_4524_ = v___x_4549_;
v___y_4525_ = v___x_4548_;
v___y_4526_ = v_size_4550_;
goto v___jp_4523_;
}
else
{
lean_object* v___x_4551_; 
v___x_4551_ = lean_unsigned_to_nat(0u);
v___y_4524_ = v___x_4549_;
v___y_4525_ = v___x_4548_;
v___y_4526_ = v___x_4551_;
goto v___jp_4523_;
}
}
}
}
}
else
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4567_; 
v___x_4561_ = lean_unsigned_to_nat(1u);
v___x_4562_ = lean_nat_add(v___x_4561_, v_size_4320_);
lean_dec(v_size_4320_);
v___x_4563_ = lean_nat_add(v___x_4562_, v_size_4495_);
lean_dec(v___x_4562_);
v___x_4564_ = lean_nat_add(v___x_4561_, v_size_4495_);
v___x_4565_ = lean_nat_add(v___x_4564_, v_size_4509_);
lean_dec(v___x_4564_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 4, v_tree_4492_);
lean_ctor_set(v___x_4489_, 3, v_r_4324_);
lean_ctor_set(v___x_4489_, 2, v_v_4494_);
lean_ctor_set(v___x_4489_, 1, v_k_4493_);
lean_ctor_set(v___x_4489_, 0, v___x_4565_);
v___x_4567_ = v___x_4489_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4565_);
lean_ctor_set(v_reuseFailAlloc_4571_, 1, v_k_4493_);
lean_ctor_set(v_reuseFailAlloc_4571_, 2, v_v_4494_);
lean_ctor_set(v_reuseFailAlloc_4571_, 3, v_r_4324_);
lean_ctor_set(v_reuseFailAlloc_4571_, 4, v_tree_4492_);
v___x_4567_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
lean_object* v___x_4569_; 
if (v_isShared_4507_ == 0)
{
lean_ctor_set(v___x_4506_, 4, v___x_4567_);
lean_ctor_set(v___x_4506_, 0, v___x_4563_);
v___x_4569_ = v___x_4506_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4563_);
lean_ctor_set(v_reuseFailAlloc_4570_, 1, v_k_4321_);
lean_ctor_set(v_reuseFailAlloc_4570_, 2, v_v_4322_);
lean_ctor_set(v_reuseFailAlloc_4570_, 3, v_l_4323_);
lean_ctor_set(v_reuseFailAlloc_4570_, 4, v___x_4567_);
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
lean_object* v___x_4572_; lean_object* v___x_4573_; 
lean_dec_ref(v_l_4323_);
lean_del_object(v___x_4506_);
lean_dec(v_v_4494_);
lean_dec(v_k_4493_);
lean_dec_ref(v_tree_4492_);
lean_del_object(v___x_4489_);
lean_dec(v_v_4322_);
lean_dec(v_k_4321_);
lean_dec(v_size_4320_);
v___x_4572_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3);
v___x_4573_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4572_);
return v___x_4573_;
}
}
else
{
lean_object* v___x_4574_; lean_object* v___x_4575_; 
lean_del_object(v___x_4506_);
lean_dec(v_v_4494_);
lean_dec(v_k_4493_);
lean_dec_ref(v_tree_4492_);
lean_del_object(v___x_4489_);
lean_dec(v_r_4324_);
lean_dec(v_v_4322_);
lean_dec(v_k_4321_);
lean_dec(v_size_4320_);
v___x_4574_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4);
v___x_4575_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4574_);
return v___x_4575_;
}
}
}
}
else
{
if (lean_obj_tag(v_l_4323_) == 0)
{
lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4607_; 
lean_inc_ref(v_l_4323_);
lean_inc(v_v_4322_);
lean_inc(v_k_4321_);
lean_inc(v_size_4320_);
v_isSharedCheck_4607_ = !lean_is_exclusive(v_l_4140_);
if (v_isSharedCheck_4607_ == 0)
{
lean_object* v_unused_4608_; lean_object* v_unused_4609_; lean_object* v_unused_4610_; lean_object* v_unused_4611_; lean_object* v_unused_4612_; 
v_unused_4608_ = lean_ctor_get(v_l_4140_, 4);
lean_dec(v_unused_4608_);
v_unused_4609_ = lean_ctor_get(v_l_4140_, 3);
lean_dec(v_unused_4609_);
v_unused_4610_ = lean_ctor_get(v_l_4140_, 2);
lean_dec(v_unused_4610_);
v_unused_4611_ = lean_ctor_get(v_l_4140_, 1);
lean_dec(v_unused_4611_);
v_unused_4612_ = lean_ctor_get(v_l_4140_, 0);
lean_dec(v_unused_4612_);
v___x_4583_ = v_l_4140_;
v_isShared_4584_ = v_isSharedCheck_4607_;
goto v_resetjp_4582_;
}
else
{
lean_dec(v_l_4140_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4607_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
if (lean_obj_tag(v_r_4324_) == 0)
{
lean_object* v_k_4585_; lean_object* v_v_4586_; lean_object* v_size_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4592_; 
v_k_4585_ = lean_ctor_get(v_d_4491_, 0);
lean_inc(v_k_4585_);
v_v_4586_ = lean_ctor_get(v_d_4491_, 1);
lean_inc(v_v_4586_);
lean_dec_ref(v_d_4491_);
v_size_4587_ = lean_ctor_get(v_r_4324_, 0);
v___x_4588_ = lean_unsigned_to_nat(1u);
v___x_4589_ = lean_nat_add(v___x_4588_, v_size_4320_);
lean_dec(v_size_4320_);
v___x_4590_ = lean_nat_add(v___x_4588_, v_size_4587_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 4, v_tree_4492_);
lean_ctor_set(v___x_4489_, 3, v_r_4324_);
lean_ctor_set(v___x_4489_, 2, v_v_4586_);
lean_ctor_set(v___x_4489_, 1, v_k_4585_);
lean_ctor_set(v___x_4489_, 0, v___x_4590_);
v___x_4592_ = v___x_4489_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4590_);
lean_ctor_set(v_reuseFailAlloc_4596_, 1, v_k_4585_);
lean_ctor_set(v_reuseFailAlloc_4596_, 2, v_v_4586_);
lean_ctor_set(v_reuseFailAlloc_4596_, 3, v_r_4324_);
lean_ctor_set(v_reuseFailAlloc_4596_, 4, v_tree_4492_);
v___x_4592_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
lean_object* v___x_4594_; 
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 4, v___x_4592_);
lean_ctor_set(v___x_4583_, 0, v___x_4589_);
v___x_4594_ = v___x_4583_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4589_);
lean_ctor_set(v_reuseFailAlloc_4595_, 1, v_k_4321_);
lean_ctor_set(v_reuseFailAlloc_4595_, 2, v_v_4322_);
lean_ctor_set(v_reuseFailAlloc_4595_, 3, v_l_4323_);
lean_ctor_set(v_reuseFailAlloc_4595_, 4, v___x_4592_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
else
{
lean_object* v_k_4597_; lean_object* v_v_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4602_; 
lean_dec(v_size_4320_);
v_k_4597_ = lean_ctor_get(v_d_4491_, 0);
lean_inc(v_k_4597_);
v_v_4598_ = lean_ctor_get(v_d_4491_, 1);
lean_inc(v_v_4598_);
lean_dec_ref(v_d_4491_);
v___x_4599_ = lean_unsigned_to_nat(3u);
v___x_4600_ = lean_unsigned_to_nat(1u);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 4, v_r_4324_);
lean_ctor_set(v___x_4489_, 3, v_r_4324_);
lean_ctor_set(v___x_4489_, 2, v_v_4598_);
lean_ctor_set(v___x_4489_, 1, v_k_4597_);
lean_ctor_set(v___x_4489_, 0, v___x_4600_);
v___x_4602_ = v___x_4489_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4600_);
lean_ctor_set(v_reuseFailAlloc_4606_, 1, v_k_4597_);
lean_ctor_set(v_reuseFailAlloc_4606_, 2, v_v_4598_);
lean_ctor_set(v_reuseFailAlloc_4606_, 3, v_r_4324_);
lean_ctor_set(v_reuseFailAlloc_4606_, 4, v_r_4324_);
v___x_4602_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
lean_object* v___x_4604_; 
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 4, v___x_4602_);
lean_ctor_set(v___x_4583_, 0, v___x_4599_);
v___x_4604_ = v___x_4583_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4599_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_k_4321_);
lean_ctor_set(v_reuseFailAlloc_4605_, 2, v_v_4322_);
lean_ctor_set(v_reuseFailAlloc_4605_, 3, v_l_4323_);
lean_ctor_set(v_reuseFailAlloc_4605_, 4, v___x_4602_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4324_) == 0)
{
lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4638_; 
lean_inc(v_l_4323_);
lean_inc(v_v_4322_);
lean_inc(v_k_4321_);
v_isSharedCheck_4638_ = !lean_is_exclusive(v_l_4140_);
if (v_isSharedCheck_4638_ == 0)
{
lean_object* v_unused_4639_; lean_object* v_unused_4640_; lean_object* v_unused_4641_; lean_object* v_unused_4642_; lean_object* v_unused_4643_; 
v_unused_4639_ = lean_ctor_get(v_l_4140_, 4);
lean_dec(v_unused_4639_);
v_unused_4640_ = lean_ctor_get(v_l_4140_, 3);
lean_dec(v_unused_4640_);
v_unused_4641_ = lean_ctor_get(v_l_4140_, 2);
lean_dec(v_unused_4641_);
v_unused_4642_ = lean_ctor_get(v_l_4140_, 1);
lean_dec(v_unused_4642_);
v_unused_4643_ = lean_ctor_get(v_l_4140_, 0);
lean_dec(v_unused_4643_);
v___x_4614_ = v_l_4140_;
v_isShared_4615_ = v_isSharedCheck_4638_;
goto v_resetjp_4613_;
}
else
{
lean_dec(v_l_4140_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4638_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v_k_4616_; lean_object* v_v_4617_; lean_object* v_k_4618_; lean_object* v_v_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4634_; 
v_k_4616_ = lean_ctor_get(v_d_4491_, 0);
lean_inc(v_k_4616_);
v_v_4617_ = lean_ctor_get(v_d_4491_, 1);
lean_inc(v_v_4617_);
lean_dec_ref(v_d_4491_);
v_k_4618_ = lean_ctor_get(v_r_4324_, 1);
v_v_4619_ = lean_ctor_get(v_r_4324_, 2);
v_isSharedCheck_4634_ = !lean_is_exclusive(v_r_4324_);
if (v_isSharedCheck_4634_ == 0)
{
lean_object* v_unused_4635_; lean_object* v_unused_4636_; lean_object* v_unused_4637_; 
v_unused_4635_ = lean_ctor_get(v_r_4324_, 4);
lean_dec(v_unused_4635_);
v_unused_4636_ = lean_ctor_get(v_r_4324_, 3);
lean_dec(v_unused_4636_);
v_unused_4637_ = lean_ctor_get(v_r_4324_, 0);
lean_dec(v_unused_4637_);
v___x_4621_ = v_r_4324_;
v_isShared_4622_ = v_isSharedCheck_4634_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_v_4619_);
lean_inc(v_k_4618_);
lean_dec(v_r_4324_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4634_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4626_; 
v___x_4623_ = lean_unsigned_to_nat(3u);
v___x_4624_ = lean_unsigned_to_nat(1u);
if (v_isShared_4622_ == 0)
{
lean_ctor_set(v___x_4621_, 4, v_l_4323_);
lean_ctor_set(v___x_4621_, 3, v_l_4323_);
lean_ctor_set(v___x_4621_, 2, v_v_4322_);
lean_ctor_set(v___x_4621_, 1, v_k_4321_);
lean_ctor_set(v___x_4621_, 0, v___x_4624_);
v___x_4626_ = v___x_4621_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4624_);
lean_ctor_set(v_reuseFailAlloc_4633_, 1, v_k_4321_);
lean_ctor_set(v_reuseFailAlloc_4633_, 2, v_v_4322_);
lean_ctor_set(v_reuseFailAlloc_4633_, 3, v_l_4323_);
lean_ctor_set(v_reuseFailAlloc_4633_, 4, v_l_4323_);
v___x_4626_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
lean_object* v___x_4628_; 
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 4, v_l_4323_);
lean_ctor_set(v___x_4489_, 3, v_l_4323_);
lean_ctor_set(v___x_4489_, 2, v_v_4617_);
lean_ctor_set(v___x_4489_, 1, v_k_4616_);
lean_ctor_set(v___x_4489_, 0, v___x_4624_);
v___x_4628_ = v___x_4489_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v___x_4624_);
lean_ctor_set(v_reuseFailAlloc_4632_, 1, v_k_4616_);
lean_ctor_set(v_reuseFailAlloc_4632_, 2, v_v_4617_);
lean_ctor_set(v_reuseFailAlloc_4632_, 3, v_l_4323_);
lean_ctor_set(v_reuseFailAlloc_4632_, 4, v_l_4323_);
v___x_4628_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
lean_object* v___x_4630_; 
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 4, v___x_4628_);
lean_ctor_set(v___x_4614_, 3, v___x_4626_);
lean_ctor_set(v___x_4614_, 2, v_v_4619_);
lean_ctor_set(v___x_4614_, 1, v_k_4618_);
lean_ctor_set(v___x_4614_, 0, v___x_4623_);
v___x_4630_ = v___x_4614_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4623_);
lean_ctor_set(v_reuseFailAlloc_4631_, 1, v_k_4618_);
lean_ctor_set(v_reuseFailAlloc_4631_, 2, v_v_4619_);
lean_ctor_set(v_reuseFailAlloc_4631_, 3, v___x_4626_);
lean_ctor_set(v_reuseFailAlloc_4631_, 4, v___x_4628_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
}
}
else
{
lean_object* v_k_4644_; lean_object* v_v_4645_; lean_object* v___x_4646_; lean_object* v___x_4648_; 
v_k_4644_ = lean_ctor_get(v_d_4491_, 0);
lean_inc(v_k_4644_);
v_v_4645_ = lean_ctor_get(v_d_4491_, 1);
lean_inc(v_v_4645_);
lean_dec_ref(v_d_4491_);
v___x_4646_ = lean_unsigned_to_nat(2u);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 4, v_r_4324_);
lean_ctor_set(v___x_4489_, 3, v_l_4140_);
lean_ctor_set(v___x_4489_, 2, v_v_4645_);
lean_ctor_set(v___x_4489_, 1, v_k_4644_);
lean_ctor_set(v___x_4489_, 0, v___x_4646_);
v___x_4648_ = v___x_4489_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v___x_4646_);
lean_ctor_set(v_reuseFailAlloc_4649_, 1, v_k_4644_);
lean_ctor_set(v_reuseFailAlloc_4649_, 2, v_v_4645_);
lean_ctor_set(v_reuseFailAlloc_4649_, 3, v_l_4140_);
lean_ctor_set(v_reuseFailAlloc_4649_, 4, v_r_4324_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
}
}
}
}
}
else
{
return v_l_4140_;
}
}
else
{
return v_r_4141_;
}
}
default: 
{
lean_object* v___x_4656_; 
v___x_4656_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4135_, v_k_4136_, v_r_4141_);
if (lean_obj_tag(v___x_4656_) == 0)
{
if (lean_obj_tag(v_l_4140_) == 0)
{
lean_object* v_size_4657_; lean_object* v_size_4658_; lean_object* v_k_4659_; lean_object* v_v_4660_; lean_object* v_l_4661_; lean_object* v_r_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; uint8_t v___x_4665_; 
v_size_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_size_4657_);
v_size_4658_ = lean_ctor_get(v_l_4140_, 0);
v_k_4659_ = lean_ctor_get(v_l_4140_, 1);
v_v_4660_ = lean_ctor_get(v_l_4140_, 2);
v_l_4661_ = lean_ctor_get(v_l_4140_, 3);
v_r_4662_ = lean_ctor_get(v_l_4140_, 4);
lean_inc(v_r_4662_);
v___x_4663_ = lean_unsigned_to_nat(3u);
v___x_4664_ = lean_nat_mul(v___x_4663_, v_size_4657_);
v___x_4665_ = lean_nat_dec_lt(v___x_4664_, v_size_4658_);
lean_dec(v___x_4664_);
if (v___x_4665_ == 0)
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4670_; 
lean_dec(v_r_4662_);
v___x_4666_ = lean_unsigned_to_nat(1u);
v___x_4667_ = lean_nat_add(v___x_4666_, v_size_4658_);
v___x_4668_ = lean_nat_add(v___x_4667_, v_size_4657_);
lean_dec(v_size_4657_);
lean_dec(v___x_4667_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 4, v___x_4656_);
lean_ctor_set(v___x_4143_, 0, v___x_4668_);
v___x_4670_ = v___x_4143_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v___x_4668_);
lean_ctor_set(v_reuseFailAlloc_4671_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4671_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4671_, 3, v_l_4140_);
lean_ctor_set(v_reuseFailAlloc_4671_, 4, v___x_4656_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
else
{
lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4743_; 
lean_inc(v_l_4661_);
lean_inc(v_v_4660_);
lean_inc(v_k_4659_);
lean_inc(v_size_4658_);
v_isSharedCheck_4743_ = !lean_is_exclusive(v_l_4140_);
if (v_isSharedCheck_4743_ == 0)
{
lean_object* v_unused_4744_; lean_object* v_unused_4745_; lean_object* v_unused_4746_; lean_object* v_unused_4747_; lean_object* v_unused_4748_; 
v_unused_4744_ = lean_ctor_get(v_l_4140_, 4);
lean_dec(v_unused_4744_);
v_unused_4745_ = lean_ctor_get(v_l_4140_, 3);
lean_dec(v_unused_4745_);
v_unused_4746_ = lean_ctor_get(v_l_4140_, 2);
lean_dec(v_unused_4746_);
v_unused_4747_ = lean_ctor_get(v_l_4140_, 1);
lean_dec(v_unused_4747_);
v_unused_4748_ = lean_ctor_get(v_l_4140_, 0);
lean_dec(v_unused_4748_);
v___x_4673_ = v_l_4140_;
v_isShared_4674_ = v_isSharedCheck_4743_;
goto v_resetjp_4672_;
}
else
{
lean_dec(v_l_4140_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4743_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
if (lean_obj_tag(v_l_4661_) == 0)
{
if (lean_obj_tag(v_r_4662_) == 0)
{
lean_object* v_size_4675_; lean_object* v_size_4676_; lean_object* v_k_4677_; lean_object* v_v_4678_; lean_object* v_l_4679_; lean_object* v_r_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; uint8_t v___x_4683_; 
v_size_4675_ = lean_ctor_get(v_l_4661_, 0);
v_size_4676_ = lean_ctor_get(v_r_4662_, 0);
v_k_4677_ = lean_ctor_get(v_r_4662_, 1);
v_v_4678_ = lean_ctor_get(v_r_4662_, 2);
v_l_4679_ = lean_ctor_get(v_r_4662_, 3);
v_r_4680_ = lean_ctor_get(v_r_4662_, 4);
v___x_4681_ = lean_unsigned_to_nat(2u);
v___x_4682_ = lean_nat_mul(v___x_4681_, v_size_4675_);
v___x_4683_ = lean_nat_dec_lt(v_size_4676_, v___x_4682_);
lean_dec(v___x_4682_);
if (v___x_4683_ == 0)
{
lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4713_; 
lean_inc(v_r_4680_);
lean_inc(v_l_4679_);
lean_inc(v_v_4678_);
lean_inc(v_k_4677_);
v_isSharedCheck_4713_ = !lean_is_exclusive(v_r_4662_);
if (v_isSharedCheck_4713_ == 0)
{
lean_object* v_unused_4714_; lean_object* v_unused_4715_; lean_object* v_unused_4716_; lean_object* v_unused_4717_; lean_object* v_unused_4718_; 
v_unused_4714_ = lean_ctor_get(v_r_4662_, 4);
lean_dec(v_unused_4714_);
v_unused_4715_ = lean_ctor_get(v_r_4662_, 3);
lean_dec(v_unused_4715_);
v_unused_4716_ = lean_ctor_get(v_r_4662_, 2);
lean_dec(v_unused_4716_);
v_unused_4717_ = lean_ctor_get(v_r_4662_, 1);
lean_dec(v_unused_4717_);
v_unused_4718_ = lean_ctor_get(v_r_4662_, 0);
lean_dec(v_unused_4718_);
v___x_4685_ = v_r_4662_;
v_isShared_4686_ = v_isSharedCheck_4713_;
goto v_resetjp_4684_;
}
else
{
lean_dec(v_r_4662_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4713_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___y_4691_; lean_object* v___y_4692_; lean_object* v___y_4693_; lean_object* v___x_4701_; lean_object* v___y_4703_; 
v___x_4687_ = lean_unsigned_to_nat(1u);
v___x_4688_ = lean_nat_add(v___x_4687_, v_size_4658_);
lean_dec(v_size_4658_);
v___x_4689_ = lean_nat_add(v___x_4688_, v_size_4657_);
lean_dec(v___x_4688_);
v___x_4701_ = lean_nat_add(v___x_4687_, v_size_4675_);
if (lean_obj_tag(v_l_4679_) == 0)
{
lean_object* v_size_4711_; 
v_size_4711_ = lean_ctor_get(v_l_4679_, 0);
lean_inc(v_size_4711_);
v___y_4703_ = v_size_4711_;
goto v___jp_4702_;
}
else
{
lean_object* v___x_4712_; 
v___x_4712_ = lean_unsigned_to_nat(0u);
v___y_4703_ = v___x_4712_;
goto v___jp_4702_;
}
v___jp_4690_:
{
lean_object* v___x_4694_; lean_object* v___x_4696_; 
v___x_4694_ = lean_nat_add(v___y_4692_, v___y_4693_);
lean_dec(v___y_4693_);
lean_dec(v___y_4692_);
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 4, v___x_4656_);
lean_ctor_set(v___x_4685_, 3, v_r_4680_);
lean_ctor_set(v___x_4685_, 2, v_v_4139_);
lean_ctor_set(v___x_4685_, 1, v_k_4138_);
lean_ctor_set(v___x_4685_, 0, v___x_4694_);
v___x_4696_ = v___x_4685_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v___x_4694_);
lean_ctor_set(v_reuseFailAlloc_4700_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4700_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4700_, 3, v_r_4680_);
lean_ctor_set(v_reuseFailAlloc_4700_, 4, v___x_4656_);
v___x_4696_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
lean_object* v___x_4698_; 
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 4, v___x_4696_);
lean_ctor_set(v___x_4673_, 3, v___y_4691_);
lean_ctor_set(v___x_4673_, 2, v_v_4678_);
lean_ctor_set(v___x_4673_, 1, v_k_4677_);
lean_ctor_set(v___x_4673_, 0, v___x_4689_);
v___x_4698_ = v___x_4673_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v___x_4689_);
lean_ctor_set(v_reuseFailAlloc_4699_, 1, v_k_4677_);
lean_ctor_set(v_reuseFailAlloc_4699_, 2, v_v_4678_);
lean_ctor_set(v_reuseFailAlloc_4699_, 3, v___y_4691_);
lean_ctor_set(v_reuseFailAlloc_4699_, 4, v___x_4696_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
v___jp_4702_:
{
lean_object* v___x_4704_; lean_object* v___x_4706_; 
v___x_4704_ = lean_nat_add(v___x_4701_, v___y_4703_);
lean_dec(v___y_4703_);
lean_dec(v___x_4701_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 4, v_l_4679_);
lean_ctor_set(v___x_4143_, 3, v_l_4661_);
lean_ctor_set(v___x_4143_, 2, v_v_4660_);
lean_ctor_set(v___x_4143_, 1, v_k_4659_);
lean_ctor_set(v___x_4143_, 0, v___x_4704_);
v___x_4706_ = v___x_4143_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v___x_4704_);
lean_ctor_set(v_reuseFailAlloc_4710_, 1, v_k_4659_);
lean_ctor_set(v_reuseFailAlloc_4710_, 2, v_v_4660_);
lean_ctor_set(v_reuseFailAlloc_4710_, 3, v_l_4661_);
lean_ctor_set(v_reuseFailAlloc_4710_, 4, v_l_4679_);
v___x_4706_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
lean_object* v___x_4707_; 
v___x_4707_ = lean_nat_add(v___x_4687_, v_size_4657_);
lean_dec(v_size_4657_);
if (lean_obj_tag(v_r_4680_) == 0)
{
lean_object* v_size_4708_; 
v_size_4708_ = lean_ctor_get(v_r_4680_, 0);
lean_inc(v_size_4708_);
v___y_4691_ = v___x_4706_;
v___y_4692_ = v___x_4707_;
v___y_4693_ = v_size_4708_;
goto v___jp_4690_;
}
else
{
lean_object* v___x_4709_; 
v___x_4709_ = lean_unsigned_to_nat(0u);
v___y_4691_ = v___x_4706_;
v___y_4692_ = v___x_4707_;
v___y_4693_ = v___x_4709_;
goto v___jp_4690_;
}
}
}
}
}
else
{
lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4725_; 
lean_del_object(v___x_4143_);
v___x_4719_ = lean_unsigned_to_nat(1u);
v___x_4720_ = lean_nat_add(v___x_4719_, v_size_4658_);
lean_dec(v_size_4658_);
v___x_4721_ = lean_nat_add(v___x_4720_, v_size_4657_);
lean_dec(v___x_4720_);
v___x_4722_ = lean_nat_add(v___x_4719_, v_size_4657_);
lean_dec(v_size_4657_);
v___x_4723_ = lean_nat_add(v___x_4722_, v_size_4676_);
lean_dec(v___x_4722_);
lean_inc_ref(v___x_4656_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 4, v___x_4656_);
lean_ctor_set(v___x_4673_, 3, v_r_4662_);
lean_ctor_set(v___x_4673_, 2, v_v_4139_);
lean_ctor_set(v___x_4673_, 1, v_k_4138_);
lean_ctor_set(v___x_4673_, 0, v___x_4723_);
v___x_4725_ = v___x_4673_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v___x_4723_);
lean_ctor_set(v_reuseFailAlloc_4738_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4738_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4738_, 3, v_r_4662_);
lean_ctor_set(v_reuseFailAlloc_4738_, 4, v___x_4656_);
v___x_4725_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4732_; 
v_isSharedCheck_4732_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4732_ == 0)
{
lean_object* v_unused_4733_; lean_object* v_unused_4734_; lean_object* v_unused_4735_; lean_object* v_unused_4736_; lean_object* v_unused_4737_; 
v_unused_4733_ = lean_ctor_get(v___x_4656_, 4);
lean_dec(v_unused_4733_);
v_unused_4734_ = lean_ctor_get(v___x_4656_, 3);
lean_dec(v_unused_4734_);
v_unused_4735_ = lean_ctor_get(v___x_4656_, 2);
lean_dec(v_unused_4735_);
v_unused_4736_ = lean_ctor_get(v___x_4656_, 1);
lean_dec(v_unused_4736_);
v_unused_4737_ = lean_ctor_get(v___x_4656_, 0);
lean_dec(v_unused_4737_);
v___x_4727_ = v___x_4656_;
v_isShared_4728_ = v_isSharedCheck_4732_;
goto v_resetjp_4726_;
}
else
{
lean_dec(v___x_4656_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4732_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v___x_4730_; 
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 4, v___x_4725_);
lean_ctor_set(v___x_4727_, 3, v_l_4661_);
lean_ctor_set(v___x_4727_, 2, v_v_4660_);
lean_ctor_set(v___x_4727_, 1, v_k_4659_);
lean_ctor_set(v___x_4727_, 0, v___x_4721_);
v___x_4730_ = v___x_4727_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v___x_4721_);
lean_ctor_set(v_reuseFailAlloc_4731_, 1, v_k_4659_);
lean_ctor_set(v_reuseFailAlloc_4731_, 2, v_v_4660_);
lean_ctor_set(v_reuseFailAlloc_4731_, 3, v_l_4661_);
lean_ctor_set(v_reuseFailAlloc_4731_, 4, v___x_4725_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
}
}
else
{
lean_object* v___x_4739_; lean_object* v___x_4740_; 
lean_dec_ref(v_l_4661_);
lean_del_object(v___x_4673_);
lean_dec(v_v_4660_);
lean_dec(v_k_4659_);
lean_dec(v_size_4658_);
lean_dec(v_size_4657_);
lean_dec_ref(v___x_4656_);
lean_del_object(v___x_4143_);
lean_dec(v_v_4139_);
lean_dec(v_k_4138_);
v___x_4739_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3);
v___x_4740_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4739_);
return v___x_4740_;
}
}
else
{
lean_object* v___x_4741_; lean_object* v___x_4742_; 
lean_del_object(v___x_4673_);
lean_dec(v_r_4662_);
lean_dec(v_v_4660_);
lean_dec(v_k_4659_);
lean_dec(v_size_4658_);
lean_dec(v_size_4657_);
lean_dec_ref(v___x_4656_);
lean_del_object(v___x_4143_);
lean_dec(v_v_4139_);
lean_dec(v_k_4138_);
v___x_4741_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4);
v___x_4742_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4741_);
return v___x_4742_;
}
}
}
}
else
{
lean_object* v_size_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4753_; 
v_size_4749_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_size_4749_);
v___x_4750_ = lean_unsigned_to_nat(1u);
v___x_4751_ = lean_nat_add(v___x_4750_, v_size_4749_);
lean_dec(v_size_4749_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 4, v___x_4656_);
lean_ctor_set(v___x_4143_, 0, v___x_4751_);
v___x_4753_ = v___x_4143_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4751_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4754_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4754_, 3, v_l_4140_);
lean_ctor_set(v_reuseFailAlloc_4754_, 4, v___x_4656_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
else
{
if (lean_obj_tag(v_l_4140_) == 0)
{
lean_object* v_l_4755_; 
v_l_4755_ = lean_ctor_get(v_l_4140_, 3);
if (lean_obj_tag(v_l_4755_) == 0)
{
lean_object* v_r_4756_; 
lean_inc_ref(v_l_4755_);
v_r_4756_ = lean_ctor_get(v_l_4140_, 4);
lean_inc(v_r_4756_);
if (lean_obj_tag(v_r_4756_) == 0)
{
lean_object* v_size_4757_; lean_object* v_k_4758_; lean_object* v_v_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4773_; 
v_size_4757_ = lean_ctor_get(v_l_4140_, 0);
v_k_4758_ = lean_ctor_get(v_l_4140_, 1);
v_v_4759_ = lean_ctor_get(v_l_4140_, 2);
v_isSharedCheck_4773_ = !lean_is_exclusive(v_l_4140_);
if (v_isSharedCheck_4773_ == 0)
{
lean_object* v_unused_4774_; lean_object* v_unused_4775_; 
v_unused_4774_ = lean_ctor_get(v_l_4140_, 4);
lean_dec(v_unused_4774_);
v_unused_4775_ = lean_ctor_get(v_l_4140_, 3);
lean_dec(v_unused_4775_);
v___x_4761_ = v_l_4140_;
v_isShared_4762_ = v_isSharedCheck_4773_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_v_4759_);
lean_inc(v_k_4758_);
lean_inc(v_size_4757_);
lean_dec(v_l_4140_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4773_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v_size_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4768_; 
v_size_4763_ = lean_ctor_get(v_r_4756_, 0);
v___x_4764_ = lean_unsigned_to_nat(1u);
v___x_4765_ = lean_nat_add(v___x_4764_, v_size_4757_);
lean_dec(v_size_4757_);
v___x_4766_ = lean_nat_add(v___x_4764_, v_size_4763_);
if (v_isShared_4762_ == 0)
{
lean_ctor_set(v___x_4761_, 4, v___x_4656_);
lean_ctor_set(v___x_4761_, 3, v_r_4756_);
lean_ctor_set(v___x_4761_, 2, v_v_4139_);
lean_ctor_set(v___x_4761_, 1, v_k_4138_);
lean_ctor_set(v___x_4761_, 0, v___x_4766_);
v___x_4768_ = v___x_4761_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v___x_4766_);
lean_ctor_set(v_reuseFailAlloc_4772_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4772_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4772_, 3, v_r_4756_);
lean_ctor_set(v_reuseFailAlloc_4772_, 4, v___x_4656_);
v___x_4768_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
lean_object* v___x_4770_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 4, v___x_4768_);
lean_ctor_set(v___x_4143_, 3, v_l_4755_);
lean_ctor_set(v___x_4143_, 2, v_v_4759_);
lean_ctor_set(v___x_4143_, 1, v_k_4758_);
lean_ctor_set(v___x_4143_, 0, v___x_4765_);
v___x_4770_ = v___x_4143_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v___x_4765_);
lean_ctor_set(v_reuseFailAlloc_4771_, 1, v_k_4758_);
lean_ctor_set(v_reuseFailAlloc_4771_, 2, v_v_4759_);
lean_ctor_set(v_reuseFailAlloc_4771_, 3, v_l_4755_);
lean_ctor_set(v_reuseFailAlloc_4771_, 4, v___x_4768_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
}
else
{
lean_object* v_k_4776_; lean_object* v_v_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4789_; 
v_k_4776_ = lean_ctor_get(v_l_4140_, 1);
v_v_4777_ = lean_ctor_get(v_l_4140_, 2);
v_isSharedCheck_4789_ = !lean_is_exclusive(v_l_4140_);
if (v_isSharedCheck_4789_ == 0)
{
lean_object* v_unused_4790_; lean_object* v_unused_4791_; lean_object* v_unused_4792_; 
v_unused_4790_ = lean_ctor_get(v_l_4140_, 4);
lean_dec(v_unused_4790_);
v_unused_4791_ = lean_ctor_get(v_l_4140_, 3);
lean_dec(v_unused_4791_);
v_unused_4792_ = lean_ctor_get(v_l_4140_, 0);
lean_dec(v_unused_4792_);
v___x_4779_ = v_l_4140_;
v_isShared_4780_ = v_isSharedCheck_4789_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_v_4777_);
lean_inc(v_k_4776_);
lean_dec(v_l_4140_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4789_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4784_; 
v___x_4781_ = lean_unsigned_to_nat(3u);
v___x_4782_ = lean_unsigned_to_nat(1u);
if (v_isShared_4780_ == 0)
{
lean_ctor_set(v___x_4779_, 3, v_r_4756_);
lean_ctor_set(v___x_4779_, 2, v_v_4139_);
lean_ctor_set(v___x_4779_, 1, v_k_4138_);
lean_ctor_set(v___x_4779_, 0, v___x_4782_);
v___x_4784_ = v___x_4779_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4782_);
lean_ctor_set(v_reuseFailAlloc_4788_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4788_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4788_, 3, v_r_4756_);
lean_ctor_set(v_reuseFailAlloc_4788_, 4, v_r_4756_);
v___x_4784_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
lean_object* v___x_4786_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 4, v___x_4784_);
lean_ctor_set(v___x_4143_, 3, v_l_4755_);
lean_ctor_set(v___x_4143_, 2, v_v_4777_);
lean_ctor_set(v___x_4143_, 1, v_k_4776_);
lean_ctor_set(v___x_4143_, 0, v___x_4781_);
v___x_4786_ = v___x_4143_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4781_);
lean_ctor_set(v_reuseFailAlloc_4787_, 1, v_k_4776_);
lean_ctor_set(v_reuseFailAlloc_4787_, 2, v_v_4777_);
lean_ctor_set(v_reuseFailAlloc_4787_, 3, v_l_4755_);
lean_ctor_set(v_reuseFailAlloc_4787_, 4, v___x_4784_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
}
}
}
else
{
lean_object* v_r_4793_; 
v_r_4793_ = lean_ctor_get(v_l_4140_, 4);
lean_inc(v_r_4793_);
if (lean_obj_tag(v_r_4793_) == 0)
{
lean_object* v_k_4794_; lean_object* v_v_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4819_; 
lean_inc(v_l_4755_);
v_k_4794_ = lean_ctor_get(v_l_4140_, 1);
v_v_4795_ = lean_ctor_get(v_l_4140_, 2);
v_isSharedCheck_4819_ = !lean_is_exclusive(v_l_4140_);
if (v_isSharedCheck_4819_ == 0)
{
lean_object* v_unused_4820_; lean_object* v_unused_4821_; lean_object* v_unused_4822_; 
v_unused_4820_ = lean_ctor_get(v_l_4140_, 4);
lean_dec(v_unused_4820_);
v_unused_4821_ = lean_ctor_get(v_l_4140_, 3);
lean_dec(v_unused_4821_);
v_unused_4822_ = lean_ctor_get(v_l_4140_, 0);
lean_dec(v_unused_4822_);
v___x_4797_ = v_l_4140_;
v_isShared_4798_ = v_isSharedCheck_4819_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_v_4795_);
lean_inc(v_k_4794_);
lean_dec(v_l_4140_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4819_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v_k_4799_; lean_object* v_v_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4815_; 
v_k_4799_ = lean_ctor_get(v_r_4793_, 1);
v_v_4800_ = lean_ctor_get(v_r_4793_, 2);
v_isSharedCheck_4815_ = !lean_is_exclusive(v_r_4793_);
if (v_isSharedCheck_4815_ == 0)
{
lean_object* v_unused_4816_; lean_object* v_unused_4817_; lean_object* v_unused_4818_; 
v_unused_4816_ = lean_ctor_get(v_r_4793_, 4);
lean_dec(v_unused_4816_);
v_unused_4817_ = lean_ctor_get(v_r_4793_, 3);
lean_dec(v_unused_4817_);
v_unused_4818_ = lean_ctor_get(v_r_4793_, 0);
lean_dec(v_unused_4818_);
v___x_4802_ = v_r_4793_;
v_isShared_4803_ = v_isSharedCheck_4815_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_v_4800_);
lean_inc(v_k_4799_);
lean_dec(v_r_4793_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4815_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4807_; 
v___x_4804_ = lean_unsigned_to_nat(3u);
v___x_4805_ = lean_unsigned_to_nat(1u);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 4, v_l_4755_);
lean_ctor_set(v___x_4802_, 3, v_l_4755_);
lean_ctor_set(v___x_4802_, 2, v_v_4795_);
lean_ctor_set(v___x_4802_, 1, v_k_4794_);
lean_ctor_set(v___x_4802_, 0, v___x_4805_);
v___x_4807_ = v___x_4802_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4805_);
lean_ctor_set(v_reuseFailAlloc_4814_, 1, v_k_4794_);
lean_ctor_set(v_reuseFailAlloc_4814_, 2, v_v_4795_);
lean_ctor_set(v_reuseFailAlloc_4814_, 3, v_l_4755_);
lean_ctor_set(v_reuseFailAlloc_4814_, 4, v_l_4755_);
v___x_4807_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
lean_object* v___x_4809_; 
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 4, v_l_4755_);
lean_ctor_set(v___x_4797_, 2, v_v_4139_);
lean_ctor_set(v___x_4797_, 1, v_k_4138_);
lean_ctor_set(v___x_4797_, 0, v___x_4805_);
v___x_4809_ = v___x_4797_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4805_);
lean_ctor_set(v_reuseFailAlloc_4813_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4813_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4813_, 3, v_l_4755_);
lean_ctor_set(v_reuseFailAlloc_4813_, 4, v_l_4755_);
v___x_4809_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
lean_object* v___x_4811_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 4, v___x_4809_);
lean_ctor_set(v___x_4143_, 3, v___x_4807_);
lean_ctor_set(v___x_4143_, 2, v_v_4800_);
lean_ctor_set(v___x_4143_, 1, v_k_4799_);
lean_ctor_set(v___x_4143_, 0, v___x_4804_);
v___x_4811_ = v___x_4143_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v___x_4804_);
lean_ctor_set(v_reuseFailAlloc_4812_, 1, v_k_4799_);
lean_ctor_set(v_reuseFailAlloc_4812_, 2, v_v_4800_);
lean_ctor_set(v_reuseFailAlloc_4812_, 3, v___x_4807_);
lean_ctor_set(v_reuseFailAlloc_4812_, 4, v___x_4809_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
}
}
else
{
lean_object* v___x_4823_; lean_object* v___x_4825_; 
v___x_4823_ = lean_unsigned_to_nat(2u);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 4, v_r_4793_);
lean_ctor_set(v___x_4143_, 0, v___x_4823_);
v___x_4825_ = v___x_4143_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4823_);
lean_ctor_set(v_reuseFailAlloc_4826_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4826_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4826_, 3, v_l_4140_);
lean_ctor_set(v_reuseFailAlloc_4826_, 4, v_r_4793_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
}
}
else
{
lean_object* v___x_4827_; lean_object* v___x_4829_; 
v___x_4827_ = lean_unsigned_to_nat(1u);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 4, v_l_4140_);
lean_ctor_set(v___x_4143_, 0, v___x_4827_);
v___x_4829_ = v___x_4143_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4827_);
lean_ctor_set(v_reuseFailAlloc_4830_, 1, v_k_4138_);
lean_ctor_set(v_reuseFailAlloc_4830_, 2, v_v_4139_);
lean_ctor_set(v_reuseFailAlloc_4830_, 3, v_l_4140_);
lean_ctor_set(v_reuseFailAlloc_4830_, 4, v_l_4140_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_4136_);
lean_dec_ref(v_cmp_4135_);
return v_t_4137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(lean_object* v_cmp_4833_, lean_object* v_init_4834_, lean_object* v_x_4835_){
_start:
{
if (lean_obj_tag(v_x_4835_) == 0)
{
lean_object* v_k_4836_; lean_object* v_l_4837_; lean_object* v_r_4838_; lean_object* v___x_4839_; lean_object* v_a_4840_; lean_object* v_r_4841_; 
v_k_4836_ = lean_ctor_get(v_x_4835_, 1);
lean_inc(v_k_4836_);
v_l_4837_ = lean_ctor_get(v_x_4835_, 3);
lean_inc(v_l_4837_);
v_r_4838_ = lean_ctor_get(v_x_4835_, 4);
lean_inc(v_r_4838_);
lean_dec_ref(v_x_4835_);
lean_inc_ref_n(v_cmp_4833_, 2);
v___x_4839_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4833_, v_init_4834_, v_l_4837_);
v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
lean_inc(v_a_4840_);
lean_dec_ref(v___x_4839_);
v_r_4841_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4833_, v_k_4836_, v_a_4840_);
v_init_4834_ = v_r_4841_;
v_x_4835_ = v_r_4838_;
goto _start;
}
else
{
lean_object* v___x_4843_; 
lean_dec_ref(v_cmp_4833_);
v___x_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4843_, 0, v_init_4834_);
return v___x_4843_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(lean_object* v_cmp_4844_, lean_object* v_t_u2081_4845_, lean_object* v_t_u2082_4846_){
_start:
{
lean_object* v___y_4848_; lean_object* v___y_4849_; lean_object* v___y_4855_; 
if (lean_obj_tag(v_t_u2081_4845_) == 0)
{
lean_object* v_size_4858_; 
v_size_4858_ = lean_ctor_get(v_t_u2081_4845_, 0);
lean_inc(v_size_4858_);
v___y_4855_ = v_size_4858_;
goto v___jp_4854_;
}
else
{
lean_object* v___x_4859_; 
v___x_4859_ = lean_unsigned_to_nat(0u);
v___y_4855_ = v___x_4859_;
goto v___jp_4854_;
}
v___jp_4847_:
{
uint8_t v___x_4850_; 
v___x_4850_ = lean_nat_dec_le(v___y_4848_, v___y_4849_);
lean_dec(v___y_4849_);
lean_dec(v___y_4848_);
if (v___x_4850_ == 0)
{
lean_object* v___x_4851_; lean_object* v_a_4852_; 
v___x_4851_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4844_, v_t_u2081_4845_, v_t_u2082_4846_);
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref(v___x_4851_);
return v_a_4852_;
}
else
{
lean_object* v___x_4853_; 
v___x_4853_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4844_, v_t_u2082_4846_, v_t_u2081_4845_);
return v___x_4853_;
}
}
v___jp_4854_:
{
if (lean_obj_tag(v_t_u2082_4846_) == 0)
{
lean_object* v_size_4856_; 
v_size_4856_ = lean_ctor_get(v_t_u2082_4846_, 0);
lean_inc(v_size_4856_);
v___y_4848_ = v___y_4855_;
v___y_4849_ = v_size_4856_;
goto v___jp_4847_;
}
else
{
lean_object* v___x_4857_; 
v___x_4857_ = lean_unsigned_to_nat(0u);
v___y_4848_ = v___y_4855_;
v___y_4849_ = v___x_4857_;
goto v___jp_4847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff___redArg(lean_object* v_cmp_4860_, lean_object* v_t_u2081_4861_, lean_object* v_t_u2082_4862_){
_start:
{
lean_object* v___x_4863_; 
v___x_4863_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4860_, v_t_u2081_4861_, v_t_u2082_4862_);
return v___x_4863_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff(lean_object* v_00_u03b1_4864_, lean_object* v_00_u03b2_4865_, lean_object* v_cmp_4866_, lean_object* v_t_u2081_4867_, lean_object* v_t_u2082_4868_){
_start:
{
lean_object* v___x_4869_; 
v___x_4869_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4866_, v_t_u2081_4867_, v_t_u2082_4868_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0(lean_object* v_00_u03b1_4870_, lean_object* v_cmp_4871_, lean_object* v_00_u03b2_4872_, lean_object* v_t_u2081_4873_, lean_object* v_t_u2082_4874_){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4871_, v_t_u2081_4873_, v_t_u2082_4874_);
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0(lean_object* v_00_u03b1_4876_, lean_object* v_cmp_4877_, lean_object* v_00_u03b2_4878_, lean_object* v_k_4879_, lean_object* v_t_4880_){
_start:
{
lean_object* v___x_4881_; 
v___x_4881_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4877_, v_k_4879_, v_t_4880_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1(lean_object* v_00_u03b1_4882_, lean_object* v_00_u03b2_4883_, lean_object* v_cmp_4884_, lean_object* v_init_4885_, lean_object* v_x_4886_){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4884_, v_init_4885_, v_x_4886_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2(lean_object* v_00_u03b1_4888_, lean_object* v_00_u03b2_4889_, lean_object* v_cmp_4890_, lean_object* v_t_u2082_4891_, lean_object* v_t_4892_){
_start:
{
lean_object* v___x_4893_; 
v___x_4893_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4890_, v_t_u2082_4891_, v_t_4892_);
return v___x_4893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff___redArg(lean_object* v_cmp_4894_){
_start:
{
lean_object* v___x_4895_; 
v___x_4895_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_4895_, 0, lean_box(0));
lean_closure_set(v___x_4895_, 1, lean_box(0));
lean_closure_set(v___x_4895_, 2, v_cmp_4894_);
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff(lean_object* v_00_u03b1_4896_, lean_object* v_00_u03b2_4897_, lean_object* v_cmp_4898_){
_start:
{
lean_object* v___x_4899_; 
v___x_4899_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_4899_, 0, lean_box(0));
lean_closure_set(v___x_4899_, 1, lean_box(0));
lean_closure_set(v___x_4899_, 2, v_cmp_4898_);
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_4900_, lean_object* v_a_4901_, lean_object* v_____s_4902_){
_start:
{
lean_object* v_r_4903_; lean_object* v___x_4904_; 
v_r_4903_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_4900_, v_a_4901_, v_____s_4902_);
v___x_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4904_, 0, v_r_4903_);
return v___x_4904_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg(lean_object* v_cmp_4905_, lean_object* v_inst_4906_, lean_object* v_t_4907_, lean_object* v_l_4908_){
_start:
{
lean_object* v___f_4909_; lean_object* v___x_4910_; 
v___f_4909_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4909_, 0, v_cmp_4905_);
v___x_4910_ = lean_apply_4(v_inst_4906_, lean_box(0), v_l_4908_, v_t_4907_, v___f_4909_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany(lean_object* v_00_u03b1_4911_, lean_object* v_00_u03b2_4912_, lean_object* v_cmp_4913_, lean_object* v_00_u03c1_4914_, lean_object* v_inst_4915_, lean_object* v_t_4916_, lean_object* v_l_4917_){
_start:
{
lean_object* v___f_4918_; lean_object* v___x_4919_; 
v___f_4918_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4918_, 0, v_cmp_4913_);
v___x_4919_ = lean_apply_4(v_inst_4915_, lean_box(0), v_l_4917_, v_t_4916_, v___f_4918_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0(lean_object* v_cmp_4920_, lean_object* v_x_4921_, lean_object* v_____s_4922_){
_start:
{
lean_object* v_fst_4923_; lean_object* v_snd_4924_; lean_object* v_r_4925_; lean_object* v___x_4926_; 
v_fst_4923_ = lean_ctor_get(v_x_4921_, 0);
lean_inc(v_fst_4923_);
v_snd_4924_ = lean_ctor_get(v_x_4921_, 1);
lean_inc(v_snd_4924_);
lean_dec_ref(v_x_4921_);
v_r_4925_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_4920_, v_fst_4923_, v_snd_4924_, v_____s_4922_);
v___x_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4926_, 0, v_r_4925_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg(lean_object* v_cmp_4927_, lean_object* v_inst_4928_, lean_object* v_t_4929_, lean_object* v_l_4930_){
_start:
{
lean_object* v___f_4931_; lean_object* v___x_4932_; 
v___f_4931_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4931_, 0, v_cmp_4927_);
v___x_4932_ = lean_apply_4(v_inst_4928_, lean_box(0), v_l_4930_, v_t_4929_, v___f_4931_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany(lean_object* v_00_u03b1_4933_, lean_object* v_cmp_4934_, lean_object* v_00_u03b2_4935_, lean_object* v_00_u03c1_4936_, lean_object* v_inst_4937_, lean_object* v_t_4938_, lean_object* v_l_4939_){
_start:
{
lean_object* v___f_4940_; lean_object* v___x_4941_; 
v___f_4940_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4940_, 0, v_cmp_4934_);
v___x_4941_ = lean_apply_4(v_inst_4937_, lean_box(0), v_l_4939_, v_t_4938_, v___f_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_4942_, lean_object* v_a_4943_, lean_object* v_____s_4944_){
_start:
{
uint8_t v___x_4945_; 
lean_inc(v_____s_4944_);
lean_inc(v_a_4943_);
lean_inc_ref(v_cmp_4942_);
v___x_4945_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4942_, v_a_4943_, v_____s_4944_);
if (v___x_4945_ == 0)
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4946_ = lean_box(0);
v___x_4947_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_4942_, v_a_4943_, v___x_4946_, v_____s_4944_);
v___x_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4947_);
return v___x_4948_;
}
else
{
lean_object* v___x_4949_; 
lean_dec(v_a_4943_);
lean_dec_ref(v_cmp_4942_);
v___x_4949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4949_, 0, v_____s_4944_);
return v___x_4949_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_4950_, lean_object* v_inst_4951_, lean_object* v_t_4952_, lean_object* v_l_4953_){
_start:
{
lean_object* v___f_4954_; lean_object* v___x_4955_; 
v___f_4954_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4954_, 0, v_cmp_4950_);
v___x_4955_ = lean_apply_4(v_inst_4951_, lean_box(0), v_l_4953_, v_t_4952_, v___f_4954_);
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_4956_, lean_object* v_cmp_4957_, lean_object* v_00_u03c1_4958_, lean_object* v_inst_4959_, lean_object* v_t_4960_, lean_object* v_l_4961_){
_start:
{
lean_object* v___f_4962_; lean_object* v___x_4963_; 
v___f_4962_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4962_, 0, v_cmp_4957_);
v___x_4963_ = lean_apply_4(v_inst_4959_, lean_box(0), v_l_4961_, v_t_4960_, v___f_4962_);
return v___x_4963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(lean_object* v___f_4967_, lean_object* v___x_4968_, lean_object* v_m_4969_, lean_object* v_prec_4970_){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4971_ = ((lean_object*)(l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__1));
v___x_4972_ = lean_box(0);
v___x_4973_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_4974_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_4973_, v___f_4967_, v___x_4972_, v_m_4969_);
v___x_4975_ = l_List_repr___redArg(v___x_4968_, v___x_4974_);
v___x_4976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4971_);
lean_ctor_set(v___x_4976_, 1, v___x_4975_);
v___x_4977_ = l_Repr_addAppParen(v___x_4976_, v_prec_4970_);
return v___x_4977_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_4978_, lean_object* v___x_4979_, lean_object* v_m_4980_, lean_object* v_prec_4981_){
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(v___f_4978_, v___x_4979_, v_m_4980_, v_prec_4981_);
lean_dec(v_prec_4981_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg(lean_object* v_inst_4983_, lean_object* v_inst_4984_){
_start:
{
lean_object* v___f_4985_; lean_object* v___x_4986_; lean_object* v___f_4987_; 
v___f_4985_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_4986_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_4986_, 0, lean_box(0));
lean_closure_set(v___x_4986_, 1, lean_box(0));
lean_closure_set(v___x_4986_, 2, v_inst_4983_);
lean_closure_set(v___x_4986_, 3, v_inst_4984_);
v___f_4987_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4987_, 0, v___f_4985_);
lean_closure_set(v___f_4987_, 1, v___x_4986_);
return v___f_4987_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr(lean_object* v_00_u03b1_4988_, lean_object* v_00_u03b2_4989_, lean_object* v_cmp_4990_, lean_object* v_inst_4991_, lean_object* v_inst_4992_){
_start:
{
lean_object* v___x_4993_; 
v___x_4993_ = l_Std_DTreeMap_Raw_instRepr___redArg(v_inst_4991_, v_inst_4992_);
return v___x_4993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___boxed(lean_object* v_00_u03b1_4994_, lean_object* v_00_u03b2_4995_, lean_object* v_cmp_4996_, lean_object* v_inst_4997_, lean_object* v_inst_4998_){
_start:
{
lean_object* v_res_4999_; 
v_res_4999_ = l_Std_DTreeMap_Raw_instRepr(v_00_u03b1_4994_, v_00_u03b2_4995_, v_cmp_4996_, v_inst_4997_, v_inst_4998_);
lean_dec_ref(v_cmp_4996_);
return v_res_4999_;
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
