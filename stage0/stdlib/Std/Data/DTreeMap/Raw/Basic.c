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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(lean_object*);
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
lean_object* l_panic___redArg(lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_171_);
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
lean_inc(v_quotContext_177_);
v_currMacroScope_178_ = lean_ctor_get(v_a_171_, 2);
lean_inc(v_currMacroScope_178_);
v_ref_179_ = lean_ctor_get(v_a_171_, 5);
lean_inc(v_ref_179_);
lean_dec_ref(v_a_171_);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = l_Lean_Syntax_getArg(v_x_170_, v___x_180_);
v___x_182_ = lean_unsigned_to_nat(2u);
v___x_183_ = l_Lean_Syntax_getArg(v_x_170_, v___x_182_);
lean_dec(v_x_170_);
v___x_184_ = 0;
v___x_185_ = l_Lean_SourceInfo_fromRef(v_ref_179_, v___x_184_);
lean_dec(v_ref_179_);
v___x_186_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2));
v___x_187_ = lean_obj_once(&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4, &l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4_once, _init_l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4);
v___x_188_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__5));
v___x_189_ = l_Lean_addMacroScope(v_quotContext_177_, v___x_188_, v_currMacroScope_178_);
v___x_190_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__10));
lean_inc(v___x_185_);
v___x_191_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_191_, 0, v___x_185_);
lean_ctor_set(v___x_191_, 1, v___x_187_);
lean_ctor_set(v___x_191_, 2, v___x_189_);
lean_ctor_set(v___x_191_, 3, v___x_190_);
v___x_192_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__9));
lean_inc(v___x_185_);
v___x_193_ = l_Lean_Syntax_node2(v___x_185_, v___x_192_, v___x_181_, v___x_183_);
v___x_194_ = l_Lean_Syntax_node2(v___x_185_, v___x_186_, v___x_191_, v___x_193_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_a_172_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1(lean_object* v_x_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2));
lean_inc(v_x_199_);
v___x_203_ = l_Lean_Syntax_isOfKind(v_x_199_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v_x_199_);
v___x_204_ = lean_box(0);
v___x_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v_a_201_);
return v___x_205_;
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = l_Lean_Syntax_getArg(v_x_199_, v___x_206_);
v___x_208_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_207_);
v___x_209_ = l_Lean_Syntax_isOfKind(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec(v___x_207_);
lean_dec(v_x_199_);
v___x_210_ = lean_box(0);
v___x_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v_a_201_);
return v___x_211_;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_212_ = lean_unsigned_to_nat(1u);
v___x_213_ = l_Lean_Syntax_getArg(v_x_199_, v___x_212_);
lean_dec(v_x_199_);
v___x_214_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_213_);
v___x_215_ = l_Lean_Syntax_matchesNull(v___x_213_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec(v___x_213_);
lean_dec(v___x_207_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v_a_201_);
return v___x_217_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_ref_220_; uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_218_ = l_Lean_Syntax_getArg(v___x_213_, v___x_206_);
v___x_219_ = l_Lean_Syntax_getArg(v___x_213_, v___x_212_);
lean_dec(v___x_213_);
v_ref_220_ = l_Lean_replaceRef(v___x_207_, v_a_200_);
lean_dec(v___x_207_);
v___x_221_ = 0;
v___x_222_ = l_Lean_SourceInfo_fromRef(v_ref_220_, v___x_221_);
lean_dec(v_ref_220_);
v___x_223_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__4));
v___x_224_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_222_);
v___x_225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_222_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = l_Lean_Syntax_node3(v___x_222_, v___x_223_, v___x_218_, v___x_225_, v___x_219_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_a_201_);
return v___x_227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___boxed(lean_object* v_x_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1(v_x_228_, v_a_229_, v_a_230_);
lean_dec(v_a_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insert___redArg(lean_object* v_cmp_232_, lean_object* v_t_233_, lean_object* v_a_234_, lean_object* v_b_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_232_, v_a_234_, v_b_235_, v_t_233_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insert(lean_object* v_00_u03b1_237_, lean_object* v_00_u03b2_238_, lean_object* v_cmp_239_, lean_object* v_t_240_, lean_object* v_a_241_, lean_object* v_b_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_239_, v_a_241_, v_b_242_, v_t_240_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0(lean_object* v_cmp_244_, lean_object* v_e_245_){
_start:
{
lean_object* v_fst_246_; lean_object* v_snd_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_fst_246_ = lean_ctor_get(v_e_245_, 0);
lean_inc(v_fst_246_);
v_snd_247_ = lean_ctor_get(v_e_245_, 1);
lean_inc(v_snd_247_);
lean_dec_ref(v_e_245_);
v___x_248_ = lean_box(1);
v___x_249_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_244_, v_fst_246_, v_snd_247_, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma___redArg(lean_object* v_cmp_250_){
_start:
{
lean_object* v___f_251_; 
v___f_251_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_251_, 0, v_cmp_250_);
return v___f_251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma(lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_, lean_object* v_cmp_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_255_, 0, v_cmp_254_);
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0(lean_object* v_cmp_256_, lean_object* v_e_257_, lean_object* v_s_258_){
_start:
{
lean_object* v_fst_259_; lean_object* v_snd_260_; lean_object* v___x_261_; 
v_fst_259_ = lean_ctor_get(v_e_257_, 0);
lean_inc(v_fst_259_);
v_snd_260_ = lean_ctor_get(v_e_257_, 1);
lean_inc(v_snd_260_);
lean_dec_ref(v_e_257_);
v___x_261_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_256_, v_fst_259_, v_snd_260_, v_s_258_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma___redArg(lean_object* v_cmp_262_){
_start:
{
lean_object* v___f_263_; 
v___f_263_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_263_, 0, v_cmp_262_);
return v___f_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma(lean_object* v_00_u03b1_264_, lean_object* v_00_u03b2_265_, lean_object* v_cmp_266_){
_start:
{
lean_object* v___f_267_; 
v___f_267_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_267_, 0, v_cmp_266_);
return v___f_267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertIfNew___redArg(lean_object* v_cmp_268_, lean_object* v_t_269_, lean_object* v_a_270_, lean_object* v_b_271_){
_start:
{
uint8_t v___x_272_; 
lean_inc(v_t_269_);
lean_inc(v_a_270_);
lean_inc_ref(v_cmp_268_);
v___x_272_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_268_, v_a_270_, v_t_269_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_268_, v_a_270_, v_b_271_, v_t_269_);
return v___x_273_;
}
else
{
lean_dec(v_b_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_cmp_268_);
return v_t_269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertIfNew(lean_object* v_00_u03b1_274_, lean_object* v_00_u03b2_275_, lean_object* v_cmp_276_, lean_object* v_t_277_, lean_object* v_a_278_, lean_object* v_b_279_){
_start:
{
uint8_t v___x_280_; 
lean_inc(v_t_277_);
lean_inc(v_a_278_);
lean_inc_ref(v_cmp_276_);
v___x_280_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_276_, v_a_278_, v_t_277_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_276_, v_a_278_, v_b_279_, v_t_277_);
return v___x_281_;
}
else
{
lean_dec(v_b_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_cmp_276_);
return v_t_277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsert___redArg(lean_object* v_cmp_282_, lean_object* v_t_283_, lean_object* v_a_284_, lean_object* v_b_285_){
_start:
{
lean_object* v_sz_286_; lean_object* v_m_287_; lean_object* v___y_289_; 
v_sz_286_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_283_);
v_m_287_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_282_, v_a_284_, v_b_285_, v_t_283_);
if (lean_obj_tag(v_m_287_) == 0)
{
lean_object* v_size_293_; 
v_size_293_ = lean_ctor_get(v_m_287_, 0);
lean_inc(v_size_293_);
v___y_289_ = v_size_293_;
goto v___jp_288_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___y_289_ = v___x_294_;
goto v___jp_288_;
}
v___jp_288_:
{
uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_nat_dec_eq(v_sz_286_, v___y_289_);
lean_dec(v___y_289_);
lean_dec(v_sz_286_);
v___x_291_ = lean_box(v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_m_287_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsert(lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_cmp_297_, lean_object* v_t_298_, lean_object* v_a_299_, lean_object* v_b_300_){
_start:
{
lean_object* v_sz_301_; lean_object* v_m_302_; lean_object* v___y_304_; 
v_sz_301_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_298_);
v_m_302_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_297_, v_a_299_, v_b_300_, v_t_298_);
if (lean_obj_tag(v_m_302_) == 0)
{
lean_object* v_size_308_; 
v_size_308_ = lean_ctor_get(v_m_302_, 0);
lean_inc(v_size_308_);
v___y_304_ = v_size_308_;
goto v___jp_303_;
}
else
{
lean_object* v___x_309_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___y_304_ = v___x_309_;
goto v___jp_303_;
}
v___jp_303_:
{
uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_nat_dec_eq(v_sz_301_, v___y_304_);
lean_dec(v___y_304_);
lean_dec(v_sz_301_);
v___x_306_ = lean_box(v___x_305_);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v_m_302_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_cmp_310_, lean_object* v_t_311_, lean_object* v_a_312_, lean_object* v_b_313_){
_start:
{
uint8_t v___x_314_; 
lean_inc(v_t_311_);
lean_inc(v_a_312_);
lean_inc_ref(v_cmp_310_);
v___x_314_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_310_, v_a_312_, v_t_311_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_310_, v_a_312_, v_b_313_, v_t_311_);
v___x_316_ = lean_box(v___x_314_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_315_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_b_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_cmp_310_);
v___x_318_ = lean_box(v___x_314_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_t_311_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_320_, lean_object* v_00_u03b2_321_, lean_object* v_cmp_322_, lean_object* v_t_323_, lean_object* v_a_324_, lean_object* v_b_325_){
_start:
{
uint8_t v___x_326_; 
lean_inc(v_t_323_);
lean_inc(v_a_324_);
lean_inc_ref(v_cmp_322_);
v___x_326_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_322_, v_a_324_, v_t_323_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_322_, v_a_324_, v_b_325_, v_t_323_);
v___x_328_ = lean_box(v___x_326_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_b_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_cmp_322_);
v___x_330_ = lean_box(v___x_326_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v_t_323_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_332_, lean_object* v_t_333_, lean_object* v_a_334_, lean_object* v_b_335_){
_start:
{
lean_object* v___x_336_; 
lean_inc(v_a_334_);
lean_inc(v_t_333_);
lean_inc_ref(v_cmp_332_);
v___x_336_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_332_, v_t_333_, v_a_334_);
if (lean_obj_tag(v___x_336_) == 0)
{
uint8_t v___x_337_; 
lean_inc(v_t_333_);
lean_inc(v_a_334_);
lean_inc_ref(v_cmp_332_);
v___x_337_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_332_, v_a_334_, v_t_333_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_332_, v_a_334_, v_b_335_, v_t_333_);
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
lean_dec_ref(v_cmp_332_);
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
lean_dec_ref(v_cmp_332_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_336_);
lean_ctor_set(v___x_341_, 1, v_t_333_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_342_, lean_object* v_00_u03b2_343_, lean_object* v_cmp_344_, lean_object* v_inst_345_, lean_object* v_t_346_, lean_object* v_a_347_, lean_object* v_b_348_){
_start:
{
lean_object* v___x_349_; 
lean_inc(v_a_347_);
lean_inc(v_t_346_);
lean_inc_ref(v_cmp_344_);
v___x_349_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_344_, v_t_346_, v_a_347_);
if (lean_obj_tag(v___x_349_) == 0)
{
uint8_t v___x_350_; 
lean_inc(v_t_346_);
lean_inc(v_a_347_);
lean_inc_ref(v_cmp_344_);
v___x_350_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_344_, v_a_347_, v_t_346_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_344_, v_a_347_, v_b_348_, v_t_346_);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_349_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; 
lean_dec(v_b_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_cmp_344_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_349_);
lean_ctor_set(v___x_353_, 1, v_t_346_);
return v___x_353_;
}
}
else
{
lean_object* v___x_354_; 
lean_dec(v_b_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_cmp_344_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_349_);
lean_ctor_set(v___x_354_, 1, v_t_346_);
return v___x_354_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_contains___redArg(lean_object* v_cmp_355_, lean_object* v_t_356_, lean_object* v_a_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_355_, v_a_357_, v_t_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_contains___redArg___boxed(lean_object* v_cmp_359_, lean_object* v_t_360_, lean_object* v_a_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Std_DTreeMap_Raw_contains___redArg(v_cmp_359_, v_t_360_, v_a_361_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_contains(lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_cmp_366_, lean_object* v_t_367_, lean_object* v_a_368_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_366_, v_a_368_, v_t_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_contains___boxed(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_cmp_372_, lean_object* v_t_373_, lean_object* v_a_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Std_DTreeMap_Raw_contains(v_00_u03b1_370_, v_00_u03b2_371_, v_cmp_372_, v_t_373_, v_a_374_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership(lean_object* v_00_u03b1_377_, lean_object* v_00_u03b2_378_, lean_object* v_cmp_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_box(0);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___boxed(lean_object* v_00_u03b1_381_, lean_object* v_00_u03b2_382_, lean_object* v_cmp_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_DTreeMap_Raw_instMembership(v_00_u03b1_381_, v_00_u03b2_382_, v_cmp_383_);
lean_dec_ref(v_cmp_383_);
return v_res_384_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableMem___redArg(lean_object* v_cmp_385_, lean_object* v_t_386_, lean_object* v_a_387_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_385_, v_a_387_, v_t_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_389_, lean_object* v_t_390_, lean_object* v_a_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Std_DTreeMap_Raw_instDecidableMem___redArg(v_cmp_389_, v_t_390_, v_a_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableMem(lean_object* v_00_u03b1_394_, lean_object* v_00_u03b2_395_, lean_object* v_cmp_396_, lean_object* v_t_397_, lean_object* v_a_398_){
_start:
{
uint8_t v___x_399_; 
v___x_399_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_396_, v_a_398_, v_t_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_400_, lean_object* v_00_u03b2_401_, lean_object* v_cmp_402_, lean_object* v_t_403_, lean_object* v_a_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Std_DTreeMap_Raw_instDecidableMem(v_00_u03b1_400_, v_00_u03b2_401_, v_cmp_402_, v_t_403_, v_a_404_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___redArg(lean_object* v_t_407_){
_start:
{
if (lean_obj_tag(v_t_407_) == 0)
{
lean_object* v_size_408_; 
v_size_408_ = lean_ctor_get(v_t_407_, 0);
lean_inc(v_size_408_);
return v_size_408_;
}
else
{
lean_object* v___x_409_; 
v___x_409_ = lean_unsigned_to_nat(0u);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___redArg___boxed(lean_object* v_t_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_DTreeMap_Raw_size___redArg(v_t_410_);
lean_dec(v_t_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_cmp_414_, lean_object* v_t_415_){
_start:
{
if (lean_obj_tag(v_t_415_) == 0)
{
lean_object* v_size_416_; 
v_size_416_ = lean_ctor_get(v_t_415_, 0);
lean_inc(v_size_416_);
return v_size_416_;
}
else
{
lean_object* v___x_417_; 
v___x_417_ = lean_unsigned_to_nat(0u);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___boxed(lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_cmp_420_, lean_object* v_t_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Std_DTreeMap_Raw_size(v_00_u03b1_418_, v_00_u03b2_419_, v_cmp_420_, v_t_421_);
lean_dec(v_t_421_);
lean_dec_ref(v_cmp_420_);
return v_res_422_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_isEmpty___redArg(lean_object* v_t_423_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_isEmpty___redArg___boxed(lean_object* v_t_426_){
_start:
{
uint8_t v_res_427_; lean_object* v_r_428_; 
v_res_427_ = l_Std_DTreeMap_Raw_isEmpty___redArg(v_t_426_);
lean_dec(v_t_426_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_isEmpty(lean_object* v_00_u03b1_429_, lean_object* v_00_u03b2_430_, lean_object* v_cmp_431_, lean_object* v_t_432_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_435_, lean_object* v_00_u03b2_436_, lean_object* v_cmp_437_, lean_object* v_t_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Std_DTreeMap_Raw_isEmpty(v_00_u03b1_435_, v_00_u03b2_436_, v_cmp_437_, v_t_438_);
lean_dec(v_t_438_);
lean_dec_ref(v_cmp_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_erase___redArg(lean_object* v_cmp_441_, lean_object* v_t_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_441_, v_a_443_, v_t_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_erase(lean_object* v_00_u03b1_445_, lean_object* v_00_u03b2_446_, lean_object* v_cmp_447_, lean_object* v_t_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_447_, v_a_449_, v_t_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x3f___redArg(lean_object* v_cmp_451_, lean_object* v_t_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_451_, v_t_452_, v_a_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x3f(lean_object* v_00_u03b1_455_, lean_object* v_00_u03b2_456_, lean_object* v_cmp_457_, lean_object* v_inst_458_, lean_object* v_t_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_457_, v_t_459_, v_a_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get___redArg(lean_object* v_cmp_462_, lean_object* v_t_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_462_, v_t_463_, v_a_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get(lean_object* v_00_u03b1_466_, lean_object* v_00_u03b2_467_, lean_object* v_cmp_468_, lean_object* v_inst_469_, lean_object* v_t_470_, lean_object* v_a_471_, lean_object* v_h_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_468_, v_t_470_, v_a_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___redArg(lean_object* v_cmp_474_, lean_object* v_t_475_, lean_object* v_a_476_, lean_object* v_inst_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_474_, v_t_475_, v_a_476_, v_inst_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21(lean_object* v_00_u03b1_479_, lean_object* v_00_u03b2_480_, lean_object* v_cmp_481_, lean_object* v_inst_482_, lean_object* v_t_483_, lean_object* v_a_484_, lean_object* v_inst_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_481_, v_t_483_, v_a_484_, v_inst_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg(lean_object* v_cmp_487_, lean_object* v_t_488_, lean_object* v_a_489_, lean_object* v_fallback_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_487_, v_t_488_, v_a_489_, v_fallback_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg___boxed(lean_object* v_cmp_492_, lean_object* v_t_493_, lean_object* v_a_494_, lean_object* v_fallback_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_DTreeMap_Raw_getD___redArg(v_cmp_492_, v_t_493_, v_a_494_, v_fallback_495_);
lean_dec(v_fallback_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD(lean_object* v_00_u03b1_497_, lean_object* v_00_u03b2_498_, lean_object* v_cmp_499_, lean_object* v_inst_500_, lean_object* v_t_501_, lean_object* v_a_502_, lean_object* v_fallback_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_499_, v_t_501_, v_a_502_, v_fallback_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___boxed(lean_object* v_00_u03b1_505_, lean_object* v_00_u03b2_506_, lean_object* v_cmp_507_, lean_object* v_inst_508_, lean_object* v_t_509_, lean_object* v_a_510_, lean_object* v_fallback_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_DTreeMap_Raw_getD(v_00_u03b1_505_, v_00_u03b2_506_, v_cmp_507_, v_inst_508_, v_t_509_, v_a_510_, v_fallback_511_);
lean_dec(v_fallback_511_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f___redArg(lean_object* v_cmp_513_, lean_object* v_t_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_513_, v_t_514_, v_a_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f(lean_object* v_00_u03b1_517_, lean_object* v_00_u03b2_518_, lean_object* v_cmp_519_, lean_object* v_t_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_519_, v_t_520_, v_a_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry___redArg(lean_object* v_cmp_523_, lean_object* v_t_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_523_, v_t_524_, v_a_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry(lean_object* v_00_u03b1_527_, lean_object* v_00_u03b2_528_, lean_object* v_cmp_529_, lean_object* v_inst_530_, lean_object* v_t_531_, lean_object* v_a_532_, lean_object* v_h_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_529_, v_t_531_, v_a_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___redArg(lean_object* v_cmp_535_, lean_object* v_inst_536_, lean_object* v_t_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_535_, v_inst_536_, v_t_537_, v_a_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21(lean_object* v_00_u03b1_540_, lean_object* v_00_u03b2_541_, lean_object* v_cmp_542_, lean_object* v_inst_543_, lean_object* v_t_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_542_, v_inst_543_, v_t_544_, v_a_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg(lean_object* v_cmp_547_, lean_object* v_t_548_, lean_object* v_a_549_, lean_object* v_fallback_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_547_, v_t_548_, v_a_549_, v_fallback_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg___boxed(lean_object* v_cmp_552_, lean_object* v_t_553_, lean_object* v_a_554_, lean_object* v_fallback_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_DTreeMap_Raw_getEntryD___redArg(v_cmp_552_, v_t_553_, v_a_554_, v_fallback_555_);
lean_dec_ref(v_fallback_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD(lean_object* v_00_u03b1_557_, lean_object* v_00_u03b2_558_, lean_object* v_cmp_559_, lean_object* v_t_560_, lean_object* v_a_561_, lean_object* v_fallback_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_559_, v_t_560_, v_a_561_, v_fallback_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___boxed(lean_object* v_00_u03b1_564_, lean_object* v_00_u03b2_565_, lean_object* v_cmp_566_, lean_object* v_t_567_, lean_object* v_a_568_, lean_object* v_fallback_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_DTreeMap_Raw_getEntryD(v_00_u03b1_564_, v_00_u03b2_565_, v_cmp_566_, v_t_567_, v_a_568_, v_fallback_569_);
lean_dec_ref(v_fallback_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f___redArg(lean_object* v_cmp_571_, lean_object* v_t_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_571_, v_t_572_, v_a_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f(lean_object* v_00_u03b1_575_, lean_object* v_00_u03b2_576_, lean_object* v_cmp_577_, lean_object* v_t_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_577_, v_t_578_, v_a_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey___redArg(lean_object* v_cmp_581_, lean_object* v_t_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_581_, v_t_582_, v_a_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey(lean_object* v_00_u03b1_585_, lean_object* v_00_u03b2_586_, lean_object* v_cmp_587_, lean_object* v_t_588_, lean_object* v_a_589_, lean_object* v_h_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_587_, v_t_588_, v_a_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___redArg(lean_object* v_cmp_592_, lean_object* v_inst_593_, lean_object* v_t_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_592_, v_t_594_, v_a_595_, v_inst_593_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21(lean_object* v_00_u03b1_597_, lean_object* v_00_u03b2_598_, lean_object* v_cmp_599_, lean_object* v_inst_600_, lean_object* v_t_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_599_, v_t_601_, v_a_602_, v_inst_600_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___redArg(lean_object* v_cmp_604_, lean_object* v_t_605_, lean_object* v_a_606_, lean_object* v_fallback_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_604_, v_t_605_, v_a_606_, v_fallback_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___redArg___boxed(lean_object* v_cmp_609_, lean_object* v_t_610_, lean_object* v_a_611_, lean_object* v_fallback_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_DTreeMap_Raw_getKeyD___redArg(v_cmp_609_, v_t_610_, v_a_611_, v_fallback_612_);
lean_dec(v_fallback_612_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD(lean_object* v_00_u03b1_614_, lean_object* v_00_u03b2_615_, lean_object* v_cmp_616_, lean_object* v_t_617_, lean_object* v_a_618_, lean_object* v_fallback_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_616_, v_t_617_, v_a_618_, v_fallback_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_621_, lean_object* v_00_u03b2_622_, lean_object* v_cmp_623_, lean_object* v_t_624_, lean_object* v_a_625_, lean_object* v_fallback_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_DTreeMap_Raw_getKeyD(v_00_u03b1_621_, v_00_u03b2_622_, v_cmp_623_, v_t_624_, v_a_625_, v_fallback_626_);
lean_dec(v_fallback_626_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___redArg(lean_object* v_t_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___redArg___boxed(lean_object* v_t_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std_DTreeMap_Raw_minEntry_x3f___redArg(v_t_630_);
lean_dec(v_t_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f(lean_object* v_00_u03b1_632_, lean_object* v_00_u03b2_633_, lean_object* v_cmp_634_, lean_object* v_t_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___boxed(lean_object* v_00_u03b1_637_, lean_object* v_00_u03b2_638_, lean_object* v_cmp_639_, lean_object* v_t_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_DTreeMap_Raw_minEntry_x3f(v_00_u03b1_637_, v_00_u03b2_638_, v_cmp_639_, v_t_640_);
lean_dec(v_t_640_);
lean_dec_ref(v_cmp_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___redArg(lean_object* v_inst_642_, lean_object* v_t_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_642_, v_t_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___redArg___boxed(lean_object* v_inst_645_, lean_object* v_t_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_DTreeMap_Raw_minEntry_x21___redArg(v_inst_645_, v_t_646_);
lean_dec(v_t_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21(lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_cmp_650_, lean_object* v_inst_651_, lean_object* v_t_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_651_, v_t_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___boxed(lean_object* v_00_u03b1_654_, lean_object* v_00_u03b2_655_, lean_object* v_cmp_656_, lean_object* v_inst_657_, lean_object* v_t_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_DTreeMap_Raw_minEntry_x21(v_00_u03b1_654_, v_00_u03b2_655_, v_cmp_656_, v_inst_657_, v_t_658_);
lean_dec(v_t_658_);
lean_dec_ref(v_cmp_656_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___redArg(lean_object* v_t_660_, lean_object* v_fallback_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_660_, v_fallback_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___redArg___boxed(lean_object* v_t_663_, lean_object* v_fallback_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_DTreeMap_Raw_minEntryD___redArg(v_t_663_, v_fallback_664_);
lean_dec_ref(v_fallback_664_);
lean_dec(v_t_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD(lean_object* v_00_u03b1_666_, lean_object* v_00_u03b2_667_, lean_object* v_cmp_668_, lean_object* v_t_669_, lean_object* v_fallback_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_669_, v_fallback_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___boxed(lean_object* v_00_u03b1_672_, lean_object* v_00_u03b2_673_, lean_object* v_cmp_674_, lean_object* v_t_675_, lean_object* v_fallback_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_DTreeMap_Raw_minEntryD(v_00_u03b1_672_, v_00_u03b2_673_, v_cmp_674_, v_t_675_, v_fallback_676_);
lean_dec_ref(v_fallback_676_);
lean_dec(v_t_675_);
lean_dec_ref(v_cmp_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___redArg(lean_object* v_t_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___redArg___boxed(lean_object* v_t_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_DTreeMap_Raw_maxEntry_x3f___redArg(v_t_680_);
lean_dec(v_t_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f(lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_cmp_684_, lean_object* v_t_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___boxed(lean_object* v_00_u03b1_687_, lean_object* v_00_u03b2_688_, lean_object* v_cmp_689_, lean_object* v_t_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_DTreeMap_Raw_maxEntry_x3f(v_00_u03b1_687_, v_00_u03b2_688_, v_cmp_689_, v_t_690_);
lean_dec(v_t_690_);
lean_dec_ref(v_cmp_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___redArg(lean_object* v_inst_692_, lean_object* v_t_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_692_, v_t_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___redArg___boxed(lean_object* v_inst_695_, lean_object* v_t_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_DTreeMap_Raw_maxEntry_x21___redArg(v_inst_695_, v_t_696_);
lean_dec(v_t_696_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_cmp_700_, lean_object* v_inst_701_, lean_object* v_t_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_701_, v_t_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___boxed(lean_object* v_00_u03b1_704_, lean_object* v_00_u03b2_705_, lean_object* v_cmp_706_, lean_object* v_inst_707_, lean_object* v_t_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_DTreeMap_Raw_maxEntry_x21(v_00_u03b1_704_, v_00_u03b2_705_, v_cmp_706_, v_inst_707_, v_t_708_);
lean_dec(v_t_708_);
lean_dec_ref(v_cmp_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___redArg(lean_object* v_t_710_, lean_object* v_fallback_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_710_, v_fallback_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___redArg___boxed(lean_object* v_t_713_, lean_object* v_fallback_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_DTreeMap_Raw_maxEntryD___redArg(v_t_713_, v_fallback_714_);
lean_dec_ref(v_fallback_714_);
lean_dec(v_t_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD(lean_object* v_00_u03b1_716_, lean_object* v_00_u03b2_717_, lean_object* v_cmp_718_, lean_object* v_t_719_, lean_object* v_fallback_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_719_, v_fallback_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___boxed(lean_object* v_00_u03b1_722_, lean_object* v_00_u03b2_723_, lean_object* v_cmp_724_, lean_object* v_t_725_, lean_object* v_fallback_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_DTreeMap_Raw_maxEntryD(v_00_u03b1_722_, v_00_u03b2_723_, v_cmp_724_, v_t_725_, v_fallback_726_);
lean_dec_ref(v_fallback_726_);
lean_dec(v_t_725_);
lean_dec_ref(v_cmp_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___redArg(lean_object* v_t_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___redArg___boxed(lean_object* v_t_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_DTreeMap_Raw_minKey_x3f___redArg(v_t_730_);
lean_dec(v_t_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f(lean_object* v_00_u03b1_732_, lean_object* v_00_u03b2_733_, lean_object* v_cmp_734_, lean_object* v_t_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___boxed(lean_object* v_00_u03b1_737_, lean_object* v_00_u03b2_738_, lean_object* v_cmp_739_, lean_object* v_t_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Std_DTreeMap_Raw_minKey_x3f(v_00_u03b1_737_, v_00_u03b2_738_, v_cmp_739_, v_t_740_);
lean_dec(v_t_740_);
lean_dec_ref(v_cmp_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___redArg(lean_object* v_t_742_, lean_object* v_fallback_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_742_, v_fallback_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___redArg___boxed(lean_object* v_t_745_, lean_object* v_fallback_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_DTreeMap_Raw_minKeyD___redArg(v_t_745_, v_fallback_746_);
lean_dec(v_fallback_746_);
lean_dec(v_t_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD(lean_object* v_00_u03b1_748_, lean_object* v_00_u03b2_749_, lean_object* v_cmp_750_, lean_object* v_t_751_, lean_object* v_fallback_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_751_, v_fallback_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___boxed(lean_object* v_00_u03b1_754_, lean_object* v_00_u03b2_755_, lean_object* v_cmp_756_, lean_object* v_t_757_, lean_object* v_fallback_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_DTreeMap_Raw_minKeyD(v_00_u03b1_754_, v_00_u03b2_755_, v_cmp_756_, v_t_757_, v_fallback_758_);
lean_dec(v_fallback_758_);
lean_dec(v_t_757_);
lean_dec_ref(v_cmp_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___redArg(lean_object* v_inst_760_, lean_object* v_t_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_760_, v_t_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___redArg___boxed(lean_object* v_inst_763_, lean_object* v_t_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_DTreeMap_Raw_minKey_x21___redArg(v_inst_763_, v_t_764_);
lean_dec(v_t_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21(lean_object* v_00_u03b1_766_, lean_object* v_00_u03b2_767_, lean_object* v_cmp_768_, lean_object* v_inst_769_, lean_object* v_t_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_769_, v_t_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___boxed(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_cmp_774_, lean_object* v_inst_775_, lean_object* v_t_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_DTreeMap_Raw_minKey_x21(v_00_u03b1_772_, v_00_u03b2_773_, v_cmp_774_, v_inst_775_, v_t_776_);
lean_dec(v_t_776_);
lean_dec_ref(v_cmp_774_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___redArg(lean_object* v_t_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___redArg___boxed(lean_object* v_t_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Std_DTreeMap_Raw_maxKey_x3f___redArg(v_t_780_);
lean_dec(v_t_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f(lean_object* v_00_u03b1_782_, lean_object* v_00_u03b2_783_, lean_object* v_cmp_784_, lean_object* v_t_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___boxed(lean_object* v_00_u03b1_787_, lean_object* v_00_u03b2_788_, lean_object* v_cmp_789_, lean_object* v_t_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_DTreeMap_Raw_maxKey_x3f(v_00_u03b1_787_, v_00_u03b2_788_, v_cmp_789_, v_t_790_);
lean_dec(v_t_790_);
lean_dec_ref(v_cmp_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___redArg(lean_object* v_inst_792_, lean_object* v_t_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_792_, v_t_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___redArg___boxed(lean_object* v_inst_795_, lean_object* v_t_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_DTreeMap_Raw_maxKey_x21___redArg(v_inst_795_, v_t_796_);
lean_dec(v_t_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21(lean_object* v_00_u03b1_798_, lean_object* v_00_u03b2_799_, lean_object* v_cmp_800_, lean_object* v_inst_801_, lean_object* v_t_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_801_, v_t_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___boxed(lean_object* v_00_u03b1_804_, lean_object* v_00_u03b2_805_, lean_object* v_cmp_806_, lean_object* v_inst_807_, lean_object* v_t_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_DTreeMap_Raw_maxKey_x21(v_00_u03b1_804_, v_00_u03b2_805_, v_cmp_806_, v_inst_807_, v_t_808_);
lean_dec(v_t_808_);
lean_dec_ref(v_cmp_806_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___redArg(lean_object* v_t_810_, lean_object* v_fallback_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_810_, v_fallback_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___redArg___boxed(lean_object* v_t_813_, lean_object* v_fallback_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_DTreeMap_Raw_maxKeyD___redArg(v_t_813_, v_fallback_814_);
lean_dec(v_fallback_814_);
lean_dec(v_t_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_cmp_818_, lean_object* v_t_819_, lean_object* v_fallback_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_819_, v_fallback_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___boxed(lean_object* v_00_u03b1_822_, lean_object* v_00_u03b2_823_, lean_object* v_cmp_824_, lean_object* v_t_825_, lean_object* v_fallback_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_DTreeMap_Raw_maxKeyD(v_00_u03b1_822_, v_00_u03b2_823_, v_cmp_824_, v_t_825_, v_fallback_826_);
lean_dec(v_fallback_826_);
lean_dec(v_t_825_);
lean_dec_ref(v_cmp_824_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg(lean_object* v_t_828_, lean_object* v_n_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_828_, v_n_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_831_, lean_object* v_n_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg(v_t_831_, v_n_832_);
lean_dec(v_t_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f(lean_object* v_00_u03b1_834_, lean_object* v_00_u03b2_835_, lean_object* v_cmp_836_, lean_object* v_t_837_, lean_object* v_n_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_837_, v_n_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_840_, lean_object* v_00_u03b2_841_, lean_object* v_cmp_842_, lean_object* v_t_843_, lean_object* v_n_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_DTreeMap_Raw_entryAtIdx_x3f(v_00_u03b1_840_, v_00_u03b2_841_, v_cmp_842_, v_t_843_, v_n_844_);
lean_dec(v_t_843_);
lean_dec_ref(v_cmp_842_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg(lean_object* v_inst_846_, lean_object* v_t_847_, lean_object* v_n_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_846_, v_t_847_, v_n_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_850_, lean_object* v_t_851_, lean_object* v_n_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg(v_inst_850_, v_t_851_, v_n_852_);
lean_dec(v_t_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21(lean_object* v_00_u03b1_854_, lean_object* v_00_u03b2_855_, lean_object* v_cmp_856_, lean_object* v_inst_857_, lean_object* v_t_858_, lean_object* v_n_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_857_, v_t_858_, v_n_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_861_, lean_object* v_00_u03b2_862_, lean_object* v_cmp_863_, lean_object* v_inst_864_, lean_object* v_t_865_, lean_object* v_n_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Std_DTreeMap_Raw_entryAtIdx_x21(v_00_u03b1_861_, v_00_u03b2_862_, v_cmp_863_, v_inst_864_, v_t_865_, v_n_866_);
lean_dec(v_t_865_);
lean_dec_ref(v_cmp_863_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___redArg(lean_object* v_t_868_, lean_object* v_n_869_, lean_object* v_fallback_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_868_, v_n_869_, v_fallback_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___redArg___boxed(lean_object* v_t_872_, lean_object* v_n_873_, lean_object* v_fallback_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Std_DTreeMap_Raw_entryAtIdxD___redArg(v_t_872_, v_n_873_, v_fallback_874_);
lean_dec_ref(v_fallback_874_);
lean_dec(v_t_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD(lean_object* v_00_u03b1_876_, lean_object* v_00_u03b2_877_, lean_object* v_cmp_878_, lean_object* v_t_879_, lean_object* v_n_880_, lean_object* v_fallback_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_879_, v_n_880_, v_fallback_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___boxed(lean_object* v_00_u03b1_883_, lean_object* v_00_u03b2_884_, lean_object* v_cmp_885_, lean_object* v_t_886_, lean_object* v_n_887_, lean_object* v_fallback_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_DTreeMap_Raw_entryAtIdxD(v_00_u03b1_883_, v_00_u03b2_884_, v_cmp_885_, v_t_886_, v_n_887_, v_fallback_888_);
lean_dec_ref(v_fallback_888_);
lean_dec(v_t_886_);
lean_dec_ref(v_cmp_885_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg(lean_object* v_t_890_, lean_object* v_n_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_890_, v_n_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_893_, lean_object* v_n_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg(v_t_893_, v_n_894_);
lean_dec(v_t_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f(lean_object* v_00_u03b1_896_, lean_object* v_00_u03b2_897_, lean_object* v_cmp_898_, lean_object* v_t_899_, lean_object* v_n_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_899_, v_n_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_cmp_904_, lean_object* v_t_905_, lean_object* v_n_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_DTreeMap_Raw_keyAtIdx_x3f(v_00_u03b1_902_, v_00_u03b2_903_, v_cmp_904_, v_t_905_, v_n_906_);
lean_dec(v_t_905_);
lean_dec_ref(v_cmp_904_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg(lean_object* v_inst_908_, lean_object* v_t_909_, lean_object* v_n_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_908_, v_t_909_, v_n_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_912_, lean_object* v_t_913_, lean_object* v_n_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg(v_inst_912_, v_t_913_, v_n_914_);
lean_dec(v_t_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21(lean_object* v_00_u03b1_916_, lean_object* v_00_u03b2_917_, lean_object* v_cmp_918_, lean_object* v_inst_919_, lean_object* v_t_920_, lean_object* v_n_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_919_, v_t_920_, v_n_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_923_, lean_object* v_00_u03b2_924_, lean_object* v_cmp_925_, lean_object* v_inst_926_, lean_object* v_t_927_, lean_object* v_n_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_DTreeMap_Raw_keyAtIdx_x21(v_00_u03b1_923_, v_00_u03b2_924_, v_cmp_925_, v_inst_926_, v_t_927_, v_n_928_);
lean_dec(v_t_927_);
lean_dec_ref(v_cmp_925_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___redArg(lean_object* v_t_930_, lean_object* v_n_931_, lean_object* v_fallback_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_930_, v_n_931_, v_fallback_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___redArg___boxed(lean_object* v_t_934_, lean_object* v_n_935_, lean_object* v_fallback_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_DTreeMap_Raw_keyAtIdxD___redArg(v_t_934_, v_n_935_, v_fallback_936_);
lean_dec(v_fallback_936_);
lean_dec(v_t_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD(lean_object* v_00_u03b1_938_, lean_object* v_00_u03b2_939_, lean_object* v_cmp_940_, lean_object* v_t_941_, lean_object* v_n_942_, lean_object* v_fallback_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_941_, v_n_942_, v_fallback_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___boxed(lean_object* v_00_u03b1_945_, lean_object* v_00_u03b2_946_, lean_object* v_cmp_947_, lean_object* v_t_948_, lean_object* v_n_949_, lean_object* v_fallback_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_DTreeMap_Raw_keyAtIdxD(v_00_u03b1_945_, v_00_u03b2_946_, v_cmp_947_, v_t_948_, v_n_949_, v_fallback_950_);
lean_dec(v_fallback_950_);
lean_dec(v_t_948_);
lean_dec_ref(v_cmp_947_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x3f___redArg(lean_object* v_cmp_952_, lean_object* v_t_953_, lean_object* v_k_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_box(0);
v___x_956_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_952_, v_k_954_, v___x_955_, v_t_953_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x3f(lean_object* v_00_u03b1_957_, lean_object* v_00_u03b2_958_, lean_object* v_cmp_959_, lean_object* v_t_960_, lean_object* v_k_961_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_box(0);
v___x_963_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_959_, v_k_961_, v___x_962_, v_t_960_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x3f___redArg(lean_object* v_cmp_964_, lean_object* v_t_965_, lean_object* v_k_966_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_box(0);
v___x_968_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_964_, v_k_966_, v___x_967_, v_t_965_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x3f(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_cmp_971_, lean_object* v_t_972_, lean_object* v_k_973_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_box(0);
v___x_975_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_971_, v_k_973_, v___x_974_, v_t_972_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x3f___redArg(lean_object* v_cmp_976_, lean_object* v_t_977_, lean_object* v_k_978_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_box(0);
v___x_980_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_976_, v_k_978_, v___x_979_, v_t_977_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x3f(lean_object* v_00_u03b1_981_, lean_object* v_00_u03b2_982_, lean_object* v_cmp_983_, lean_object* v_t_984_, lean_object* v_k_985_){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_box(0);
v___x_987_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_983_, v_k_985_, v___x_986_, v_t_984_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x3f___redArg(lean_object* v_cmp_988_, lean_object* v_t_989_, lean_object* v_k_990_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_box(0);
v___x_992_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_988_, v_k_990_, v___x_991_, v_t_989_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x3f(lean_object* v_00_u03b1_993_, lean_object* v_00_u03b2_994_, lean_object* v_cmp_995_, lean_object* v_t_996_, lean_object* v_k_997_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_box(0);
v___x_999_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_995_, v_k_997_, v___x_998_, v_t_996_);
return v___x_999_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1003_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__2));
v___x_1004_ = lean_unsigned_to_nat(14u);
v___x_1005_ = lean_unsigned_to_nat(22u);
v___x_1006_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__1));
v___x_1007_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__0));
v___x_1008_ = l_mkPanicMessageWithDecl(v___x_1007_, v___x_1006_, v___x_1005_, v___x_1004_, v___x_1003_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg(lean_object* v_cmp_1009_, lean_object* v_inst_1010_, lean_object* v_t_1011_, lean_object* v_k_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1009_, v_k_1012_, v___x_1013_, v_t_1011_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1016_ = l_panic___redArg(v_inst_1010_, v___x_1015_);
return v___x_1016_;
}
else
{
lean_object* v_val_1017_; 
lean_dec_ref(v_inst_1010_);
v_val_1017_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_val_1017_);
lean_dec_ref(v___x_1014_);
return v_val_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21(lean_object* v_00_u03b1_1018_, lean_object* v_00_u03b2_1019_, lean_object* v_cmp_1020_, lean_object* v_inst_1021_, lean_object* v_t_1022_, lean_object* v_k_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1020_, v_k_1023_, v___x_1024_, v_t_1022_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1027_ = l_panic___redArg(v_inst_1021_, v___x_1026_);
return v___x_1027_;
}
else
{
lean_object* v_val_1028_; 
lean_dec_ref(v_inst_1021_);
v_val_1028_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_val_1028_);
lean_dec_ref(v___x_1025_);
return v_val_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___redArg(lean_object* v_cmp_1029_, lean_object* v_inst_1030_, lean_object* v_t_1031_, lean_object* v_k_1032_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_box(0);
v___x_1034_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1029_, v_k_1032_, v___x_1033_, v_t_1031_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1036_ = l_panic___redArg(v_inst_1030_, v___x_1035_);
return v___x_1036_;
}
else
{
lean_object* v_val_1037_; 
lean_dec_ref(v_inst_1030_);
v_val_1037_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_val_1037_);
lean_dec_ref(v___x_1034_);
return v_val_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21(lean_object* v_00_u03b1_1038_, lean_object* v_00_u03b2_1039_, lean_object* v_cmp_1040_, lean_object* v_inst_1041_, lean_object* v_t_1042_, lean_object* v_k_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1040_, v_k_1043_, v___x_1044_, v_t_1042_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1047_ = l_panic___redArg(v_inst_1041_, v___x_1046_);
return v___x_1047_;
}
else
{
lean_object* v_val_1048_; 
lean_dec_ref(v_inst_1041_);
v_val_1048_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_val_1048_);
lean_dec_ref(v___x_1045_);
return v_val_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___redArg(lean_object* v_cmp_1049_, lean_object* v_inst_1050_, lean_object* v_t_1051_, lean_object* v_k_1052_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_box(0);
v___x_1054_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1049_, v_k_1052_, v___x_1053_, v_t_1051_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1056_ = l_panic___redArg(v_inst_1050_, v___x_1055_);
return v___x_1056_;
}
else
{
lean_object* v_val_1057_; 
lean_dec_ref(v_inst_1050_);
v_val_1057_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_val_1057_);
lean_dec_ref(v___x_1054_);
return v_val_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21(lean_object* v_00_u03b1_1058_, lean_object* v_00_u03b2_1059_, lean_object* v_cmp_1060_, lean_object* v_inst_1061_, lean_object* v_t_1062_, lean_object* v_k_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1060_, v_k_1063_, v___x_1064_, v_t_1062_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1067_ = l_panic___redArg(v_inst_1061_, v___x_1066_);
return v___x_1067_;
}
else
{
lean_object* v_val_1068_; 
lean_dec_ref(v_inst_1061_);
v_val_1068_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_val_1068_);
lean_dec_ref(v___x_1065_);
return v_val_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___redArg(lean_object* v_cmp_1069_, lean_object* v_inst_1070_, lean_object* v_t_1071_, lean_object* v_k_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1069_, v_k_1072_, v___x_1073_, v_t_1071_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1076_ = l_panic___redArg(v_inst_1070_, v___x_1075_);
return v___x_1076_;
}
else
{
lean_object* v_val_1077_; 
lean_dec_ref(v_inst_1070_);
v_val_1077_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_val_1077_);
lean_dec_ref(v___x_1074_);
return v_val_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_cmp_1080_, lean_object* v_inst_1081_, lean_object* v_t_1082_, lean_object* v_k_1083_){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_box(0);
v___x_1085_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1080_, v_k_1083_, v___x_1084_, v_t_1082_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1087_ = l_panic___redArg(v_inst_1081_, v___x_1086_);
return v___x_1087_;
}
else
{
lean_object* v_val_1088_; 
lean_dec_ref(v_inst_1081_);
v_val_1088_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_val_1088_);
lean_dec_ref(v___x_1085_);
return v_val_1088_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___redArg(lean_object* v_cmp_1089_, lean_object* v_t_1090_, lean_object* v_k_1091_, lean_object* v_fallback_1092_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_box(0);
v___x_1094_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1089_, v_k_1091_, v___x_1093_, v_t_1090_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_inc_ref(v_fallback_1092_);
return v_fallback_1092_;
}
else
{
lean_object* v_val_1095_; 
v_val_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_val_1095_);
lean_dec_ref(v___x_1094_);
return v_val_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___redArg___boxed(lean_object* v_cmp_1096_, lean_object* v_t_1097_, lean_object* v_k_1098_, lean_object* v_fallback_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Std_DTreeMap_Raw_getEntryGED___redArg(v_cmp_1096_, v_t_1097_, v_k_1098_, v_fallback_1099_);
lean_dec_ref(v_fallback_1099_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED(lean_object* v_00_u03b1_1101_, lean_object* v_00_u03b2_1102_, lean_object* v_cmp_1103_, lean_object* v_t_1104_, lean_object* v_k_1105_, lean_object* v_fallback_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_box(0);
v___x_1108_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1103_, v_k_1105_, v___x_1107_, v_t_1104_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_inc_ref(v_fallback_1106_);
return v_fallback_1106_;
}
else
{
lean_object* v_val_1109_; 
v_val_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_val_1109_);
lean_dec_ref(v___x_1108_);
return v_val_1109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___boxed(lean_object* v_00_u03b1_1110_, lean_object* v_00_u03b2_1111_, lean_object* v_cmp_1112_, lean_object* v_t_1113_, lean_object* v_k_1114_, lean_object* v_fallback_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Std_DTreeMap_Raw_getEntryGED(v_00_u03b1_1110_, v_00_u03b2_1111_, v_cmp_1112_, v_t_1113_, v_k_1114_, v_fallback_1115_);
lean_dec_ref(v_fallback_1115_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___redArg(lean_object* v_cmp_1117_, lean_object* v_t_1118_, lean_object* v_k_1119_, lean_object* v_fallback_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_box(0);
v___x_1122_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1117_, v_k_1119_, v___x_1121_, v_t_1118_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_inc_ref(v_fallback_1120_);
return v_fallback_1120_;
}
else
{
lean_object* v_val_1123_; 
v_val_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_val_1123_);
lean_dec_ref(v___x_1122_);
return v_val_1123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___redArg___boxed(lean_object* v_cmp_1124_, lean_object* v_t_1125_, lean_object* v_k_1126_, lean_object* v_fallback_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Std_DTreeMap_Raw_getEntryGTD___redArg(v_cmp_1124_, v_t_1125_, v_k_1126_, v_fallback_1127_);
lean_dec_ref(v_fallback_1127_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_cmp_1131_, lean_object* v_t_1132_, lean_object* v_k_1133_, lean_object* v_fallback_1134_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_box(0);
v___x_1136_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1131_, v_k_1133_, v___x_1135_, v_t_1132_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_inc_ref(v_fallback_1134_);
return v_fallback_1134_;
}
else
{
lean_object* v_val_1137_; 
v_val_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_val_1137_);
lean_dec_ref(v___x_1136_);
return v_val_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___boxed(lean_object* v_00_u03b1_1138_, lean_object* v_00_u03b2_1139_, lean_object* v_cmp_1140_, lean_object* v_t_1141_, lean_object* v_k_1142_, lean_object* v_fallback_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_DTreeMap_Raw_getEntryGTD(v_00_u03b1_1138_, v_00_u03b2_1139_, v_cmp_1140_, v_t_1141_, v_k_1142_, v_fallback_1143_);
lean_dec_ref(v_fallback_1143_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___redArg(lean_object* v_cmp_1145_, lean_object* v_t_1146_, lean_object* v_k_1147_, lean_object* v_fallback_1148_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_box(0);
v___x_1150_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1145_, v_k_1147_, v___x_1149_, v_t_1146_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_inc_ref(v_fallback_1148_);
return v_fallback_1148_;
}
else
{
lean_object* v_val_1151_; 
v_val_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_val_1151_);
lean_dec_ref(v___x_1150_);
return v_val_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___redArg___boxed(lean_object* v_cmp_1152_, lean_object* v_t_1153_, lean_object* v_k_1154_, lean_object* v_fallback_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_DTreeMap_Raw_getEntryLED___redArg(v_cmp_1152_, v_t_1153_, v_k_1154_, v_fallback_1155_);
lean_dec_ref(v_fallback_1155_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_cmp_1159_, lean_object* v_t_1160_, lean_object* v_k_1161_, lean_object* v_fallback_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_box(0);
v___x_1164_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1159_, v_k_1161_, v___x_1163_, v_t_1160_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_inc_ref(v_fallback_1162_);
return v_fallback_1162_;
}
else
{
lean_object* v_val_1165_; 
v_val_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_val_1165_);
lean_dec_ref(v___x_1164_);
return v_val_1165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___boxed(lean_object* v_00_u03b1_1166_, lean_object* v_00_u03b2_1167_, lean_object* v_cmp_1168_, lean_object* v_t_1169_, lean_object* v_k_1170_, lean_object* v_fallback_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Std_DTreeMap_Raw_getEntryLED(v_00_u03b1_1166_, v_00_u03b2_1167_, v_cmp_1168_, v_t_1169_, v_k_1170_, v_fallback_1171_);
lean_dec_ref(v_fallback_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___redArg(lean_object* v_cmp_1173_, lean_object* v_t_1174_, lean_object* v_k_1175_, lean_object* v_fallback_1176_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1173_, v_k_1175_, v___x_1177_, v_t_1174_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_inc_ref(v_fallback_1176_);
return v_fallback_1176_;
}
else
{
lean_object* v_val_1179_; 
v_val_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_val_1179_);
lean_dec_ref(v___x_1178_);
return v_val_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___redArg___boxed(lean_object* v_cmp_1180_, lean_object* v_t_1181_, lean_object* v_k_1182_, lean_object* v_fallback_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_DTreeMap_Raw_getEntryLTD___redArg(v_cmp_1180_, v_t_1181_, v_k_1182_, v_fallback_1183_);
lean_dec_ref(v_fallback_1183_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD(lean_object* v_00_u03b1_1185_, lean_object* v_00_u03b2_1186_, lean_object* v_cmp_1187_, lean_object* v_t_1188_, lean_object* v_k_1189_, lean_object* v_fallback_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1187_, v_k_1189_, v___x_1191_, v_t_1188_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_inc_ref(v_fallback_1190_);
return v_fallback_1190_;
}
else
{
lean_object* v_val_1193_; 
v_val_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_val_1193_);
lean_dec_ref(v___x_1192_);
return v_val_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___boxed(lean_object* v_00_u03b1_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_cmp_1196_, lean_object* v_t_1197_, lean_object* v_k_1198_, lean_object* v_fallback_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_DTreeMap_Raw_getEntryLTD(v_00_u03b1_1194_, v_00_u03b2_1195_, v_cmp_1196_, v_t_1197_, v_k_1198_, v_fallback_1199_);
lean_dec_ref(v_fallback_1199_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x3f___redArg(lean_object* v_cmp_1201_, lean_object* v_t_1202_, lean_object* v_k_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1201_, v_k_1203_, v___x_1204_, v_t_1202_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x3f(lean_object* v_00_u03b1_1206_, lean_object* v_00_u03b2_1207_, lean_object* v_cmp_1208_, lean_object* v_t_1209_, lean_object* v_k_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1208_, v_k_1210_, v___x_1211_, v_t_1209_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x3f___redArg(lean_object* v_cmp_1213_, lean_object* v_t_1214_, lean_object* v_k_1215_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1213_, v_k_1215_, v___x_1216_, v_t_1214_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x3f(lean_object* v_00_u03b1_1218_, lean_object* v_00_u03b2_1219_, lean_object* v_cmp_1220_, lean_object* v_t_1221_, lean_object* v_k_1222_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_box(0);
v___x_1224_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1220_, v_k_1222_, v___x_1223_, v_t_1221_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x3f___redArg(lean_object* v_cmp_1225_, lean_object* v_t_1226_, lean_object* v_k_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_box(0);
v___x_1229_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1225_, v_k_1227_, v___x_1228_, v_t_1226_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x3f(lean_object* v_00_u03b1_1230_, lean_object* v_00_u03b2_1231_, lean_object* v_cmp_1232_, lean_object* v_t_1233_, lean_object* v_k_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_box(0);
v___x_1236_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1232_, v_k_1234_, v___x_1235_, v_t_1233_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x3f___redArg(lean_object* v_cmp_1237_, lean_object* v_t_1238_, lean_object* v_k_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1237_, v_k_1239_, v___x_1240_, v_t_1238_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x3f(lean_object* v_00_u03b1_1242_, lean_object* v_00_u03b2_1243_, lean_object* v_cmp_1244_, lean_object* v_t_1245_, lean_object* v_k_1246_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_box(0);
v___x_1248_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1244_, v_k_1246_, v___x_1247_, v_t_1245_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___redArg(lean_object* v_cmp_1249_, lean_object* v_inst_1250_, lean_object* v_t_1251_, lean_object* v_k_1252_){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_box(0);
v___x_1254_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1249_, v_k_1252_, v___x_1253_, v_t_1251_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1256_ = l_panic___redArg(v_inst_1250_, v___x_1255_);
return v___x_1256_;
}
else
{
lean_object* v_val_1257_; 
lean_dec(v_inst_1250_);
v_val_1257_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_val_1257_);
lean_dec_ref(v___x_1254_);
return v_val_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21(lean_object* v_00_u03b1_1258_, lean_object* v_00_u03b2_1259_, lean_object* v_cmp_1260_, lean_object* v_inst_1261_, lean_object* v_t_1262_, lean_object* v_k_1263_){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_box(0);
v___x_1265_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1260_, v_k_1263_, v___x_1264_, v_t_1262_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1267_ = l_panic___redArg(v_inst_1261_, v___x_1266_);
return v___x_1267_;
}
else
{
lean_object* v_val_1268_; 
lean_dec(v_inst_1261_);
v_val_1268_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_val_1268_);
lean_dec_ref(v___x_1265_);
return v_val_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___redArg(lean_object* v_cmp_1269_, lean_object* v_inst_1270_, lean_object* v_t_1271_, lean_object* v_k_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_box(0);
v___x_1274_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1269_, v_k_1272_, v___x_1273_, v_t_1271_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1276_ = l_panic___redArg(v_inst_1270_, v___x_1275_);
return v___x_1276_;
}
else
{
lean_object* v_val_1277_; 
lean_dec(v_inst_1270_);
v_val_1277_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_val_1277_);
lean_dec_ref(v___x_1274_);
return v_val_1277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21(lean_object* v_00_u03b1_1278_, lean_object* v_00_u03b2_1279_, lean_object* v_cmp_1280_, lean_object* v_inst_1281_, lean_object* v_t_1282_, lean_object* v_k_1283_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_box(0);
v___x_1285_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1280_, v_k_1283_, v___x_1284_, v_t_1282_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1287_ = l_panic___redArg(v_inst_1281_, v___x_1286_);
return v___x_1287_;
}
else
{
lean_object* v_val_1288_; 
lean_dec(v_inst_1281_);
v_val_1288_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_val_1288_);
lean_dec_ref(v___x_1285_);
return v_val_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___redArg(lean_object* v_cmp_1289_, lean_object* v_inst_1290_, lean_object* v_t_1291_, lean_object* v_k_1292_){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_box(0);
v___x_1294_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1289_, v_k_1292_, v___x_1293_, v_t_1291_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1296_ = l_panic___redArg(v_inst_1290_, v___x_1295_);
return v___x_1296_;
}
else
{
lean_object* v_val_1297_; 
lean_dec(v_inst_1290_);
v_val_1297_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_val_1297_);
lean_dec_ref(v___x_1294_);
return v_val_1297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21(lean_object* v_00_u03b1_1298_, lean_object* v_00_u03b2_1299_, lean_object* v_cmp_1300_, lean_object* v_inst_1301_, lean_object* v_t_1302_, lean_object* v_k_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1300_, v_k_1303_, v___x_1304_, v_t_1302_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1307_ = l_panic___redArg(v_inst_1301_, v___x_1306_);
return v___x_1307_;
}
else
{
lean_object* v_val_1308_; 
lean_dec(v_inst_1301_);
v_val_1308_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_val_1308_);
lean_dec_ref(v___x_1305_);
return v_val_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___redArg(lean_object* v_cmp_1309_, lean_object* v_inst_1310_, lean_object* v_t_1311_, lean_object* v_k_1312_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_box(0);
v___x_1314_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1309_, v_k_1312_, v___x_1313_, v_t_1311_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1316_ = l_panic___redArg(v_inst_1310_, v___x_1315_);
return v___x_1316_;
}
else
{
lean_object* v_val_1317_; 
lean_dec(v_inst_1310_);
v_val_1317_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_val_1317_);
lean_dec_ref(v___x_1314_);
return v_val_1317_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21(lean_object* v_00_u03b1_1318_, lean_object* v_00_u03b2_1319_, lean_object* v_cmp_1320_, lean_object* v_inst_1321_, lean_object* v_t_1322_, lean_object* v_k_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1320_, v_k_1323_, v___x_1324_, v_t_1322_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1327_ = l_panic___redArg(v_inst_1321_, v___x_1326_);
return v___x_1327_;
}
else
{
lean_object* v_val_1328_; 
lean_dec(v_inst_1321_);
v_val_1328_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_val_1328_);
lean_dec_ref(v___x_1325_);
return v_val_1328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___redArg(lean_object* v_cmp_1329_, lean_object* v_t_1330_, lean_object* v_k_1331_, lean_object* v_fallback_1332_){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_box(0);
v___x_1334_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1329_, v_k_1331_, v___x_1333_, v_t_1330_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_inc(v_fallback_1332_);
return v_fallback_1332_;
}
else
{
lean_object* v_val_1335_; 
v_val_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_val_1335_);
lean_dec_ref(v___x_1334_);
return v_val_1335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___redArg___boxed(lean_object* v_cmp_1336_, lean_object* v_t_1337_, lean_object* v_k_1338_, lean_object* v_fallback_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Std_DTreeMap_Raw_getKeyGED___redArg(v_cmp_1336_, v_t_1337_, v_k_1338_, v_fallback_1339_);
lean_dec(v_fallback_1339_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED(lean_object* v_00_u03b1_1341_, lean_object* v_00_u03b2_1342_, lean_object* v_cmp_1343_, lean_object* v_t_1344_, lean_object* v_k_1345_, lean_object* v_fallback_1346_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_box(0);
v___x_1348_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1343_, v_k_1345_, v___x_1347_, v_t_1344_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_inc(v_fallback_1346_);
return v_fallback_1346_;
}
else
{
lean_object* v_val_1349_; 
v_val_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_val_1349_);
lean_dec_ref(v___x_1348_);
return v_val_1349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___boxed(lean_object* v_00_u03b1_1350_, lean_object* v_00_u03b2_1351_, lean_object* v_cmp_1352_, lean_object* v_t_1353_, lean_object* v_k_1354_, lean_object* v_fallback_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Std_DTreeMap_Raw_getKeyGED(v_00_u03b1_1350_, v_00_u03b2_1351_, v_cmp_1352_, v_t_1353_, v_k_1354_, v_fallback_1355_);
lean_dec(v_fallback_1355_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___redArg(lean_object* v_cmp_1357_, lean_object* v_t_1358_, lean_object* v_k_1359_, lean_object* v_fallback_1360_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_box(0);
v___x_1362_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1357_, v_k_1359_, v___x_1361_, v_t_1358_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_inc(v_fallback_1360_);
return v_fallback_1360_;
}
else
{
lean_object* v_val_1363_; 
v_val_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_val_1363_);
lean_dec_ref(v___x_1362_);
return v_val_1363_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___redArg___boxed(lean_object* v_cmp_1364_, lean_object* v_t_1365_, lean_object* v_k_1366_, lean_object* v_fallback_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Std_DTreeMap_Raw_getKeyGTD___redArg(v_cmp_1364_, v_t_1365_, v_k_1366_, v_fallback_1367_);
lean_dec(v_fallback_1367_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD(lean_object* v_00_u03b1_1369_, lean_object* v_00_u03b2_1370_, lean_object* v_cmp_1371_, lean_object* v_t_1372_, lean_object* v_k_1373_, lean_object* v_fallback_1374_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1371_, v_k_1373_, v___x_1375_, v_t_1372_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_inc(v_fallback_1374_);
return v_fallback_1374_;
}
else
{
lean_object* v_val_1377_; 
v_val_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_val_1377_);
lean_dec_ref(v___x_1376_);
return v_val_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___boxed(lean_object* v_00_u03b1_1378_, lean_object* v_00_u03b2_1379_, lean_object* v_cmp_1380_, lean_object* v_t_1381_, lean_object* v_k_1382_, lean_object* v_fallback_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Std_DTreeMap_Raw_getKeyGTD(v_00_u03b1_1378_, v_00_u03b2_1379_, v_cmp_1380_, v_t_1381_, v_k_1382_, v_fallback_1383_);
lean_dec(v_fallback_1383_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___redArg(lean_object* v_cmp_1385_, lean_object* v_t_1386_, lean_object* v_k_1387_, lean_object* v_fallback_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1385_, v_k_1387_, v___x_1389_, v_t_1386_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_inc(v_fallback_1388_);
return v_fallback_1388_;
}
else
{
lean_object* v_val_1391_; 
v_val_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_val_1391_);
lean_dec_ref(v___x_1390_);
return v_val_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___redArg___boxed(lean_object* v_cmp_1392_, lean_object* v_t_1393_, lean_object* v_k_1394_, lean_object* v_fallback_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Std_DTreeMap_Raw_getKeyLED___redArg(v_cmp_1392_, v_t_1393_, v_k_1394_, v_fallback_1395_);
lean_dec(v_fallback_1395_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED(lean_object* v_00_u03b1_1397_, lean_object* v_00_u03b2_1398_, lean_object* v_cmp_1399_, lean_object* v_t_1400_, lean_object* v_k_1401_, lean_object* v_fallback_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_box(0);
v___x_1404_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1399_, v_k_1401_, v___x_1403_, v_t_1400_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_inc(v_fallback_1402_);
return v_fallback_1402_;
}
else
{
lean_object* v_val_1405_; 
v_val_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_val_1405_);
lean_dec_ref(v___x_1404_);
return v_val_1405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___boxed(lean_object* v_00_u03b1_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_cmp_1408_, lean_object* v_t_1409_, lean_object* v_k_1410_, lean_object* v_fallback_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Std_DTreeMap_Raw_getKeyLED(v_00_u03b1_1406_, v_00_u03b2_1407_, v_cmp_1408_, v_t_1409_, v_k_1410_, v_fallback_1411_);
lean_dec(v_fallback_1411_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___redArg(lean_object* v_cmp_1413_, lean_object* v_t_1414_, lean_object* v_k_1415_, lean_object* v_fallback_1416_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_box(0);
v___x_1418_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1413_, v_k_1415_, v___x_1417_, v_t_1414_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_inc(v_fallback_1416_);
return v_fallback_1416_;
}
else
{
lean_object* v_val_1419_; 
v_val_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_val_1419_);
lean_dec_ref(v___x_1418_);
return v_val_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___redArg___boxed(lean_object* v_cmp_1420_, lean_object* v_t_1421_, lean_object* v_k_1422_, lean_object* v_fallback_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Std_DTreeMap_Raw_getKeyLTD___redArg(v_cmp_1420_, v_t_1421_, v_k_1422_, v_fallback_1423_);
lean_dec(v_fallback_1423_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD(lean_object* v_00_u03b1_1425_, lean_object* v_00_u03b2_1426_, lean_object* v_cmp_1427_, lean_object* v_t_1428_, lean_object* v_k_1429_, lean_object* v_fallback_1430_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_box(0);
v___x_1432_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1427_, v_k_1429_, v___x_1431_, v_t_1428_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_inc(v_fallback_1430_);
return v_fallback_1430_;
}
else
{
lean_object* v_val_1433_; 
v_val_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_val_1433_);
lean_dec_ref(v___x_1432_);
return v_val_1433_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___boxed(lean_object* v_00_u03b1_1434_, lean_object* v_00_u03b2_1435_, lean_object* v_cmp_1436_, lean_object* v_t_1437_, lean_object* v_k_1438_, lean_object* v_fallback_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Std_DTreeMap_Raw_getKeyLTD(v_00_u03b1_1434_, v_00_u03b2_1435_, v_cmp_1436_, v_t_1437_, v_k_1438_, v_fallback_1439_);
lean_dec(v_fallback_1439_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1441_, lean_object* v_t_1442_, lean_object* v_a_1443_, lean_object* v_b_1444_){
_start:
{
lean_object* v___x_1445_; 
lean_inc(v_a_1443_);
lean_inc(v_t_1442_);
lean_inc_ref(v_cmp_1441_);
v___x_1445_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1441_, v_t_1442_, v_a_1443_);
if (lean_obj_tag(v___x_1445_) == 0)
{
uint8_t v___x_1446_; 
lean_inc(v_t_1442_);
lean_inc(v_a_1443_);
lean_inc_ref(v_cmp_1441_);
v___x_1446_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1441_, v_a_1443_, v_t_1442_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1441_, v_a_1443_, v_b_1444_, v_t_1442_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1445_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
return v___x_1448_;
}
else
{
lean_object* v___x_1449_; 
lean_dec(v_b_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_cmp_1441_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1445_);
lean_ctor_set(v___x_1449_, 1, v_t_1442_);
return v___x_1449_;
}
}
else
{
lean_object* v___x_1450_; 
lean_dec(v_b_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_cmp_1441_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1445_);
lean_ctor_set(v___x_1450_, 1, v_t_1442_);
return v___x_1450_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1451_, lean_object* v_cmp_1452_, lean_object* v_00_u03b2_1453_, lean_object* v_t_1454_, lean_object* v_a_1455_, lean_object* v_b_1456_){
_start:
{
lean_object* v___x_1457_; 
lean_inc(v_a_1455_);
lean_inc(v_t_1454_);
lean_inc_ref(v_cmp_1452_);
v___x_1457_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1452_, v_t_1454_, v_a_1455_);
if (lean_obj_tag(v___x_1457_) == 0)
{
uint8_t v___x_1458_; 
lean_inc(v_t_1454_);
lean_inc(v_a_1455_);
lean_inc_ref(v_cmp_1452_);
v___x_1458_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1452_, v_a_1455_, v_t_1454_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1452_, v_a_1455_, v_b_1456_, v_t_1454_);
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1457_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
return v___x_1460_;
}
else
{
lean_object* v___x_1461_; 
lean_dec(v_b_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_cmp_1452_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1457_);
lean_ctor_set(v___x_1461_, 1, v_t_1454_);
return v___x_1461_;
}
}
else
{
lean_object* v___x_1462_; 
lean_dec(v_b_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_cmp_1452_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1457_);
lean_ctor_set(v___x_1462_, 1, v_t_1454_);
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x3f___redArg(lean_object* v_cmp_1463_, lean_object* v_t_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1463_, v_t_1464_, v_a_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x3f(lean_object* v_00_u03b1_1467_, lean_object* v_cmp_1468_, lean_object* v_00_u03b2_1469_, lean_object* v_t_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1468_, v_t_1470_, v_a_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get___redArg(lean_object* v_cmp_1473_, lean_object* v_t_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1473_, v_t_1474_, v_a_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get(lean_object* v_00_u03b1_1477_, lean_object* v_cmp_1478_, lean_object* v_00_u03b2_1479_, lean_object* v_t_1480_, lean_object* v_a_1481_, lean_object* v_h_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1478_, v_t_1480_, v_a_1481_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___redArg(lean_object* v_cmp_1484_, lean_object* v_inst_1485_, lean_object* v_t_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1484_, v_inst_1485_, v_t_1486_, v_a_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21(lean_object* v_00_u03b1_1489_, lean_object* v_cmp_1490_, lean_object* v_00_u03b2_1491_, lean_object* v_inst_1492_, lean_object* v_t_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1490_, v_inst_1492_, v_t_1493_, v_a_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___redArg(lean_object* v_cmp_1496_, lean_object* v_t_1497_, lean_object* v_a_1498_, lean_object* v_fallback_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1496_, v_t_1497_, v_a_1498_, v_fallback_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___redArg___boxed(lean_object* v_cmp_1501_, lean_object* v_t_1502_, lean_object* v_a_1503_, lean_object* v_fallback_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Std_DTreeMap_Raw_Const_getD___redArg(v_cmp_1501_, v_t_1502_, v_a_1503_, v_fallback_1504_);
lean_dec(v_fallback_1504_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD(lean_object* v_00_u03b1_1506_, lean_object* v_cmp_1507_, lean_object* v_00_u03b2_1508_, lean_object* v_t_1509_, lean_object* v_a_1510_, lean_object* v_fallback_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1507_, v_t_1509_, v_a_1510_, v_fallback_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___boxed(lean_object* v_00_u03b1_1513_, lean_object* v_cmp_1514_, lean_object* v_00_u03b2_1515_, lean_object* v_t_1516_, lean_object* v_a_1517_, lean_object* v_fallback_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Std_DTreeMap_Raw_Const_getD(v_00_u03b1_1513_, v_cmp_1514_, v_00_u03b2_1515_, v_t_1516_, v_a_1517_, v_fallback_1518_);
lean_dec(v_fallback_1518_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg(lean_object* v_t_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg(v_t_1522_);
lean_dec(v_t_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f(lean_object* v_00_u03b1_1524_, lean_object* v_cmp_1525_, lean_object* v_00_u03b2_1526_, lean_object* v_t_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1529_, lean_object* v_cmp_1530_, lean_object* v_00_u03b2_1531_, lean_object* v_t_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Std_DTreeMap_Raw_Const_minEntry_x3f(v_00_u03b1_1529_, v_cmp_1530_, v_00_u03b2_1531_, v_t_1532_);
lean_dec(v_t_1532_);
lean_dec_ref(v_cmp_1530_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg(lean_object* v_inst_1534_, lean_object* v_t_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1534_, v_t_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1537_, lean_object* v_t_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg(v_inst_1537_, v_t_1538_);
lean_dec(v_t_1538_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21(lean_object* v_00_u03b1_1540_, lean_object* v_cmp_1541_, lean_object* v_00_u03b2_1542_, lean_object* v_inst_1543_, lean_object* v_t_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1543_, v_t_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1546_, lean_object* v_cmp_1547_, lean_object* v_00_u03b2_1548_, lean_object* v_inst_1549_, lean_object* v_t_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Std_DTreeMap_Raw_Const_minEntry_x21(v_00_u03b1_1546_, v_cmp_1547_, v_00_u03b2_1548_, v_inst_1549_, v_t_1550_);
lean_dec(v_t_1550_);
lean_dec_ref(v_cmp_1547_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___redArg(lean_object* v_t_1552_, lean_object* v_fallback_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1552_, v_fallback_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___redArg___boxed(lean_object* v_t_1555_, lean_object* v_fallback_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Std_DTreeMap_Raw_Const_minEntryD___redArg(v_t_1555_, v_fallback_1556_);
lean_dec_ref(v_fallback_1556_);
lean_dec(v_t_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD(lean_object* v_00_u03b1_1558_, lean_object* v_cmp_1559_, lean_object* v_00_u03b2_1560_, lean_object* v_t_1561_, lean_object* v_fallback_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1561_, v_fallback_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___boxed(lean_object* v_00_u03b1_1564_, lean_object* v_cmp_1565_, lean_object* v_00_u03b2_1566_, lean_object* v_t_1567_, lean_object* v_fallback_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Std_DTreeMap_Raw_Const_minEntryD(v_00_u03b1_1564_, v_cmp_1565_, v_00_u03b2_1566_, v_t_1567_, v_fallback_1568_);
lean_dec_ref(v_fallback_1568_);
lean_dec(v_t_1567_);
lean_dec_ref(v_cmp_1565_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg(lean_object* v_t_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg(v_t_1572_);
lean_dec(v_t_1572_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f(lean_object* v_00_u03b1_1574_, lean_object* v_cmp_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_t_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1579_, lean_object* v_cmp_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_t_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Std_DTreeMap_Raw_Const_maxEntry_x3f(v_00_u03b1_1579_, v_cmp_1580_, v_00_u03b2_1581_, v_t_1582_);
lean_dec(v_t_1582_);
lean_dec_ref(v_cmp_1580_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg(lean_object* v_inst_1584_, lean_object* v_t_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1584_, v_t_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_1587_, lean_object* v_t_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg(v_inst_1587_, v_t_1588_);
lean_dec(v_t_1588_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21(lean_object* v_00_u03b1_1590_, lean_object* v_cmp_1591_, lean_object* v_00_u03b2_1592_, lean_object* v_inst_1593_, lean_object* v_t_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1593_, v_t_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_1596_, lean_object* v_cmp_1597_, lean_object* v_00_u03b2_1598_, lean_object* v_inst_1599_, lean_object* v_t_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Std_DTreeMap_Raw_Const_maxEntry_x21(v_00_u03b1_1596_, v_cmp_1597_, v_00_u03b2_1598_, v_inst_1599_, v_t_1600_);
lean_dec(v_t_1600_);
lean_dec_ref(v_cmp_1597_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___redArg(lean_object* v_t_1602_, lean_object* v_fallback_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1602_, v_fallback_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___redArg___boxed(lean_object* v_t_1605_, lean_object* v_fallback_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Std_DTreeMap_Raw_Const_maxEntryD___redArg(v_t_1605_, v_fallback_1606_);
lean_dec_ref(v_fallback_1606_);
lean_dec(v_t_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD(lean_object* v_00_u03b1_1608_, lean_object* v_cmp_1609_, lean_object* v_00_u03b2_1610_, lean_object* v_t_1611_, lean_object* v_fallback_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1611_, v_fallback_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___boxed(lean_object* v_00_u03b1_1614_, lean_object* v_cmp_1615_, lean_object* v_00_u03b2_1616_, lean_object* v_t_1617_, lean_object* v_fallback_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Std_DTreeMap_Raw_Const_maxEntryD(v_00_u03b1_1614_, v_cmp_1615_, v_00_u03b2_1616_, v_t_1617_, v_fallback_1618_);
lean_dec_ref(v_fallback_1618_);
lean_dec(v_t_1617_);
lean_dec_ref(v_cmp_1615_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg(lean_object* v_t_1620_, lean_object* v_n_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1620_, v_n_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_1623_, lean_object* v_n_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg(v_t_1623_, v_n_1624_);
lean_dec(v_t_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_1626_, lean_object* v_cmp_1627_, lean_object* v_00_u03b2_1628_, lean_object* v_t_1629_, lean_object* v_n_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1629_, v_n_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1632_, lean_object* v_cmp_1633_, lean_object* v_00_u03b2_1634_, lean_object* v_t_1635_, lean_object* v_n_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f(v_00_u03b1_1632_, v_cmp_1633_, v_00_u03b2_1634_, v_t_1635_, v_n_1636_);
lean_dec(v_t_1635_);
lean_dec_ref(v_cmp_1633_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg(lean_object* v_inst_1638_, lean_object* v_t_1639_, lean_object* v_n_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1638_, v_t_1639_, v_n_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_1642_, lean_object* v_t_1643_, lean_object* v_n_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg(v_inst_1642_, v_t_1643_, v_n_1644_);
lean_dec(v_t_1643_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21(lean_object* v_00_u03b1_1646_, lean_object* v_cmp_1647_, lean_object* v_00_u03b2_1648_, lean_object* v_inst_1649_, lean_object* v_t_1650_, lean_object* v_n_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1649_, v_t_1650_, v_n_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_1653_, lean_object* v_cmp_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_inst_1656_, lean_object* v_t_1657_, lean_object* v_n_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x21(v_00_u03b1_1653_, v_cmp_1654_, v_00_u03b2_1655_, v_inst_1656_, v_t_1657_, v_n_1658_);
lean_dec(v_t_1657_);
lean_dec_ref(v_cmp_1654_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg(lean_object* v_t_1660_, lean_object* v_n_1661_, lean_object* v_fallback_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1660_, v_n_1661_, v_fallback_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_1664_, lean_object* v_n_1665_, lean_object* v_fallback_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg(v_t_1664_, v_n_1665_, v_fallback_1666_);
lean_dec_ref(v_fallback_1666_);
lean_dec(v_t_1664_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD(lean_object* v_00_u03b1_1668_, lean_object* v_cmp_1669_, lean_object* v_00_u03b2_1670_, lean_object* v_t_1671_, lean_object* v_n_1672_, lean_object* v_fallback_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1671_, v_n_1672_, v_fallback_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_1675_, lean_object* v_cmp_1676_, lean_object* v_00_u03b2_1677_, lean_object* v_t_1678_, lean_object* v_n_1679_, lean_object* v_fallback_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Std_DTreeMap_Raw_Const_entryAtIdxD(v_00_u03b1_1675_, v_cmp_1676_, v_00_u03b2_1677_, v_t_1678_, v_n_1679_, v_fallback_1680_);
lean_dec_ref(v_fallback_1680_);
lean_dec(v_t_1678_);
lean_dec_ref(v_cmp_1676_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_1682_, lean_object* v_t_1683_, lean_object* v_k_1684_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = lean_box(0);
v___x_1686_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1682_, v_k_1684_, v___x_1685_, v_t_1683_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x3f(lean_object* v_00_u03b1_1687_, lean_object* v_cmp_1688_, lean_object* v_00_u03b2_1689_, lean_object* v_t_1690_, lean_object* v_k_1691_){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_box(0);
v___x_1693_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1688_, v_k_1691_, v___x_1692_, v_t_1690_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_1694_, lean_object* v_t_1695_, lean_object* v_k_1696_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_box(0);
v___x_1698_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1694_, v_k_1696_, v___x_1697_, v_t_1695_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x3f(lean_object* v_00_u03b1_1699_, lean_object* v_cmp_1700_, lean_object* v_00_u03b2_1701_, lean_object* v_t_1702_, lean_object* v_k_1703_){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_box(0);
v___x_1705_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1700_, v_k_1703_, v___x_1704_, v_t_1702_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_1706_, lean_object* v_t_1707_, lean_object* v_k_1708_){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_box(0);
v___x_1710_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1706_, v_k_1708_, v___x_1709_, v_t_1707_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x3f(lean_object* v_00_u03b1_1711_, lean_object* v_cmp_1712_, lean_object* v_00_u03b2_1713_, lean_object* v_t_1714_, lean_object* v_k_1715_){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_box(0);
v___x_1717_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1712_, v_k_1715_, v___x_1716_, v_t_1714_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_1718_, lean_object* v_t_1719_, lean_object* v_k_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_box(0);
v___x_1722_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1718_, v_k_1720_, v___x_1721_, v_t_1719_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x3f(lean_object* v_00_u03b1_1723_, lean_object* v_cmp_1724_, lean_object* v_00_u03b2_1725_, lean_object* v_t_1726_, lean_object* v_k_1727_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_box(0);
v___x_1729_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1724_, v_k_1727_, v___x_1728_, v_t_1726_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg(lean_object* v_cmp_1730_, lean_object* v_inst_1731_, lean_object* v_t_1732_, lean_object* v_k_1733_){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_box(0);
v___x_1735_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1730_, v_k_1733_, v___x_1734_, v_t_1732_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1737_ = l_panic___redArg(v_inst_1731_, v___x_1736_);
return v___x_1737_;
}
else
{
lean_object* v_val_1738_; 
lean_dec_ref(v_inst_1731_);
v_val_1738_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_val_1738_);
lean_dec_ref(v___x_1735_);
return v_val_1738_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21(lean_object* v_00_u03b1_1739_, lean_object* v_cmp_1740_, lean_object* v_00_u03b2_1741_, lean_object* v_inst_1742_, lean_object* v_t_1743_, lean_object* v_k_1744_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_box(0);
v___x_1746_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1740_, v_k_1744_, v___x_1745_, v_t_1743_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1748_ = l_panic___redArg(v_inst_1742_, v___x_1747_);
return v___x_1748_;
}
else
{
lean_object* v_val_1749_; 
lean_dec_ref(v_inst_1742_);
v_val_1749_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_val_1749_);
lean_dec_ref(v___x_1746_);
return v_val_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg(lean_object* v_cmp_1750_, lean_object* v_inst_1751_, lean_object* v_t_1752_, lean_object* v_k_1753_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_box(0);
v___x_1755_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1750_, v_k_1753_, v___x_1754_, v_t_1752_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1757_ = l_panic___redArg(v_inst_1751_, v___x_1756_);
return v___x_1757_;
}
else
{
lean_object* v_val_1758_; 
lean_dec_ref(v_inst_1751_);
v_val_1758_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_val_1758_);
lean_dec_ref(v___x_1755_);
return v_val_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21(lean_object* v_00_u03b1_1759_, lean_object* v_cmp_1760_, lean_object* v_00_u03b2_1761_, lean_object* v_inst_1762_, lean_object* v_t_1763_, lean_object* v_k_1764_){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_box(0);
v___x_1766_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1760_, v_k_1764_, v___x_1765_, v_t_1763_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1768_ = l_panic___redArg(v_inst_1762_, v___x_1767_);
return v___x_1768_;
}
else
{
lean_object* v_val_1769_; 
lean_dec_ref(v_inst_1762_);
v_val_1769_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_val_1769_);
lean_dec_ref(v___x_1766_);
return v_val_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg(lean_object* v_cmp_1770_, lean_object* v_inst_1771_, lean_object* v_t_1772_, lean_object* v_k_1773_){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_box(0);
v___x_1775_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1770_, v_k_1773_, v___x_1774_, v_t_1772_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1777_ = l_panic___redArg(v_inst_1771_, v___x_1776_);
return v___x_1777_;
}
else
{
lean_object* v_val_1778_; 
lean_dec_ref(v_inst_1771_);
v_val_1778_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_val_1778_);
lean_dec_ref(v___x_1775_);
return v_val_1778_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21(lean_object* v_00_u03b1_1779_, lean_object* v_cmp_1780_, lean_object* v_00_u03b2_1781_, lean_object* v_inst_1782_, lean_object* v_t_1783_, lean_object* v_k_1784_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_box(0);
v___x_1786_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1780_, v_k_1784_, v___x_1785_, v_t_1783_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1788_ = l_panic___redArg(v_inst_1782_, v___x_1787_);
return v___x_1788_;
}
else
{
lean_object* v_val_1789_; 
lean_dec_ref(v_inst_1782_);
v_val_1789_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_val_1789_);
lean_dec_ref(v___x_1786_);
return v_val_1789_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg(lean_object* v_cmp_1790_, lean_object* v_inst_1791_, lean_object* v_t_1792_, lean_object* v_k_1793_){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_box(0);
v___x_1795_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1790_, v_k_1793_, v___x_1794_, v_t_1792_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1797_ = l_panic___redArg(v_inst_1791_, v___x_1796_);
return v___x_1797_;
}
else
{
lean_object* v_val_1798_; 
lean_dec_ref(v_inst_1791_);
v_val_1798_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_val_1798_);
lean_dec_ref(v___x_1795_);
return v_val_1798_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21(lean_object* v_00_u03b1_1799_, lean_object* v_cmp_1800_, lean_object* v_00_u03b2_1801_, lean_object* v_inst_1802_, lean_object* v_t_1803_, lean_object* v_k_1804_){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = lean_box(0);
v___x_1806_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1800_, v_k_1804_, v___x_1805_, v_t_1803_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1808_ = l_panic___redArg(v_inst_1802_, v___x_1807_);
return v___x_1808_;
}
else
{
lean_object* v_val_1809_; 
lean_dec_ref(v_inst_1802_);
v_val_1809_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_val_1809_);
lean_dec_ref(v___x_1806_);
return v_val_1809_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___redArg(lean_object* v_cmp_1810_, lean_object* v_t_1811_, lean_object* v_k_1812_, lean_object* v_fallback_1813_){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = lean_box(0);
v___x_1815_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1810_, v_k_1812_, v___x_1814_, v_t_1811_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_inc_ref(v_fallback_1813_);
return v_fallback_1813_;
}
else
{
lean_object* v_val_1816_; 
v_val_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_val_1816_);
lean_dec_ref(v___x_1815_);
return v_val_1816_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_1817_, lean_object* v_t_1818_, lean_object* v_k_1819_, lean_object* v_fallback_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Std_DTreeMap_Raw_Const_getEntryGED___redArg(v_cmp_1817_, v_t_1818_, v_k_1819_, v_fallback_1820_);
lean_dec_ref(v_fallback_1820_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED(lean_object* v_00_u03b1_1822_, lean_object* v_cmp_1823_, lean_object* v_00_u03b2_1824_, lean_object* v_t_1825_, lean_object* v_k_1826_, lean_object* v_fallback_1827_){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_box(0);
v___x_1829_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1823_, v_k_1826_, v___x_1828_, v_t_1825_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_inc_ref(v_fallback_1827_);
return v_fallback_1827_;
}
else
{
lean_object* v_val_1830_; 
v_val_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_val_1830_);
lean_dec_ref(v___x_1829_);
return v_val_1830_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___boxed(lean_object* v_00_u03b1_1831_, lean_object* v_cmp_1832_, lean_object* v_00_u03b2_1833_, lean_object* v_t_1834_, lean_object* v_k_1835_, lean_object* v_fallback_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Std_DTreeMap_Raw_Const_getEntryGED(v_00_u03b1_1831_, v_cmp_1832_, v_00_u03b2_1833_, v_t_1834_, v_k_1835_, v_fallback_1836_);
lean_dec_ref(v_fallback_1836_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg(lean_object* v_cmp_1838_, lean_object* v_t_1839_, lean_object* v_k_1840_, lean_object* v_fallback_1841_){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = lean_box(0);
v___x_1843_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1838_, v_k_1840_, v___x_1842_, v_t_1839_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_inc_ref(v_fallback_1841_);
return v_fallback_1841_;
}
else
{
lean_object* v_val_1844_; 
v_val_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_val_1844_);
lean_dec_ref(v___x_1843_);
return v_val_1844_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_1845_, lean_object* v_t_1846_, lean_object* v_k_1847_, lean_object* v_fallback_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg(v_cmp_1845_, v_t_1846_, v_k_1847_, v_fallback_1848_);
lean_dec_ref(v_fallback_1848_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD(lean_object* v_00_u03b1_1850_, lean_object* v_cmp_1851_, lean_object* v_00_u03b2_1852_, lean_object* v_t_1853_, lean_object* v_k_1854_, lean_object* v_fallback_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_box(0);
v___x_1857_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1851_, v_k_1854_, v___x_1856_, v_t_1853_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_inc_ref(v_fallback_1855_);
return v_fallback_1855_;
}
else
{
lean_object* v_val_1858_; 
v_val_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_val_1858_);
lean_dec_ref(v___x_1857_);
return v_val_1858_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_1859_, lean_object* v_cmp_1860_, lean_object* v_00_u03b2_1861_, lean_object* v_t_1862_, lean_object* v_k_1863_, lean_object* v_fallback_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Std_DTreeMap_Raw_Const_getEntryGTD(v_00_u03b1_1859_, v_cmp_1860_, v_00_u03b2_1861_, v_t_1862_, v_k_1863_, v_fallback_1864_);
lean_dec_ref(v_fallback_1864_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___redArg(lean_object* v_cmp_1866_, lean_object* v_t_1867_, lean_object* v_k_1868_, lean_object* v_fallback_1869_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_box(0);
v___x_1871_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1866_, v_k_1868_, v___x_1870_, v_t_1867_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_inc_ref(v_fallback_1869_);
return v_fallback_1869_;
}
else
{
lean_object* v_val_1872_; 
v_val_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_val_1872_);
lean_dec_ref(v___x_1871_);
return v_val_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_1873_, lean_object* v_t_1874_, lean_object* v_k_1875_, lean_object* v_fallback_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Std_DTreeMap_Raw_Const_getEntryLED___redArg(v_cmp_1873_, v_t_1874_, v_k_1875_, v_fallback_1876_);
lean_dec_ref(v_fallback_1876_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED(lean_object* v_00_u03b1_1878_, lean_object* v_cmp_1879_, lean_object* v_00_u03b2_1880_, lean_object* v_t_1881_, lean_object* v_k_1882_, lean_object* v_fallback_1883_){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_box(0);
v___x_1885_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1879_, v_k_1882_, v___x_1884_, v_t_1881_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_inc_ref(v_fallback_1883_);
return v_fallback_1883_;
}
else
{
lean_object* v_val_1886_; 
v_val_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_val_1886_);
lean_dec_ref(v___x_1885_);
return v_val_1886_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___boxed(lean_object* v_00_u03b1_1887_, lean_object* v_cmp_1888_, lean_object* v_00_u03b2_1889_, lean_object* v_t_1890_, lean_object* v_k_1891_, lean_object* v_fallback_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Std_DTreeMap_Raw_Const_getEntryLED(v_00_u03b1_1887_, v_cmp_1888_, v_00_u03b2_1889_, v_t_1890_, v_k_1891_, v_fallback_1892_);
lean_dec_ref(v_fallback_1892_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg(lean_object* v_cmp_1894_, lean_object* v_t_1895_, lean_object* v_k_1896_, lean_object* v_fallback_1897_){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_box(0);
v___x_1899_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1894_, v_k_1896_, v___x_1898_, v_t_1895_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_inc_ref(v_fallback_1897_);
return v_fallback_1897_;
}
else
{
lean_object* v_val_1900_; 
v_val_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_val_1900_);
lean_dec_ref(v___x_1899_);
return v_val_1900_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_1901_, lean_object* v_t_1902_, lean_object* v_k_1903_, lean_object* v_fallback_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg(v_cmp_1901_, v_t_1902_, v_k_1903_, v_fallback_1904_);
lean_dec_ref(v_fallback_1904_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD(lean_object* v_00_u03b1_1906_, lean_object* v_cmp_1907_, lean_object* v_00_u03b2_1908_, lean_object* v_t_1909_, lean_object* v_k_1910_, lean_object* v_fallback_1911_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_box(0);
v___x_1913_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1907_, v_k_1910_, v___x_1912_, v_t_1909_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_inc_ref(v_fallback_1911_);
return v_fallback_1911_;
}
else
{
lean_object* v_val_1914_; 
v_val_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_val_1914_);
lean_dec_ref(v___x_1913_);
return v_val_1914_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_1915_, lean_object* v_cmp_1916_, lean_object* v_00_u03b2_1917_, lean_object* v_t_1918_, lean_object* v_k_1919_, lean_object* v_fallback_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Std_DTreeMap_Raw_Const_getEntryLTD(v_00_u03b1_1915_, v_cmp_1916_, v_00_u03b2_1917_, v_t_1918_, v_k_1919_, v_fallback_1920_);
lean_dec_ref(v_fallback_1920_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter___redArg(lean_object* v_f_1922_, lean_object* v_t_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_1922_, v_t_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter(lean_object* v_00_u03b1_1925_, lean_object* v_00_u03b2_1926_, lean_object* v_cmp_1927_, lean_object* v_f_1928_, lean_object* v_t_1929_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_1928_, v_t_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter___boxed(lean_object* v_00_u03b1_1931_, lean_object* v_00_u03b2_1932_, lean_object* v_cmp_1933_, lean_object* v_f_1934_, lean_object* v_t_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Std_DTreeMap_Raw_filter(v_00_u03b1_1931_, v_00_u03b2_1932_, v_cmp_1933_, v_f_1934_, v_t_1935_);
lean_dec_ref(v_cmp_1933_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM___redArg(lean_object* v_inst_1937_, lean_object* v_f_1938_, lean_object* v_init_1939_, lean_object* v_t_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1937_, v_f_1938_, v_init_1939_, v_t_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM(lean_object* v_00_u03b1_1942_, lean_object* v_00_u03b2_1943_, lean_object* v_cmp_1944_, lean_object* v_00_u03b4_1945_, lean_object* v_m_1946_, lean_object* v_inst_1947_, lean_object* v_f_1948_, lean_object* v_init_1949_, lean_object* v_t_1950_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1947_, v_f_1948_, v_init_1949_, v_t_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_00_u03b2_1953_, lean_object* v_cmp_1954_, lean_object* v_00_u03b4_1955_, lean_object* v_m_1956_, lean_object* v_inst_1957_, lean_object* v_f_1958_, lean_object* v_init_1959_, lean_object* v_t_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Std_DTreeMap_Raw_foldlM(v_00_u03b1_1952_, v_00_u03b2_1953_, v_cmp_1954_, v_00_u03b4_1955_, v_m_1956_, v_inst_1957_, v_f_1958_, v_init_1959_, v_t_1960_);
lean_dec_ref(v_cmp_1954_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl___redArg(lean_object* v_f_1962_, lean_object* v_init_1963_, lean_object* v_t_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1962_, v_init_1963_, v_t_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl(lean_object* v_00_u03b1_1966_, lean_object* v_00_u03b2_1967_, lean_object* v_cmp_1968_, lean_object* v_00_u03b4_1969_, lean_object* v_f_1970_, lean_object* v_init_1971_, lean_object* v_t_1972_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1970_, v_init_1971_, v_t_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl___boxed(lean_object* v_00_u03b1_1974_, lean_object* v_00_u03b2_1975_, lean_object* v_cmp_1976_, lean_object* v_00_u03b4_1977_, lean_object* v_f_1978_, lean_object* v_init_1979_, lean_object* v_t_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Std_DTreeMap_Raw_foldl(v_00_u03b1_1974_, v_00_u03b2_1975_, v_cmp_1976_, v_00_u03b4_1977_, v_f_1978_, v_init_1979_, v_t_1980_);
lean_dec_ref(v_cmp_1976_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM___redArg(lean_object* v_inst_1982_, lean_object* v_f_1983_, lean_object* v_init_1984_, lean_object* v_t_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1982_, v_f_1983_, v_init_1984_, v_t_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM(lean_object* v_00_u03b1_1987_, lean_object* v_00_u03b2_1988_, lean_object* v_cmp_1989_, lean_object* v_00_u03b4_1990_, lean_object* v_m_1991_, lean_object* v_inst_1992_, lean_object* v_f_1993_, lean_object* v_init_1994_, lean_object* v_t_1995_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1992_, v_f_1993_, v_init_1994_, v_t_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM___boxed(lean_object* v_00_u03b1_1997_, lean_object* v_00_u03b2_1998_, lean_object* v_cmp_1999_, lean_object* v_00_u03b4_2000_, lean_object* v_m_2001_, lean_object* v_inst_2002_, lean_object* v_f_2003_, lean_object* v_init_2004_, lean_object* v_t_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Std_DTreeMap_Raw_foldrM(v_00_u03b1_1997_, v_00_u03b2_1998_, v_cmp_1999_, v_00_u03b4_2000_, v_m_2001_, v_inst_2002_, v_f_2003_, v_init_2004_, v_t_2005_);
lean_dec_ref(v_cmp_1999_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___redArg___lam__0(lean_object* v_f_2007_, lean_object* v_x1_2008_, lean_object* v_x2_2009_, lean_object* v_x3_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_apply_3(v_f_2007_, v_x1_2008_, v_x2_2009_, v_x3_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___redArg(lean_object* v_f_2031_, lean_object* v_init_2032_, lean_object* v_t_2033_){
_start:
{
lean_object* v___f_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___f_2034_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2034_, 0, v_f_2031_);
v___x_2035_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2036_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2035_, v___f_2034_, v_init_2032_, v_t_2033_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr(lean_object* v_00_u03b1_2037_, lean_object* v_00_u03b2_2038_, lean_object* v_cmp_2039_, lean_object* v_00_u03b4_2040_, lean_object* v_f_2041_, lean_object* v_init_2042_, lean_object* v_t_2043_){
_start:
{
lean_object* v___f_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___f_2044_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2044_, 0, v_f_2041_);
v___x_2045_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2046_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2045_, v___f_2044_, v_init_2042_, v_t_2043_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___boxed(lean_object* v_00_u03b1_2047_, lean_object* v_00_u03b2_2048_, lean_object* v_cmp_2049_, lean_object* v_00_u03b4_2050_, lean_object* v_f_2051_, lean_object* v_init_2052_, lean_object* v_t_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Std_DTreeMap_Raw_foldr(v_00_u03b1_2047_, v_00_u03b2_2048_, v_cmp_2049_, v_00_u03b4_2050_, v_f_2051_, v_init_2052_, v_t_2053_);
lean_dec_ref(v_cmp_2049_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition___redArg___lam__0(lean_object* v_f_2055_, lean_object* v_cmp_2056_, lean_object* v_x_2057_, lean_object* v_a_2058_, lean_object* v_b_2059_){
_start:
{
lean_object* v_fst_2060_; lean_object* v_snd_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2075_; 
v_fst_2060_ = lean_ctor_get(v_x_2057_, 0);
v_snd_2061_ = lean_ctor_get(v_x_2057_, 1);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_x_2057_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2063_ = v_x_2057_;
v_isShared_2064_ = v_isSharedCheck_2075_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_snd_2061_);
lean_inc(v_fst_2060_);
lean_dec(v_x_2057_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2075_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; uint8_t v___x_2066_; 
lean_inc(v_b_2059_);
lean_inc(v_a_2058_);
v___x_2065_ = lean_apply_2(v_f_2055_, v_a_2058_, v_b_2059_);
v___x_2066_ = lean_unbox(v___x_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2056_, v_a_2058_, v_b_2059_, v_snd_2061_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v___x_2067_);
v___x_2069_ = v___x_2063_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_fst_2060_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2056_, v_a_2058_, v_b_2059_, v_fst_2060_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2071_);
v___x_2073_ = v___x_2063_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_snd_2061_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition___redArg(lean_object* v_cmp_2078_, lean_object* v_f_2079_, lean_object* v_t_2080_){
_start:
{
lean_object* v___f_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___f_2081_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2081_, 0, v_f_2079_);
lean_closure_set(v___f_2081_, 1, v_cmp_2078_);
v___x_2082_ = ((lean_object*)(l_Std_DTreeMap_Raw_partition___redArg___closed__0));
v___x_2083_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2081_, v___x_2082_, v_t_2080_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition(lean_object* v_00_u03b1_2084_, lean_object* v_00_u03b2_2085_, lean_object* v_cmp_2086_, lean_object* v_f_2087_, lean_object* v_t_2088_){
_start:
{
lean_object* v___f_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___f_2089_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2089_, 0, v_f_2087_);
lean_closure_set(v___f_2089_, 1, v_cmp_2086_);
v___x_2090_ = ((lean_object*)(l_Std_DTreeMap_Raw_partition___redArg___closed__0));
v___x_2091_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2089_, v___x_2090_, v_t_2088_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___redArg___lam__0(lean_object* v_f_2092_, lean_object* v_x_2093_, lean_object* v_k_2094_, lean_object* v_v_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = lean_apply_2(v_f_2092_, v_k_2094_, v_v_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___redArg(lean_object* v_inst_2097_, lean_object* v_f_2098_, lean_object* v_t_2099_){
_start:
{
lean_object* v___f_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___f_2100_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2100_, 0, v_f_2098_);
v___x_2101_ = lean_box(0);
v___x_2102_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2097_, v___f_2100_, v___x_2101_, v_t_2099_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM(lean_object* v_00_u03b1_2103_, lean_object* v_00_u03b2_2104_, lean_object* v_cmp_2105_, lean_object* v_m_2106_, lean_object* v_inst_2107_, lean_object* v_f_2108_, lean_object* v_t_2109_){
_start:
{
lean_object* v___f_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___f_2110_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2110_, 0, v_f_2108_);
v___x_2111_ = lean_box(0);
v___x_2112_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2107_, v___f_2110_, v___x_2111_, v_t_2109_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_00_u03b2_2114_, lean_object* v_cmp_2115_, lean_object* v_m_2116_, lean_object* v_inst_2117_, lean_object* v_f_2118_, lean_object* v_t_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Std_DTreeMap_Raw_forM(v_00_u03b1_2113_, v_00_u03b2_2114_, v_cmp_2115_, v_m_2116_, v_inst_2117_, v_f_2118_, v_t_2119_);
lean_dec_ref(v_cmp_2115_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___redArg___lam__0(lean_object* v_toPure_2121_, lean_object* v_____do__lift_2122_){
_start:
{
lean_object* v_a_2123_; lean_object* v___x_2124_; 
v_a_2123_ = lean_ctor_get(v_____do__lift_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref(v_____do__lift_2122_);
v___x_2124_ = lean_apply_2(v_toPure_2121_, lean_box(0), v_a_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___redArg(lean_object* v_inst_2125_, lean_object* v_f_2126_, lean_object* v_init_2127_, lean_object* v_t_2128_){
_start:
{
lean_object* v_toApplicative_2129_; lean_object* v_toBind_2130_; lean_object* v_toPure_2131_; lean_object* v___x_2132_; lean_object* v___f_2133_; lean_object* v___x_2134_; 
v_toApplicative_2129_ = lean_ctor_get(v_inst_2125_, 0);
v_toBind_2130_ = lean_ctor_get(v_inst_2125_, 1);
lean_inc(v_toBind_2130_);
v_toPure_2131_ = lean_ctor_get(v_toApplicative_2129_, 1);
lean_inc(v_toPure_2131_);
v___x_2132_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2125_, v_f_2126_, v_init_2127_, v_t_2128_);
v___f_2133_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2133_, 0, v_toPure_2131_);
v___x_2134_ = lean_apply_4(v_toBind_2130_, lean_box(0), lean_box(0), v___x_2132_, v___f_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn(lean_object* v_00_u03b1_2135_, lean_object* v_00_u03b2_2136_, lean_object* v_cmp_2137_, lean_object* v_00_u03b4_2138_, lean_object* v_m_2139_, lean_object* v_inst_2140_, lean_object* v_f_2141_, lean_object* v_init_2142_, lean_object* v_t_2143_){
_start:
{
lean_object* v_toApplicative_2144_; lean_object* v_toBind_2145_; lean_object* v_toPure_2146_; lean_object* v___x_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; 
v_toApplicative_2144_ = lean_ctor_get(v_inst_2140_, 0);
v_toBind_2145_ = lean_ctor_get(v_inst_2140_, 1);
lean_inc(v_toBind_2145_);
v_toPure_2146_ = lean_ctor_get(v_toApplicative_2144_, 1);
lean_inc(v_toPure_2146_);
v___x_2147_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2140_, v_f_2141_, v_init_2142_, v_t_2143_);
v___f_2148_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2148_, 0, v_toPure_2146_);
v___x_2149_ = lean_apply_4(v_toBind_2145_, lean_box(0), lean_box(0), v___x_2147_, v___f_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___boxed(lean_object* v_00_u03b1_2150_, lean_object* v_00_u03b2_2151_, lean_object* v_cmp_2152_, lean_object* v_00_u03b4_2153_, lean_object* v_m_2154_, lean_object* v_inst_2155_, lean_object* v_f_2156_, lean_object* v_init_2157_, lean_object* v_t_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Std_DTreeMap_Raw_forIn(v_00_u03b1_2150_, v_00_u03b2_2151_, v_cmp_2152_, v_00_u03b4_2153_, v_m_2154_, v_inst_2155_, v_f_2156_, v_init_2157_, v_t_2158_);
lean_dec_ref(v_cmp_2152_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_2160_, lean_object* v_x_2161_, lean_object* v_k_2162_, lean_object* v_v_2163_){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v_k_2162_);
lean_ctor_set(v___x_2164_, 1, v_v_2163_);
v___x_2165_ = lean_apply_1(v_f_2160_, v___x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1(lean_object* v_inst_2166_, lean_object* v_t_2167_, lean_object* v_f_2168_){
_start:
{
lean_object* v___f_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___f_2169_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2169_, 0, v_f_2168_);
v___x_2170_ = lean_box(0);
v___x_2171_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2166_, v___f_2169_, v___x_2170_, v_t_2167_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg(lean_object* v_inst_2172_){
_start:
{
lean_object* v___f_2173_; 
v___f_2173_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2173_, 0, v_inst_2172_);
return v___f_2173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad(lean_object* v_00_u03b1_2174_, lean_object* v_00_u03b2_2175_, lean_object* v_cmp_2176_, lean_object* v_m_2177_, lean_object* v_inst_2178_){
_start:
{
lean_object* v___f_2179_; 
v___f_2179_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2179_, 0, v_inst_2178_);
return v___f_2179_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___boxed(lean_object* v_00_u03b1_2180_, lean_object* v_00_u03b2_2181_, lean_object* v_cmp_2182_, lean_object* v_m_2183_, lean_object* v_inst_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Std_DTreeMap_Raw_instForMSigmaOfMonad(v_00_u03b1_2180_, v_00_u03b2_2181_, v_cmp_2182_, v_m_2183_, v_inst_2184_);
lean_dec_ref(v_cmp_2182_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_2186_, lean_object* v_a_2187_, lean_object* v_b_2188_, lean_object* v_acc_2189_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v_a_2187_);
lean_ctor_set(v___x_2190_, 1, v_b_2188_);
v___x_2191_ = lean_apply_2(v_f_2186_, v___x_2190_, v_acc_2189_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_2192_, lean_object* v_00_u03b2_2193_, lean_object* v_t_2194_, lean_object* v_init_2195_, lean_object* v_f_2196_){
_start:
{
lean_object* v_toApplicative_2197_; lean_object* v_toBind_2198_; lean_object* v_toPure_2199_; lean_object* v___f_2200_; lean_object* v___x_2201_; lean_object* v___f_2202_; lean_object* v___x_2203_; 
v_toApplicative_2197_ = lean_ctor_get(v_inst_2192_, 0);
v_toBind_2198_ = lean_ctor_get(v_inst_2192_, 1);
lean_inc(v_toBind_2198_);
v_toPure_2199_ = lean_ctor_get(v_toApplicative_2197_, 1);
lean_inc(v_toPure_2199_);
v___f_2200_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2200_, 0, v_f_2196_);
v___x_2201_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2192_, v___f_2200_, v_init_2195_, v_t_2194_);
v___f_2202_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2202_, 0, v_toPure_2199_);
v___x_2203_ = lean_apply_4(v_toBind_2198_, lean_box(0), lean_box(0), v___x_2201_, v___f_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg(lean_object* v_inst_2204_){
_start:
{
lean_object* v___f_2205_; 
v___f_2205_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2205_, 0, v_inst_2204_);
return v___f_2205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad(lean_object* v_00_u03b1_2206_, lean_object* v_00_u03b2_2207_, lean_object* v_cmp_2208_, lean_object* v_m_2209_, lean_object* v_inst_2210_){
_start:
{
lean_object* v___f_2211_; 
v___f_2211_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2211_, 0, v_inst_2210_);
return v___f_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___boxed(lean_object* v_00_u03b1_2212_, lean_object* v_00_u03b2_2213_, lean_object* v_cmp_2214_, lean_object* v_m_2215_, lean_object* v_inst_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Std_DTreeMap_Raw_instForInSigmaOfMonad(v_00_u03b1_2212_, v_00_u03b2_2213_, v_cmp_2214_, v_m_2215_, v_inst_2216_);
lean_dec_ref(v_cmp_2214_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2218_, lean_object* v_x_2219_, lean_object* v_k_2220_, lean_object* v_v_2221_){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_k_2220_);
lean_ctor_set(v___x_2222_, 1, v_v_2221_);
v___x_2223_ = lean_apply_1(v_f_2218_, v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___redArg(lean_object* v_inst_2224_, lean_object* v_f_2225_, lean_object* v_t_2226_){
_start:
{
lean_object* v___f_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___f_2227_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2227_, 0, v_f_2225_);
v___x_2228_ = lean_box(0);
v___x_2229_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2224_, v___f_2227_, v___x_2228_, v_t_2226_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried(lean_object* v_00_u03b1_2230_, lean_object* v_cmp_2231_, lean_object* v_m_2232_, lean_object* v_inst_2233_, lean_object* v_00_u03b2_2234_, lean_object* v_f_2235_, lean_object* v_t_2236_){
_start:
{
lean_object* v___f_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___f_2237_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2237_, 0, v_f_2235_);
v___x_2238_ = lean_box(0);
v___x_2239_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2233_, v___f_2237_, v___x_2238_, v_t_2236_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2240_, lean_object* v_cmp_2241_, lean_object* v_m_2242_, lean_object* v_inst_2243_, lean_object* v_00_u03b2_2244_, lean_object* v_f_2245_, lean_object* v_t_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Std_DTreeMap_Raw_Const_forMUncurried(v_00_u03b1_2240_, v_cmp_2241_, v_m_2242_, v_inst_2243_, v_00_u03b2_2244_, v_f_2245_, v_t_2246_);
lean_dec_ref(v_cmp_2241_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2248_, lean_object* v_a_2249_, lean_object* v_b_2250_, lean_object* v_d_2251_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v_a_2249_);
lean_ctor_set(v___x_2252_, 1, v_b_2250_);
v___x_2253_ = lean_apply_2(v_f_2248_, v___x_2252_, v_d_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___redArg(lean_object* v_inst_2254_, lean_object* v_f_2255_, lean_object* v_init_2256_, lean_object* v_t_2257_){
_start:
{
lean_object* v_toApplicative_2258_; lean_object* v_toBind_2259_; lean_object* v_toPure_2260_; lean_object* v___f_2261_; lean_object* v___x_2262_; lean_object* v___f_2263_; lean_object* v___x_2264_; 
v_toApplicative_2258_ = lean_ctor_get(v_inst_2254_, 0);
v_toBind_2259_ = lean_ctor_get(v_inst_2254_, 1);
lean_inc(v_toBind_2259_);
v_toPure_2260_ = lean_ctor_get(v_toApplicative_2258_, 1);
lean_inc(v_toPure_2260_);
v___f_2261_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2261_, 0, v_f_2255_);
v___x_2262_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2254_, v___f_2261_, v_init_2256_, v_t_2257_);
v___f_2263_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2263_, 0, v_toPure_2260_);
v___x_2264_ = lean_apply_4(v_toBind_2259_, lean_box(0), lean_box(0), v___x_2262_, v___f_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried(lean_object* v_00_u03b1_2265_, lean_object* v_cmp_2266_, lean_object* v_00_u03b4_2267_, lean_object* v_m_2268_, lean_object* v_inst_2269_, lean_object* v_00_u03b2_2270_, lean_object* v_f_2271_, lean_object* v_init_2272_, lean_object* v_t_2273_){
_start:
{
lean_object* v_toApplicative_2274_; lean_object* v_toBind_2275_; lean_object* v_toPure_2276_; lean_object* v___f_2277_; lean_object* v___x_2278_; lean_object* v___f_2279_; lean_object* v___x_2280_; 
v_toApplicative_2274_ = lean_ctor_get(v_inst_2269_, 0);
v_toBind_2275_ = lean_ctor_get(v_inst_2269_, 1);
lean_inc(v_toBind_2275_);
v_toPure_2276_ = lean_ctor_get(v_toApplicative_2274_, 1);
lean_inc(v_toPure_2276_);
v___f_2277_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2277_, 0, v_f_2271_);
v___x_2278_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2269_, v___f_2277_, v_init_2272_, v_t_2273_);
v___f_2279_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2279_, 0, v_toPure_2276_);
v___x_2280_ = lean_apply_4(v_toBind_2275_, lean_box(0), lean_box(0), v___x_2278_, v___f_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2281_, lean_object* v_cmp_2282_, lean_object* v_00_u03b4_2283_, lean_object* v_m_2284_, lean_object* v_inst_2285_, lean_object* v_00_u03b2_2286_, lean_object* v_f_2287_, lean_object* v_init_2288_, lean_object* v_t_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Std_DTreeMap_Raw_Const_forInUncurried(v_00_u03b1_2281_, v_cmp_2282_, v_00_u03b4_2283_, v_m_2284_, v_inst_2285_, v_00_u03b2_2286_, v_f_2287_, v_init_2288_, v_t_2289_);
lean_dec_ref(v_cmp_2282_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___lam__0(lean_object* v_p_2291_, lean_object* v___x_2292_, lean_object* v___x_2293_, lean_object* v_a_2294_, lean_object* v_b_2295_, lean_object* v_acc_2296_){
_start:
{
lean_object* v___x_2297_; uint8_t v___x_2298_; 
v___x_2297_ = lean_apply_2(v_p_2291_, v_a_2294_, v_b_2295_);
v___x_2298_ = lean_unbox(v___x_2297_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2292_);
return v___x_2299_;
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_dec_ref(v___x_2292_);
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2297_);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v___x_2293_);
v___x_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_2303_, lean_object* v___x_2304_, lean_object* v___x_2305_, lean_object* v_a_2306_, lean_object* v_b_2307_, lean_object* v_acc_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Std_DTreeMap_Raw_any___redArg___lam__0(v_p_2303_, v___x_2304_, v___x_2305_, v_a_2306_, v_b_2307_, v_acc_2308_);
lean_dec_ref(v_acc_2308_);
return v_res_2309_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_any___redArg(lean_object* v_t_2313_, lean_object* v_p_2314_){
_start:
{
lean_object* v___y_2316_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___f_2324_; lean_object* v___x_2325_; lean_object* v_a_2326_; 
v___x_2321_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2322_ = lean_box(0);
v___x_2323_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2324_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2324_, 0, v_p_2314_);
lean_closure_set(v___f_2324_, 1, v___x_2323_);
lean_closure_set(v___f_2324_, 2, v___x_2322_);
v___x_2325_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2321_, v___f_2324_, v___x_2323_, v_t_2313_);
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___y_2316_ = v_a_2326_;
goto v___jp_2315_;
v___jp_2315_:
{
lean_object* v_fst_2317_; 
v_fst_2317_ = lean_ctor_get(v___y_2316_, 0);
lean_inc(v_fst_2317_);
lean_dec_ref(v___y_2316_);
if (lean_obj_tag(v_fst_2317_) == 0)
{
uint8_t v___x_2318_; 
v___x_2318_ = 0;
return v___x_2318_;
}
else
{
lean_object* v_val_2319_; uint8_t v___x_2320_; 
v_val_2319_ = lean_ctor_get(v_fst_2317_, 0);
lean_inc(v_val_2319_);
lean_dec_ref(v_fst_2317_);
v___x_2320_ = lean_unbox(v_val_2319_);
lean_dec(v_val_2319_);
return v___x_2320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___boxed(lean_object* v_t_2327_, lean_object* v_p_2328_){
_start:
{
uint8_t v_res_2329_; lean_object* v_r_2330_; 
v_res_2329_ = l_Std_DTreeMap_Raw_any___redArg(v_t_2327_, v_p_2328_);
v_r_2330_ = lean_box(v_res_2329_);
return v_r_2330_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_any(lean_object* v_00_u03b1_2331_, lean_object* v_00_u03b2_2332_, lean_object* v_cmp_2333_, lean_object* v_t_2334_, lean_object* v_p_2335_){
_start:
{
lean_object* v___y_2337_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___f_2345_; lean_object* v___x_2346_; lean_object* v_a_2347_; 
v___x_2342_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2343_ = lean_box(0);
v___x_2344_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2345_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2345_, 0, v_p_2335_);
lean_closure_set(v___f_2345_, 1, v___x_2344_);
lean_closure_set(v___f_2345_, 2, v___x_2343_);
v___x_2346_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2342_, v___f_2345_, v___x_2344_, v_t_2334_);
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___y_2337_ = v_a_2347_;
goto v___jp_2336_;
v___jp_2336_:
{
lean_object* v_fst_2338_; 
v_fst_2338_ = lean_ctor_get(v___y_2337_, 0);
lean_inc(v_fst_2338_);
lean_dec_ref(v___y_2337_);
if (lean_obj_tag(v_fst_2338_) == 0)
{
uint8_t v___x_2339_; 
v___x_2339_ = 0;
return v___x_2339_;
}
else
{
lean_object* v_val_2340_; uint8_t v___x_2341_; 
v_val_2340_ = lean_ctor_get(v_fst_2338_, 0);
lean_inc(v_val_2340_);
lean_dec_ref(v_fst_2338_);
v___x_2341_ = lean_unbox(v_val_2340_);
lean_dec(v_val_2340_);
return v___x_2341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___boxed(lean_object* v_00_u03b1_2348_, lean_object* v_00_u03b2_2349_, lean_object* v_cmp_2350_, lean_object* v_t_2351_, lean_object* v_p_2352_){
_start:
{
uint8_t v_res_2353_; lean_object* v_r_2354_; 
v_res_2353_ = l_Std_DTreeMap_Raw_any(v_00_u03b1_2348_, v_00_u03b2_2349_, v_cmp_2350_, v_t_2351_, v_p_2352_);
lean_dec_ref(v_cmp_2350_);
v_r_2354_ = lean_box(v_res_2353_);
return v_r_2354_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___lam__0(lean_object* v_p_2355_, lean_object* v___x_2356_, lean_object* v___x_2357_, lean_object* v_a_2358_, lean_object* v_b_2359_, lean_object* v_acc_2360_){
_start:
{
lean_object* v___x_2361_; uint8_t v___x_2362_; 
v___x_2361_ = lean_apply_2(v_p_2355_, v_a_2358_, v_b_2359_);
v___x_2362_ = lean_unbox(v___x_2361_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_dec_ref(v___x_2357_);
v___x_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
v___x_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
lean_ctor_set(v___x_2364_, 1, v___x_2356_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
else
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2357_);
return v___x_2366_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_2367_, lean_object* v___x_2368_, lean_object* v___x_2369_, lean_object* v_a_2370_, lean_object* v_b_2371_, lean_object* v_acc_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Std_DTreeMap_Raw_all___redArg___lam__0(v_p_2367_, v___x_2368_, v___x_2369_, v_a_2370_, v_b_2371_, v_acc_2372_);
lean_dec_ref(v_acc_2372_);
return v_res_2373_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_all___redArg(lean_object* v_t_2374_, lean_object* v_p_2375_){
_start:
{
lean_object* v___y_2377_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___f_2385_; lean_object* v___x_2386_; lean_object* v_a_2387_; 
v___x_2382_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2383_ = lean_box(0);
v___x_2384_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2385_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2385_, 0, v_p_2375_);
lean_closure_set(v___f_2385_, 1, v___x_2383_);
lean_closure_set(v___f_2385_, 2, v___x_2384_);
v___x_2386_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2382_, v___f_2385_, v___x_2384_, v_t_2374_);
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___y_2377_ = v_a_2387_;
goto v___jp_2376_;
v___jp_2376_:
{
lean_object* v_fst_2378_; 
v_fst_2378_ = lean_ctor_get(v___y_2377_, 0);
lean_inc(v_fst_2378_);
lean_dec_ref(v___y_2377_);
if (lean_obj_tag(v_fst_2378_) == 0)
{
uint8_t v___x_2379_; 
v___x_2379_ = 1;
return v___x_2379_;
}
else
{
lean_object* v_val_2380_; uint8_t v___x_2381_; 
v_val_2380_ = lean_ctor_get(v_fst_2378_, 0);
lean_inc(v_val_2380_);
lean_dec_ref(v_fst_2378_);
v___x_2381_ = lean_unbox(v_val_2380_);
lean_dec(v_val_2380_);
return v___x_2381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___boxed(lean_object* v_t_2388_, lean_object* v_p_2389_){
_start:
{
uint8_t v_res_2390_; lean_object* v_r_2391_; 
v_res_2390_ = l_Std_DTreeMap_Raw_all___redArg(v_t_2388_, v_p_2389_);
v_r_2391_ = lean_box(v_res_2390_);
return v_r_2391_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_all(lean_object* v_00_u03b1_2392_, lean_object* v_00_u03b2_2393_, lean_object* v_cmp_2394_, lean_object* v_t_2395_, lean_object* v_p_2396_){
_start:
{
lean_object* v___y_2398_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___f_2406_; lean_object* v___x_2407_; lean_object* v_a_2408_; 
v___x_2403_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2404_ = lean_box(0);
v___x_2405_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2406_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2406_, 0, v_p_2396_);
lean_closure_set(v___f_2406_, 1, v___x_2404_);
lean_closure_set(v___f_2406_, 2, v___x_2405_);
v___x_2407_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2403_, v___f_2406_, v___x_2405_, v_t_2395_);
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___y_2398_ = v_a_2408_;
goto v___jp_2397_;
v___jp_2397_:
{
lean_object* v_fst_2399_; 
v_fst_2399_ = lean_ctor_get(v___y_2398_, 0);
lean_inc(v_fst_2399_);
lean_dec_ref(v___y_2398_);
if (lean_obj_tag(v_fst_2399_) == 0)
{
uint8_t v___x_2400_; 
v___x_2400_ = 1;
return v___x_2400_;
}
else
{
lean_object* v_val_2401_; uint8_t v___x_2402_; 
v_val_2401_ = lean_ctor_get(v_fst_2399_, 0);
lean_inc(v_val_2401_);
lean_dec_ref(v_fst_2399_);
v___x_2402_ = lean_unbox(v_val_2401_);
lean_dec(v_val_2401_);
return v___x_2402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___boxed(lean_object* v_00_u03b1_2409_, lean_object* v_00_u03b2_2410_, lean_object* v_cmp_2411_, lean_object* v_t_2412_, lean_object* v_p_2413_){
_start:
{
uint8_t v_res_2414_; lean_object* v_r_2415_; 
v_res_2414_ = l_Std_DTreeMap_Raw_all(v_00_u03b1_2409_, v_00_u03b2_2410_, v_cmp_2411_, v_t_2412_, v_p_2413_);
lean_dec_ref(v_cmp_2411_);
v_r_2415_ = lean_box(v_res_2414_);
return v_r_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg___lam__0(lean_object* v_x1_2416_, lean_object* v_x2_2417_, lean_object* v_x3_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2419_, 0, v_x1_2416_);
lean_ctor_set(v___x_2419_, 1, v_x3_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_x1_2420_, lean_object* v_x2_2421_, lean_object* v_x3_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Std_DTreeMap_Raw_keys___redArg___lam__0(v_x1_2420_, v_x2_2421_, v_x3_2422_);
lean_dec(v_x2_2421_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg(lean_object* v_t_2425_){
_start:
{
lean_object* v___f_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___f_2426_ = ((lean_object*)(l_Std_DTreeMap_Raw_keys___redArg___closed__0));
v___x_2427_ = lean_box(0);
v___x_2428_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2429_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2428_, v___f_2426_, v___x_2427_, v_t_2425_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys(lean_object* v_00_u03b1_2430_, lean_object* v_00_u03b2_2431_, lean_object* v_cmp_2432_, lean_object* v_t_2433_){
_start:
{
lean_object* v___f_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___f_2434_ = ((lean_object*)(l_Std_DTreeMap_Raw_keys___redArg___closed__0));
v___x_2435_ = lean_box(0);
v___x_2436_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2437_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2436_, v___f_2434_, v___x_2435_, v_t_2433_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___boxed(lean_object* v_00_u03b1_2438_, lean_object* v_00_u03b2_2439_, lean_object* v_cmp_2440_, lean_object* v_t_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Std_DTreeMap_Raw_keys(v_00_u03b1_2438_, v_00_u03b2_2439_, v_cmp_2440_, v_t_2441_);
lean_dec_ref(v_cmp_2440_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___lam__0(lean_object* v_l_2443_, lean_object* v_k_2444_, lean_object* v_x_2445_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_array_push(v_l_2443_, v_k_2444_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_l_2447_, lean_object* v_k_2448_, lean_object* v_x_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Std_DTreeMap_Raw_keysArray___redArg___lam__0(v_l_2447_, v_k_2448_, v_x_2449_);
lean_dec(v_x_2449_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg(lean_object* v_t_2452_){
_start:
{
lean_object* v___f_2453_; lean_object* v___y_2455_; 
v___f_2453_ = ((lean_object*)(l_Std_DTreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2452_) == 0)
{
lean_object* v_size_2458_; 
v_size_2458_ = lean_ctor_get(v_t_2452_, 0);
lean_inc(v_size_2458_);
v___y_2455_ = v_size_2458_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_unsigned_to_nat(0u);
v___y_2455_ = v___x_2459_;
goto v___jp_2454_;
}
v___jp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = lean_mk_empty_array_with_capacity(v___y_2455_);
lean_dec(v___y_2455_);
v___x_2457_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2453_, v___x_2456_, v_t_2452_);
return v___x_2457_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray(lean_object* v_00_u03b1_2460_, lean_object* v_00_u03b2_2461_, lean_object* v_cmp_2462_, lean_object* v_t_2463_){
_start:
{
lean_object* v___f_2464_; lean_object* v___y_2466_; 
v___f_2464_ = ((lean_object*)(l_Std_DTreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2463_) == 0)
{
lean_object* v_size_2469_; 
v_size_2469_ = lean_ctor_get(v_t_2463_, 0);
lean_inc(v_size_2469_);
v___y_2466_ = v_size_2469_;
goto v___jp_2465_;
}
else
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_unsigned_to_nat(0u);
v___y_2466_ = v___x_2470_;
goto v___jp_2465_;
}
v___jp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_mk_empty_array_with_capacity(v___y_2466_);
lean_dec(v___y_2466_);
v___x_2468_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2464_, v___x_2467_, v_t_2463_);
return v___x_2468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___boxed(lean_object* v_00_u03b1_2471_, lean_object* v_00_u03b2_2472_, lean_object* v_cmp_2473_, lean_object* v_t_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Std_DTreeMap_Raw_keysArray(v_00_u03b1_2471_, v_00_u03b2_2472_, v_cmp_2473_, v_t_2474_);
lean_dec_ref(v_cmp_2473_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg___lam__0(lean_object* v_x1_2476_, lean_object* v_x2_2477_, lean_object* v_x3_2478_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2479_, 0, v_x2_2477_);
lean_ctor_set(v___x_2479_, 1, v_x3_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg___lam__0___boxed(lean_object* v_x1_2480_, lean_object* v_x2_2481_, lean_object* v_x3_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Std_DTreeMap_Raw_values___redArg___lam__0(v_x1_2480_, v_x2_2481_, v_x3_2482_);
lean_dec(v_x1_2480_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg(lean_object* v_t_2485_){
_start:
{
lean_object* v___f_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___f_2486_ = ((lean_object*)(l_Std_DTreeMap_Raw_values___redArg___closed__0));
v___x_2487_ = lean_box(0);
v___x_2488_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2489_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2488_, v___f_2486_, v___x_2487_, v_t_2485_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values(lean_object* v_00_u03b1_2490_, lean_object* v_cmp_2491_, lean_object* v_00_u03b2_2492_, lean_object* v_t_2493_){
_start:
{
lean_object* v___f_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___f_2494_ = ((lean_object*)(l_Std_DTreeMap_Raw_values___redArg___closed__0));
v___x_2495_ = lean_box(0);
v___x_2496_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2497_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2496_, v___f_2494_, v___x_2495_, v_t_2493_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___boxed(lean_object* v_00_u03b1_2498_, lean_object* v_cmp_2499_, lean_object* v_00_u03b2_2500_, lean_object* v_t_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Std_DTreeMap_Raw_values(v_00_u03b1_2498_, v_cmp_2499_, v_00_u03b2_2500_, v_t_2501_);
lean_dec_ref(v_cmp_2499_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0(lean_object* v_l_2503_, lean_object* v_x_2504_, lean_object* v_v_2505_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_array_push(v_l_2503_, v_v_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2507_, lean_object* v_x_2508_, lean_object* v_v_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0(v_l_2507_, v_x_2508_, v_v_2509_);
lean_dec(v_x_2508_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg(lean_object* v_t_2512_){
_start:
{
lean_object* v___f_2513_; lean_object* v___y_2515_; 
v___f_2513_ = ((lean_object*)(l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2512_) == 0)
{
lean_object* v_size_2518_; 
v_size_2518_ = lean_ctor_get(v_t_2512_, 0);
lean_inc(v_size_2518_);
v___y_2515_ = v_size_2518_;
goto v___jp_2514_;
}
else
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_unsigned_to_nat(0u);
v___y_2515_ = v___x_2519_;
goto v___jp_2514_;
}
v___jp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_mk_empty_array_with_capacity(v___y_2515_);
lean_dec(v___y_2515_);
v___x_2517_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2513_, v___x_2516_, v_t_2512_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray(lean_object* v_00_u03b1_2520_, lean_object* v_cmp_2521_, lean_object* v_00_u03b2_2522_, lean_object* v_t_2523_){
_start:
{
lean_object* v___f_2524_; lean_object* v___y_2526_; 
v___f_2524_ = ((lean_object*)(l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2523_) == 0)
{
lean_object* v_size_2529_; 
v_size_2529_ = lean_ctor_get(v_t_2523_, 0);
lean_inc(v_size_2529_);
v___y_2526_ = v_size_2529_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_unsigned_to_nat(0u);
v___y_2526_ = v___x_2530_;
goto v___jp_2525_;
}
v___jp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = lean_mk_empty_array_with_capacity(v___y_2526_);
lean_dec(v___y_2526_);
v___x_2528_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2524_, v___x_2527_, v_t_2523_);
return v___x_2528_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___boxed(lean_object* v_00_u03b1_2531_, lean_object* v_cmp_2532_, lean_object* v_00_u03b2_2533_, lean_object* v_t_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Std_DTreeMap_Raw_valuesArray(v_00_u03b1_2531_, v_cmp_2532_, v_00_u03b2_2533_, v_t_2534_);
lean_dec_ref(v_cmp_2532_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___redArg___lam__0(lean_object* v_x1_2536_, lean_object* v_x2_2537_, lean_object* v_x3_2538_){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v_x1_2536_);
lean_ctor_set(v___x_2539_, 1, v_x2_2537_);
v___x_2540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
lean_ctor_set(v___x_2540_, 1, v_x3_2538_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___redArg(lean_object* v_t_2542_){
_start:
{
lean_object* v___f_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___f_2543_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_2544_ = lean_box(0);
v___x_2545_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2546_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2545_, v___f_2543_, v___x_2544_, v_t_2542_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList(lean_object* v_00_u03b1_2547_, lean_object* v_00_u03b2_2548_, lean_object* v_cmp_2549_, lean_object* v_t_2550_){
_start:
{
lean_object* v___f_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___f_2551_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_2552_ = lean_box(0);
v___x_2553_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2554_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2553_, v___f_2551_, v___x_2552_, v_t_2550_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___boxed(lean_object* v_00_u03b1_2555_, lean_object* v_00_u03b2_2556_, lean_object* v_cmp_2557_, lean_object* v_t_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Std_DTreeMap_Raw_toList(v_00_u03b1_2555_, v_00_u03b2_2556_, v_cmp_2557_, v_t_2558_);
lean_dec_ref(v_cmp_2557_);
return v_res_2559_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg___lam__0(lean_object* v_cmp_2561_, lean_object* v_a_2562_, lean_object* v_x_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_fst_2565_; lean_object* v_snd_2566_; lean_object* v_r_2567_; lean_object* v___x_2568_; 
v_fst_2565_ = lean_ctor_get(v_a_2562_, 0);
lean_inc(v_fst_2565_);
v_snd_2566_ = lean_ctor_get(v_a_2562_, 1);
lean_inc(v_snd_2566_);
lean_dec_ref(v_a_2562_);
v_r_2567_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2561_, v_fst_2565_, v_snd_2566_, v___y_2564_);
v___x_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_r_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg(lean_object* v_l_2569_, lean_object* v_cmp_2570_){
_start:
{
lean_object* v___f_2571_; lean_object* v___x_2572_; lean_object* v_r_2573_; lean_object* v___x_2574_; 
v___f_2571_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2571_, 0, v_cmp_2570_);
v___x_2572_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2573_ = lean_box(1);
v___x_2574_ = l_List_forIn_x27_loop___redArg(v___x_2572_, v___f_2571_, v_l_2569_, v_r_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList(lean_object* v_00_u03b1_2575_, lean_object* v_00_u03b2_2576_, lean_object* v_l_2577_, lean_object* v_cmp_2578_){
_start:
{
lean_object* v___f_2579_; lean_object* v___x_2580_; lean_object* v_r_2581_; lean_object* v___x_2582_; 
v___f_2579_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2579_, 0, v_cmp_2578_);
v___x_2580_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2581_ = lean_box(1);
v___x_2582_ = l_List_forIn_x27_loop___redArg(v___x_2580_, v___f_2579_, v_l_2577_, v_r_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg___lam__0(lean_object* v_l_2583_, lean_object* v_k_2584_, lean_object* v_v_2585_){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v_k_2584_);
lean_ctor_set(v___x_2586_, 1, v_v_2585_);
v___x_2587_ = lean_array_push(v_l_2583_, v___x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg(lean_object* v_t_2589_){
_start:
{
lean_object* v___f_2590_; lean_object* v___y_2592_; 
v___f_2590_ = ((lean_object*)(l_Std_DTreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2589_) == 0)
{
lean_object* v_size_2595_; 
v_size_2595_ = lean_ctor_get(v_t_2589_, 0);
lean_inc(v_size_2595_);
v___y_2592_ = v_size_2595_;
goto v___jp_2591_;
}
else
{
lean_object* v___x_2596_; 
v___x_2596_ = lean_unsigned_to_nat(0u);
v___y_2592_ = v___x_2596_;
goto v___jp_2591_;
}
v___jp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_mk_empty_array_with_capacity(v___y_2592_);
lean_dec(v___y_2592_);
v___x_2594_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2590_, v___x_2593_, v_t_2589_);
return v___x_2594_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray(lean_object* v_00_u03b1_2597_, lean_object* v_00_u03b2_2598_, lean_object* v_cmp_2599_, lean_object* v_t_2600_){
_start:
{
lean_object* v___f_2601_; lean_object* v___y_2603_; 
v___f_2601_ = ((lean_object*)(l_Std_DTreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2600_) == 0)
{
lean_object* v_size_2606_; 
v_size_2606_ = lean_ctor_get(v_t_2600_, 0);
lean_inc(v_size_2606_);
v___y_2603_ = v_size_2606_;
goto v___jp_2602_;
}
else
{
lean_object* v___x_2607_; 
v___x_2607_ = lean_unsigned_to_nat(0u);
v___y_2603_ = v___x_2607_;
goto v___jp_2602_;
}
v___jp_2602_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_mk_empty_array_with_capacity(v___y_2603_);
lean_dec(v___y_2603_);
v___x_2605_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2601_, v___x_2604_, v_t_2600_);
return v___x_2605_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___boxed(lean_object* v_00_u03b1_2608_, lean_object* v_00_u03b2_2609_, lean_object* v_cmp_2610_, lean_object* v_t_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Std_DTreeMap_Raw_toArray(v_00_u03b1_2608_, v_00_u03b2_2609_, v_cmp_2610_, v_t_2611_);
lean_dec_ref(v_cmp_2610_);
return v_res_2612_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray___redArg(lean_object* v_a_2614_, lean_object* v_cmp_2615_){
_start:
{
lean_object* v___f_2616_; lean_object* v___x_2617_; lean_object* v_r_2618_; size_t v_sz_2619_; size_t v___x_2620_; lean_object* v___x_2621_; 
v___f_2616_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2616_, 0, v_cmp_2615_);
v___x_2617_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2618_ = lean_box(1);
v_sz_2619_ = lean_array_size(v_a_2614_);
v___x_2620_ = ((size_t)0ULL);
v___x_2621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2617_, v_a_2614_, v___f_2616_, v_sz_2619_, v___x_2620_, v_r_2618_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray(lean_object* v_00_u03b1_2622_, lean_object* v_00_u03b2_2623_, lean_object* v_a_2624_, lean_object* v_cmp_2625_){
_start:
{
lean_object* v___f_2626_; lean_object* v___x_2627_; lean_object* v_r_2628_; size_t v_sz_2629_; size_t v___x_2630_; lean_object* v___x_2631_; 
v___f_2626_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2626_, 0, v_cmp_2625_);
v___x_2627_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2628_ = lean_box(1);
v_sz_2629_ = lean_array_size(v_a_2624_);
v___x_2630_ = ((size_t)0ULL);
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2627_, v_a_2624_, v___f_2626_, v_sz_2629_, v___x_2630_, v_r_2628_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify___redArg(lean_object* v_cmp_2632_, lean_object* v_t_2633_, lean_object* v_a_2634_, lean_object* v_f_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2632_, v_a_2634_, v_f_2635_, v_t_2633_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify(lean_object* v_00_u03b1_2637_, lean_object* v_00_u03b2_2638_, lean_object* v_cmp_2639_, lean_object* v_inst_2640_, lean_object* v_t_2641_, lean_object* v_a_2642_, lean_object* v_f_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2639_, v_a_2642_, v_f_2643_, v_t_2641_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter___redArg(lean_object* v_cmp_2645_, lean_object* v_t_2646_, lean_object* v_a_2647_, lean_object* v_f_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2645_, v_a_2647_, v_f_2648_, v_t_2646_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter(lean_object* v_00_u03b1_2650_, lean_object* v_00_u03b2_2651_, lean_object* v_cmp_2652_, lean_object* v_inst_2653_, lean_object* v_t_2654_, lean_object* v_a_2655_, lean_object* v_f_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2652_, v_a_2655_, v_f_2656_, v_t_2654_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2658_, lean_object* v_mergeFn_2659_, lean_object* v_a_2660_, lean_object* v_x_2661_){
_start:
{
if (lean_obj_tag(v_x_2661_) == 0)
{
lean_object* v___x_2662_; 
lean_dec(v_a_2660_);
lean_dec(v_mergeFn_2659_);
v___x_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_b_u2082_2658_);
return v___x_2662_;
}
else
{
lean_object* v_val_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2671_; 
v_val_2663_ = lean_ctor_get(v_x_2661_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_x_2661_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2665_ = v_x_2661_;
v_isShared_2666_ = v_isSharedCheck_2671_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_val_2663_);
lean_dec(v_x_2661_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2671_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2667_ = lean_apply_3(v_mergeFn_2659_, v_a_2660_, v_val_2663_, v_b_u2082_2658_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2667_);
v___x_2669_ = v___x_2665_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2672_, lean_object* v_cmp_2673_, lean_object* v_t_2674_, lean_object* v_a_2675_, lean_object* v_b_u2082_2676_){
_start:
{
lean_object* v___f_2677_; lean_object* v___x_2678_; 
lean_inc(v_a_2675_);
v___f_2677_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2677_, 0, v_b_u2082_2676_);
lean_closure_set(v___f_2677_, 1, v_mergeFn_2672_);
lean_closure_set(v___f_2677_, 2, v_a_2675_);
v___x_2678_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2673_, v_a_2675_, v___f_2677_, v_t_2674_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg(lean_object* v_cmp_2679_, lean_object* v_mergeFn_2680_, lean_object* v_t_u2081_2681_, lean_object* v_t_u2082_2682_){
_start:
{
lean_object* v___f_2683_; lean_object* v___x_2684_; 
v___f_2683_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2683_, 0, v_mergeFn_2680_);
lean_closure_set(v___f_2683_, 1, v_cmp_2679_);
v___x_2684_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2683_, v_t_u2081_2681_, v_t_u2082_2682_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith(lean_object* v_00_u03b1_2685_, lean_object* v_00_u03b2_2686_, lean_object* v_cmp_2687_, lean_object* v_inst_2688_, lean_object* v_mergeFn_2689_, lean_object* v_t_u2081_2690_, lean_object* v_t_u2082_2691_){
_start:
{
lean_object* v___f_2692_; lean_object* v___x_2693_; 
v___f_2692_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2692_, 0, v_mergeFn_2689_);
lean_closure_set(v___f_2692_, 1, v_cmp_2687_);
v___x_2693_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2692_, v_t_u2081_2690_, v_t_u2082_2691_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg___lam__0(lean_object* v_x1_2694_, lean_object* v_x2_2695_, lean_object* v_x3_2696_){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v_x1_2694_);
lean_ctor_set(v___x_2697_, 1, v_x2_2695_);
v___x_2698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v_x3_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg(lean_object* v_t_2700_){
_start:
{
lean_object* v___f_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___f_2701_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0));
v___x_2702_ = lean_box(0);
v___x_2703_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2704_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2703_, v___f_2701_, v___x_2702_, v_t_2700_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList(lean_object* v_00_u03b1_2705_, lean_object* v_cmp_2706_, lean_object* v_00_u03b2_2707_, lean_object* v_t_2708_){
_start:
{
lean_object* v___f_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___f_2709_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0));
v___x_2710_ = lean_box(0);
v___x_2711_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2712_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2711_, v___f_2709_, v___x_2710_, v_t_2708_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___boxed(lean_object* v_00_u03b1_2713_, lean_object* v_cmp_2714_, lean_object* v_00_u03b2_2715_, lean_object* v_t_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Std_DTreeMap_Raw_Const_toList(v_00_u03b1_2713_, v_cmp_2714_, v_00_u03b2_2715_, v_t_2716_);
lean_dec_ref(v_cmp_2714_);
return v_res_2717_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0(lean_object* v_cmp_2719_, lean_object* v_a_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_fst_2723_; lean_object* v_snd_2724_; lean_object* v_r_2725_; lean_object* v___x_2726_; 
v_fst_2723_ = lean_ctor_get(v_a_2720_, 0);
lean_inc(v_fst_2723_);
v_snd_2724_ = lean_ctor_get(v_a_2720_, 1);
lean_inc(v_snd_2724_);
lean_dec_ref(v_a_2720_);
v_r_2725_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2719_, v_fst_2723_, v_snd_2724_, v___y_2722_);
v___x_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_r_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg(lean_object* v_l_2727_, lean_object* v_cmp_2728_){
_start:
{
lean_object* v___f_2729_; lean_object* v___x_2730_; lean_object* v_r_2731_; lean_object* v___x_2732_; 
v___f_2729_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2729_, 0, v_cmp_2728_);
v___x_2730_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2731_ = lean_box(1);
v___x_2732_ = l_List_forIn_x27_loop___redArg(v___x_2730_, v___f_2729_, v_l_2727_, v_r_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList(lean_object* v_00_u03b1_2733_, lean_object* v_00_u03b2_2734_, lean_object* v_l_2735_, lean_object* v_cmp_2736_){
_start:
{
lean_object* v___f_2737_; lean_object* v___x_2738_; lean_object* v_r_2739_; lean_object* v___x_2740_; 
v___f_2737_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2737_, 0, v_cmp_2736_);
v___x_2738_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2739_ = lean_box(1);
v___x_2740_ = l_List_forIn_x27_loop___redArg(v___x_2738_, v___f_2737_, v_l_2735_, v_r_2739_);
return v___x_2740_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_2742_, lean_object* v_a_2743_, lean_object* v_x_2744_, lean_object* v___y_2745_){
_start:
{
uint8_t v___x_2746_; 
lean_inc(v___y_2745_);
lean_inc(v_a_2743_);
lean_inc_ref(v_cmp_2742_);
v___x_2746_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2742_, v_a_2743_, v___y_2745_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = lean_box(0);
v___x_2748_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2742_, v_a_2743_, v___x_2747_, v___y_2745_);
v___x_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
return v___x_2749_;
}
else
{
lean_object* v___x_2750_; 
lean_dec(v_a_2743_);
lean_dec_ref(v_cmp_2742_);
v___x_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___y_2745_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg(lean_object* v_l_2751_, lean_object* v_cmp_2752_){
_start:
{
lean_object* v___f_2753_; lean_object* v___x_2754_; lean_object* v_r_2755_; lean_object* v___x_2756_; 
v___f_2753_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2753_, 0, v_cmp_2752_);
v___x_2754_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2755_ = lean_box(1);
v___x_2756_ = l_List_forIn_x27_loop___redArg(v___x_2754_, v___f_2753_, v_l_2751_, v_r_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList(lean_object* v_00_u03b1_2757_, lean_object* v_l_2758_, lean_object* v_cmp_2759_){
_start:
{
lean_object* v___f_2760_; lean_object* v___x_2761_; lean_object* v_r_2762_; lean_object* v___x_2763_; 
v___f_2760_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2760_, 0, v_cmp_2759_);
v___x_2761_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2762_ = lean_box(1);
v___x_2763_ = l_List_forIn_x27_loop___redArg(v___x_2761_, v___f_2760_, v_l_2758_, v_r_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg___lam__0(lean_object* v_l_2764_, lean_object* v_k_2765_, lean_object* v_v_2766_){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_k_2765_);
lean_ctor_set(v___x_2767_, 1, v_v_2766_);
v___x_2768_ = lean_array_push(v_l_2764_, v___x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg(lean_object* v_t_2770_){
_start:
{
lean_object* v___f_2771_; lean_object* v___y_2773_; 
v___f_2771_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2770_) == 0)
{
lean_object* v_size_2776_; 
v_size_2776_ = lean_ctor_get(v_t_2770_, 0);
lean_inc(v_size_2776_);
v___y_2773_ = v_size_2776_;
goto v___jp_2772_;
}
else
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_unsigned_to_nat(0u);
v___y_2773_ = v___x_2777_;
goto v___jp_2772_;
}
v___jp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_mk_empty_array_with_capacity(v___y_2773_);
lean_dec(v___y_2773_);
v___x_2775_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2771_, v___x_2774_, v_t_2770_);
return v___x_2775_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray(lean_object* v_00_u03b1_2778_, lean_object* v_cmp_2779_, lean_object* v_00_u03b2_2780_, lean_object* v_t_2781_){
_start:
{
lean_object* v___f_2782_; lean_object* v___y_2784_; 
v___f_2782_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2781_) == 0)
{
lean_object* v_size_2787_; 
v_size_2787_ = lean_ctor_get(v_t_2781_, 0);
lean_inc(v_size_2787_);
v___y_2784_ = v_size_2787_;
goto v___jp_2783_;
}
else
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_unsigned_to_nat(0u);
v___y_2784_ = v___x_2788_;
goto v___jp_2783_;
}
v___jp_2783_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = lean_mk_empty_array_with_capacity(v___y_2784_);
lean_dec(v___y_2784_);
v___x_2786_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2782_, v___x_2785_, v_t_2781_);
return v___x_2786_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___boxed(lean_object* v_00_u03b1_2789_, lean_object* v_cmp_2790_, lean_object* v_00_u03b2_2791_, lean_object* v_t_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Std_DTreeMap_Raw_Const_toArray(v_00_u03b1_2789_, v_cmp_2790_, v_00_u03b2_2791_, v_t_2792_);
lean_dec_ref(v_cmp_2790_);
return v_res_2793_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray___redArg(lean_object* v_a_2795_, lean_object* v_cmp_2796_){
_start:
{
lean_object* v___f_2797_; lean_object* v___x_2798_; lean_object* v_r_2799_; size_t v_sz_2800_; size_t v___x_2801_; lean_object* v___x_2802_; 
v___f_2797_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2797_, 0, v_cmp_2796_);
v___x_2798_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2799_ = lean_box(1);
v_sz_2800_ = lean_array_size(v_a_2795_);
v___x_2801_ = ((size_t)0ULL);
v___x_2802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2798_, v_a_2795_, v___f_2797_, v_sz_2800_, v___x_2801_, v_r_2799_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray(lean_object* v_00_u03b1_2803_, lean_object* v_00_u03b2_2804_, lean_object* v_a_2805_, lean_object* v_cmp_2806_){
_start:
{
lean_object* v___f_2807_; lean_object* v___x_2808_; lean_object* v_r_2809_; size_t v_sz_2810_; size_t v___x_2811_; lean_object* v___x_2812_; 
v___f_2807_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2807_, 0, v_cmp_2806_);
v___x_2808_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2809_ = lean_box(1);
v_sz_2810_ = lean_array_size(v_a_2805_);
v___x_2811_ = ((size_t)0ULL);
v___x_2812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2808_, v_a_2805_, v___f_2807_, v_sz_2810_, v___x_2811_, v_r_2809_);
return v___x_2812_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray___redArg(lean_object* v_a_2814_, lean_object* v_cmp_2815_){
_start:
{
lean_object* v___f_2816_; lean_object* v___x_2817_; lean_object* v_r_2818_; size_t v_sz_2819_; size_t v___x_2820_; lean_object* v___x_2821_; 
v___f_2816_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2816_, 0, v_cmp_2815_);
v___x_2817_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2818_ = lean_box(1);
v_sz_2819_ = lean_array_size(v_a_2814_);
v___x_2820_ = ((size_t)0ULL);
v___x_2821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2817_, v_a_2814_, v___f_2816_, v_sz_2819_, v___x_2820_, v_r_2818_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray(lean_object* v_00_u03b1_2822_, lean_object* v_a_2823_, lean_object* v_cmp_2824_){
_start:
{
lean_object* v___f_2825_; lean_object* v___x_2826_; lean_object* v_r_2827_; size_t v_sz_2828_; size_t v___x_2829_; lean_object* v___x_2830_; 
v___f_2825_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2825_, 0, v_cmp_2824_);
v___x_2826_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2827_ = lean_box(1);
v_sz_2828_ = lean_array_size(v_a_2823_);
v___x_2829_ = ((size_t)0ULL);
v___x_2830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2826_, v_a_2823_, v___f_2825_, v_sz_2828_, v___x_2829_, v_r_2827_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify___redArg(lean_object* v_cmp_2831_, lean_object* v_t_2832_, lean_object* v_a_2833_, lean_object* v_f_2834_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2831_, v_a_2833_, v_f_2834_, v_t_2832_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify(lean_object* v_00_u03b1_2836_, lean_object* v_cmp_2837_, lean_object* v_00_u03b2_2838_, lean_object* v_t_2839_, lean_object* v_a_2840_, lean_object* v_f_2841_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2837_, v_a_2840_, v_f_2841_, v_t_2839_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter___redArg(lean_object* v_cmp_2843_, lean_object* v_t_2844_, lean_object* v_a_2845_, lean_object* v_f_2846_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_2843_, v_a_2845_, v_f_2846_, v_t_2844_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter(lean_object* v_00_u03b1_2848_, lean_object* v_cmp_2849_, lean_object* v_00_u03b2_2850_, lean_object* v_t_2851_, lean_object* v_a_2852_, lean_object* v_f_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_2849_, v_a_2852_, v_f_2853_, v_t_2851_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2855_, lean_object* v_cmp_2856_, lean_object* v_t_2857_, lean_object* v_a_2858_, lean_object* v_b_u2082_2859_){
_start:
{
lean_object* v___f_2860_; lean_object* v___x_2861_; 
lean_inc(v_a_2858_);
v___f_2860_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2860_, 0, v_b_u2082_2859_);
lean_closure_set(v___f_2860_, 1, v_mergeFn_2855_);
lean_closure_set(v___f_2860_, 2, v_a_2858_);
v___x_2861_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_2856_, v_a_2858_, v___f_2860_, v_t_2857_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg(lean_object* v_cmp_2862_, lean_object* v_mergeFn_2863_, lean_object* v_t_u2081_2864_, lean_object* v_t_u2082_2865_){
_start:
{
lean_object* v___f_2866_; lean_object* v___x_2867_; 
v___f_2866_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2866_, 0, v_mergeFn_2863_);
lean_closure_set(v___f_2866_, 1, v_cmp_2862_);
v___x_2867_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2866_, v_t_u2081_2864_, v_t_u2082_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith(lean_object* v_00_u03b1_2868_, lean_object* v_cmp_2869_, lean_object* v_00_u03b2_2870_, lean_object* v_mergeFn_2871_, lean_object* v_t_u2081_2872_, lean_object* v_t_u2082_2873_){
_start:
{
lean_object* v___f_2874_; lean_object* v___x_2875_; 
v___f_2874_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2874_, 0, v_mergeFn_2871_);
lean_closure_set(v___f_2874_, 1, v_cmp_2869_);
v___x_2875_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2874_, v_t_u2081_2872_, v_t_u2082_2873_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_2876_, lean_object* v_x_2877_, lean_object* v_____s_2878_){
_start:
{
lean_object* v_fst_2879_; lean_object* v_snd_2880_; lean_object* v_r_2881_; lean_object* v___x_2882_; 
v_fst_2879_ = lean_ctor_get(v_x_2877_, 0);
lean_inc(v_fst_2879_);
v_snd_2880_ = lean_ctor_get(v_x_2877_, 1);
lean_inc(v_snd_2880_);
lean_dec_ref(v_x_2877_);
v_r_2881_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2876_, v_fst_2879_, v_snd_2880_, v_____s_2878_);
v___x_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2882_, 0, v_r_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg(lean_object* v_cmp_2883_, lean_object* v_inst_2884_, lean_object* v_t_2885_, lean_object* v_l_2886_){
_start:
{
lean_object* v___f_2887_; lean_object* v___x_2888_; 
v___f_2887_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2887_, 0, v_cmp_2883_);
v___x_2888_ = lean_apply_4(v_inst_2884_, lean_box(0), v_l_2886_, v_t_2885_, v___f_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany(lean_object* v_00_u03b1_2889_, lean_object* v_00_u03b2_2890_, lean_object* v_cmp_2891_, lean_object* v_00_u03c1_2892_, lean_object* v_inst_2893_, lean_object* v_t_2894_, lean_object* v_l_2895_){
_start:
{
lean_object* v___f_2896_; lean_object* v___x_2897_; 
v___f_2896_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2896_, 0, v_cmp_2891_);
v___x_2897_ = lean_apply_4(v_inst_2893_, lean_box(0), v_l_2895_, v_t_2894_, v___f_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_2898_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = lean_box(1);
v___x_2900_ = lean_panic_fn(v___x_2899_, v_msg_2898_);
return v___x_2900_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2904_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__2));
v___x_2905_ = lean_unsigned_to_nat(35u);
v___x_2906_ = lean_unsigned_to_nat(182u);
v___x_2907_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__1));
v___x_2908_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0));
v___x_2909_ = l_mkPanicMessageWithDecl(v___x_2908_, v___x_2907_, v___x_2906_, v___x_2905_, v___x_2904_);
return v___x_2909_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2910_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__2));
v___x_2911_ = lean_unsigned_to_nat(21u);
v___x_2912_ = lean_unsigned_to_nat(183u);
v___x_2913_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__1));
v___x_2914_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0));
v___x_2915_ = l_mkPanicMessageWithDecl(v___x_2914_, v___x_2913_, v___x_2912_, v___x_2911_, v___x_2910_);
return v___x_2915_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2918_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__6));
v___x_2919_ = lean_unsigned_to_nat(35u);
v___x_2920_ = lean_unsigned_to_nat(276u);
v___x_2921_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__5));
v___x_2922_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0));
v___x_2923_ = l_mkPanicMessageWithDecl(v___x_2922_, v___x_2921_, v___x_2920_, v___x_2919_, v___x_2918_);
return v___x_2923_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2924_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__6));
v___x_2925_ = lean_unsigned_to_nat(21u);
v___x_2926_ = lean_unsigned_to_nat(277u);
v___x_2927_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__5));
v___x_2928_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__0));
v___x_2929_ = l_mkPanicMessageWithDecl(v___x_2928_, v___x_2927_, v___x_2926_, v___x_2925_, v___x_2924_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(lean_object* v_cmp_2930_, lean_object* v_k_2931_, lean_object* v_v_2932_, lean_object* v_t_2933_){
_start:
{
if (lean_obj_tag(v_t_2933_) == 0)
{
lean_object* v_size_2934_; lean_object* v_k_2935_; lean_object* v_v_2936_; lean_object* v_l_2937_; lean_object* v_r_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_3295_; 
v_size_2934_ = lean_ctor_get(v_t_2933_, 0);
v_k_2935_ = lean_ctor_get(v_t_2933_, 1);
v_v_2936_ = lean_ctor_get(v_t_2933_, 2);
v_l_2937_ = lean_ctor_get(v_t_2933_, 3);
v_r_2938_ = lean_ctor_get(v_t_2933_, 4);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_t_2933_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_2940_ = v_t_2933_;
v_isShared_2941_ = v_isSharedCheck_3295_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_r_2938_);
lean_inc(v_l_2937_);
lean_inc(v_v_2936_);
lean_inc(v_k_2935_);
lean_inc(v_size_2934_);
lean_dec(v_t_2933_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_3295_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; uint8_t v___x_2943_; 
lean_inc_ref(v_cmp_2930_);
lean_inc(v_k_2935_);
lean_inc(v_k_2931_);
v___x_2942_ = lean_apply_2(v_cmp_2930_, v_k_2931_, v_k_2935_);
v___x_2943_ = lean_unbox(v___x_2942_);
switch(v___x_2943_)
{
case 0:
{
lean_object* v___x_2944_; 
lean_dec(v_size_2934_);
v___x_2944_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_2930_, v_k_2931_, v_v_2932_, v_l_2937_);
if (lean_obj_tag(v_r_2938_) == 0)
{
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_size_2945_; lean_object* v_size_2946_; lean_object* v_k_2947_; lean_object* v_v_2948_; lean_object* v_l_2949_; lean_object* v_r_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v_size_2945_ = lean_ctor_get(v_r_2938_, 0);
v_size_2946_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_size_2946_);
v_k_2947_ = lean_ctor_get(v___x_2944_, 1);
lean_inc(v_k_2947_);
v_v_2948_ = lean_ctor_get(v___x_2944_, 2);
lean_inc(v_v_2948_);
v_l_2949_ = lean_ctor_get(v___x_2944_, 3);
lean_inc(v_l_2949_);
v_r_2950_ = lean_ctor_get(v___x_2944_, 4);
lean_inc(v_r_2950_);
v___x_2951_ = lean_unsigned_to_nat(3u);
v___x_2952_ = lean_nat_mul(v___x_2951_, v_size_2945_);
v___x_2953_ = lean_nat_dec_lt(v___x_2952_, v_size_2946_);
lean_dec(v___x_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
lean_dec(v_r_2950_);
lean_dec(v_l_2949_);
lean_dec(v_v_2948_);
lean_dec(v_k_2947_);
v___x_2954_ = lean_unsigned_to_nat(1u);
v___x_2955_ = lean_nat_add(v___x_2954_, v_size_2946_);
lean_dec(v_size_2946_);
v___x_2956_ = lean_nat_add(v___x_2955_, v_size_2945_);
lean_dec(v___x_2955_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 3, v___x_2944_);
lean_ctor_set(v___x_2940_, 0, v___x_2956_);
v___x_2958_ = v___x_2940_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_2959_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_2959_, 3, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_2959_, 4, v_r_2938_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
else
{
lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_3031_; 
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3031_ == 0)
{
lean_object* v_unused_3032_; lean_object* v_unused_3033_; lean_object* v_unused_3034_; lean_object* v_unused_3035_; lean_object* v_unused_3036_; 
v_unused_3032_ = lean_ctor_get(v___x_2944_, 4);
lean_dec(v_unused_3032_);
v_unused_3033_ = lean_ctor_get(v___x_2944_, 3);
lean_dec(v_unused_3033_);
v_unused_3034_ = lean_ctor_get(v___x_2944_, 2);
lean_dec(v_unused_3034_);
v_unused_3035_ = lean_ctor_get(v___x_2944_, 1);
lean_dec(v_unused_3035_);
v_unused_3036_ = lean_ctor_get(v___x_2944_, 0);
lean_dec(v_unused_3036_);
v___x_2961_ = v___x_2944_;
v_isShared_2962_ = v_isSharedCheck_3031_;
goto v_resetjp_2960_;
}
else
{
lean_dec(v___x_2944_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_3031_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
if (lean_obj_tag(v_l_2949_) == 0)
{
if (lean_obj_tag(v_r_2950_) == 0)
{
lean_object* v_size_2963_; lean_object* v_size_2964_; lean_object* v_k_2965_; lean_object* v_v_2966_; lean_object* v_l_2967_; lean_object* v_r_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v_size_2963_ = lean_ctor_get(v_l_2949_, 0);
v_size_2964_ = lean_ctor_get(v_r_2950_, 0);
v_k_2965_ = lean_ctor_get(v_r_2950_, 1);
v_v_2966_ = lean_ctor_get(v_r_2950_, 2);
v_l_2967_ = lean_ctor_get(v_r_2950_, 3);
v_r_2968_ = lean_ctor_get(v_r_2950_, 4);
v___x_2969_ = lean_unsigned_to_nat(2u);
v___x_2970_ = lean_nat_mul(v___x_2969_, v_size_2963_);
v___x_2971_ = lean_nat_dec_lt(v_size_2964_, v___x_2970_);
lean_dec(v___x_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3001_; 
lean_inc(v_r_2968_);
lean_inc(v_l_2967_);
lean_inc(v_v_2966_);
lean_inc(v_k_2965_);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_r_2950_);
if (v_isSharedCheck_3001_ == 0)
{
lean_object* v_unused_3002_; lean_object* v_unused_3003_; lean_object* v_unused_3004_; lean_object* v_unused_3005_; lean_object* v_unused_3006_; 
v_unused_3002_ = lean_ctor_get(v_r_2950_, 4);
lean_dec(v_unused_3002_);
v_unused_3003_ = lean_ctor_get(v_r_2950_, 3);
lean_dec(v_unused_3003_);
v_unused_3004_ = lean_ctor_get(v_r_2950_, 2);
lean_dec(v_unused_3004_);
v_unused_3005_ = lean_ctor_get(v_r_2950_, 1);
lean_dec(v_unused_3005_);
v_unused_3006_ = lean_ctor_get(v_r_2950_, 0);
lean_dec(v_unused_3006_);
v___x_2973_ = v_r_2950_;
v_isShared_2974_ = v_isSharedCheck_3001_;
goto v_resetjp_2972_;
}
else
{
lean_dec(v_r_2950_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3001_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___x_2989_; lean_object* v___y_2991_; 
v___x_2975_ = lean_unsigned_to_nat(1u);
v___x_2976_ = lean_nat_add(v___x_2975_, v_size_2946_);
lean_dec(v_size_2946_);
v___x_2977_ = lean_nat_add(v___x_2976_, v_size_2945_);
lean_dec(v___x_2976_);
v___x_2989_ = lean_nat_add(v___x_2975_, v_size_2963_);
if (lean_obj_tag(v_l_2967_) == 0)
{
lean_object* v_size_2999_; 
v_size_2999_ = lean_ctor_get(v_l_2967_, 0);
lean_inc(v_size_2999_);
v___y_2991_ = v_size_2999_;
goto v___jp_2990_;
}
else
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_unsigned_to_nat(0u);
v___y_2991_ = v___x_3000_;
goto v___jp_2990_;
}
v___jp_2978_:
{
lean_object* v___x_2982_; lean_object* v___x_2984_; 
v___x_2982_ = lean_nat_add(v___y_2980_, v___y_2981_);
lean_dec(v___y_2981_);
lean_dec(v___y_2980_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 4, v_r_2938_);
lean_ctor_set(v___x_2973_, 3, v_r_2968_);
lean_ctor_set(v___x_2973_, 2, v_v_2936_);
lean_ctor_set(v___x_2973_, 1, v_k_2935_);
lean_ctor_set(v___x_2973_, 0, v___x_2982_);
v___x_2984_ = v___x_2973_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2982_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_2988_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_2988_, 3, v_r_2968_);
lean_ctor_set(v_reuseFailAlloc_2988_, 4, v_r_2938_);
v___x_2984_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2986_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 4, v___x_2984_);
lean_ctor_set(v___x_2961_, 3, v___y_2979_);
lean_ctor_set(v___x_2961_, 2, v_v_2966_);
lean_ctor_set(v___x_2961_, 1, v_k_2965_);
lean_ctor_set(v___x_2961_, 0, v___x_2977_);
v___x_2986_ = v___x_2961_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2977_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_k_2965_);
lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_v_2966_);
lean_ctor_set(v_reuseFailAlloc_2987_, 3, v___y_2979_);
lean_ctor_set(v_reuseFailAlloc_2987_, 4, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
v___jp_2990_:
{
lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2992_ = lean_nat_add(v___x_2989_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec(v___x_2989_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v_l_2967_);
lean_ctor_set(v___x_2940_, 3, v_l_2949_);
lean_ctor_set(v___x_2940_, 2, v_v_2948_);
lean_ctor_set(v___x_2940_, 1, v_k_2947_);
lean_ctor_set(v___x_2940_, 0, v___x_2992_);
v___x_2994_ = v___x_2940_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_k_2947_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v_v_2948_);
lean_ctor_set(v_reuseFailAlloc_2998_, 3, v_l_2949_);
lean_ctor_set(v_reuseFailAlloc_2998_, 4, v_l_2967_);
v___x_2994_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_nat_add(v___x_2975_, v_size_2945_);
if (lean_obj_tag(v_r_2968_) == 0)
{
lean_object* v_size_2996_; 
v_size_2996_ = lean_ctor_get(v_r_2968_, 0);
lean_inc(v_size_2996_);
v___y_2979_ = v___x_2994_;
v___y_2980_ = v___x_2995_;
v___y_2981_ = v_size_2996_;
goto v___jp_2978_;
}
else
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_unsigned_to_nat(0u);
v___y_2979_ = v___x_2994_;
v___y_2980_ = v___x_2995_;
v___y_2981_ = v___x_2997_;
goto v___jp_2978_;
}
}
}
}
}
else
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3013_; 
lean_del_object(v___x_2940_);
v___x_3007_ = lean_unsigned_to_nat(1u);
v___x_3008_ = lean_nat_add(v___x_3007_, v_size_2946_);
lean_dec(v_size_2946_);
v___x_3009_ = lean_nat_add(v___x_3008_, v_size_2945_);
lean_dec(v___x_3008_);
v___x_3010_ = lean_nat_add(v___x_3007_, v_size_2945_);
v___x_3011_ = lean_nat_add(v___x_3010_, v_size_2964_);
lean_dec(v___x_3010_);
lean_inc_ref(v_r_2938_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 4, v_r_2938_);
lean_ctor_set(v___x_2961_, 3, v_r_2950_);
lean_ctor_set(v___x_2961_, 2, v_v_2936_);
lean_ctor_set(v___x_2961_, 1, v_k_2935_);
lean_ctor_set(v___x_2961_, 0, v___x_3011_);
v___x_3013_ = v___x_2961_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3026_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3026_, 3, v_r_2950_);
lean_ctor_set(v_reuseFailAlloc_3026_, 4, v_r_2938_);
v___x_3013_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
v_isSharedCheck_3020_ = !lean_is_exclusive(v_r_2938_);
if (v_isSharedCheck_3020_ == 0)
{
lean_object* v_unused_3021_; lean_object* v_unused_3022_; lean_object* v_unused_3023_; lean_object* v_unused_3024_; lean_object* v_unused_3025_; 
v_unused_3021_ = lean_ctor_get(v_r_2938_, 4);
lean_dec(v_unused_3021_);
v_unused_3022_ = lean_ctor_get(v_r_2938_, 3);
lean_dec(v_unused_3022_);
v_unused_3023_ = lean_ctor_get(v_r_2938_, 2);
lean_dec(v_unused_3023_);
v_unused_3024_ = lean_ctor_get(v_r_2938_, 1);
lean_dec(v_unused_3024_);
v_unused_3025_ = lean_ctor_get(v_r_2938_, 0);
lean_dec(v_unused_3025_);
v___x_3015_ = v_r_2938_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_dec(v_r_2938_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 4, v___x_3013_);
lean_ctor_set(v___x_3015_, 3, v_l_2949_);
lean_ctor_set(v___x_3015_, 2, v_v_2948_);
lean_ctor_set(v___x_3015_, 1, v_k_2947_);
lean_ctor_set(v___x_3015_, 0, v___x_3009_);
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3009_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_k_2947_);
lean_ctor_set(v_reuseFailAlloc_3019_, 2, v_v_2948_);
lean_ctor_set(v_reuseFailAlloc_3019_, 3, v_l_2949_);
lean_ctor_set(v_reuseFailAlloc_3019_, 4, v___x_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
lean_dec_ref(v_l_2949_);
lean_del_object(v___x_2961_);
lean_dec(v_v_2948_);
lean_dec(v_k_2947_);
lean_dec(v_size_2946_);
lean_dec_ref(v_r_2938_);
lean_del_object(v___x_2940_);
lean_dec(v_v_2936_);
lean_dec(v_k_2935_);
v___x_3027_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3);
v___x_3028_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_3027_);
return v___x_3028_;
}
}
else
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_del_object(v___x_2961_);
lean_dec(v_r_2950_);
lean_dec(v_v_2948_);
lean_dec(v_k_2947_);
lean_dec(v_size_2946_);
lean_dec_ref(v_r_2938_);
lean_del_object(v___x_2940_);
lean_dec(v_v_2936_);
lean_dec(v_k_2935_);
v___x_3029_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4);
v___x_3030_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_3029_);
return v___x_3030_;
}
}
}
}
else
{
lean_object* v_size_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
v_size_3037_ = lean_ctor_get(v_r_2938_, 0);
v___x_3038_ = lean_unsigned_to_nat(1u);
v___x_3039_ = lean_nat_add(v___x_3038_, v_size_3037_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 3, v___x_2944_);
lean_ctor_set(v___x_2940_, 0, v___x_3039_);
v___x_3041_ = v___x_2940_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3042_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3042_, 3, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_3042_, 4, v_r_2938_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
else
{
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_l_3043_; 
v_l_3043_ = lean_ctor_get(v___x_2944_, 3);
lean_inc(v_l_3043_);
if (lean_obj_tag(v_l_3043_) == 0)
{
lean_object* v_r_3044_; 
v_r_3044_ = lean_ctor_get(v___x_2944_, 4);
lean_inc(v_r_3044_);
if (lean_obj_tag(v_r_3044_) == 0)
{
lean_object* v_size_3045_; lean_object* v_k_3046_; lean_object* v_v_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3061_; 
v_size_3045_ = lean_ctor_get(v___x_2944_, 0);
v_k_3046_ = lean_ctor_get(v___x_2944_, 1);
v_v_3047_ = lean_ctor_get(v___x_2944_, 2);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3061_ == 0)
{
lean_object* v_unused_3062_; lean_object* v_unused_3063_; 
v_unused_3062_ = lean_ctor_get(v___x_2944_, 4);
lean_dec(v_unused_3062_);
v_unused_3063_ = lean_ctor_get(v___x_2944_, 3);
lean_dec(v_unused_3063_);
v___x_3049_ = v___x_2944_;
v_isShared_3050_ = v_isSharedCheck_3061_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_v_3047_);
lean_inc(v_k_3046_);
lean_inc(v_size_3045_);
lean_dec(v___x_2944_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3061_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_size_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
v_size_3051_ = lean_ctor_get(v_r_3044_, 0);
v___x_3052_ = lean_unsigned_to_nat(1u);
v___x_3053_ = lean_nat_add(v___x_3052_, v_size_3045_);
lean_dec(v_size_3045_);
v___x_3054_ = lean_nat_add(v___x_3052_, v_size_3051_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 4, v_r_2938_);
lean_ctor_set(v___x_3049_, 3, v_r_3044_);
lean_ctor_set(v___x_3049_, 2, v_v_2936_);
lean_ctor_set(v___x_3049_, 1, v_k_2935_);
lean_ctor_set(v___x_3049_, 0, v___x_3054_);
v___x_3056_ = v___x_3049_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3060_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3060_, 3, v_r_3044_);
lean_ctor_set(v_reuseFailAlloc_3060_, 4, v_r_2938_);
v___x_3056_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3058_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v___x_3056_);
lean_ctor_set(v___x_2940_, 3, v_l_3043_);
lean_ctor_set(v___x_2940_, 2, v_v_3047_);
lean_ctor_set(v___x_2940_, 1, v_k_3046_);
lean_ctor_set(v___x_2940_, 0, v___x_3053_);
v___x_3058_ = v___x_2940_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3053_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_k_3046_);
lean_ctor_set(v_reuseFailAlloc_3059_, 2, v_v_3047_);
lean_ctor_set(v_reuseFailAlloc_3059_, 3, v_l_3043_);
lean_ctor_set(v_reuseFailAlloc_3059_, 4, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_object* v_k_3064_; lean_object* v_v_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3077_; 
v_k_3064_ = lean_ctor_get(v___x_2944_, 1);
v_v_3065_ = lean_ctor_get(v___x_2944_, 2);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; lean_object* v_unused_3079_; lean_object* v_unused_3080_; 
v_unused_3078_ = lean_ctor_get(v___x_2944_, 4);
lean_dec(v_unused_3078_);
v_unused_3079_ = lean_ctor_get(v___x_2944_, 3);
lean_dec(v_unused_3079_);
v_unused_3080_ = lean_ctor_get(v___x_2944_, 0);
lean_dec(v_unused_3080_);
v___x_3067_ = v___x_2944_;
v_isShared_3068_ = v_isSharedCheck_3077_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_v_3065_);
lean_inc(v_k_3064_);
lean_dec(v___x_2944_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3077_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3072_; 
v___x_3069_ = lean_unsigned_to_nat(3u);
v___x_3070_ = lean_unsigned_to_nat(1u);
if (v_isShared_3068_ == 0)
{
lean_ctor_set(v___x_3067_, 3, v_r_3044_);
lean_ctor_set(v___x_3067_, 2, v_v_2936_);
lean_ctor_set(v___x_3067_, 1, v_k_2935_);
lean_ctor_set(v___x_3067_, 0, v___x_3070_);
v___x_3072_ = v___x_3067_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_r_3044_);
lean_ctor_set(v_reuseFailAlloc_3076_, 4, v_r_3044_);
v___x_3072_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3074_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v___x_3072_);
lean_ctor_set(v___x_2940_, 3, v_l_3043_);
lean_ctor_set(v___x_2940_, 2, v_v_3065_);
lean_ctor_set(v___x_2940_, 1, v_k_3064_);
lean_ctor_set(v___x_2940_, 0, v___x_3069_);
v___x_3074_ = v___x_2940_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3069_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_k_3064_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_v_3065_);
lean_ctor_set(v_reuseFailAlloc_3075_, 3, v_l_3043_);
lean_ctor_set(v_reuseFailAlloc_3075_, 4, v___x_3072_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
else
{
lean_object* v_r_3081_; 
v_r_3081_ = lean_ctor_get(v___x_2944_, 4);
lean_inc(v_r_3081_);
if (lean_obj_tag(v_r_3081_) == 0)
{
lean_object* v_k_3082_; lean_object* v_v_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3107_; 
v_k_3082_ = lean_ctor_get(v___x_2944_, 1);
v_v_3083_ = lean_ctor_get(v___x_2944_, 2);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; lean_object* v_unused_3109_; lean_object* v_unused_3110_; 
v_unused_3108_ = lean_ctor_get(v___x_2944_, 4);
lean_dec(v_unused_3108_);
v_unused_3109_ = lean_ctor_get(v___x_2944_, 3);
lean_dec(v_unused_3109_);
v_unused_3110_ = lean_ctor_get(v___x_2944_, 0);
lean_dec(v_unused_3110_);
v___x_3085_ = v___x_2944_;
v_isShared_3086_ = v_isSharedCheck_3107_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_v_3083_);
lean_inc(v_k_3082_);
lean_dec(v___x_2944_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3107_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v_k_3087_; lean_object* v_v_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3103_; 
v_k_3087_ = lean_ctor_get(v_r_3081_, 1);
v_v_3088_ = lean_ctor_get(v_r_3081_, 2);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_r_3081_);
if (v_isSharedCheck_3103_ == 0)
{
lean_object* v_unused_3104_; lean_object* v_unused_3105_; lean_object* v_unused_3106_; 
v_unused_3104_ = lean_ctor_get(v_r_3081_, 4);
lean_dec(v_unused_3104_);
v_unused_3105_ = lean_ctor_get(v_r_3081_, 3);
lean_dec(v_unused_3105_);
v_unused_3106_ = lean_ctor_get(v_r_3081_, 0);
lean_dec(v_unused_3106_);
v___x_3090_ = v_r_3081_;
v_isShared_3091_ = v_isSharedCheck_3103_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_v_3088_);
lean_inc(v_k_3087_);
lean_dec(v_r_3081_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3103_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3095_; 
v___x_3092_ = lean_unsigned_to_nat(3u);
v___x_3093_ = lean_unsigned_to_nat(1u);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 4, v_l_3043_);
lean_ctor_set(v___x_3090_, 3, v_l_3043_);
lean_ctor_set(v___x_3090_, 2, v_v_3083_);
lean_ctor_set(v___x_3090_, 1, v_k_3082_);
lean_ctor_set(v___x_3090_, 0, v___x_3093_);
v___x_3095_ = v___x_3090_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_k_3082_);
lean_ctor_set(v_reuseFailAlloc_3102_, 2, v_v_3083_);
lean_ctor_set(v_reuseFailAlloc_3102_, 3, v_l_3043_);
lean_ctor_set(v_reuseFailAlloc_3102_, 4, v_l_3043_);
v___x_3095_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3097_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 4, v_l_3043_);
lean_ctor_set(v___x_3085_, 2, v_v_2936_);
lean_ctor_set(v___x_3085_, 1, v_k_2935_);
lean_ctor_set(v___x_3085_, 0, v___x_3093_);
v___x_3097_ = v___x_3085_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3101_, 3, v_l_3043_);
lean_ctor_set(v_reuseFailAlloc_3101_, 4, v_l_3043_);
v___x_3097_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
lean_object* v___x_3099_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v___x_3097_);
lean_ctor_set(v___x_2940_, 3, v___x_3095_);
lean_ctor_set(v___x_2940_, 2, v_v_3088_);
lean_ctor_set(v___x_2940_, 1, v_k_3087_);
lean_ctor_set(v___x_2940_, 0, v___x_3092_);
v___x_3099_ = v___x_2940_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3092_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3100_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3100_, 3, v___x_3095_);
lean_ctor_set(v_reuseFailAlloc_3100_, 4, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3111_ = lean_unsigned_to_nat(2u);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v_r_3081_);
lean_ctor_set(v___x_2940_, 3, v___x_2944_);
lean_ctor_set(v___x_2940_, 0, v___x_3111_);
v___x_3113_ = v___x_2940_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3114_, 3, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_3114_, 4, v_r_3081_);
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
else
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3115_ = lean_unsigned_to_nat(1u);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v___x_2944_);
lean_ctor_set(v___x_2940_, 3, v___x_2944_);
lean_ctor_set(v___x_2940_, 0, v___x_3115_);
v___x_3117_ = v___x_2940_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3118_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3118_, 3, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_3118_, 4, v___x_2944_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
case 1:
{
lean_object* v___x_3120_; 
lean_dec(v_v_2936_);
lean_dec(v_k_2935_);
lean_dec_ref(v_cmp_2930_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 2, v_v_2932_);
lean_ctor_set(v___x_2940_, 1, v_k_2931_);
v___x_3120_ = v___x_2940_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_size_2934_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_k_2931_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v_v_2932_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v_l_2937_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v_r_2938_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
default: 
{
lean_object* v___x_3122_; 
lean_dec(v_size_2934_);
v___x_3122_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_2930_, v_k_2931_, v_v_2932_, v_r_2938_);
if (lean_obj_tag(v_l_2937_) == 0)
{
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_size_3123_; lean_object* v_size_3124_; lean_object* v_k_3125_; lean_object* v_v_3126_; lean_object* v_l_3127_; lean_object* v_r_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v_size_3123_ = lean_ctor_get(v_l_2937_, 0);
v_size_3124_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_size_3124_);
v_k_3125_ = lean_ctor_get(v___x_3122_, 1);
lean_inc(v_k_3125_);
v_v_3126_ = lean_ctor_get(v___x_3122_, 2);
lean_inc(v_v_3126_);
v_l_3127_ = lean_ctor_get(v___x_3122_, 3);
lean_inc(v_l_3127_);
v_r_3128_ = lean_ctor_get(v___x_3122_, 4);
lean_inc(v_r_3128_);
v___x_3129_ = lean_unsigned_to_nat(3u);
v___x_3130_ = lean_nat_mul(v___x_3129_, v_size_3123_);
v___x_3131_ = lean_nat_dec_lt(v___x_3130_, v_size_3124_);
lean_dec(v___x_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
lean_dec(v_r_3128_);
lean_dec(v_l_3127_);
lean_dec(v_v_3126_);
lean_dec(v_k_3125_);
v___x_3132_ = lean_unsigned_to_nat(1u);
v___x_3133_ = lean_nat_add(v___x_3132_, v_size_3123_);
v___x_3134_ = lean_nat_add(v___x_3133_, v_size_3124_);
lean_dec(v_size_3124_);
lean_dec(v___x_3133_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v___x_3122_);
lean_ctor_set(v___x_2940_, 0, v___x_3134_);
v___x_3136_ = v___x_2940_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3137_, 3, v_l_2937_);
lean_ctor_set(v_reuseFailAlloc_3137_, 4, v___x_3122_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
else
{
lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3207_; 
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3207_ == 0)
{
lean_object* v_unused_3208_; lean_object* v_unused_3209_; lean_object* v_unused_3210_; lean_object* v_unused_3211_; lean_object* v_unused_3212_; 
v_unused_3208_ = lean_ctor_get(v___x_3122_, 4);
lean_dec(v_unused_3208_);
v_unused_3209_ = lean_ctor_get(v___x_3122_, 3);
lean_dec(v_unused_3209_);
v_unused_3210_ = lean_ctor_get(v___x_3122_, 2);
lean_dec(v_unused_3210_);
v_unused_3211_ = lean_ctor_get(v___x_3122_, 1);
lean_dec(v_unused_3211_);
v_unused_3212_ = lean_ctor_get(v___x_3122_, 0);
lean_dec(v_unused_3212_);
v___x_3139_ = v___x_3122_;
v_isShared_3140_ = v_isSharedCheck_3207_;
goto v_resetjp_3138_;
}
else
{
lean_dec(v___x_3122_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3207_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
if (lean_obj_tag(v_l_3127_) == 0)
{
if (lean_obj_tag(v_r_3128_) == 0)
{
lean_object* v_size_3141_; lean_object* v_k_3142_; lean_object* v_v_3143_; lean_object* v_l_3144_; lean_object* v_r_3145_; lean_object* v_size_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_size_3141_ = lean_ctor_get(v_l_3127_, 0);
v_k_3142_ = lean_ctor_get(v_l_3127_, 1);
v_v_3143_ = lean_ctor_get(v_l_3127_, 2);
v_l_3144_ = lean_ctor_get(v_l_3127_, 3);
v_r_3145_ = lean_ctor_get(v_l_3127_, 4);
v_size_3146_ = lean_ctor_get(v_r_3128_, 0);
v___x_3147_ = lean_unsigned_to_nat(2u);
v___x_3148_ = lean_nat_mul(v___x_3147_, v_size_3146_);
v___x_3149_ = lean_nat_dec_lt(v_size_3141_, v___x_3148_);
lean_dec(v___x_3148_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3178_; 
lean_inc(v_r_3145_);
lean_inc(v_l_3144_);
lean_inc(v_v_3143_);
lean_inc(v_k_3142_);
v_isSharedCheck_3178_ = !lean_is_exclusive(v_l_3127_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; lean_object* v_unused_3180_; lean_object* v_unused_3181_; lean_object* v_unused_3182_; lean_object* v_unused_3183_; 
v_unused_3179_ = lean_ctor_get(v_l_3127_, 4);
lean_dec(v_unused_3179_);
v_unused_3180_ = lean_ctor_get(v_l_3127_, 3);
lean_dec(v_unused_3180_);
v_unused_3181_ = lean_ctor_get(v_l_3127_, 2);
lean_dec(v_unused_3181_);
v_unused_3182_ = lean_ctor_get(v_l_3127_, 1);
lean_dec(v_unused_3182_);
v_unused_3183_ = lean_ctor_get(v_l_3127_, 0);
lean_dec(v_unused_3183_);
v___x_3151_ = v_l_3127_;
v_isShared_3152_ = v_isSharedCheck_3178_;
goto v_resetjp_3150_;
}
else
{
lean_dec(v_l_3127_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3178_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3168_; 
v___x_3153_ = lean_unsigned_to_nat(1u);
v___x_3154_ = lean_nat_add(v___x_3153_, v_size_3123_);
v___x_3155_ = lean_nat_add(v___x_3154_, v_size_3124_);
lean_dec(v_size_3124_);
if (lean_obj_tag(v_l_3144_) == 0)
{
lean_object* v_size_3176_; 
v_size_3176_ = lean_ctor_get(v_l_3144_, 0);
lean_inc(v_size_3176_);
v___y_3168_ = v_size_3176_;
goto v___jp_3167_;
}
else
{
lean_object* v___x_3177_; 
v___x_3177_ = lean_unsigned_to_nat(0u);
v___y_3168_ = v___x_3177_;
goto v___jp_3167_;
}
v___jp_3156_:
{
lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3160_ = lean_nat_add(v___y_3157_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec(v___y_3157_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 4, v_r_3128_);
lean_ctor_set(v___x_3151_, 3, v_r_3145_);
lean_ctor_set(v___x_3151_, 2, v_v_3126_);
lean_ctor_set(v___x_3151_, 1, v_k_3125_);
lean_ctor_set(v___x_3151_, 0, v___x_3160_);
v___x_3162_ = v___x_3151_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_k_3125_);
lean_ctor_set(v_reuseFailAlloc_3166_, 2, v_v_3126_);
lean_ctor_set(v_reuseFailAlloc_3166_, 3, v_r_3145_);
lean_ctor_set(v_reuseFailAlloc_3166_, 4, v_r_3128_);
v___x_3162_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3164_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 4, v___x_3162_);
lean_ctor_set(v___x_3139_, 3, v___y_3158_);
lean_ctor_set(v___x_3139_, 2, v_v_3143_);
lean_ctor_set(v___x_3139_, 1, v_k_3142_);
lean_ctor_set(v___x_3139_, 0, v___x_3155_);
v___x_3164_ = v___x_3139_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_k_3142_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_v_3143_);
lean_ctor_set(v_reuseFailAlloc_3165_, 3, v___y_3158_);
lean_ctor_set(v_reuseFailAlloc_3165_, 4, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
v___jp_3167_:
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3169_ = lean_nat_add(v___x_3154_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec(v___x_3154_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v_l_3144_);
lean_ctor_set(v___x_2940_, 0, v___x_3169_);
v___x_3171_ = v___x_2940_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3175_, 3, v_l_2937_);
lean_ctor_set(v_reuseFailAlloc_3175_, 4, v_l_3144_);
v___x_3171_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; 
v___x_3172_ = lean_nat_add(v___x_3153_, v_size_3146_);
if (lean_obj_tag(v_r_3145_) == 0)
{
lean_object* v_size_3173_; 
v_size_3173_ = lean_ctor_get(v_r_3145_, 0);
lean_inc(v_size_3173_);
v___y_3157_ = v___x_3172_;
v___y_3158_ = v___x_3171_;
v___y_3159_ = v_size_3173_;
goto v___jp_3156_;
}
else
{
lean_object* v___x_3174_; 
v___x_3174_ = lean_unsigned_to_nat(0u);
v___y_3157_ = v___x_3172_;
v___y_3158_ = v___x_3171_;
v___y_3159_ = v___x_3174_;
goto v___jp_3156_;
}
}
}
}
}
else
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
lean_del_object(v___x_2940_);
v___x_3184_ = lean_unsigned_to_nat(1u);
v___x_3185_ = lean_nat_add(v___x_3184_, v_size_3123_);
v___x_3186_ = lean_nat_add(v___x_3185_, v_size_3124_);
lean_dec(v_size_3124_);
v___x_3187_ = lean_nat_add(v___x_3185_, v_size_3141_);
lean_dec(v___x_3185_);
lean_inc_ref(v_l_2937_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 4, v_l_3127_);
lean_ctor_set(v___x_3139_, 3, v_l_2937_);
lean_ctor_set(v___x_3139_, 2, v_v_2936_);
lean_ctor_set(v___x_3139_, 1, v_k_2935_);
lean_ctor_set(v___x_3139_, 0, v___x_3187_);
v___x_3189_ = v___x_3139_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3202_, 3, v_l_2937_);
lean_ctor_set(v_reuseFailAlloc_3202_, 4, v_l_3127_);
v___x_3189_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
v_isSharedCheck_3196_ = !lean_is_exclusive(v_l_2937_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; lean_object* v_unused_3198_; lean_object* v_unused_3199_; lean_object* v_unused_3200_; lean_object* v_unused_3201_; 
v_unused_3197_ = lean_ctor_get(v_l_2937_, 4);
lean_dec(v_unused_3197_);
v_unused_3198_ = lean_ctor_get(v_l_2937_, 3);
lean_dec(v_unused_3198_);
v_unused_3199_ = lean_ctor_get(v_l_2937_, 2);
lean_dec(v_unused_3199_);
v_unused_3200_ = lean_ctor_get(v_l_2937_, 1);
lean_dec(v_unused_3200_);
v_unused_3201_ = lean_ctor_get(v_l_2937_, 0);
lean_dec(v_unused_3201_);
v___x_3191_ = v_l_2937_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_dec(v_l_2937_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 4, v_r_3128_);
lean_ctor_set(v___x_3191_, 3, v___x_3189_);
lean_ctor_set(v___x_3191_, 2, v_v_3126_);
lean_ctor_set(v___x_3191_, 1, v_k_3125_);
lean_ctor_set(v___x_3191_, 0, v___x_3186_);
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_k_3125_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_v_3126_);
lean_ctor_set(v_reuseFailAlloc_3195_, 3, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3195_, 4, v_r_3128_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_dec_ref(v_l_3127_);
lean_del_object(v___x_3139_);
lean_dec(v_v_3126_);
lean_dec(v_k_3125_);
lean_dec(v_size_3124_);
lean_dec_ref(v_l_2937_);
lean_del_object(v___x_2940_);
lean_dec(v_v_2936_);
lean_dec(v_k_2935_);
v___x_3203_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7);
v___x_3204_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_3203_);
return v___x_3204_;
}
}
else
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_del_object(v___x_3139_);
lean_dec(v_r_3128_);
lean_dec(v_v_3126_);
lean_dec(v_k_3125_);
lean_dec(v_size_3124_);
lean_dec_ref(v_l_2937_);
lean_del_object(v___x_2940_);
lean_dec(v_v_2936_);
lean_dec(v_k_2935_);
v___x_3205_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8);
v___x_3206_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_3205_);
return v___x_3206_;
}
}
}
}
else
{
lean_object* v_size_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3217_; 
v_size_3213_ = lean_ctor_get(v_l_2937_, 0);
v___x_3214_ = lean_unsigned_to_nat(1u);
v___x_3215_ = lean_nat_add(v___x_3214_, v_size_3213_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v___x_3122_);
lean_ctor_set(v___x_2940_, 0, v___x_3215_);
v___x_3217_ = v___x_2940_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v_l_2937_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v___x_3122_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
else
{
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_l_3219_; 
v_l_3219_ = lean_ctor_get(v___x_3122_, 3);
lean_inc(v_l_3219_);
if (lean_obj_tag(v_l_3219_) == 0)
{
lean_object* v_r_3220_; 
v_r_3220_ = lean_ctor_get(v___x_3122_, 4);
lean_inc(v_r_3220_);
if (lean_obj_tag(v_r_3220_) == 0)
{
lean_object* v_size_3221_; lean_object* v_k_3222_; lean_object* v_v_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3237_; 
v_size_3221_ = lean_ctor_get(v___x_3122_, 0);
v_k_3222_ = lean_ctor_get(v___x_3122_, 1);
v_v_3223_ = lean_ctor_get(v___x_3122_, 2);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3237_ == 0)
{
lean_object* v_unused_3238_; lean_object* v_unused_3239_; 
v_unused_3238_ = lean_ctor_get(v___x_3122_, 4);
lean_dec(v_unused_3238_);
v_unused_3239_ = lean_ctor_get(v___x_3122_, 3);
lean_dec(v_unused_3239_);
v___x_3225_ = v___x_3122_;
v_isShared_3226_ = v_isSharedCheck_3237_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_v_3223_);
lean_inc(v_k_3222_);
lean_inc(v_size_3221_);
lean_dec(v___x_3122_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3237_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v_size_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v_size_3227_ = lean_ctor_get(v_l_3219_, 0);
v___x_3228_ = lean_unsigned_to_nat(1u);
v___x_3229_ = lean_nat_add(v___x_3228_, v_size_3221_);
lean_dec(v_size_3221_);
v___x_3230_ = lean_nat_add(v___x_3228_, v_size_3227_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 4, v_l_3219_);
lean_ctor_set(v___x_3225_, 3, v_l_2937_);
lean_ctor_set(v___x_3225_, 2, v_v_2936_);
lean_ctor_set(v___x_3225_, 1, v_k_2935_);
lean_ctor_set(v___x_3225_, 0, v___x_3230_);
v___x_3232_ = v___x_3225_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3236_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3236_, 3, v_l_2937_);
lean_ctor_set(v_reuseFailAlloc_3236_, 4, v_l_3219_);
v___x_3232_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3234_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v_r_3220_);
lean_ctor_set(v___x_2940_, 3, v___x_3232_);
lean_ctor_set(v___x_2940_, 2, v_v_3223_);
lean_ctor_set(v___x_2940_, 1, v_k_3222_);
lean_ctor_set(v___x_2940_, 0, v___x_3229_);
v___x_3234_ = v___x_2940_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_k_3222_);
lean_ctor_set(v_reuseFailAlloc_3235_, 2, v_v_3223_);
lean_ctor_set(v_reuseFailAlloc_3235_, 3, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3235_, 4, v_r_3220_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
else
{
lean_object* v_k_3240_; lean_object* v_v_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3265_; 
v_k_3240_ = lean_ctor_get(v___x_3122_, 1);
v_v_3241_ = lean_ctor_get(v___x_3122_, 2);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3265_ == 0)
{
lean_object* v_unused_3266_; lean_object* v_unused_3267_; lean_object* v_unused_3268_; 
v_unused_3266_ = lean_ctor_get(v___x_3122_, 4);
lean_dec(v_unused_3266_);
v_unused_3267_ = lean_ctor_get(v___x_3122_, 3);
lean_dec(v_unused_3267_);
v_unused_3268_ = lean_ctor_get(v___x_3122_, 0);
lean_dec(v_unused_3268_);
v___x_3243_ = v___x_3122_;
v_isShared_3244_ = v_isSharedCheck_3265_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_v_3241_);
lean_inc(v_k_3240_);
lean_dec(v___x_3122_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3265_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v_k_3245_; lean_object* v_v_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3261_; 
v_k_3245_ = lean_ctor_get(v_l_3219_, 1);
v_v_3246_ = lean_ctor_get(v_l_3219_, 2);
v_isSharedCheck_3261_ = !lean_is_exclusive(v_l_3219_);
if (v_isSharedCheck_3261_ == 0)
{
lean_object* v_unused_3262_; lean_object* v_unused_3263_; lean_object* v_unused_3264_; 
v_unused_3262_ = lean_ctor_get(v_l_3219_, 4);
lean_dec(v_unused_3262_);
v_unused_3263_ = lean_ctor_get(v_l_3219_, 3);
lean_dec(v_unused_3263_);
v_unused_3264_ = lean_ctor_get(v_l_3219_, 0);
lean_dec(v_unused_3264_);
v___x_3248_ = v_l_3219_;
v_isShared_3249_ = v_isSharedCheck_3261_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_v_3246_);
lean_inc(v_k_3245_);
lean_dec(v_l_3219_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3261_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3253_; 
v___x_3250_ = lean_unsigned_to_nat(3u);
v___x_3251_ = lean_unsigned_to_nat(1u);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 4, v_r_3220_);
lean_ctor_set(v___x_3248_, 3, v_r_3220_);
lean_ctor_set(v___x_3248_, 2, v_v_2936_);
lean_ctor_set(v___x_3248_, 1, v_k_2935_);
lean_ctor_set(v___x_3248_, 0, v___x_3251_);
v___x_3253_ = v___x_3248_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3260_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3260_, 3, v_r_3220_);
lean_ctor_set(v_reuseFailAlloc_3260_, 4, v_r_3220_);
v___x_3253_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3255_; 
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 3, v_r_3220_);
lean_ctor_set(v___x_3243_, 0, v___x_3251_);
v___x_3255_ = v___x_3243_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_k_3240_);
lean_ctor_set(v_reuseFailAlloc_3259_, 2, v_v_3241_);
lean_ctor_set(v_reuseFailAlloc_3259_, 3, v_r_3220_);
lean_ctor_set(v_reuseFailAlloc_3259_, 4, v_r_3220_);
v___x_3255_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3257_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v___x_3255_);
lean_ctor_set(v___x_2940_, 3, v___x_3253_);
lean_ctor_set(v___x_2940_, 2, v_v_3246_);
lean_ctor_set(v___x_2940_, 1, v_k_3245_);
lean_ctor_set(v___x_2940_, 0, v___x_3250_);
v___x_3257_ = v___x_2940_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_k_3245_);
lean_ctor_set(v_reuseFailAlloc_3258_, 2, v_v_3246_);
lean_ctor_set(v_reuseFailAlloc_3258_, 3, v___x_3253_);
lean_ctor_set(v_reuseFailAlloc_3258_, 4, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3269_; 
v_r_3269_ = lean_ctor_get(v___x_3122_, 4);
lean_inc(v_r_3269_);
if (lean_obj_tag(v_r_3269_) == 0)
{
lean_object* v_k_3270_; lean_object* v_v_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3283_; 
v_k_3270_ = lean_ctor_get(v___x_3122_, 1);
v_v_3271_ = lean_ctor_get(v___x_3122_, 2);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3283_ == 0)
{
lean_object* v_unused_3284_; lean_object* v_unused_3285_; lean_object* v_unused_3286_; 
v_unused_3284_ = lean_ctor_get(v___x_3122_, 4);
lean_dec(v_unused_3284_);
v_unused_3285_ = lean_ctor_get(v___x_3122_, 3);
lean_dec(v_unused_3285_);
v_unused_3286_ = lean_ctor_get(v___x_3122_, 0);
lean_dec(v_unused_3286_);
v___x_3273_ = v___x_3122_;
v_isShared_3274_ = v_isSharedCheck_3283_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_v_3271_);
lean_inc(v_k_3270_);
lean_dec(v___x_3122_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3283_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3275_ = lean_unsigned_to_nat(3u);
v___x_3276_ = lean_unsigned_to_nat(1u);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 4, v_l_3219_);
lean_ctor_set(v___x_3273_, 2, v_v_2936_);
lean_ctor_set(v___x_3273_, 1, v_k_2935_);
lean_ctor_set(v___x_3273_, 0, v___x_3276_);
v___x_3278_ = v___x_3273_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3282_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3282_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3282_, 3, v_l_3219_);
lean_ctor_set(v_reuseFailAlloc_3282_, 4, v_l_3219_);
v___x_3278_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3280_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v_r_3269_);
lean_ctor_set(v___x_2940_, 3, v___x_3278_);
lean_ctor_set(v___x_2940_, 2, v_v_3271_);
lean_ctor_set(v___x_2940_, 1, v_k_3270_);
lean_ctor_set(v___x_2940_, 0, v___x_3275_);
v___x_3280_ = v___x_2940_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3275_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_k_3270_);
lean_ctor_set(v_reuseFailAlloc_3281_, 2, v_v_3271_);
lean_ctor_set(v_reuseFailAlloc_3281_, 3, v___x_3278_);
lean_ctor_set(v_reuseFailAlloc_3281_, 4, v_r_3269_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
else
{
lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3287_ = lean_unsigned_to_nat(2u);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v___x_3122_);
lean_ctor_set(v___x_2940_, 3, v_r_3269_);
lean_ctor_set(v___x_2940_, 0, v___x_3287_);
v___x_3289_ = v___x_2940_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3290_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3290_, 3, v_r_3269_);
lean_ctor_set(v_reuseFailAlloc_3290_, 4, v___x_3122_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
else
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3291_ = lean_unsigned_to_nat(1u);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v___x_3122_);
lean_ctor_set(v___x_2940_, 3, v___x_3122_);
lean_ctor_set(v___x_2940_, 0, v___x_3291_);
v___x_3293_ = v___x_2940_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_3294_, 2, v_v_2936_);
lean_ctor_set(v_reuseFailAlloc_3294_, 3, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3294_, 4, v___x_3122_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
lean_dec_ref(v_cmp_2930_);
v___x_3296_ = lean_unsigned_to_nat(1u);
v___x_3297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
lean_ctor_set(v___x_3297_, 1, v_k_2931_);
lean_ctor_set(v___x_3297_, 2, v_v_2932_);
lean_ctor_set(v___x_3297_, 3, v_t_2933_);
lean_ctor_set(v___x_3297_, 4, v_t_2933_);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(lean_object* v_cmp_3298_, lean_object* v_init_3299_, lean_object* v_x_3300_){
_start:
{
if (lean_obj_tag(v_x_3300_) == 0)
{
lean_object* v_k_3301_; lean_object* v_v_3302_; lean_object* v_l_3303_; lean_object* v_r_3304_; lean_object* v___x_3305_; lean_object* v_a_3306_; lean_object* v_r_3307_; 
v_k_3301_ = lean_ctor_get(v_x_3300_, 1);
lean_inc(v_k_3301_);
v_v_3302_ = lean_ctor_get(v_x_3300_, 2);
lean_inc(v_v_3302_);
v_l_3303_ = lean_ctor_get(v_x_3300_, 3);
lean_inc(v_l_3303_);
v_r_3304_ = lean_ctor_get(v_x_3300_, 4);
lean_inc(v_r_3304_);
lean_dec_ref(v_x_3300_);
lean_inc_ref(v_cmp_3298_);
v___x_3305_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3298_, v_init_3299_, v_l_3303_);
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref(v___x_3305_);
lean_inc_ref(v_cmp_3298_);
v_r_3307_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3298_, v_k_3301_, v_v_3302_, v_a_3306_);
v_init_3299_ = v_r_3307_;
v_x_3300_ = v_r_3304_;
goto _start;
}
else
{
lean_object* v___x_3309_; 
lean_dec_ref(v_cmp_3298_);
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v_init_3299_);
return v___x_3309_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(lean_object* v_cmp_3310_, lean_object* v_k_3311_, lean_object* v_t_3312_){
_start:
{
if (lean_obj_tag(v_t_3312_) == 0)
{
lean_object* v_k_3313_; lean_object* v_l_3314_; lean_object* v_r_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; 
v_k_3313_ = lean_ctor_get(v_t_3312_, 1);
lean_inc(v_k_3313_);
v_l_3314_ = lean_ctor_get(v_t_3312_, 3);
lean_inc(v_l_3314_);
v_r_3315_ = lean_ctor_get(v_t_3312_, 4);
lean_inc(v_r_3315_);
lean_dec_ref(v_t_3312_);
lean_inc_ref(v_cmp_3310_);
lean_inc(v_k_3311_);
v___x_3316_ = lean_apply_2(v_cmp_3310_, v_k_3311_, v_k_3313_);
v___x_3317_ = lean_unbox(v___x_3316_);
switch(v___x_3317_)
{
case 0:
{
lean_dec(v_r_3315_);
v_t_3312_ = v_l_3314_;
goto _start;
}
case 1:
{
uint8_t v___x_3319_; 
lean_dec(v_r_3315_);
lean_dec(v_l_3314_);
lean_dec(v_k_3311_);
lean_dec_ref(v_cmp_3310_);
v___x_3319_ = 1;
return v___x_3319_;
}
default: 
{
lean_dec(v_l_3314_);
v_t_3312_ = v_r_3315_;
goto _start;
}
}
}
else
{
uint8_t v___x_3321_; 
lean_dec(v_k_3311_);
lean_dec_ref(v_cmp_3310_);
v___x_3321_ = 0;
return v___x_3321_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_3322_, lean_object* v_k_3323_, lean_object* v_t_3324_){
_start:
{
uint8_t v_res_3325_; lean_object* v_r_3326_; 
v_res_3325_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3322_, v_k_3323_, v_t_3324_);
v_r_3326_ = lean_box(v_res_3325_);
return v_r_3326_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(lean_object* v_cmp_3327_, lean_object* v_init_3328_, lean_object* v_x_3329_){
_start:
{
if (lean_obj_tag(v_x_3329_) == 0)
{
lean_object* v_k_3330_; lean_object* v_v_3331_; lean_object* v_l_3332_; lean_object* v_r_3333_; lean_object* v___x_3334_; lean_object* v_a_3335_; uint8_t v___x_3336_; 
v_k_3330_ = lean_ctor_get(v_x_3329_, 1);
lean_inc(v_k_3330_);
v_v_3331_ = lean_ctor_get(v_x_3329_, 2);
lean_inc(v_v_3331_);
v_l_3332_ = lean_ctor_get(v_x_3329_, 3);
lean_inc(v_l_3332_);
v_r_3333_ = lean_ctor_get(v_x_3329_, 4);
lean_inc(v_r_3333_);
lean_dec_ref(v_x_3329_);
lean_inc_ref(v_cmp_3327_);
v___x_3334_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3327_, v_init_3328_, v_l_3332_);
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref(v___x_3334_);
lean_inc(v_a_3335_);
lean_inc(v_k_3330_);
lean_inc_ref(v_cmp_3327_);
v___x_3336_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3327_, v_k_3330_, v_a_3335_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; 
lean_inc_ref(v_cmp_3327_);
v___x_3337_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3327_, v_k_3330_, v_v_3331_, v_a_3335_);
v_init_3328_ = v___x_3337_;
v_x_3329_ = v_r_3333_;
goto _start;
}
else
{
lean_dec(v_v_3331_);
lean_dec(v_k_3330_);
v_init_3328_ = v_a_3335_;
v_x_3329_ = v_r_3333_;
goto _start;
}
}
else
{
lean_object* v___x_3340_; 
lean_dec_ref(v_cmp_3327_);
v___x_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3340_, 0, v_init_3328_);
return v___x_3340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(lean_object* v_cmp_3341_, lean_object* v_t_u2081_3342_, lean_object* v_t_u2082_3343_){
_start:
{
lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3353_; 
if (lean_obj_tag(v_t_u2081_3342_) == 0)
{
lean_object* v_size_3356_; 
v_size_3356_ = lean_ctor_get(v_t_u2081_3342_, 0);
lean_inc(v_size_3356_);
v___y_3353_ = v_size_3356_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_unsigned_to_nat(0u);
v___y_3353_ = v___x_3357_;
goto v___jp_3352_;
}
v___jp_3344_:
{
uint8_t v___x_3347_; 
v___x_3347_ = lean_nat_dec_le(v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; lean_object* v_a_3349_; 
v___x_3348_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3341_, v_t_u2081_3342_, v_t_u2082_3343_);
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref(v___x_3348_);
return v_a_3349_;
}
else
{
lean_object* v___x_3350_; lean_object* v_a_3351_; 
v___x_3350_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3341_, v_t_u2082_3343_, v_t_u2081_3342_);
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref(v___x_3350_);
return v_a_3351_;
}
}
v___jp_3352_:
{
if (lean_obj_tag(v_t_u2082_3343_) == 0)
{
lean_object* v_size_3354_; 
v_size_3354_ = lean_ctor_get(v_t_u2082_3343_, 0);
lean_inc(v_size_3354_);
v___y_3345_ = v___y_3353_;
v___y_3346_ = v_size_3354_;
goto v___jp_3344_;
}
else
{
lean_object* v___x_3355_; 
v___x_3355_ = lean_unsigned_to_nat(0u);
v___y_3345_ = v___y_3353_;
v___y_3346_ = v___x_3355_;
goto v___jp_3344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union___redArg(lean_object* v_cmp_3358_, lean_object* v_t_u2081_3359_, lean_object* v_t_u2082_3360_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3358_, v_t_u2081_3359_, v_t_u2082_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union(lean_object* v_00_u03b1_3362_, lean_object* v_00_u03b2_3363_, lean_object* v_cmp_3364_, lean_object* v_t_u2081_3365_, lean_object* v_t_u2082_3366_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3364_, v_t_u2081_3365_, v_t_u2082_3366_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0(lean_object* v_00_u03b1_3368_, lean_object* v_cmp_3369_, lean_object* v_00_u03b2_3370_, lean_object* v_t_u2081_3371_, lean_object* v_t_u2082_3372_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3369_, v_t_u2081_3371_, v_t_u2082_3372_);
return v___x_3373_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0(lean_object* v_00_u03b1_3374_, lean_object* v_cmp_3375_, lean_object* v_00_u03b2_3376_, lean_object* v_k_3377_, lean_object* v_t_3378_){
_start:
{
uint8_t v___x_3379_; 
v___x_3379_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3375_, v_k_3377_, v_t_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3380_, lean_object* v_cmp_3381_, lean_object* v_00_u03b2_3382_, lean_object* v_k_3383_, lean_object* v_t_3384_){
_start:
{
uint8_t v_res_3385_; lean_object* v_r_3386_; 
v_res_3385_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0(v_00_u03b1_3380_, v_cmp_3381_, v_00_u03b2_3382_, v_k_3383_, v_t_3384_);
v_r_3386_ = lean_box(v_res_3385_);
return v_r_3386_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3387_, lean_object* v_00_u03b2_3388_, lean_object* v_msg_3389_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v_msg_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1(lean_object* v_00_u03b1_3391_, lean_object* v_cmp_3392_, lean_object* v_00_u03b2_3393_, lean_object* v_k_3394_, lean_object* v_v_3395_, lean_object* v_t_3396_){
_start:
{
lean_object* v___x_3397_; 
v___x_3397_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3392_, v_k_3394_, v_v_3395_, v_t_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2(lean_object* v_00_u03b1_3398_, lean_object* v_00_u03b2_3399_, lean_object* v_cmp_3400_, lean_object* v_init_3401_, lean_object* v_x_3402_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3400_, v_init_3401_, v_x_3402_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3(lean_object* v_00_u03b1_3404_, lean_object* v_00_u03b2_3405_, lean_object* v_cmp_3406_, lean_object* v_init_3407_, lean_object* v_x_3408_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3406_, v_init_3407_, v_x_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion___redArg(lean_object* v_cmp_3410_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_3411_, 0, lean_box(0));
lean_closure_set(v___x_3411_, 1, lean_box(0));
lean_closure_set(v___x_3411_, 2, v_cmp_3410_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion(lean_object* v_00_u03b1_3412_, lean_object* v_00_u03b2_3413_, lean_object* v_cmp_3414_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_3415_, 0, lean_box(0));
lean_closure_set(v___x_3415_, 1, lean_box(0));
lean_closure_set(v___x_3415_, 2, v_cmp_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(lean_object* v_cmp_3416_, lean_object* v_k_3417_, lean_object* v_v_3418_, lean_object* v_t_3419_){
_start:
{
if (lean_obj_tag(v_t_3419_) == 0)
{
lean_object* v_size_3420_; lean_object* v_k_3421_; lean_object* v_v_3422_; lean_object* v_l_3423_; lean_object* v_r_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3705_; 
v_size_3420_ = lean_ctor_get(v_t_3419_, 0);
v_k_3421_ = lean_ctor_get(v_t_3419_, 1);
v_v_3422_ = lean_ctor_get(v_t_3419_, 2);
v_l_3423_ = lean_ctor_get(v_t_3419_, 3);
v_r_3424_ = lean_ctor_get(v_t_3419_, 4);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_t_3419_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3426_ = v_t_3419_;
v_isShared_3427_ = v_isSharedCheck_3705_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_r_3424_);
lean_inc(v_l_3423_);
lean_inc(v_v_3422_);
lean_inc(v_k_3421_);
lean_inc(v_size_3420_);
lean_dec(v_t_3419_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3705_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; uint8_t v___x_3429_; 
lean_inc_ref(v_cmp_3416_);
lean_inc(v_k_3421_);
lean_inc(v_k_3417_);
v___x_3428_ = lean_apply_2(v_cmp_3416_, v_k_3417_, v_k_3421_);
v___x_3429_ = lean_unbox(v___x_3428_);
switch(v___x_3429_)
{
case 0:
{
lean_object* v_impl_3430_; lean_object* v___x_3431_; 
lean_dec(v_size_3420_);
v_impl_3430_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3416_, v_k_3417_, v_v_3418_, v_l_3423_);
v___x_3431_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3424_) == 0)
{
lean_object* v_size_3432_; lean_object* v_size_3433_; lean_object* v_k_3434_; lean_object* v_v_3435_; lean_object* v_l_3436_; lean_object* v_r_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; uint8_t v___x_3440_; 
v_size_3432_ = lean_ctor_get(v_r_3424_, 0);
v_size_3433_ = lean_ctor_get(v_impl_3430_, 0);
lean_inc(v_size_3433_);
v_k_3434_ = lean_ctor_get(v_impl_3430_, 1);
lean_inc(v_k_3434_);
v_v_3435_ = lean_ctor_get(v_impl_3430_, 2);
lean_inc(v_v_3435_);
v_l_3436_ = lean_ctor_get(v_impl_3430_, 3);
lean_inc(v_l_3436_);
v_r_3437_ = lean_ctor_get(v_impl_3430_, 4);
lean_inc(v_r_3437_);
v___x_3438_ = lean_unsigned_to_nat(3u);
v___x_3439_ = lean_nat_mul(v___x_3438_, v_size_3432_);
v___x_3440_ = lean_nat_dec_lt(v___x_3439_, v_size_3433_);
lean_dec(v___x_3439_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3444_; 
lean_dec(v_r_3437_);
lean_dec(v_l_3436_);
lean_dec(v_v_3435_);
lean_dec(v_k_3434_);
v___x_3441_ = lean_nat_add(v___x_3431_, v_size_3433_);
lean_dec(v_size_3433_);
v___x_3442_ = lean_nat_add(v___x_3441_, v_size_3432_);
lean_dec(v___x_3441_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 3, v_impl_3430_);
lean_ctor_set(v___x_3426_, 0, v___x_3442_);
v___x_3444_ = v___x_3426_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3445_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3445_, 3, v_impl_3430_);
lean_ctor_set(v_reuseFailAlloc_3445_, 4, v_r_3424_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
else
{
lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3511_; 
v_isSharedCheck_3511_ = !lean_is_exclusive(v_impl_3430_);
if (v_isSharedCheck_3511_ == 0)
{
lean_object* v_unused_3512_; lean_object* v_unused_3513_; lean_object* v_unused_3514_; lean_object* v_unused_3515_; lean_object* v_unused_3516_; 
v_unused_3512_ = lean_ctor_get(v_impl_3430_, 4);
lean_dec(v_unused_3512_);
v_unused_3513_ = lean_ctor_get(v_impl_3430_, 3);
lean_dec(v_unused_3513_);
v_unused_3514_ = lean_ctor_get(v_impl_3430_, 2);
lean_dec(v_unused_3514_);
v_unused_3515_ = lean_ctor_get(v_impl_3430_, 1);
lean_dec(v_unused_3515_);
v_unused_3516_ = lean_ctor_get(v_impl_3430_, 0);
lean_dec(v_unused_3516_);
v___x_3447_ = v_impl_3430_;
v_isShared_3448_ = v_isSharedCheck_3511_;
goto v_resetjp_3446_;
}
else
{
lean_dec(v_impl_3430_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3511_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v_size_3449_; lean_object* v_size_3450_; lean_object* v_k_3451_; lean_object* v_v_3452_; lean_object* v_l_3453_; lean_object* v_r_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; 
v_size_3449_ = lean_ctor_get(v_l_3436_, 0);
v_size_3450_ = lean_ctor_get(v_r_3437_, 0);
v_k_3451_ = lean_ctor_get(v_r_3437_, 1);
v_v_3452_ = lean_ctor_get(v_r_3437_, 2);
v_l_3453_ = lean_ctor_get(v_r_3437_, 3);
v_r_3454_ = lean_ctor_get(v_r_3437_, 4);
v___x_3455_ = lean_unsigned_to_nat(2u);
v___x_3456_ = lean_nat_mul(v___x_3455_, v_size_3449_);
v___x_3457_ = lean_nat_dec_lt(v_size_3450_, v___x_3456_);
lean_dec(v___x_3456_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3486_; 
lean_inc(v_r_3454_);
lean_inc(v_l_3453_);
lean_inc(v_v_3452_);
lean_inc(v_k_3451_);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_r_3437_);
if (v_isSharedCheck_3486_ == 0)
{
lean_object* v_unused_3487_; lean_object* v_unused_3488_; lean_object* v_unused_3489_; lean_object* v_unused_3490_; lean_object* v_unused_3491_; 
v_unused_3487_ = lean_ctor_get(v_r_3437_, 4);
lean_dec(v_unused_3487_);
v_unused_3488_ = lean_ctor_get(v_r_3437_, 3);
lean_dec(v_unused_3488_);
v_unused_3489_ = lean_ctor_get(v_r_3437_, 2);
lean_dec(v_unused_3489_);
v_unused_3490_ = lean_ctor_get(v_r_3437_, 1);
lean_dec(v_unused_3490_);
v_unused_3491_ = lean_ctor_get(v_r_3437_, 0);
lean_dec(v_unused_3491_);
v___x_3459_ = v_r_3437_;
v_isShared_3460_ = v_isSharedCheck_3486_;
goto v_resetjp_3458_;
}
else
{
lean_dec(v_r_3437_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3486_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___x_3474_; lean_object* v___y_3476_; 
v___x_3461_ = lean_nat_add(v___x_3431_, v_size_3433_);
lean_dec(v_size_3433_);
v___x_3462_ = lean_nat_add(v___x_3461_, v_size_3432_);
lean_dec(v___x_3461_);
v___x_3474_ = lean_nat_add(v___x_3431_, v_size_3449_);
if (lean_obj_tag(v_l_3453_) == 0)
{
lean_object* v_size_3484_; 
v_size_3484_ = lean_ctor_get(v_l_3453_, 0);
lean_inc(v_size_3484_);
v___y_3476_ = v_size_3484_;
goto v___jp_3475_;
}
else
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_unsigned_to_nat(0u);
v___y_3476_ = v___x_3485_;
goto v___jp_3475_;
}
v___jp_3463_:
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3467_ = lean_nat_add(v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec(v___y_3465_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 4, v_r_3424_);
lean_ctor_set(v___x_3459_, 3, v_r_3454_);
lean_ctor_set(v___x_3459_, 2, v_v_3422_);
lean_ctor_set(v___x_3459_, 1, v_k_3421_);
lean_ctor_set(v___x_3459_, 0, v___x_3467_);
v___x_3469_ = v___x_3459_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3467_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3473_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3473_, 3, v_r_3454_);
lean_ctor_set(v_reuseFailAlloc_3473_, 4, v_r_3424_);
v___x_3469_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3471_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 4, v___x_3469_);
lean_ctor_set(v___x_3447_, 3, v___y_3464_);
lean_ctor_set(v___x_3447_, 2, v_v_3452_);
lean_ctor_set(v___x_3447_, 1, v_k_3451_);
lean_ctor_set(v___x_3447_, 0, v___x_3462_);
v___x_3471_ = v___x_3447_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_k_3451_);
lean_ctor_set(v_reuseFailAlloc_3472_, 2, v_v_3452_);
lean_ctor_set(v_reuseFailAlloc_3472_, 3, v___y_3464_);
lean_ctor_set(v_reuseFailAlloc_3472_, 4, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
v___jp_3475_:
{
lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3477_ = lean_nat_add(v___x_3474_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec(v___x_3474_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 4, v_l_3453_);
lean_ctor_set(v___x_3426_, 3, v_l_3436_);
lean_ctor_set(v___x_3426_, 2, v_v_3435_);
lean_ctor_set(v___x_3426_, 1, v_k_3434_);
lean_ctor_set(v___x_3426_, 0, v___x_3477_);
v___x_3479_ = v___x_3426_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_k_3434_);
lean_ctor_set(v_reuseFailAlloc_3483_, 2, v_v_3435_);
lean_ctor_set(v_reuseFailAlloc_3483_, 3, v_l_3436_);
lean_ctor_set(v_reuseFailAlloc_3483_, 4, v_l_3453_);
v___x_3479_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; 
v___x_3480_ = lean_nat_add(v___x_3431_, v_size_3432_);
if (lean_obj_tag(v_r_3454_) == 0)
{
lean_object* v_size_3481_; 
v_size_3481_ = lean_ctor_get(v_r_3454_, 0);
lean_inc(v_size_3481_);
v___y_3464_ = v___x_3479_;
v___y_3465_ = v___x_3480_;
v___y_3466_ = v_size_3481_;
goto v___jp_3463_;
}
else
{
lean_object* v___x_3482_; 
v___x_3482_ = lean_unsigned_to_nat(0u);
v___y_3464_ = v___x_3479_;
v___y_3465_ = v___x_3480_;
v___y_3466_ = v___x_3482_;
goto v___jp_3463_;
}
}
}
}
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
lean_del_object(v___x_3426_);
v___x_3492_ = lean_nat_add(v___x_3431_, v_size_3433_);
lean_dec(v_size_3433_);
v___x_3493_ = lean_nat_add(v___x_3492_, v_size_3432_);
lean_dec(v___x_3492_);
v___x_3494_ = lean_nat_add(v___x_3431_, v_size_3432_);
v___x_3495_ = lean_nat_add(v___x_3494_, v_size_3450_);
lean_dec(v___x_3494_);
lean_inc_ref(v_r_3424_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 4, v_r_3424_);
lean_ctor_set(v___x_3447_, 3, v_r_3437_);
lean_ctor_set(v___x_3447_, 2, v_v_3422_);
lean_ctor_set(v___x_3447_, 1, v_k_3421_);
lean_ctor_set(v___x_3447_, 0, v___x_3495_);
v___x_3497_ = v___x_3447_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3510_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3510_, 3, v_r_3437_);
lean_ctor_set(v_reuseFailAlloc_3510_, 4, v_r_3424_);
v___x_3497_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
v_isSharedCheck_3504_ = !lean_is_exclusive(v_r_3424_);
if (v_isSharedCheck_3504_ == 0)
{
lean_object* v_unused_3505_; lean_object* v_unused_3506_; lean_object* v_unused_3507_; lean_object* v_unused_3508_; lean_object* v_unused_3509_; 
v_unused_3505_ = lean_ctor_get(v_r_3424_, 4);
lean_dec(v_unused_3505_);
v_unused_3506_ = lean_ctor_get(v_r_3424_, 3);
lean_dec(v_unused_3506_);
v_unused_3507_ = lean_ctor_get(v_r_3424_, 2);
lean_dec(v_unused_3507_);
v_unused_3508_ = lean_ctor_get(v_r_3424_, 1);
lean_dec(v_unused_3508_);
v_unused_3509_ = lean_ctor_get(v_r_3424_, 0);
lean_dec(v_unused_3509_);
v___x_3499_ = v_r_3424_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_dec(v_r_3424_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 4, v___x_3497_);
lean_ctor_set(v___x_3499_, 3, v_l_3436_);
lean_ctor_set(v___x_3499_, 2, v_v_3435_);
lean_ctor_set(v___x_3499_, 1, v_k_3434_);
lean_ctor_set(v___x_3499_, 0, v___x_3493_);
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_k_3434_);
lean_ctor_set(v_reuseFailAlloc_3503_, 2, v_v_3435_);
lean_ctor_set(v_reuseFailAlloc_3503_, 3, v_l_3436_);
lean_ctor_set(v_reuseFailAlloc_3503_, 4, v___x_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3517_; 
v_l_3517_ = lean_ctor_get(v_impl_3430_, 3);
lean_inc(v_l_3517_);
if (lean_obj_tag(v_l_3517_) == 0)
{
lean_object* v_r_3518_; lean_object* v_k_3519_; lean_object* v_v_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3531_; 
v_r_3518_ = lean_ctor_get(v_impl_3430_, 4);
v_k_3519_ = lean_ctor_get(v_impl_3430_, 1);
v_v_3520_ = lean_ctor_get(v_impl_3430_, 2);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_impl_3430_);
if (v_isSharedCheck_3531_ == 0)
{
lean_object* v_unused_3532_; lean_object* v_unused_3533_; 
v_unused_3532_ = lean_ctor_get(v_impl_3430_, 3);
lean_dec(v_unused_3532_);
v_unused_3533_ = lean_ctor_get(v_impl_3430_, 0);
lean_dec(v_unused_3533_);
v___x_3522_ = v_impl_3430_;
v_isShared_3523_ = v_isSharedCheck_3531_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_r_3518_);
lean_inc(v_v_3520_);
lean_inc(v_k_3519_);
lean_dec(v_impl_3430_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3531_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3524_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3518_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 3, v_r_3518_);
lean_ctor_set(v___x_3522_, 2, v_v_3422_);
lean_ctor_set(v___x_3522_, 1, v_k_3421_);
lean_ctor_set(v___x_3522_, 0, v___x_3431_);
v___x_3526_ = v___x_3522_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3530_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3530_, 3, v_r_3518_);
lean_ctor_set(v_reuseFailAlloc_3530_, 4, v_r_3518_);
v___x_3526_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3528_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 4, v___x_3526_);
lean_ctor_set(v___x_3426_, 3, v_l_3517_);
lean_ctor_set(v___x_3426_, 2, v_v_3520_);
lean_ctor_set(v___x_3426_, 1, v_k_3519_);
lean_ctor_set(v___x_3426_, 0, v___x_3524_);
v___x_3528_ = v___x_3426_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3524_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_k_3519_);
lean_ctor_set(v_reuseFailAlloc_3529_, 2, v_v_3520_);
lean_ctor_set(v_reuseFailAlloc_3529_, 3, v_l_3517_);
lean_ctor_set(v_reuseFailAlloc_3529_, 4, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
else
{
lean_object* v_r_3534_; 
v_r_3534_ = lean_ctor_get(v_impl_3430_, 4);
lean_inc(v_r_3534_);
if (lean_obj_tag(v_r_3534_) == 0)
{
lean_object* v_k_3535_; lean_object* v_v_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3559_; 
v_k_3535_ = lean_ctor_get(v_impl_3430_, 1);
v_v_3536_ = lean_ctor_get(v_impl_3430_, 2);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_impl_3430_);
if (v_isSharedCheck_3559_ == 0)
{
lean_object* v_unused_3560_; lean_object* v_unused_3561_; lean_object* v_unused_3562_; 
v_unused_3560_ = lean_ctor_get(v_impl_3430_, 4);
lean_dec(v_unused_3560_);
v_unused_3561_ = lean_ctor_get(v_impl_3430_, 3);
lean_dec(v_unused_3561_);
v_unused_3562_ = lean_ctor_get(v_impl_3430_, 0);
lean_dec(v_unused_3562_);
v___x_3538_ = v_impl_3430_;
v_isShared_3539_ = v_isSharedCheck_3559_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_v_3536_);
lean_inc(v_k_3535_);
lean_dec(v_impl_3430_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3559_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v_k_3540_; lean_object* v_v_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3555_; 
v_k_3540_ = lean_ctor_get(v_r_3534_, 1);
v_v_3541_ = lean_ctor_get(v_r_3534_, 2);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_r_3534_);
if (v_isSharedCheck_3555_ == 0)
{
lean_object* v_unused_3556_; lean_object* v_unused_3557_; lean_object* v_unused_3558_; 
v_unused_3556_ = lean_ctor_get(v_r_3534_, 4);
lean_dec(v_unused_3556_);
v_unused_3557_ = lean_ctor_get(v_r_3534_, 3);
lean_dec(v_unused_3557_);
v_unused_3558_ = lean_ctor_get(v_r_3534_, 0);
lean_dec(v_unused_3558_);
v___x_3543_ = v_r_3534_;
v_isShared_3544_ = v_isSharedCheck_3555_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_v_3541_);
lean_inc(v_k_3540_);
lean_dec(v_r_3534_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3555_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3545_; lean_object* v___x_3547_; 
v___x_3545_ = lean_unsigned_to_nat(3u);
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 4, v_l_3517_);
lean_ctor_set(v___x_3543_, 3, v_l_3517_);
lean_ctor_set(v___x_3543_, 2, v_v_3536_);
lean_ctor_set(v___x_3543_, 1, v_k_3535_);
lean_ctor_set(v___x_3543_, 0, v___x_3431_);
v___x_3547_ = v___x_3543_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_k_3535_);
lean_ctor_set(v_reuseFailAlloc_3554_, 2, v_v_3536_);
lean_ctor_set(v_reuseFailAlloc_3554_, 3, v_l_3517_);
lean_ctor_set(v_reuseFailAlloc_3554_, 4, v_l_3517_);
v___x_3547_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3549_; 
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 4, v_l_3517_);
lean_ctor_set(v___x_3538_, 2, v_v_3422_);
lean_ctor_set(v___x_3538_, 1, v_k_3421_);
lean_ctor_set(v___x_3538_, 0, v___x_3431_);
v___x_3549_ = v___x_3538_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3553_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3553_, 3, v_l_3517_);
lean_ctor_set(v_reuseFailAlloc_3553_, 4, v_l_3517_);
v___x_3549_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3551_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 4, v___x_3549_);
lean_ctor_set(v___x_3426_, 3, v___x_3547_);
lean_ctor_set(v___x_3426_, 2, v_v_3541_);
lean_ctor_set(v___x_3426_, 1, v_k_3540_);
lean_ctor_set(v___x_3426_, 0, v___x_3545_);
v___x_3551_ = v___x_3426_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_k_3540_);
lean_ctor_set(v_reuseFailAlloc_3552_, 2, v_v_3541_);
lean_ctor_set(v_reuseFailAlloc_3552_, 3, v___x_3547_);
lean_ctor_set(v_reuseFailAlloc_3552_, 4, v___x_3549_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3565_; 
v___x_3563_ = lean_unsigned_to_nat(2u);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 4, v_r_3534_);
lean_ctor_set(v___x_3426_, 3, v_impl_3430_);
lean_ctor_set(v___x_3426_, 0, v___x_3563_);
v___x_3565_ = v___x_3426_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3563_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3566_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3566_, 3, v_impl_3430_);
lean_ctor_set(v_reuseFailAlloc_3566_, 4, v_r_3534_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3568_; 
lean_dec(v_v_3422_);
lean_dec(v_k_3421_);
lean_dec_ref(v_cmp_3416_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 2, v_v_3418_);
lean_ctor_set(v___x_3426_, 1, v_k_3417_);
v___x_3568_ = v___x_3426_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_size_3420_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_k_3417_);
lean_ctor_set(v_reuseFailAlloc_3569_, 2, v_v_3418_);
lean_ctor_set(v_reuseFailAlloc_3569_, 3, v_l_3423_);
lean_ctor_set(v_reuseFailAlloc_3569_, 4, v_r_3424_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
default: 
{
lean_object* v_impl_3570_; lean_object* v___x_3571_; 
lean_dec(v_size_3420_);
v_impl_3570_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3416_, v_k_3417_, v_v_3418_, v_r_3424_);
v___x_3571_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3423_) == 0)
{
lean_object* v_size_3572_; lean_object* v_size_3573_; lean_object* v_k_3574_; lean_object* v_v_3575_; lean_object* v_l_3576_; lean_object* v_r_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; uint8_t v___x_3580_; 
v_size_3572_ = lean_ctor_get(v_l_3423_, 0);
v_size_3573_ = lean_ctor_get(v_impl_3570_, 0);
lean_inc(v_size_3573_);
v_k_3574_ = lean_ctor_get(v_impl_3570_, 1);
lean_inc(v_k_3574_);
v_v_3575_ = lean_ctor_get(v_impl_3570_, 2);
lean_inc(v_v_3575_);
v_l_3576_ = lean_ctor_get(v_impl_3570_, 3);
lean_inc(v_l_3576_);
v_r_3577_ = lean_ctor_get(v_impl_3570_, 4);
lean_inc(v_r_3577_);
v___x_3578_ = lean_unsigned_to_nat(3u);
v___x_3579_ = lean_nat_mul(v___x_3578_, v_size_3572_);
v___x_3580_ = lean_nat_dec_lt(v___x_3579_, v_size_3573_);
lean_dec(v___x_3579_);
if (v___x_3580_ == 0)
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3584_; 
lean_dec(v_r_3577_);
lean_dec(v_l_3576_);
lean_dec(v_v_3575_);
lean_dec(v_k_3574_);
v___x_3581_ = lean_nat_add(v___x_3571_, v_size_3572_);
v___x_3582_ = lean_nat_add(v___x_3581_, v_size_3573_);
lean_dec(v_size_3573_);
lean_dec(v___x_3581_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 4, v_impl_3570_);
lean_ctor_set(v___x_3426_, 0, v___x_3582_);
v___x_3584_ = v___x_3426_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3585_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3585_, 3, v_l_3423_);
lean_ctor_set(v_reuseFailAlloc_3585_, 4, v_impl_3570_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
else
{
lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3649_; 
v_isSharedCheck_3649_ = !lean_is_exclusive(v_impl_3570_);
if (v_isSharedCheck_3649_ == 0)
{
lean_object* v_unused_3650_; lean_object* v_unused_3651_; lean_object* v_unused_3652_; lean_object* v_unused_3653_; lean_object* v_unused_3654_; 
v_unused_3650_ = lean_ctor_get(v_impl_3570_, 4);
lean_dec(v_unused_3650_);
v_unused_3651_ = lean_ctor_get(v_impl_3570_, 3);
lean_dec(v_unused_3651_);
v_unused_3652_ = lean_ctor_get(v_impl_3570_, 2);
lean_dec(v_unused_3652_);
v_unused_3653_ = lean_ctor_get(v_impl_3570_, 1);
lean_dec(v_unused_3653_);
v_unused_3654_ = lean_ctor_get(v_impl_3570_, 0);
lean_dec(v_unused_3654_);
v___x_3587_ = v_impl_3570_;
v_isShared_3588_ = v_isSharedCheck_3649_;
goto v_resetjp_3586_;
}
else
{
lean_dec(v_impl_3570_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3649_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v_size_3589_; lean_object* v_k_3590_; lean_object* v_v_3591_; lean_object* v_l_3592_; lean_object* v_r_3593_; lean_object* v_size_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; uint8_t v___x_3597_; 
v_size_3589_ = lean_ctor_get(v_l_3576_, 0);
v_k_3590_ = lean_ctor_get(v_l_3576_, 1);
v_v_3591_ = lean_ctor_get(v_l_3576_, 2);
v_l_3592_ = lean_ctor_get(v_l_3576_, 3);
v_r_3593_ = lean_ctor_get(v_l_3576_, 4);
v_size_3594_ = lean_ctor_get(v_r_3577_, 0);
v___x_3595_ = lean_unsigned_to_nat(2u);
v___x_3596_ = lean_nat_mul(v___x_3595_, v_size_3594_);
v___x_3597_ = lean_nat_dec_lt(v_size_3589_, v___x_3596_);
lean_dec(v___x_3596_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3625_; 
lean_inc(v_r_3593_);
lean_inc(v_l_3592_);
lean_inc(v_v_3591_);
lean_inc(v_k_3590_);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_l_3576_);
if (v_isSharedCheck_3625_ == 0)
{
lean_object* v_unused_3626_; lean_object* v_unused_3627_; lean_object* v_unused_3628_; lean_object* v_unused_3629_; lean_object* v_unused_3630_; 
v_unused_3626_ = lean_ctor_get(v_l_3576_, 4);
lean_dec(v_unused_3626_);
v_unused_3627_ = lean_ctor_get(v_l_3576_, 3);
lean_dec(v_unused_3627_);
v_unused_3628_ = lean_ctor_get(v_l_3576_, 2);
lean_dec(v_unused_3628_);
v_unused_3629_ = lean_ctor_get(v_l_3576_, 1);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_l_3576_, 0);
lean_dec(v_unused_3630_);
v___x_3599_ = v_l_3576_;
v_isShared_3600_ = v_isSharedCheck_3625_;
goto v_resetjp_3598_;
}
else
{
lean_dec(v_l_3576_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3625_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3615_; 
v___x_3601_ = lean_nat_add(v___x_3571_, v_size_3572_);
v___x_3602_ = lean_nat_add(v___x_3601_, v_size_3573_);
lean_dec(v_size_3573_);
if (lean_obj_tag(v_l_3592_) == 0)
{
lean_object* v_size_3623_; 
v_size_3623_ = lean_ctor_get(v_l_3592_, 0);
lean_inc(v_size_3623_);
v___y_3615_ = v_size_3623_;
goto v___jp_3614_;
}
else
{
lean_object* v___x_3624_; 
v___x_3624_ = lean_unsigned_to_nat(0u);
v___y_3615_ = v___x_3624_;
goto v___jp_3614_;
}
v___jp_3603_:
{
lean_object* v___x_3607_; lean_object* v___x_3609_; 
v___x_3607_ = lean_nat_add(v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec(v___y_3605_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 4, v_r_3577_);
lean_ctor_set(v___x_3599_, 3, v_r_3593_);
lean_ctor_set(v___x_3599_, 2, v_v_3575_);
lean_ctor_set(v___x_3599_, 1, v_k_3574_);
lean_ctor_set(v___x_3599_, 0, v___x_3607_);
v___x_3609_ = v___x_3599_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_k_3574_);
lean_ctor_set(v_reuseFailAlloc_3613_, 2, v_v_3575_);
lean_ctor_set(v_reuseFailAlloc_3613_, 3, v_r_3593_);
lean_ctor_set(v_reuseFailAlloc_3613_, 4, v_r_3577_);
v___x_3609_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___x_3611_; 
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 4, v___x_3609_);
lean_ctor_set(v___x_3587_, 3, v___y_3604_);
lean_ctor_set(v___x_3587_, 2, v_v_3591_);
lean_ctor_set(v___x_3587_, 1, v_k_3590_);
lean_ctor_set(v___x_3587_, 0, v___x_3602_);
v___x_3611_ = v___x_3587_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_k_3590_);
lean_ctor_set(v_reuseFailAlloc_3612_, 2, v_v_3591_);
lean_ctor_set(v_reuseFailAlloc_3612_, 3, v___y_3604_);
lean_ctor_set(v_reuseFailAlloc_3612_, 4, v___x_3609_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
v___jp_3614_:
{
lean_object* v___x_3616_; lean_object* v___x_3618_; 
v___x_3616_ = lean_nat_add(v___x_3601_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec(v___x_3601_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 4, v_l_3592_);
lean_ctor_set(v___x_3426_, 0, v___x_3616_);
v___x_3618_ = v___x_3426_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3616_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3622_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3622_, 3, v_l_3423_);
lean_ctor_set(v_reuseFailAlloc_3622_, 4, v_l_3592_);
v___x_3618_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_nat_add(v___x_3571_, v_size_3594_);
if (lean_obj_tag(v_r_3593_) == 0)
{
lean_object* v_size_3620_; 
v_size_3620_ = lean_ctor_get(v_r_3593_, 0);
lean_inc(v_size_3620_);
v___y_3604_ = v___x_3618_;
v___y_3605_ = v___x_3619_;
v___y_3606_ = v_size_3620_;
goto v___jp_3603_;
}
else
{
lean_object* v___x_3621_; 
v___x_3621_ = lean_unsigned_to_nat(0u);
v___y_3604_ = v___x_3618_;
v___y_3605_ = v___x_3619_;
v___y_3606_ = v___x_3621_;
goto v___jp_3603_;
}
}
}
}
}
else
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
lean_del_object(v___x_3426_);
v___x_3631_ = lean_nat_add(v___x_3571_, v_size_3572_);
v___x_3632_ = lean_nat_add(v___x_3631_, v_size_3573_);
lean_dec(v_size_3573_);
v___x_3633_ = lean_nat_add(v___x_3631_, v_size_3589_);
lean_dec(v___x_3631_);
lean_inc_ref(v_l_3423_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 4, v_l_3576_);
lean_ctor_set(v___x_3587_, 3, v_l_3423_);
lean_ctor_set(v___x_3587_, 2, v_v_3422_);
lean_ctor_set(v___x_3587_, 1, v_k_3421_);
lean_ctor_set(v___x_3587_, 0, v___x_3633_);
v___x_3635_ = v___x_3587_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3633_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3648_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3648_, 3, v_l_3423_);
lean_ctor_set(v_reuseFailAlloc_3648_, 4, v_l_3576_);
v___x_3635_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_isSharedCheck_3642_ = !lean_is_exclusive(v_l_3423_);
if (v_isSharedCheck_3642_ == 0)
{
lean_object* v_unused_3643_; lean_object* v_unused_3644_; lean_object* v_unused_3645_; lean_object* v_unused_3646_; lean_object* v_unused_3647_; 
v_unused_3643_ = lean_ctor_get(v_l_3423_, 4);
lean_dec(v_unused_3643_);
v_unused_3644_ = lean_ctor_get(v_l_3423_, 3);
lean_dec(v_unused_3644_);
v_unused_3645_ = lean_ctor_get(v_l_3423_, 2);
lean_dec(v_unused_3645_);
v_unused_3646_ = lean_ctor_get(v_l_3423_, 1);
lean_dec(v_unused_3646_);
v_unused_3647_ = lean_ctor_get(v_l_3423_, 0);
lean_dec(v_unused_3647_);
v___x_3637_ = v_l_3423_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_dec(v_l_3423_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 4, v_r_3577_);
lean_ctor_set(v___x_3637_, 3, v___x_3635_);
lean_ctor_set(v___x_3637_, 2, v_v_3575_);
lean_ctor_set(v___x_3637_, 1, v_k_3574_);
lean_ctor_set(v___x_3637_, 0, v___x_3632_);
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3632_);
lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_k_3574_);
lean_ctor_set(v_reuseFailAlloc_3641_, 2, v_v_3575_);
lean_ctor_set(v_reuseFailAlloc_3641_, 3, v___x_3635_);
lean_ctor_set(v_reuseFailAlloc_3641_, 4, v_r_3577_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3655_; 
v_l_3655_ = lean_ctor_get(v_impl_3570_, 3);
lean_inc(v_l_3655_);
if (lean_obj_tag(v_l_3655_) == 0)
{
lean_object* v_r_3656_; lean_object* v_k_3657_; lean_object* v_v_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3681_; 
v_r_3656_ = lean_ctor_get(v_impl_3570_, 4);
v_k_3657_ = lean_ctor_get(v_impl_3570_, 1);
v_v_3658_ = lean_ctor_get(v_impl_3570_, 2);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_impl_3570_);
if (v_isSharedCheck_3681_ == 0)
{
lean_object* v_unused_3682_; lean_object* v_unused_3683_; 
v_unused_3682_ = lean_ctor_get(v_impl_3570_, 3);
lean_dec(v_unused_3682_);
v_unused_3683_ = lean_ctor_get(v_impl_3570_, 0);
lean_dec(v_unused_3683_);
v___x_3660_ = v_impl_3570_;
v_isShared_3661_ = v_isSharedCheck_3681_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_r_3656_);
lean_inc(v_v_3658_);
lean_inc(v_k_3657_);
lean_dec(v_impl_3570_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3681_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v_k_3662_; lean_object* v_v_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3677_; 
v_k_3662_ = lean_ctor_get(v_l_3655_, 1);
v_v_3663_ = lean_ctor_get(v_l_3655_, 2);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_l_3655_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; lean_object* v_unused_3679_; lean_object* v_unused_3680_; 
v_unused_3678_ = lean_ctor_get(v_l_3655_, 4);
lean_dec(v_unused_3678_);
v_unused_3679_ = lean_ctor_get(v_l_3655_, 3);
lean_dec(v_unused_3679_);
v_unused_3680_ = lean_ctor_get(v_l_3655_, 0);
lean_dec(v_unused_3680_);
v___x_3665_ = v_l_3655_;
v_isShared_3666_ = v_isSharedCheck_3677_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_v_3663_);
lean_inc(v_k_3662_);
lean_dec(v_l_3655_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3677_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3667_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3656_, 2);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 4, v_r_3656_);
lean_ctor_set(v___x_3665_, 3, v_r_3656_);
lean_ctor_set(v___x_3665_, 2, v_v_3422_);
lean_ctor_set(v___x_3665_, 1, v_k_3421_);
lean_ctor_set(v___x_3665_, 0, v___x_3571_);
v___x_3669_ = v___x_3665_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3571_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_r_3656_);
lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_r_3656_);
v___x_3669_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3671_; 
lean_inc(v_r_3656_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 3, v_r_3656_);
lean_ctor_set(v___x_3660_, 0, v___x_3571_);
v___x_3671_ = v___x_3660_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3571_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_3675_, 3, v_r_3656_);
lean_ctor_set(v_reuseFailAlloc_3675_, 4, v_r_3656_);
v___x_3671_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3673_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 4, v___x_3671_);
lean_ctor_set(v___x_3426_, 3, v___x_3669_);
lean_ctor_set(v___x_3426_, 2, v_v_3663_);
lean_ctor_set(v___x_3426_, 1, v_k_3662_);
lean_ctor_set(v___x_3426_, 0, v___x_3667_);
v___x_3673_ = v___x_3426_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_k_3662_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v_v_3663_);
lean_ctor_set(v_reuseFailAlloc_3674_, 3, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3674_, 4, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
}
}
else
{
lean_object* v_r_3684_; 
v_r_3684_ = lean_ctor_get(v_impl_3570_, 4);
lean_inc(v_r_3684_);
if (lean_obj_tag(v_r_3684_) == 0)
{
lean_object* v_k_3685_; lean_object* v_v_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3697_; 
v_k_3685_ = lean_ctor_get(v_impl_3570_, 1);
v_v_3686_ = lean_ctor_get(v_impl_3570_, 2);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_impl_3570_);
if (v_isSharedCheck_3697_ == 0)
{
lean_object* v_unused_3698_; lean_object* v_unused_3699_; lean_object* v_unused_3700_; 
v_unused_3698_ = lean_ctor_get(v_impl_3570_, 4);
lean_dec(v_unused_3698_);
v_unused_3699_ = lean_ctor_get(v_impl_3570_, 3);
lean_dec(v_unused_3699_);
v_unused_3700_ = lean_ctor_get(v_impl_3570_, 0);
lean_dec(v_unused_3700_);
v___x_3688_ = v_impl_3570_;
v_isShared_3689_ = v_isSharedCheck_3697_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_v_3686_);
lean_inc(v_k_3685_);
lean_dec(v_impl_3570_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3697_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3690_ = lean_unsigned_to_nat(3u);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 4, v_l_3655_);
lean_ctor_set(v___x_3688_, 2, v_v_3422_);
lean_ctor_set(v___x_3688_, 1, v_k_3421_);
lean_ctor_set(v___x_3688_, 0, v___x_3571_);
v___x_3692_ = v___x_3688_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3571_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3696_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3696_, 3, v_l_3655_);
lean_ctor_set(v_reuseFailAlloc_3696_, 4, v_l_3655_);
v___x_3692_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3694_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 4, v_r_3684_);
lean_ctor_set(v___x_3426_, 3, v___x_3692_);
lean_ctor_set(v___x_3426_, 2, v_v_3686_);
lean_ctor_set(v___x_3426_, 1, v_k_3685_);
lean_ctor_set(v___x_3426_, 0, v___x_3690_);
v___x_3694_ = v___x_3426_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v_k_3685_);
lean_ctor_set(v_reuseFailAlloc_3695_, 2, v_v_3686_);
lean_ctor_set(v_reuseFailAlloc_3695_, 3, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3695_, 4, v_r_3684_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
else
{
lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3701_ = lean_unsigned_to_nat(2u);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 4, v_impl_3570_);
lean_ctor_set(v___x_3426_, 3, v_r_3684_);
lean_ctor_set(v___x_3426_, 0, v___x_3701_);
v___x_3703_ = v___x_3426_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3701_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3704_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3704_, 3, v_r_3684_);
lean_ctor_set(v_reuseFailAlloc_3704_, 4, v_impl_3570_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
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
lean_object* v___x_3706_; lean_object* v___x_3707_; 
lean_dec_ref(v_cmp_3416_);
v___x_3706_ = lean_unsigned_to_nat(1u);
v___x_3707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
lean_ctor_set(v___x_3707_, 1, v_k_3417_);
lean_ctor_set(v___x_3707_, 2, v_v_3418_);
lean_ctor_set(v___x_3707_, 3, v_t_3419_);
lean_ctor_set(v___x_3707_, 4, v_t_3419_);
return v___x_3707_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_3708_, lean_object* v_t_3709_, lean_object* v_k_3710_){
_start:
{
if (lean_obj_tag(v_t_3709_) == 0)
{
lean_object* v_k_3711_; lean_object* v_v_3712_; lean_object* v_l_3713_; lean_object* v_r_3714_; lean_object* v___x_3715_; uint8_t v___x_3716_; 
v_k_3711_ = lean_ctor_get(v_t_3709_, 1);
lean_inc(v_k_3711_);
v_v_3712_ = lean_ctor_get(v_t_3709_, 2);
lean_inc(v_v_3712_);
v_l_3713_ = lean_ctor_get(v_t_3709_, 3);
lean_inc(v_l_3713_);
v_r_3714_ = lean_ctor_get(v_t_3709_, 4);
lean_inc(v_r_3714_);
lean_dec_ref(v_t_3709_);
lean_inc_ref(v_cmp_3708_);
lean_inc(v_k_3711_);
lean_inc(v_k_3710_);
v___x_3715_ = lean_apply_2(v_cmp_3708_, v_k_3710_, v_k_3711_);
v___x_3716_ = lean_unbox(v___x_3715_);
switch(v___x_3716_)
{
case 0:
{
lean_dec(v_r_3714_);
lean_dec(v_v_3712_);
lean_dec(v_k_3711_);
v_t_3709_ = v_l_3713_;
goto _start;
}
case 1:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
lean_dec(v_r_3714_);
lean_dec(v_l_3713_);
lean_dec(v_k_3710_);
lean_dec_ref(v_cmp_3708_);
v___x_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3718_, 0, v_k_3711_);
lean_ctor_set(v___x_3718_, 1, v_v_3712_);
v___x_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
return v___x_3719_;
}
default: 
{
lean_dec(v_l_3713_);
lean_dec(v_v_3712_);
lean_dec(v_k_3711_);
v_t_3709_ = v_r_3714_;
goto _start;
}
}
}
else
{
lean_object* v___x_3721_; 
lean_dec(v_k_3710_);
lean_dec_ref(v_cmp_3708_);
v___x_3721_ = lean_box(0);
return v___x_3721_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_cmp_3722_, lean_object* v_m_u2081_3723_, lean_object* v_init_3724_, lean_object* v_x_3725_){
_start:
{
if (lean_obj_tag(v_x_3725_) == 0)
{
lean_object* v_k_3726_; lean_object* v_l_3727_; lean_object* v_r_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v_k_3726_ = lean_ctor_get(v_x_3725_, 1);
lean_inc(v_k_3726_);
v_l_3727_ = lean_ctor_get(v_x_3725_, 3);
lean_inc(v_l_3727_);
v_r_3728_ = lean_ctor_get(v_x_3725_, 4);
lean_inc(v_r_3728_);
lean_dec_ref(v_x_3725_);
lean_inc(v_m_u2081_3723_);
lean_inc_ref(v_cmp_3722_);
v___x_3729_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3722_, v_m_u2081_3723_, v_init_3724_, v_l_3727_);
lean_inc(v_m_u2081_3723_);
lean_inc_ref(v_cmp_3722_);
v___x_3730_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3722_, v_m_u2081_3723_, v_k_3726_);
if (lean_obj_tag(v___x_3730_) == 0)
{
v_init_3724_ = v___x_3729_;
v_x_3725_ = v_r_3728_;
goto _start;
}
else
{
lean_object* v_val_3732_; lean_object* v_fst_3733_; lean_object* v_snd_3734_; lean_object* v_impl_3735_; 
v_val_3732_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_val_3732_);
lean_dec_ref(v___x_3730_);
v_fst_3733_ = lean_ctor_get(v_val_3732_, 0);
lean_inc(v_fst_3733_);
v_snd_3734_ = lean_ctor_get(v_val_3732_, 1);
lean_inc(v_snd_3734_);
lean_dec(v_val_3732_);
lean_inc_ref(v_cmp_3722_);
v_impl_3735_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3722_, v_fst_3733_, v_snd_3734_, v___x_3729_);
v_init_3724_ = v_impl_3735_;
v_x_3725_ = v_r_3728_;
goto _start;
}
}
else
{
lean_dec(v_m_u2081_3723_);
lean_dec_ref(v_cmp_3722_);
return v_init_3724_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(lean_object* v_cmp_3737_, lean_object* v_m_u2081_3738_, lean_object* v_m_u2082_3739_){
_start:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3740_ = lean_box(1);
v___x_3741_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3737_, v_m_u2081_3738_, v___x_3740_, v_m_u2082_3739_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(lean_object* v_cmp_3742_, lean_object* v_m_u2082_3743_, lean_object* v_t_3744_){
_start:
{
if (lean_obj_tag(v_t_3744_) == 0)
{
lean_object* v_k_3745_; lean_object* v_v_3746_; lean_object* v_l_3747_; lean_object* v_r_3748_; uint8_t v___x_3749_; 
v_k_3745_ = lean_ctor_get(v_t_3744_, 1);
lean_inc(v_k_3745_);
v_v_3746_ = lean_ctor_get(v_t_3744_, 2);
lean_inc(v_v_3746_);
v_l_3747_ = lean_ctor_get(v_t_3744_, 3);
lean_inc(v_l_3747_);
v_r_3748_ = lean_ctor_get(v_t_3744_, 4);
lean_inc(v_r_3748_);
lean_dec_ref(v_t_3744_);
lean_inc(v_m_u2082_3743_);
lean_inc(v_k_3745_);
lean_inc_ref(v_cmp_3742_);
v___x_3749_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3742_, v_k_3745_, v_m_u2082_3743_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
lean_dec(v_v_3746_);
lean_dec(v_k_3745_);
lean_inc(v_m_u2082_3743_);
lean_inc_ref(v_cmp_3742_);
v___x_3750_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3742_, v_m_u2082_3743_, v_l_3747_);
v___x_3751_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3742_, v_m_u2082_3743_, v_r_3748_);
v___x_3752_ = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(v___x_3750_, v___x_3751_);
return v___x_3752_;
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
lean_inc(v_m_u2082_3743_);
lean_inc_ref(v_cmp_3742_);
v___x_3753_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3742_, v_m_u2082_3743_, v_l_3747_);
v___x_3754_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3742_, v_m_u2082_3743_, v_r_3748_);
v___x_3755_ = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(v_k_3745_, v_v_3746_, v___x_3753_, v___x_3754_);
return v___x_3755_;
}
}
else
{
lean_dec(v_m_u2082_3743_);
lean_dec_ref(v_cmp_3742_);
return v_t_3744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(lean_object* v_cmp_3756_, lean_object* v_m_u2081_3757_, lean_object* v_m_u2082_3758_){
_start:
{
lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3766_; 
if (lean_obj_tag(v_m_u2081_3757_) == 0)
{
lean_object* v_size_3769_; 
v_size_3769_ = lean_ctor_get(v_m_u2081_3757_, 0);
lean_inc(v_size_3769_);
v___y_3766_ = v_size_3769_;
goto v___jp_3765_;
}
else
{
lean_object* v___x_3770_; 
v___x_3770_ = lean_unsigned_to_nat(0u);
v___y_3766_ = v___x_3770_;
goto v___jp_3765_;
}
v___jp_3759_:
{
uint8_t v___x_3762_; 
v___x_3762_ = lean_nat_dec_le(v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec(v___y_3760_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(v_cmp_3756_, v_m_u2081_3757_, v_m_u2082_3758_);
return v___x_3763_;
}
else
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3756_, v_m_u2082_3758_, v_m_u2081_3757_);
return v___x_3764_;
}
}
v___jp_3765_:
{
if (lean_obj_tag(v_m_u2082_3758_) == 0)
{
lean_object* v_size_3767_; 
v_size_3767_ = lean_ctor_get(v_m_u2082_3758_, 0);
lean_inc(v_size_3767_);
v___y_3760_ = v___y_3766_;
v___y_3761_ = v_size_3767_;
goto v___jp_3759_;
}
else
{
lean_object* v___x_3768_; 
v___x_3768_ = lean_unsigned_to_nat(0u);
v___y_3760_ = v___y_3766_;
v___y_3761_ = v___x_3768_;
goto v___jp_3759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter___redArg(lean_object* v_cmp_3771_, lean_object* v_t_u2081_3772_, lean_object* v_t_u2082_3773_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_3771_, v_t_u2081_3772_, v_t_u2082_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter(lean_object* v_00_u03b1_3775_, lean_object* v_00_u03b2_3776_, lean_object* v_cmp_3777_, lean_object* v_t_u2081_3778_, lean_object* v_t_u2082_3779_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_3777_, v_t_u2081_3778_, v_t_u2082_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0(lean_object* v_00_u03b1_3781_, lean_object* v_cmp_3782_, lean_object* v_00_u03b2_3783_, lean_object* v_m_u2081_3784_, lean_object* v_m_u2082_3785_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_3782_, v_m_u2081_3784_, v_m_u2082_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0(lean_object* v_00_u03b1_3787_, lean_object* v_cmp_3788_, lean_object* v_00_u03b2_3789_, lean_object* v_m_u2081_3790_, lean_object* v_m_u2082_3791_){
_start:
{
lean_object* v___x_3792_; 
v___x_3792_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(v_cmp_3788_, v_m_u2081_3790_, v_m_u2082_3791_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1(lean_object* v_00_u03b1_3793_, lean_object* v_00_u03b2_3794_, lean_object* v_cmp_3795_, lean_object* v_m_u2082_3796_, lean_object* v_t_3797_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3795_, v_m_u2082_3796_, v_t_3797_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3799_, lean_object* v_cmp_3800_, lean_object* v_00_u03b2_3801_, lean_object* v_t_3802_, lean_object* v_k_3803_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3800_, v_t_3802_, v_k_3803_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3805_, lean_object* v_cmp_3806_, lean_object* v_00_u03b2_3807_, lean_object* v_k_3808_, lean_object* v_v_3809_, lean_object* v_t_3810_, lean_object* v_hl_3811_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3806_, v_k_3808_, v_v_3809_, v_t_3810_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3___redArg(lean_object* v_cmp_3813_, lean_object* v_m_u2081_3814_, lean_object* v_init_3815_, lean_object* v_t_3816_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3813_, v_m_u2081_3814_, v_init_3815_, v_t_3816_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3818_, lean_object* v_00_u03b2_3819_, lean_object* v_cmp_3820_, lean_object* v_m_u2081_3821_, lean_object* v_init_3822_, lean_object* v_t_3823_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3820_, v_m_u2081_3821_, v_init_3822_, v_t_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b1_3825_, lean_object* v_00_u03b2_3826_, lean_object* v_cmp_3827_, lean_object* v_m_u2081_3828_, lean_object* v_init_3829_, lean_object* v_x_3830_){
_start:
{
lean_object* v___x_3831_; 
v___x_3831_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3827_, v_m_u2081_3828_, v_init_3829_, v_x_3830_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter___redArg(lean_object* v_cmp_3832_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_3833_, 0, lean_box(0));
lean_closure_set(v___x_3833_, 1, lean_box(0));
lean_closure_set(v___x_3833_, 2, v_cmp_3832_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter(lean_object* v_00_u03b1_3834_, lean_object* v_00_u03b2_3835_, lean_object* v_cmp_3836_){
_start:
{
lean_object* v___x_3837_; 
v___x_3837_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_3837_, 0, lean_box(0));
lean_closure_set(v___x_3837_, 1, lean_box(0));
lean_closure_set(v___x_3837_, 2, v_cmp_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_beq___redArg(lean_object* v_cmp_3838_, lean_object* v_inst_3839_, lean_object* v_t_u2081_3840_, lean_object* v_t_u2082_3841_){
_start:
{
uint8_t v___x_3842_; 
v___x_3842_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3838_, v_inst_3839_, v_t_u2081_3840_, v_t_u2082_3841_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___redArg___boxed(lean_object* v_cmp_3843_, lean_object* v_inst_3844_, lean_object* v_t_u2081_3845_, lean_object* v_t_u2082_3846_){
_start:
{
uint8_t v_res_3847_; lean_object* v_r_3848_; 
v_res_3847_ = l_Std_DTreeMap_Raw_beq___redArg(v_cmp_3843_, v_inst_3844_, v_t_u2081_3845_, v_t_u2082_3846_);
v_r_3848_ = lean_box(v_res_3847_);
return v_r_3848_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_beq(lean_object* v_00_u03b1_3849_, lean_object* v_00_u03b2_3850_, lean_object* v_cmp_3851_, lean_object* v_inst_3852_, lean_object* v_inst_3853_, lean_object* v_t_u2081_3854_, lean_object* v_t_u2082_3855_){
_start:
{
uint8_t v___x_3856_; 
v___x_3856_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_3851_, v_inst_3853_, v_t_u2081_3854_, v_t_u2082_3855_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___boxed(lean_object* v_00_u03b1_3857_, lean_object* v_00_u03b2_3858_, lean_object* v_cmp_3859_, lean_object* v_inst_3860_, lean_object* v_inst_3861_, lean_object* v_t_u2081_3862_, lean_object* v_t_u2082_3863_){
_start:
{
uint8_t v_res_3864_; lean_object* v_r_3865_; 
v_res_3864_ = l_Std_DTreeMap_Raw_beq(v_00_u03b1_3857_, v_00_u03b2_3858_, v_cmp_3859_, v_inst_3860_, v_inst_3861_, v_t_u2081_3862_, v_t_u2082_3863_);
v_r_3865_ = lean_box(v_res_3864_);
return v_r_3865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp___redArg(lean_object* v_cmp_3866_, lean_object* v_inst_3867_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_3868_, 0, lean_box(0));
lean_closure_set(v___x_3868_, 1, lean_box(0));
lean_closure_set(v___x_3868_, 2, v_cmp_3866_);
lean_closure_set(v___x_3868_, 3, lean_box(0));
lean_closure_set(v___x_3868_, 4, v_inst_3867_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp(lean_object* v_00_u03b1_3869_, lean_object* v_00_u03b2_3870_, lean_object* v_cmp_3871_, lean_object* v_inst_3872_, lean_object* v_inst_3873_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_3874_, 0, lean_box(0));
lean_closure_set(v___x_3874_, 1, lean_box(0));
lean_closure_set(v___x_3874_, 2, v_cmp_3871_);
lean_closure_set(v___x_3874_, 3, lean_box(0));
lean_closure_set(v___x_3874_, 4, v_inst_3873_);
return v___x_3874_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___redArg(lean_object* v_cmp_3875_, lean_object* v_inst_3876_, lean_object* v_t_u2081_3877_, lean_object* v_t_u2082_3878_){
_start:
{
uint8_t v___x_3879_; 
v___x_3879_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3875_, v_inst_3876_, v_t_u2081_3877_, v_t_u2082_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___redArg___boxed(lean_object* v_cmp_3880_, lean_object* v_inst_3881_, lean_object* v_t_u2081_3882_, lean_object* v_t_u2082_3883_){
_start:
{
uint8_t v_res_3884_; lean_object* v_r_3885_; 
v_res_3884_ = l_Std_DTreeMap_Raw_Const_beq___redArg(v_cmp_3880_, v_inst_3881_, v_t_u2081_3882_, v_t_u2082_3883_);
v_r_3885_ = lean_box(v_res_3884_);
return v_r_3885_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq(lean_object* v_00_u03b1_3886_, lean_object* v_cmp_3887_, lean_object* v_00_u03b2_3888_, lean_object* v_inst_3889_, lean_object* v_t_u2081_3890_, lean_object* v_t_u2082_3891_){
_start:
{
uint8_t v___x_3892_; 
v___x_3892_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_3887_, v_inst_3889_, v_t_u2081_3890_, v_t_u2082_3891_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___boxed(lean_object* v_00_u03b1_3893_, lean_object* v_cmp_3894_, lean_object* v_00_u03b2_3895_, lean_object* v_inst_3896_, lean_object* v_t_u2081_3897_, lean_object* v_t_u2082_3898_){
_start:
{
uint8_t v_res_3899_; lean_object* v_r_3900_; 
v_res_3899_ = l_Std_DTreeMap_Raw_Const_beq(v_00_u03b1_3893_, v_cmp_3894_, v_00_u03b2_3895_, v_inst_3896_, v_t_u2081_3897_, v_t_u2082_3898_);
v_r_3900_ = lean_box(v_res_3899_);
return v_r_3900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(lean_object* v_cmp_3901_, lean_object* v_t_u2082_3902_, lean_object* v_t_3903_){
_start:
{
if (lean_obj_tag(v_t_3903_) == 0)
{
lean_object* v_k_3904_; lean_object* v_v_3905_; lean_object* v_l_3906_; lean_object* v_r_3907_; uint8_t v___x_3908_; 
v_k_3904_ = lean_ctor_get(v_t_3903_, 1);
lean_inc(v_k_3904_);
v_v_3905_ = lean_ctor_get(v_t_3903_, 2);
lean_inc(v_v_3905_);
v_l_3906_ = lean_ctor_get(v_t_3903_, 3);
lean_inc(v_l_3906_);
v_r_3907_ = lean_ctor_get(v_t_3903_, 4);
lean_inc(v_r_3907_);
lean_dec_ref(v_t_3903_);
lean_inc(v_t_u2082_3902_);
lean_inc(v_k_3904_);
lean_inc_ref(v_cmp_3901_);
v___x_3908_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3901_, v_k_3904_, v_t_u2082_3902_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_inc(v_t_u2082_3902_);
lean_inc_ref(v_cmp_3901_);
v___x_3909_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_3901_, v_t_u2082_3902_, v_l_3906_);
v___x_3910_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_3901_, v_t_u2082_3902_, v_r_3907_);
v___x_3911_ = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(v_k_3904_, v_v_3905_, v___x_3909_, v___x_3910_);
return v___x_3911_;
}
else
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
lean_dec(v_v_3905_);
lean_dec(v_k_3904_);
lean_inc(v_t_u2082_3902_);
lean_inc_ref(v_cmp_3901_);
v___x_3912_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_3901_, v_t_u2082_3902_, v_l_3906_);
v___x_3913_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_3901_, v_t_u2082_3902_, v_r_3907_);
v___x_3914_ = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(v___x_3912_, v___x_3913_);
return v___x_3914_;
}
}
else
{
lean_dec(v_t_u2082_3902_);
lean_dec_ref(v_cmp_3901_);
return v_t_3903_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(lean_object* v_cmp_3915_, lean_object* v_k_3916_, lean_object* v_t_3917_){
_start:
{
if (lean_obj_tag(v_t_3917_) == 0)
{
lean_object* v_k_3918_; lean_object* v_v_3919_; lean_object* v_l_3920_; lean_object* v_r_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_4611_; 
v_k_3918_ = lean_ctor_get(v_t_3917_, 1);
v_v_3919_ = lean_ctor_get(v_t_3917_, 2);
v_l_3920_ = lean_ctor_get(v_t_3917_, 3);
v_r_3921_ = lean_ctor_get(v_t_3917_, 4);
v_isSharedCheck_4611_ = !lean_is_exclusive(v_t_3917_);
if (v_isSharedCheck_4611_ == 0)
{
lean_object* v_unused_4612_; 
v_unused_4612_ = lean_ctor_get(v_t_3917_, 0);
lean_dec(v_unused_4612_);
v___x_3923_ = v_t_3917_;
v_isShared_3924_ = v_isSharedCheck_4611_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_r_3921_);
lean_inc(v_l_3920_);
lean_inc(v_v_3919_);
lean_inc(v_k_3918_);
lean_dec(v_t_3917_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_4611_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3925_; uint8_t v___x_3926_; 
lean_inc_ref(v_cmp_3915_);
lean_inc(v_k_3918_);
lean_inc(v_k_3916_);
v___x_3925_ = lean_apply_2(v_cmp_3915_, v_k_3916_, v_k_3918_);
v___x_3926_ = lean_unbox(v___x_3925_);
switch(v___x_3926_)
{
case 0:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_3915_, v_k_3916_, v_l_3920_);
if (lean_obj_tag(v___x_3927_) == 0)
{
if (lean_obj_tag(v_r_3921_) == 0)
{
lean_object* v_size_3928_; lean_object* v_size_3929_; lean_object* v_k_3930_; lean_object* v_v_3931_; lean_object* v_l_3932_; lean_object* v_r_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
v_size_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_size_3928_);
v_size_3929_ = lean_ctor_get(v_r_3921_, 0);
v_k_3930_ = lean_ctor_get(v_r_3921_, 1);
v_v_3931_ = lean_ctor_get(v_r_3921_, 2);
v_l_3932_ = lean_ctor_get(v_r_3921_, 3);
lean_inc(v_l_3932_);
v_r_3933_ = lean_ctor_get(v_r_3921_, 4);
v___x_3934_ = lean_unsigned_to_nat(3u);
v___x_3935_ = lean_nat_mul(v___x_3934_, v_size_3928_);
v___x_3936_ = lean_nat_dec_lt(v___x_3935_, v_size_3929_);
lean_dec(v___x_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3941_; 
lean_dec(v_l_3932_);
v___x_3937_ = lean_unsigned_to_nat(1u);
v___x_3938_ = lean_nat_add(v___x_3937_, v_size_3928_);
lean_dec(v_size_3928_);
v___x_3939_ = lean_nat_add(v___x_3938_, v_size_3929_);
lean_dec(v___x_3938_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 3, v___x_3927_);
lean_ctor_set(v___x_3923_, 0, v___x_3939_);
v___x_3941_ = v___x_3923_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3939_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_3942_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_3942_, 3, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3942_, 4, v_r_3921_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
else
{
lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_4012_; 
lean_inc(v_r_3933_);
lean_inc(v_v_3931_);
lean_inc(v_k_3930_);
lean_inc(v_size_3929_);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_r_3921_);
if (v_isSharedCheck_4012_ == 0)
{
lean_object* v_unused_4013_; lean_object* v_unused_4014_; lean_object* v_unused_4015_; lean_object* v_unused_4016_; lean_object* v_unused_4017_; 
v_unused_4013_ = lean_ctor_get(v_r_3921_, 4);
lean_dec(v_unused_4013_);
v_unused_4014_ = lean_ctor_get(v_r_3921_, 3);
lean_dec(v_unused_4014_);
v_unused_4015_ = lean_ctor_get(v_r_3921_, 2);
lean_dec(v_unused_4015_);
v_unused_4016_ = lean_ctor_get(v_r_3921_, 1);
lean_dec(v_unused_4016_);
v_unused_4017_ = lean_ctor_get(v_r_3921_, 0);
lean_dec(v_unused_4017_);
v___x_3944_ = v_r_3921_;
v_isShared_3945_ = v_isSharedCheck_4012_;
goto v_resetjp_3943_;
}
else
{
lean_dec(v_r_3921_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_4012_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
if (lean_obj_tag(v_l_3932_) == 0)
{
if (lean_obj_tag(v_r_3933_) == 0)
{
lean_object* v_size_3946_; lean_object* v_k_3947_; lean_object* v_v_3948_; lean_object* v_l_3949_; lean_object* v_r_3950_; lean_object* v_size_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
v_size_3946_ = lean_ctor_get(v_l_3932_, 0);
v_k_3947_ = lean_ctor_get(v_l_3932_, 1);
v_v_3948_ = lean_ctor_get(v_l_3932_, 2);
v_l_3949_ = lean_ctor_get(v_l_3932_, 3);
v_r_3950_ = lean_ctor_get(v_l_3932_, 4);
v_size_3951_ = lean_ctor_get(v_r_3933_, 0);
v___x_3952_ = lean_unsigned_to_nat(2u);
v___x_3953_ = lean_nat_mul(v___x_3952_, v_size_3951_);
v___x_3954_ = lean_nat_dec_lt(v_size_3946_, v___x_3953_);
lean_dec(v___x_3953_);
if (v___x_3954_ == 0)
{
lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3983_; 
lean_inc(v_r_3950_);
lean_inc(v_l_3949_);
lean_inc(v_v_3948_);
lean_inc(v_k_3947_);
v_isSharedCheck_3983_ = !lean_is_exclusive(v_l_3932_);
if (v_isSharedCheck_3983_ == 0)
{
lean_object* v_unused_3984_; lean_object* v_unused_3985_; lean_object* v_unused_3986_; lean_object* v_unused_3987_; lean_object* v_unused_3988_; 
v_unused_3984_ = lean_ctor_get(v_l_3932_, 4);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_l_3932_, 3);
lean_dec(v_unused_3985_);
v_unused_3986_ = lean_ctor_get(v_l_3932_, 2);
lean_dec(v_unused_3986_);
v_unused_3987_ = lean_ctor_get(v_l_3932_, 1);
lean_dec(v_unused_3987_);
v_unused_3988_ = lean_ctor_get(v_l_3932_, 0);
lean_dec(v_unused_3988_);
v___x_3956_ = v_l_3932_;
v_isShared_3957_ = v_isSharedCheck_3983_;
goto v_resetjp_3955_;
}
else
{
lean_dec(v_l_3932_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3983_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3973_; 
v___x_3958_ = lean_unsigned_to_nat(1u);
v___x_3959_ = lean_nat_add(v___x_3958_, v_size_3928_);
lean_dec(v_size_3928_);
v___x_3960_ = lean_nat_add(v___x_3959_, v_size_3929_);
lean_dec(v_size_3929_);
if (lean_obj_tag(v_l_3949_) == 0)
{
lean_object* v_size_3981_; 
v_size_3981_ = lean_ctor_get(v_l_3949_, 0);
lean_inc(v_size_3981_);
v___y_3973_ = v_size_3981_;
goto v___jp_3972_;
}
else
{
lean_object* v___x_3982_; 
v___x_3982_ = lean_unsigned_to_nat(0u);
v___y_3973_ = v___x_3982_;
goto v___jp_3972_;
}
v___jp_3961_:
{
lean_object* v___x_3965_; lean_object* v___x_3967_; 
v___x_3965_ = lean_nat_add(v___y_3962_, v___y_3964_);
lean_dec(v___y_3964_);
lean_dec(v___y_3962_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 4, v_r_3933_);
lean_ctor_set(v___x_3956_, 3, v_r_3950_);
lean_ctor_set(v___x_3956_, 2, v_v_3931_);
lean_ctor_set(v___x_3956_, 1, v_k_3930_);
lean_ctor_set(v___x_3956_, 0, v___x_3965_);
v___x_3967_ = v___x_3956_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3965_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v_k_3930_);
lean_ctor_set(v_reuseFailAlloc_3971_, 2, v_v_3931_);
lean_ctor_set(v_reuseFailAlloc_3971_, 3, v_r_3950_);
lean_ctor_set(v_reuseFailAlloc_3971_, 4, v_r_3933_);
v___x_3967_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
lean_object* v___x_3969_; 
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 4, v___x_3967_);
lean_ctor_set(v___x_3944_, 3, v___y_3963_);
lean_ctor_set(v___x_3944_, 2, v_v_3948_);
lean_ctor_set(v___x_3944_, 1, v_k_3947_);
lean_ctor_set(v___x_3944_, 0, v___x_3960_);
v___x_3969_ = v___x_3944_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3960_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v_k_3947_);
lean_ctor_set(v_reuseFailAlloc_3970_, 2, v_v_3948_);
lean_ctor_set(v_reuseFailAlloc_3970_, 3, v___y_3963_);
lean_ctor_set(v_reuseFailAlloc_3970_, 4, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
v___jp_3972_:
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
v___x_3974_ = lean_nat_add(v___x_3959_, v___y_3973_);
lean_dec(v___y_3973_);
lean_dec(v___x_3959_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v_l_3949_);
lean_ctor_set(v___x_3923_, 3, v___x_3927_);
lean_ctor_set(v___x_3923_, 0, v___x_3974_);
v___x_3976_ = v___x_3923_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3974_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_3980_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_3980_, 3, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3980_, 4, v_l_3949_);
v___x_3976_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3977_; 
v___x_3977_ = lean_nat_add(v___x_3958_, v_size_3951_);
if (lean_obj_tag(v_r_3950_) == 0)
{
lean_object* v_size_3978_; 
v_size_3978_ = lean_ctor_get(v_r_3950_, 0);
lean_inc(v_size_3978_);
v___y_3962_ = v___x_3977_;
v___y_3963_ = v___x_3976_;
v___y_3964_ = v_size_3978_;
goto v___jp_3961_;
}
else
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_unsigned_to_nat(0u);
v___y_3962_ = v___x_3977_;
v___y_3963_ = v___x_3976_;
v___y_3964_ = v___x_3979_;
goto v___jp_3961_;
}
}
}
}
}
else
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3994_; 
lean_del_object(v___x_3923_);
v___x_3989_ = lean_unsigned_to_nat(1u);
v___x_3990_ = lean_nat_add(v___x_3989_, v_size_3928_);
lean_dec(v_size_3928_);
v___x_3991_ = lean_nat_add(v___x_3990_, v_size_3929_);
lean_dec(v_size_3929_);
v___x_3992_ = lean_nat_add(v___x_3990_, v_size_3946_);
lean_dec(v___x_3990_);
lean_inc_ref(v___x_3927_);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 4, v_l_3932_);
lean_ctor_set(v___x_3944_, 3, v___x_3927_);
lean_ctor_set(v___x_3944_, 2, v_v_3919_);
lean_ctor_set(v___x_3944_, 1, v_k_3918_);
lean_ctor_set(v___x_3944_, 0, v___x_3992_);
v___x_3994_ = v___x_3944_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_3992_);
lean_ctor_set(v_reuseFailAlloc_4007_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4007_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4007_, 3, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_4007_, 4, v_l_3932_);
v___x_3994_ = v_reuseFailAlloc_4007_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_4001_ == 0)
{
lean_object* v_unused_4002_; lean_object* v_unused_4003_; lean_object* v_unused_4004_; lean_object* v_unused_4005_; lean_object* v_unused_4006_; 
v_unused_4002_ = lean_ctor_get(v___x_3927_, 4);
lean_dec(v_unused_4002_);
v_unused_4003_ = lean_ctor_get(v___x_3927_, 3);
lean_dec(v_unused_4003_);
v_unused_4004_ = lean_ctor_get(v___x_3927_, 2);
lean_dec(v_unused_4004_);
v_unused_4005_ = lean_ctor_get(v___x_3927_, 1);
lean_dec(v_unused_4005_);
v_unused_4006_ = lean_ctor_get(v___x_3927_, 0);
lean_dec(v_unused_4006_);
v___x_3996_ = v___x_3927_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_dec(v___x_3927_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 4, v_r_3933_);
lean_ctor_set(v___x_3996_, 3, v___x_3994_);
lean_ctor_set(v___x_3996_, 2, v_v_3931_);
lean_ctor_set(v___x_3996_, 1, v_k_3930_);
lean_ctor_set(v___x_3996_, 0, v___x_3991_);
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3991_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v_k_3930_);
lean_ctor_set(v_reuseFailAlloc_4000_, 2, v_v_3931_);
lean_ctor_set(v_reuseFailAlloc_4000_, 3, v___x_3994_);
lean_ctor_set(v_reuseFailAlloc_4000_, 4, v_r_3933_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
else
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
lean_dec_ref(v_l_3932_);
lean_del_object(v___x_3944_);
lean_dec(v_v_3931_);
lean_dec(v_k_3930_);
lean_dec(v_size_3929_);
lean_dec(v_size_3928_);
lean_dec_ref(v___x_3927_);
lean_del_object(v___x_3923_);
lean_dec(v_v_3919_);
lean_dec(v_k_3918_);
v___x_4008_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7);
v___x_4009_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4008_);
return v___x_4009_;
}
}
else
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
lean_del_object(v___x_3944_);
lean_dec(v_r_3933_);
lean_dec(v_v_3931_);
lean_dec(v_k_3930_);
lean_dec(v_size_3929_);
lean_dec(v_size_3928_);
lean_dec_ref(v___x_3927_);
lean_del_object(v___x_3923_);
lean_dec(v_v_3919_);
lean_dec(v_k_3918_);
v___x_4010_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8);
v___x_4011_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4010_);
return v___x_4011_;
}
}
}
}
else
{
lean_object* v_size_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4022_; 
v_size_4018_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_size_4018_);
v___x_4019_ = lean_unsigned_to_nat(1u);
v___x_4020_ = lean_nat_add(v___x_4019_, v_size_4018_);
lean_dec(v_size_4018_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 3, v___x_3927_);
lean_ctor_set(v___x_3923_, 0, v___x_4020_);
v___x_4022_ = v___x_3923_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v___x_4020_);
lean_ctor_set(v_reuseFailAlloc_4023_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4023_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4023_, 3, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_4023_, 4, v_r_3921_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
else
{
if (lean_obj_tag(v_r_3921_) == 0)
{
lean_object* v_l_4024_; 
v_l_4024_ = lean_ctor_get(v_r_3921_, 3);
lean_inc(v_l_4024_);
if (lean_obj_tag(v_l_4024_) == 0)
{
lean_object* v_r_4025_; 
v_r_4025_ = lean_ctor_get(v_r_3921_, 4);
lean_inc(v_r_4025_);
if (lean_obj_tag(v_r_4025_) == 0)
{
lean_object* v_size_4026_; lean_object* v_k_4027_; lean_object* v_v_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4042_; 
v_size_4026_ = lean_ctor_get(v_r_3921_, 0);
v_k_4027_ = lean_ctor_get(v_r_3921_, 1);
v_v_4028_ = lean_ctor_get(v_r_3921_, 2);
v_isSharedCheck_4042_ = !lean_is_exclusive(v_r_3921_);
if (v_isSharedCheck_4042_ == 0)
{
lean_object* v_unused_4043_; lean_object* v_unused_4044_; 
v_unused_4043_ = lean_ctor_get(v_r_3921_, 4);
lean_dec(v_unused_4043_);
v_unused_4044_ = lean_ctor_get(v_r_3921_, 3);
lean_dec(v_unused_4044_);
v___x_4030_ = v_r_3921_;
v_isShared_4031_ = v_isSharedCheck_4042_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_v_4028_);
lean_inc(v_k_4027_);
lean_inc(v_size_4026_);
lean_dec(v_r_3921_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4042_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v_size_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4037_; 
v_size_4032_ = lean_ctor_get(v_l_4024_, 0);
v___x_4033_ = lean_unsigned_to_nat(1u);
v___x_4034_ = lean_nat_add(v___x_4033_, v_size_4026_);
lean_dec(v_size_4026_);
v___x_4035_ = lean_nat_add(v___x_4033_, v_size_4032_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 4, v_l_4024_);
lean_ctor_set(v___x_4030_, 3, v___x_3927_);
lean_ctor_set(v___x_4030_, 2, v_v_3919_);
lean_ctor_set(v___x_4030_, 1, v_k_3918_);
lean_ctor_set(v___x_4030_, 0, v___x_4035_);
v___x_4037_ = v___x_4030_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4035_);
lean_ctor_set(v_reuseFailAlloc_4041_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4041_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4041_, 3, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_4041_, 4, v_l_4024_);
v___x_4037_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4039_; 
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v_r_4025_);
lean_ctor_set(v___x_3923_, 3, v___x_4037_);
lean_ctor_set(v___x_3923_, 2, v_v_4028_);
lean_ctor_set(v___x_3923_, 1, v_k_4027_);
lean_ctor_set(v___x_3923_, 0, v___x_4034_);
v___x_4039_ = v___x_3923_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4034_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_k_4027_);
lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_v_4028_);
lean_ctor_set(v_reuseFailAlloc_4040_, 3, v___x_4037_);
lean_ctor_set(v_reuseFailAlloc_4040_, 4, v_r_4025_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
else
{
lean_object* v_k_4045_; lean_object* v_v_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4070_; 
v_k_4045_ = lean_ctor_get(v_r_3921_, 1);
v_v_4046_ = lean_ctor_get(v_r_3921_, 2);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_r_3921_);
if (v_isSharedCheck_4070_ == 0)
{
lean_object* v_unused_4071_; lean_object* v_unused_4072_; lean_object* v_unused_4073_; 
v_unused_4071_ = lean_ctor_get(v_r_3921_, 4);
lean_dec(v_unused_4071_);
v_unused_4072_ = lean_ctor_get(v_r_3921_, 3);
lean_dec(v_unused_4072_);
v_unused_4073_ = lean_ctor_get(v_r_3921_, 0);
lean_dec(v_unused_4073_);
v___x_4048_ = v_r_3921_;
v_isShared_4049_ = v_isSharedCheck_4070_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_v_4046_);
lean_inc(v_k_4045_);
lean_dec(v_r_3921_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4070_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v_k_4050_; lean_object* v_v_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4066_; 
v_k_4050_ = lean_ctor_get(v_l_4024_, 1);
v_v_4051_ = lean_ctor_get(v_l_4024_, 2);
v_isSharedCheck_4066_ = !lean_is_exclusive(v_l_4024_);
if (v_isSharedCheck_4066_ == 0)
{
lean_object* v_unused_4067_; lean_object* v_unused_4068_; lean_object* v_unused_4069_; 
v_unused_4067_ = lean_ctor_get(v_l_4024_, 4);
lean_dec(v_unused_4067_);
v_unused_4068_ = lean_ctor_get(v_l_4024_, 3);
lean_dec(v_unused_4068_);
v_unused_4069_ = lean_ctor_get(v_l_4024_, 0);
lean_dec(v_unused_4069_);
v___x_4053_ = v_l_4024_;
v_isShared_4054_ = v_isSharedCheck_4066_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_v_4051_);
lean_inc(v_k_4050_);
lean_dec(v_l_4024_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4066_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4058_; 
v___x_4055_ = lean_unsigned_to_nat(3u);
v___x_4056_ = lean_unsigned_to_nat(1u);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 4, v_r_4025_);
lean_ctor_set(v___x_4053_, 3, v_r_4025_);
lean_ctor_set(v___x_4053_, 2, v_v_3919_);
lean_ctor_set(v___x_4053_, 1, v_k_3918_);
lean_ctor_set(v___x_4053_, 0, v___x_4056_);
v___x_4058_ = v___x_4053_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4056_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4065_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4065_, 3, v_r_4025_);
lean_ctor_set(v_reuseFailAlloc_4065_, 4, v_r_4025_);
v___x_4058_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4060_; 
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 3, v_r_4025_);
lean_ctor_set(v___x_4048_, 0, v___x_4056_);
v___x_4060_ = v___x_4048_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4056_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v_k_4045_);
lean_ctor_set(v_reuseFailAlloc_4064_, 2, v_v_4046_);
lean_ctor_set(v_reuseFailAlloc_4064_, 3, v_r_4025_);
lean_ctor_set(v_reuseFailAlloc_4064_, 4, v_r_4025_);
v___x_4060_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4062_; 
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v___x_4060_);
lean_ctor_set(v___x_3923_, 3, v___x_4058_);
lean_ctor_set(v___x_3923_, 2, v_v_4051_);
lean_ctor_set(v___x_3923_, 1, v_k_4050_);
lean_ctor_set(v___x_3923_, 0, v___x_4055_);
v___x_4062_ = v___x_3923_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4055_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v_k_4050_);
lean_ctor_set(v_reuseFailAlloc_4063_, 2, v_v_4051_);
lean_ctor_set(v_reuseFailAlloc_4063_, 3, v___x_4058_);
lean_ctor_set(v_reuseFailAlloc_4063_, 4, v___x_4060_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_4074_; 
v_r_4074_ = lean_ctor_get(v_r_3921_, 4);
lean_inc(v_r_4074_);
if (lean_obj_tag(v_r_4074_) == 0)
{
lean_object* v_k_4075_; lean_object* v_v_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4088_; 
v_k_4075_ = lean_ctor_get(v_r_3921_, 1);
v_v_4076_ = lean_ctor_get(v_r_3921_, 2);
v_isSharedCheck_4088_ = !lean_is_exclusive(v_r_3921_);
if (v_isSharedCheck_4088_ == 0)
{
lean_object* v_unused_4089_; lean_object* v_unused_4090_; lean_object* v_unused_4091_; 
v_unused_4089_ = lean_ctor_get(v_r_3921_, 4);
lean_dec(v_unused_4089_);
v_unused_4090_ = lean_ctor_get(v_r_3921_, 3);
lean_dec(v_unused_4090_);
v_unused_4091_ = lean_ctor_get(v_r_3921_, 0);
lean_dec(v_unused_4091_);
v___x_4078_ = v_r_3921_;
v_isShared_4079_ = v_isSharedCheck_4088_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_v_4076_);
lean_inc(v_k_4075_);
lean_dec(v_r_3921_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4088_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4083_; 
v___x_4080_ = lean_unsigned_to_nat(3u);
v___x_4081_ = lean_unsigned_to_nat(1u);
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 4, v_l_4024_);
lean_ctor_set(v___x_4078_, 2, v_v_3919_);
lean_ctor_set(v___x_4078_, 1, v_k_3918_);
lean_ctor_set(v___x_4078_, 0, v___x_4081_);
v___x_4083_ = v___x_4078_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4081_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4087_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4087_, 3, v_l_4024_);
lean_ctor_set(v_reuseFailAlloc_4087_, 4, v_l_4024_);
v___x_4083_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
lean_object* v___x_4085_; 
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v_r_4074_);
lean_ctor_set(v___x_3923_, 3, v___x_4083_);
lean_ctor_set(v___x_3923_, 2, v_v_4076_);
lean_ctor_set(v___x_3923_, 1, v_k_4075_);
lean_ctor_set(v___x_3923_, 0, v___x_4080_);
v___x_4085_ = v___x_3923_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4080_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v_k_4075_);
lean_ctor_set(v_reuseFailAlloc_4086_, 2, v_v_4076_);
lean_ctor_set(v_reuseFailAlloc_4086_, 3, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4086_, 4, v_r_4074_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
}
else
{
lean_object* v___x_4092_; lean_object* v___x_4094_; 
v___x_4092_ = lean_unsigned_to_nat(2u);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 3, v_r_4074_);
lean_ctor_set(v___x_3923_, 0, v___x_4092_);
v___x_4094_ = v___x_3923_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4092_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4095_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4095_, 3, v_r_4074_);
lean_ctor_set(v_reuseFailAlloc_4095_, 4, v_r_3921_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
else
{
lean_object* v___x_4096_; lean_object* v___x_4098_; 
v___x_4096_ = lean_unsigned_to_nat(1u);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 3, v_r_3921_);
lean_ctor_set(v___x_3923_, 0, v___x_4096_);
v___x_4098_ = v___x_3923_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4096_);
lean_ctor_set(v_reuseFailAlloc_4099_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4099_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4099_, 3, v_r_3921_);
lean_ctor_set(v_reuseFailAlloc_4099_, 4, v_r_3921_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3923_);
lean_dec(v_v_3919_);
lean_dec(v_k_3918_);
lean_dec(v_k_3916_);
lean_dec_ref(v_cmp_3915_);
if (lean_obj_tag(v_l_3920_) == 0)
{
if (lean_obj_tag(v_r_3921_) == 0)
{
lean_object* v_size_4100_; lean_object* v_k_4101_; lean_object* v_v_4102_; lean_object* v_l_4103_; lean_object* v_r_4104_; lean_object* v_size_4105_; lean_object* v_k_4106_; lean_object* v_v_4107_; lean_object* v_l_4108_; lean_object* v_r_4109_; uint8_t v___x_4110_; 
v_size_4100_ = lean_ctor_get(v_l_3920_, 0);
v_k_4101_ = lean_ctor_get(v_l_3920_, 1);
v_v_4102_ = lean_ctor_get(v_l_3920_, 2);
v_l_4103_ = lean_ctor_get(v_l_3920_, 3);
v_r_4104_ = lean_ctor_get(v_l_3920_, 4);
lean_inc(v_r_4104_);
v_size_4105_ = lean_ctor_get(v_r_3921_, 0);
v_k_4106_ = lean_ctor_get(v_r_3921_, 1);
v_v_4107_ = lean_ctor_get(v_r_3921_, 2);
v_l_4108_ = lean_ctor_get(v_r_3921_, 3);
lean_inc(v_l_4108_);
v_r_4109_ = lean_ctor_get(v_r_3921_, 4);
v___x_4110_ = lean_nat_dec_lt(v_size_4100_, v_size_4105_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4262_; 
lean_inc(v_l_4103_);
lean_inc(v_v_4102_);
lean_inc(v_k_4101_);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_l_3920_);
if (v_isSharedCheck_4262_ == 0)
{
lean_object* v_unused_4263_; lean_object* v_unused_4264_; lean_object* v_unused_4265_; lean_object* v_unused_4266_; lean_object* v_unused_4267_; 
v_unused_4263_ = lean_ctor_get(v_l_3920_, 4);
lean_dec(v_unused_4263_);
v_unused_4264_ = lean_ctor_get(v_l_3920_, 3);
lean_dec(v_unused_4264_);
v_unused_4265_ = lean_ctor_get(v_l_3920_, 2);
lean_dec(v_unused_4265_);
v_unused_4266_ = lean_ctor_get(v_l_3920_, 1);
lean_dec(v_unused_4266_);
v_unused_4267_ = lean_ctor_get(v_l_3920_, 0);
lean_dec(v_unused_4267_);
v___x_4112_ = v_l_3920_;
v_isShared_4113_ = v_isSharedCheck_4262_;
goto v_resetjp_4111_;
}
else
{
lean_dec(v_l_3920_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4262_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v_d_4114_; lean_object* v_tree_4115_; 
v_d_4114_ = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(v_k_4101_, v_v_4102_, v_l_4103_, v_r_4104_);
v_tree_4115_ = lean_ctor_get(v_d_4114_, 2);
lean_inc(v_tree_4115_);
if (lean_obj_tag(v_tree_4115_) == 0)
{
lean_object* v_k_4116_; lean_object* v_v_4117_; lean_object* v_size_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; uint8_t v___x_4121_; 
v_k_4116_ = lean_ctor_get(v_d_4114_, 0);
lean_inc(v_k_4116_);
v_v_4117_ = lean_ctor_get(v_d_4114_, 1);
lean_inc(v_v_4117_);
lean_dec_ref(v_d_4114_);
v_size_4118_ = lean_ctor_get(v_tree_4115_, 0);
v___x_4119_ = lean_unsigned_to_nat(3u);
v___x_4120_ = lean_nat_mul(v___x_4119_, v_size_4118_);
v___x_4121_ = lean_nat_dec_lt(v___x_4120_, v_size_4105_);
lean_dec(v___x_4120_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4126_; 
lean_dec(v_l_4108_);
v___x_4122_ = lean_unsigned_to_nat(1u);
v___x_4123_ = lean_nat_add(v___x_4122_, v_size_4118_);
v___x_4124_ = lean_nat_add(v___x_4123_, v_size_4105_);
lean_dec(v___x_4123_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v_r_3921_);
lean_ctor_set(v___x_4112_, 3, v_tree_4115_);
lean_ctor_set(v___x_4112_, 2, v_v_4117_);
lean_ctor_set(v___x_4112_, 1, v_k_4116_);
lean_ctor_set(v___x_4112_, 0, v___x_4124_);
v___x_4126_ = v___x_4112_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v_k_4116_);
lean_ctor_set(v_reuseFailAlloc_4127_, 2, v_v_4117_);
lean_ctor_set(v_reuseFailAlloc_4127_, 3, v_tree_4115_);
lean_ctor_set(v_reuseFailAlloc_4127_, 4, v_r_3921_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
else
{
lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4188_; 
lean_inc(v_r_4109_);
lean_inc(v_v_4107_);
lean_inc(v_k_4106_);
lean_inc(v_size_4105_);
v_isSharedCheck_4188_ = !lean_is_exclusive(v_r_3921_);
if (v_isSharedCheck_4188_ == 0)
{
lean_object* v_unused_4189_; lean_object* v_unused_4190_; lean_object* v_unused_4191_; lean_object* v_unused_4192_; lean_object* v_unused_4193_; 
v_unused_4189_ = lean_ctor_get(v_r_3921_, 4);
lean_dec(v_unused_4189_);
v_unused_4190_ = lean_ctor_get(v_r_3921_, 3);
lean_dec(v_unused_4190_);
v_unused_4191_ = lean_ctor_get(v_r_3921_, 2);
lean_dec(v_unused_4191_);
v_unused_4192_ = lean_ctor_get(v_r_3921_, 1);
lean_dec(v_unused_4192_);
v_unused_4193_ = lean_ctor_get(v_r_3921_, 0);
lean_dec(v_unused_4193_);
v___x_4129_ = v_r_3921_;
v_isShared_4130_ = v_isSharedCheck_4188_;
goto v_resetjp_4128_;
}
else
{
lean_dec(v_r_3921_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4188_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
if (lean_obj_tag(v_l_4108_) == 0)
{
if (lean_obj_tag(v_r_4109_) == 0)
{
lean_object* v_size_4131_; lean_object* v_k_4132_; lean_object* v_v_4133_; lean_object* v_l_4134_; lean_object* v_r_4135_; lean_object* v_size_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; uint8_t v___x_4139_; 
v_size_4131_ = lean_ctor_get(v_l_4108_, 0);
v_k_4132_ = lean_ctor_get(v_l_4108_, 1);
v_v_4133_ = lean_ctor_get(v_l_4108_, 2);
v_l_4134_ = lean_ctor_get(v_l_4108_, 3);
v_r_4135_ = lean_ctor_get(v_l_4108_, 4);
v_size_4136_ = lean_ctor_get(v_r_4109_, 0);
v___x_4137_ = lean_unsigned_to_nat(2u);
v___x_4138_ = lean_nat_mul(v___x_4137_, v_size_4136_);
v___x_4139_ = lean_nat_dec_lt(v_size_4131_, v___x_4138_);
lean_dec(v___x_4138_);
if (v___x_4139_ == 0)
{
lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4168_; 
lean_inc(v_r_4135_);
lean_inc(v_l_4134_);
lean_inc(v_v_4133_);
lean_inc(v_k_4132_);
v_isSharedCheck_4168_ = !lean_is_exclusive(v_l_4108_);
if (v_isSharedCheck_4168_ == 0)
{
lean_object* v_unused_4169_; lean_object* v_unused_4170_; lean_object* v_unused_4171_; lean_object* v_unused_4172_; lean_object* v_unused_4173_; 
v_unused_4169_ = lean_ctor_get(v_l_4108_, 4);
lean_dec(v_unused_4169_);
v_unused_4170_ = lean_ctor_get(v_l_4108_, 3);
lean_dec(v_unused_4170_);
v_unused_4171_ = lean_ctor_get(v_l_4108_, 2);
lean_dec(v_unused_4171_);
v_unused_4172_ = lean_ctor_get(v_l_4108_, 1);
lean_dec(v_unused_4172_);
v_unused_4173_ = lean_ctor_get(v_l_4108_, 0);
lean_dec(v_unused_4173_);
v___x_4141_ = v_l_4108_;
v_isShared_4142_ = v_isSharedCheck_4168_;
goto v_resetjp_4140_;
}
else
{
lean_dec(v_l_4108_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4168_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4158_; 
v___x_4143_ = lean_unsigned_to_nat(1u);
v___x_4144_ = lean_nat_add(v___x_4143_, v_size_4118_);
v___x_4145_ = lean_nat_add(v___x_4144_, v_size_4105_);
lean_dec(v_size_4105_);
if (lean_obj_tag(v_l_4134_) == 0)
{
lean_object* v_size_4166_; 
v_size_4166_ = lean_ctor_get(v_l_4134_, 0);
lean_inc(v_size_4166_);
v___y_4158_ = v_size_4166_;
goto v___jp_4157_;
}
else
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_unsigned_to_nat(0u);
v___y_4158_ = v___x_4167_;
goto v___jp_4157_;
}
v___jp_4146_:
{
lean_object* v___x_4150_; lean_object* v___x_4152_; 
v___x_4150_ = lean_nat_add(v___y_4148_, v___y_4149_);
lean_dec(v___y_4149_);
lean_dec(v___y_4148_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 4, v_r_4109_);
lean_ctor_set(v___x_4141_, 3, v_r_4135_);
lean_ctor_set(v___x_4141_, 2, v_v_4107_);
lean_ctor_set(v___x_4141_, 1, v_k_4106_);
lean_ctor_set(v___x_4141_, 0, v___x_4150_);
v___x_4152_ = v___x_4141_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4150_);
lean_ctor_set(v_reuseFailAlloc_4156_, 1, v_k_4106_);
lean_ctor_set(v_reuseFailAlloc_4156_, 2, v_v_4107_);
lean_ctor_set(v_reuseFailAlloc_4156_, 3, v_r_4135_);
lean_ctor_set(v_reuseFailAlloc_4156_, 4, v_r_4109_);
v___x_4152_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
lean_object* v___x_4154_; 
if (v_isShared_4130_ == 0)
{
lean_ctor_set(v___x_4129_, 4, v___x_4152_);
lean_ctor_set(v___x_4129_, 3, v___y_4147_);
lean_ctor_set(v___x_4129_, 2, v_v_4133_);
lean_ctor_set(v___x_4129_, 1, v_k_4132_);
lean_ctor_set(v___x_4129_, 0, v___x_4145_);
v___x_4154_ = v___x_4129_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4145_);
lean_ctor_set(v_reuseFailAlloc_4155_, 1, v_k_4132_);
lean_ctor_set(v_reuseFailAlloc_4155_, 2, v_v_4133_);
lean_ctor_set(v_reuseFailAlloc_4155_, 3, v___y_4147_);
lean_ctor_set(v_reuseFailAlloc_4155_, 4, v___x_4152_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
v___jp_4157_:
{
lean_object* v___x_4159_; lean_object* v___x_4161_; 
v___x_4159_ = lean_nat_add(v___x_4144_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec(v___x_4144_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v_l_4134_);
lean_ctor_set(v___x_4112_, 3, v_tree_4115_);
lean_ctor_set(v___x_4112_, 2, v_v_4117_);
lean_ctor_set(v___x_4112_, 1, v_k_4116_);
lean_ctor_set(v___x_4112_, 0, v___x_4159_);
v___x_4161_ = v___x_4112_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4159_);
lean_ctor_set(v_reuseFailAlloc_4165_, 1, v_k_4116_);
lean_ctor_set(v_reuseFailAlloc_4165_, 2, v_v_4117_);
lean_ctor_set(v_reuseFailAlloc_4165_, 3, v_tree_4115_);
lean_ctor_set(v_reuseFailAlloc_4165_, 4, v_l_4134_);
v___x_4161_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4162_; 
v___x_4162_ = lean_nat_add(v___x_4143_, v_size_4136_);
if (lean_obj_tag(v_r_4135_) == 0)
{
lean_object* v_size_4163_; 
v_size_4163_ = lean_ctor_get(v_r_4135_, 0);
lean_inc(v_size_4163_);
v___y_4147_ = v___x_4161_;
v___y_4148_ = v___x_4162_;
v___y_4149_ = v_size_4163_;
goto v___jp_4146_;
}
else
{
lean_object* v___x_4164_; 
v___x_4164_ = lean_unsigned_to_nat(0u);
v___y_4147_ = v___x_4161_;
v___y_4148_ = v___x_4162_;
v___y_4149_ = v___x_4164_;
goto v___jp_4146_;
}
}
}
}
}
else
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
v___x_4174_ = lean_unsigned_to_nat(1u);
v___x_4175_ = lean_nat_add(v___x_4174_, v_size_4118_);
v___x_4176_ = lean_nat_add(v___x_4175_, v_size_4105_);
lean_dec(v_size_4105_);
v___x_4177_ = lean_nat_add(v___x_4175_, v_size_4131_);
lean_dec(v___x_4175_);
if (v_isShared_4130_ == 0)
{
lean_ctor_set(v___x_4129_, 4, v_l_4108_);
lean_ctor_set(v___x_4129_, 3, v_tree_4115_);
lean_ctor_set(v___x_4129_, 2, v_v_4117_);
lean_ctor_set(v___x_4129_, 1, v_k_4116_);
lean_ctor_set(v___x_4129_, 0, v___x_4177_);
v___x_4179_ = v___x_4129_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4183_, 1, v_k_4116_);
lean_ctor_set(v_reuseFailAlloc_4183_, 2, v_v_4117_);
lean_ctor_set(v_reuseFailAlloc_4183_, 3, v_tree_4115_);
lean_ctor_set(v_reuseFailAlloc_4183_, 4, v_l_4108_);
v___x_4179_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4181_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v_r_4109_);
lean_ctor_set(v___x_4112_, 3, v___x_4179_);
lean_ctor_set(v___x_4112_, 2, v_v_4107_);
lean_ctor_set(v___x_4112_, 1, v_k_4106_);
lean_ctor_set(v___x_4112_, 0, v___x_4176_);
v___x_4181_ = v___x_4112_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4182_, 1, v_k_4106_);
lean_ctor_set(v_reuseFailAlloc_4182_, 2, v_v_4107_);
lean_ctor_set(v_reuseFailAlloc_4182_, 3, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4182_, 4, v_r_4109_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
else
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_dec_ref(v_l_4108_);
lean_del_object(v___x_4129_);
lean_dec(v_v_4117_);
lean_dec_ref(v_tree_4115_);
lean_dec(v_k_4116_);
lean_del_object(v___x_4112_);
lean_dec(v_v_4107_);
lean_dec(v_k_4106_);
lean_dec(v_size_4105_);
v___x_4184_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__7);
v___x_4185_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4184_);
return v___x_4185_;
}
}
else
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
lean_del_object(v___x_4129_);
lean_dec(v_v_4117_);
lean_dec_ref(v_tree_4115_);
lean_dec(v_k_4116_);
lean_del_object(v___x_4112_);
lean_dec(v_r_4109_);
lean_dec(v_v_4107_);
lean_dec(v_k_4106_);
lean_dec(v_size_4105_);
v___x_4186_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__8);
v___x_4187_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4186_);
return v___x_4187_;
}
}
}
}
else
{
lean_inc(v_r_4109_);
if (lean_obj_tag(v_l_4108_) == 0)
{
lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4231_; 
lean_inc(v_v_4107_);
lean_inc(v_k_4106_);
lean_inc(v_size_4105_);
v_isSharedCheck_4231_ = !lean_is_exclusive(v_r_3921_);
if (v_isSharedCheck_4231_ == 0)
{
lean_object* v_unused_4232_; lean_object* v_unused_4233_; lean_object* v_unused_4234_; lean_object* v_unused_4235_; lean_object* v_unused_4236_; 
v_unused_4232_ = lean_ctor_get(v_r_3921_, 4);
lean_dec(v_unused_4232_);
v_unused_4233_ = lean_ctor_get(v_r_3921_, 3);
lean_dec(v_unused_4233_);
v_unused_4234_ = lean_ctor_get(v_r_3921_, 2);
lean_dec(v_unused_4234_);
v_unused_4235_ = lean_ctor_get(v_r_3921_, 1);
lean_dec(v_unused_4235_);
v_unused_4236_ = lean_ctor_get(v_r_3921_, 0);
lean_dec(v_unused_4236_);
v___x_4195_ = v_r_3921_;
v_isShared_4196_ = v_isSharedCheck_4231_;
goto v_resetjp_4194_;
}
else
{
lean_dec(v_r_3921_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4231_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
if (lean_obj_tag(v_r_4109_) == 0)
{
lean_object* v_k_4197_; lean_object* v_v_4198_; lean_object* v_size_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4204_; 
v_k_4197_ = lean_ctor_get(v_d_4114_, 0);
lean_inc(v_k_4197_);
v_v_4198_ = lean_ctor_get(v_d_4114_, 1);
lean_inc(v_v_4198_);
lean_dec_ref(v_d_4114_);
v_size_4199_ = lean_ctor_get(v_l_4108_, 0);
v___x_4200_ = lean_unsigned_to_nat(1u);
v___x_4201_ = lean_nat_add(v___x_4200_, v_size_4105_);
lean_dec(v_size_4105_);
v___x_4202_ = lean_nat_add(v___x_4200_, v_size_4199_);
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 4, v_l_4108_);
lean_ctor_set(v___x_4195_, 3, v_tree_4115_);
lean_ctor_set(v___x_4195_, 2, v_v_4198_);
lean_ctor_set(v___x_4195_, 1, v_k_4197_);
lean_ctor_set(v___x_4195_, 0, v___x_4202_);
v___x_4204_ = v___x_4195_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4202_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v_k_4197_);
lean_ctor_set(v_reuseFailAlloc_4208_, 2, v_v_4198_);
lean_ctor_set(v_reuseFailAlloc_4208_, 3, v_tree_4115_);
lean_ctor_set(v_reuseFailAlloc_4208_, 4, v_l_4108_);
v___x_4204_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
lean_object* v___x_4206_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v_r_4109_);
lean_ctor_set(v___x_4112_, 3, v___x_4204_);
lean_ctor_set(v___x_4112_, 2, v_v_4107_);
lean_ctor_set(v___x_4112_, 1, v_k_4106_);
lean_ctor_set(v___x_4112_, 0, v___x_4201_);
v___x_4206_ = v___x_4112_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v___x_4201_);
lean_ctor_set(v_reuseFailAlloc_4207_, 1, v_k_4106_);
lean_ctor_set(v_reuseFailAlloc_4207_, 2, v_v_4107_);
lean_ctor_set(v_reuseFailAlloc_4207_, 3, v___x_4204_);
lean_ctor_set(v_reuseFailAlloc_4207_, 4, v_r_4109_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
else
{
lean_object* v_k_4209_; lean_object* v_v_4210_; lean_object* v_k_4211_; lean_object* v_v_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4227_; 
lean_dec(v_size_4105_);
v_k_4209_ = lean_ctor_get(v_d_4114_, 0);
lean_inc(v_k_4209_);
v_v_4210_ = lean_ctor_get(v_d_4114_, 1);
lean_inc(v_v_4210_);
lean_dec_ref(v_d_4114_);
v_k_4211_ = lean_ctor_get(v_l_4108_, 1);
v_v_4212_ = lean_ctor_get(v_l_4108_, 2);
v_isSharedCheck_4227_ = !lean_is_exclusive(v_l_4108_);
if (v_isSharedCheck_4227_ == 0)
{
lean_object* v_unused_4228_; lean_object* v_unused_4229_; lean_object* v_unused_4230_; 
v_unused_4228_ = lean_ctor_get(v_l_4108_, 4);
lean_dec(v_unused_4228_);
v_unused_4229_ = lean_ctor_get(v_l_4108_, 3);
lean_dec(v_unused_4229_);
v_unused_4230_ = lean_ctor_get(v_l_4108_, 0);
lean_dec(v_unused_4230_);
v___x_4214_ = v_l_4108_;
v_isShared_4215_ = v_isSharedCheck_4227_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_v_4212_);
lean_inc(v_k_4211_);
lean_dec(v_l_4108_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4227_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4219_; 
v___x_4216_ = lean_unsigned_to_nat(3u);
v___x_4217_ = lean_unsigned_to_nat(1u);
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 4, v_r_4109_);
lean_ctor_set(v___x_4214_, 3, v_r_4109_);
lean_ctor_set(v___x_4214_, 2, v_v_4210_);
lean_ctor_set(v___x_4214_, 1, v_k_4209_);
lean_ctor_set(v___x_4214_, 0, v___x_4217_);
v___x_4219_ = v___x_4214_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4217_);
lean_ctor_set(v_reuseFailAlloc_4226_, 1, v_k_4209_);
lean_ctor_set(v_reuseFailAlloc_4226_, 2, v_v_4210_);
lean_ctor_set(v_reuseFailAlloc_4226_, 3, v_r_4109_);
lean_ctor_set(v_reuseFailAlloc_4226_, 4, v_r_4109_);
v___x_4219_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
lean_object* v___x_4221_; 
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 3, v_r_4109_);
lean_ctor_set(v___x_4195_, 0, v___x_4217_);
v___x_4221_ = v___x_4195_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4217_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_k_4106_);
lean_ctor_set(v_reuseFailAlloc_4225_, 2, v_v_4107_);
lean_ctor_set(v_reuseFailAlloc_4225_, 3, v_r_4109_);
lean_ctor_set(v_reuseFailAlloc_4225_, 4, v_r_4109_);
v___x_4221_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
lean_object* v___x_4223_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v___x_4221_);
lean_ctor_set(v___x_4112_, 3, v___x_4219_);
lean_ctor_set(v___x_4112_, 2, v_v_4212_);
lean_ctor_set(v___x_4112_, 1, v_k_4211_);
lean_ctor_set(v___x_4112_, 0, v___x_4216_);
v___x_4223_ = v___x_4112_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4216_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v_k_4211_);
lean_ctor_set(v_reuseFailAlloc_4224_, 2, v_v_4212_);
lean_ctor_set(v_reuseFailAlloc_4224_, 3, v___x_4219_);
lean_ctor_set(v_reuseFailAlloc_4224_, 4, v___x_4221_);
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
if (lean_obj_tag(v_r_4109_) == 0)
{
lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4250_; 
lean_inc(v_v_4107_);
lean_inc(v_k_4106_);
v_isSharedCheck_4250_ = !lean_is_exclusive(v_r_3921_);
if (v_isSharedCheck_4250_ == 0)
{
lean_object* v_unused_4251_; lean_object* v_unused_4252_; lean_object* v_unused_4253_; lean_object* v_unused_4254_; lean_object* v_unused_4255_; 
v_unused_4251_ = lean_ctor_get(v_r_3921_, 4);
lean_dec(v_unused_4251_);
v_unused_4252_ = lean_ctor_get(v_r_3921_, 3);
lean_dec(v_unused_4252_);
v_unused_4253_ = lean_ctor_get(v_r_3921_, 2);
lean_dec(v_unused_4253_);
v_unused_4254_ = lean_ctor_get(v_r_3921_, 1);
lean_dec(v_unused_4254_);
v_unused_4255_ = lean_ctor_get(v_r_3921_, 0);
lean_dec(v_unused_4255_);
v___x_4238_ = v_r_3921_;
v_isShared_4239_ = v_isSharedCheck_4250_;
goto v_resetjp_4237_;
}
else
{
lean_dec(v_r_3921_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4250_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v_k_4240_; lean_object* v_v_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4245_; 
v_k_4240_ = lean_ctor_get(v_d_4114_, 0);
lean_inc(v_k_4240_);
v_v_4241_ = lean_ctor_get(v_d_4114_, 1);
lean_inc(v_v_4241_);
lean_dec_ref(v_d_4114_);
v___x_4242_ = lean_unsigned_to_nat(3u);
v___x_4243_ = lean_unsigned_to_nat(1u);
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 4, v_l_4108_);
lean_ctor_set(v___x_4238_, 2, v_v_4241_);
lean_ctor_set(v___x_4238_, 1, v_k_4240_);
lean_ctor_set(v___x_4238_, 0, v___x_4243_);
v___x_4245_ = v___x_4238_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4243_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v_k_4240_);
lean_ctor_set(v_reuseFailAlloc_4249_, 2, v_v_4241_);
lean_ctor_set(v_reuseFailAlloc_4249_, 3, v_l_4108_);
lean_ctor_set(v_reuseFailAlloc_4249_, 4, v_l_4108_);
v___x_4245_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
lean_object* v___x_4247_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v_r_4109_);
lean_ctor_set(v___x_4112_, 3, v___x_4245_);
lean_ctor_set(v___x_4112_, 2, v_v_4107_);
lean_ctor_set(v___x_4112_, 1, v_k_4106_);
lean_ctor_set(v___x_4112_, 0, v___x_4242_);
v___x_4247_ = v___x_4112_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4242_);
lean_ctor_set(v_reuseFailAlloc_4248_, 1, v_k_4106_);
lean_ctor_set(v_reuseFailAlloc_4248_, 2, v_v_4107_);
lean_ctor_set(v_reuseFailAlloc_4248_, 3, v___x_4245_);
lean_ctor_set(v_reuseFailAlloc_4248_, 4, v_r_4109_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
else
{
lean_object* v_k_4256_; lean_object* v_v_4257_; lean_object* v___x_4258_; lean_object* v___x_4260_; 
v_k_4256_ = lean_ctor_get(v_d_4114_, 0);
lean_inc(v_k_4256_);
v_v_4257_ = lean_ctor_get(v_d_4114_, 1);
lean_inc(v_v_4257_);
lean_dec_ref(v_d_4114_);
v___x_4258_ = lean_unsigned_to_nat(2u);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v_r_3921_);
lean_ctor_set(v___x_4112_, 3, v_r_4109_);
lean_ctor_set(v___x_4112_, 2, v_v_4257_);
lean_ctor_set(v___x_4112_, 1, v_k_4256_);
lean_ctor_set(v___x_4112_, 0, v___x_4258_);
v___x_4260_ = v___x_4112_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4258_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v_k_4256_);
lean_ctor_set(v_reuseFailAlloc_4261_, 2, v_v_4257_);
lean_ctor_set(v_reuseFailAlloc_4261_, 3, v_r_4109_);
lean_ctor_set(v_reuseFailAlloc_4261_, 4, v_r_3921_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
}
}
}
else
{
lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4430_; 
lean_inc(v_r_4109_);
lean_inc(v_v_4107_);
lean_inc(v_k_4106_);
v_isSharedCheck_4430_ = !lean_is_exclusive(v_r_3921_);
if (v_isSharedCheck_4430_ == 0)
{
lean_object* v_unused_4431_; lean_object* v_unused_4432_; lean_object* v_unused_4433_; lean_object* v_unused_4434_; lean_object* v_unused_4435_; 
v_unused_4431_ = lean_ctor_get(v_r_3921_, 4);
lean_dec(v_unused_4431_);
v_unused_4432_ = lean_ctor_get(v_r_3921_, 3);
lean_dec(v_unused_4432_);
v_unused_4433_ = lean_ctor_get(v_r_3921_, 2);
lean_dec(v_unused_4433_);
v_unused_4434_ = lean_ctor_get(v_r_3921_, 1);
lean_dec(v_unused_4434_);
v_unused_4435_ = lean_ctor_get(v_r_3921_, 0);
lean_dec(v_unused_4435_);
v___x_4269_ = v_r_3921_;
v_isShared_4270_ = v_isSharedCheck_4430_;
goto v_resetjp_4268_;
}
else
{
lean_dec(v_r_3921_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4430_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v_d_4271_; lean_object* v_tree_4272_; 
v_d_4271_ = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(v_k_4106_, v_v_4107_, v_l_4108_, v_r_4109_);
v_tree_4272_ = lean_ctor_get(v_d_4271_, 2);
lean_inc(v_tree_4272_);
if (lean_obj_tag(v_tree_4272_) == 0)
{
lean_object* v_k_4273_; lean_object* v_v_4274_; lean_object* v_size_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; uint8_t v___x_4278_; 
v_k_4273_ = lean_ctor_get(v_d_4271_, 0);
lean_inc(v_k_4273_);
v_v_4274_ = lean_ctor_get(v_d_4271_, 1);
lean_inc(v_v_4274_);
lean_dec_ref(v_d_4271_);
v_size_4275_ = lean_ctor_get(v_tree_4272_, 0);
v___x_4276_ = lean_unsigned_to_nat(3u);
v___x_4277_ = lean_nat_mul(v___x_4276_, v_size_4275_);
v___x_4278_ = lean_nat_dec_lt(v___x_4277_, v_size_4100_);
lean_dec(v___x_4277_);
if (v___x_4278_ == 0)
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4283_; 
lean_dec(v_r_4104_);
v___x_4279_ = lean_unsigned_to_nat(1u);
v___x_4280_ = lean_nat_add(v___x_4279_, v_size_4100_);
v___x_4281_ = lean_nat_add(v___x_4280_, v_size_4275_);
lean_dec(v___x_4280_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 4, v_tree_4272_);
lean_ctor_set(v___x_4269_, 3, v_l_3920_);
lean_ctor_set(v___x_4269_, 2, v_v_4274_);
lean_ctor_set(v___x_4269_, 1, v_k_4273_);
lean_ctor_set(v___x_4269_, 0, v___x_4281_);
v___x_4283_ = v___x_4269_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4281_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_k_4273_);
lean_ctor_set(v_reuseFailAlloc_4284_, 2, v_v_4274_);
lean_ctor_set(v_reuseFailAlloc_4284_, 3, v_l_3920_);
lean_ctor_set(v_reuseFailAlloc_4284_, 4, v_tree_4272_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
else
{
lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4356_; 
lean_inc(v_l_4103_);
lean_inc(v_v_4102_);
lean_inc(v_k_4101_);
lean_inc(v_size_4100_);
v_isSharedCheck_4356_ = !lean_is_exclusive(v_l_3920_);
if (v_isSharedCheck_4356_ == 0)
{
lean_object* v_unused_4357_; lean_object* v_unused_4358_; lean_object* v_unused_4359_; lean_object* v_unused_4360_; lean_object* v_unused_4361_; 
v_unused_4357_ = lean_ctor_get(v_l_3920_, 4);
lean_dec(v_unused_4357_);
v_unused_4358_ = lean_ctor_get(v_l_3920_, 3);
lean_dec(v_unused_4358_);
v_unused_4359_ = lean_ctor_get(v_l_3920_, 2);
lean_dec(v_unused_4359_);
v_unused_4360_ = lean_ctor_get(v_l_3920_, 1);
lean_dec(v_unused_4360_);
v_unused_4361_ = lean_ctor_get(v_l_3920_, 0);
lean_dec(v_unused_4361_);
v___x_4286_ = v_l_3920_;
v_isShared_4287_ = v_isSharedCheck_4356_;
goto v_resetjp_4285_;
}
else
{
lean_dec(v_l_3920_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4356_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
if (lean_obj_tag(v_l_4103_) == 0)
{
if (lean_obj_tag(v_r_4104_) == 0)
{
lean_object* v_size_4288_; lean_object* v_size_4289_; lean_object* v_k_4290_; lean_object* v_v_4291_; lean_object* v_l_4292_; lean_object* v_r_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; uint8_t v___x_4296_; 
v_size_4288_ = lean_ctor_get(v_l_4103_, 0);
v_size_4289_ = lean_ctor_get(v_r_4104_, 0);
v_k_4290_ = lean_ctor_get(v_r_4104_, 1);
v_v_4291_ = lean_ctor_get(v_r_4104_, 2);
v_l_4292_ = lean_ctor_get(v_r_4104_, 3);
v_r_4293_ = lean_ctor_get(v_r_4104_, 4);
v___x_4294_ = lean_unsigned_to_nat(2u);
v___x_4295_ = lean_nat_mul(v___x_4294_, v_size_4288_);
v___x_4296_ = lean_nat_dec_lt(v_size_4289_, v___x_4295_);
lean_dec(v___x_4295_);
if (v___x_4296_ == 0)
{
lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4335_; 
lean_inc(v_r_4293_);
lean_inc(v_l_4292_);
lean_inc(v_v_4291_);
lean_inc(v_k_4290_);
lean_del_object(v___x_4286_);
v_isSharedCheck_4335_ = !lean_is_exclusive(v_r_4104_);
if (v_isSharedCheck_4335_ == 0)
{
lean_object* v_unused_4336_; lean_object* v_unused_4337_; lean_object* v_unused_4338_; lean_object* v_unused_4339_; lean_object* v_unused_4340_; 
v_unused_4336_ = lean_ctor_get(v_r_4104_, 4);
lean_dec(v_unused_4336_);
v_unused_4337_ = lean_ctor_get(v_r_4104_, 3);
lean_dec(v_unused_4337_);
v_unused_4338_ = lean_ctor_get(v_r_4104_, 2);
lean_dec(v_unused_4338_);
v_unused_4339_ = lean_ctor_get(v_r_4104_, 1);
lean_dec(v_unused_4339_);
v_unused_4340_ = lean_ctor_get(v_r_4104_, 0);
lean_dec(v_unused_4340_);
v___x_4298_ = v_r_4104_;
v_isShared_4299_ = v_isSharedCheck_4335_;
goto v_resetjp_4297_;
}
else
{
lean_dec(v_r_4104_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4335_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___x_4323_; lean_object* v___y_4325_; 
v___x_4300_ = lean_unsigned_to_nat(1u);
v___x_4301_ = lean_nat_add(v___x_4300_, v_size_4100_);
lean_dec(v_size_4100_);
v___x_4302_ = lean_nat_add(v___x_4301_, v_size_4275_);
lean_dec(v___x_4301_);
v___x_4323_ = lean_nat_add(v___x_4300_, v_size_4288_);
if (lean_obj_tag(v_l_4292_) == 0)
{
lean_object* v_size_4333_; 
v_size_4333_ = lean_ctor_get(v_l_4292_, 0);
lean_inc(v_size_4333_);
v___y_4325_ = v_size_4333_;
goto v___jp_4324_;
}
else
{
lean_object* v___x_4334_; 
v___x_4334_ = lean_unsigned_to_nat(0u);
v___y_4325_ = v___x_4334_;
goto v___jp_4324_;
}
v___jp_4303_:
{
lean_object* v___x_4307_; lean_object* v___x_4309_; 
v___x_4307_ = lean_nat_add(v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec(v___y_4305_);
lean_inc_ref(v_tree_4272_);
if (v_isShared_4299_ == 0)
{
lean_ctor_set(v___x_4298_, 4, v_tree_4272_);
lean_ctor_set(v___x_4298_, 3, v_r_4293_);
lean_ctor_set(v___x_4298_, 2, v_v_4274_);
lean_ctor_set(v___x_4298_, 1, v_k_4273_);
lean_ctor_set(v___x_4298_, 0, v___x_4307_);
v___x_4309_ = v___x_4298_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4307_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v_k_4273_);
lean_ctor_set(v_reuseFailAlloc_4322_, 2, v_v_4274_);
lean_ctor_set(v_reuseFailAlloc_4322_, 3, v_r_4293_);
lean_ctor_set(v_reuseFailAlloc_4322_, 4, v_tree_4272_);
v___x_4309_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
v_isSharedCheck_4316_ = !lean_is_exclusive(v_tree_4272_);
if (v_isSharedCheck_4316_ == 0)
{
lean_object* v_unused_4317_; lean_object* v_unused_4318_; lean_object* v_unused_4319_; lean_object* v_unused_4320_; lean_object* v_unused_4321_; 
v_unused_4317_ = lean_ctor_get(v_tree_4272_, 4);
lean_dec(v_unused_4317_);
v_unused_4318_ = lean_ctor_get(v_tree_4272_, 3);
lean_dec(v_unused_4318_);
v_unused_4319_ = lean_ctor_get(v_tree_4272_, 2);
lean_dec(v_unused_4319_);
v_unused_4320_ = lean_ctor_get(v_tree_4272_, 1);
lean_dec(v_unused_4320_);
v_unused_4321_ = lean_ctor_get(v_tree_4272_, 0);
lean_dec(v_unused_4321_);
v___x_4311_ = v_tree_4272_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_dec(v_tree_4272_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
lean_ctor_set(v___x_4311_, 4, v___x_4309_);
lean_ctor_set(v___x_4311_, 3, v___y_4304_);
lean_ctor_set(v___x_4311_, 2, v_v_4291_);
lean_ctor_set(v___x_4311_, 1, v_k_4290_);
lean_ctor_set(v___x_4311_, 0, v___x_4302_);
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4302_);
lean_ctor_set(v_reuseFailAlloc_4315_, 1, v_k_4290_);
lean_ctor_set(v_reuseFailAlloc_4315_, 2, v_v_4291_);
lean_ctor_set(v_reuseFailAlloc_4315_, 3, v___y_4304_);
lean_ctor_set(v_reuseFailAlloc_4315_, 4, v___x_4309_);
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
v___jp_4324_:
{
lean_object* v___x_4326_; lean_object* v___x_4328_; 
v___x_4326_ = lean_nat_add(v___x_4323_, v___y_4325_);
lean_dec(v___y_4325_);
lean_dec(v___x_4323_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 4, v_l_4292_);
lean_ctor_set(v___x_4269_, 3, v_l_4103_);
lean_ctor_set(v___x_4269_, 2, v_v_4102_);
lean_ctor_set(v___x_4269_, 1, v_k_4101_);
lean_ctor_set(v___x_4269_, 0, v___x_4326_);
v___x_4328_ = v___x_4269_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4326_);
lean_ctor_set(v_reuseFailAlloc_4332_, 1, v_k_4101_);
lean_ctor_set(v_reuseFailAlloc_4332_, 2, v_v_4102_);
lean_ctor_set(v_reuseFailAlloc_4332_, 3, v_l_4103_);
lean_ctor_set(v_reuseFailAlloc_4332_, 4, v_l_4292_);
v___x_4328_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
lean_object* v___x_4329_; 
v___x_4329_ = lean_nat_add(v___x_4300_, v_size_4275_);
if (lean_obj_tag(v_r_4293_) == 0)
{
lean_object* v_size_4330_; 
v_size_4330_ = lean_ctor_get(v_r_4293_, 0);
lean_inc(v_size_4330_);
v___y_4304_ = v___x_4328_;
v___y_4305_ = v___x_4329_;
v___y_4306_ = v_size_4330_;
goto v___jp_4303_;
}
else
{
lean_object* v___x_4331_; 
v___x_4331_ = lean_unsigned_to_nat(0u);
v___y_4304_ = v___x_4328_;
v___y_4305_ = v___x_4329_;
v___y_4306_ = v___x_4331_;
goto v___jp_4303_;
}
}
}
}
}
else
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4347_; 
v___x_4341_ = lean_unsigned_to_nat(1u);
v___x_4342_ = lean_nat_add(v___x_4341_, v_size_4100_);
lean_dec(v_size_4100_);
v___x_4343_ = lean_nat_add(v___x_4342_, v_size_4275_);
lean_dec(v___x_4342_);
v___x_4344_ = lean_nat_add(v___x_4341_, v_size_4275_);
v___x_4345_ = lean_nat_add(v___x_4344_, v_size_4289_);
lean_dec(v___x_4344_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 4, v_tree_4272_);
lean_ctor_set(v___x_4269_, 3, v_r_4104_);
lean_ctor_set(v___x_4269_, 2, v_v_4274_);
lean_ctor_set(v___x_4269_, 1, v_k_4273_);
lean_ctor_set(v___x_4269_, 0, v___x_4345_);
v___x_4347_ = v___x_4269_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4345_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v_k_4273_);
lean_ctor_set(v_reuseFailAlloc_4351_, 2, v_v_4274_);
lean_ctor_set(v_reuseFailAlloc_4351_, 3, v_r_4104_);
lean_ctor_set(v_reuseFailAlloc_4351_, 4, v_tree_4272_);
v___x_4347_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
lean_object* v___x_4349_; 
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 4, v___x_4347_);
lean_ctor_set(v___x_4286_, 0, v___x_4343_);
v___x_4349_ = v___x_4286_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4343_);
lean_ctor_set(v_reuseFailAlloc_4350_, 1, v_k_4101_);
lean_ctor_set(v_reuseFailAlloc_4350_, 2, v_v_4102_);
lean_ctor_set(v_reuseFailAlloc_4350_, 3, v_l_4103_);
lean_ctor_set(v_reuseFailAlloc_4350_, 4, v___x_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
else
{
lean_object* v___x_4352_; lean_object* v___x_4353_; 
lean_dec_ref(v_l_4103_);
lean_del_object(v___x_4286_);
lean_dec(v_v_4274_);
lean_dec_ref(v_tree_4272_);
lean_dec(v_k_4273_);
lean_del_object(v___x_4269_);
lean_dec(v_v_4102_);
lean_dec(v_k_4101_);
lean_dec(v_size_4100_);
v___x_4352_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3);
v___x_4353_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4352_);
return v___x_4353_;
}
}
else
{
lean_object* v___x_4354_; lean_object* v___x_4355_; 
lean_del_object(v___x_4286_);
lean_dec(v_v_4274_);
lean_dec(v_k_4273_);
lean_dec_ref(v_tree_4272_);
lean_del_object(v___x_4269_);
lean_dec(v_r_4104_);
lean_dec(v_v_4102_);
lean_dec(v_k_4101_);
lean_dec(v_size_4100_);
v___x_4354_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4);
v___x_4355_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4354_);
return v___x_4355_;
}
}
}
}
else
{
if (lean_obj_tag(v_l_4103_) == 0)
{
lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4387_; 
lean_inc_ref(v_l_4103_);
lean_inc(v_v_4102_);
lean_inc(v_k_4101_);
lean_inc(v_size_4100_);
v_isSharedCheck_4387_ = !lean_is_exclusive(v_l_3920_);
if (v_isSharedCheck_4387_ == 0)
{
lean_object* v_unused_4388_; lean_object* v_unused_4389_; lean_object* v_unused_4390_; lean_object* v_unused_4391_; lean_object* v_unused_4392_; 
v_unused_4388_ = lean_ctor_get(v_l_3920_, 4);
lean_dec(v_unused_4388_);
v_unused_4389_ = lean_ctor_get(v_l_3920_, 3);
lean_dec(v_unused_4389_);
v_unused_4390_ = lean_ctor_get(v_l_3920_, 2);
lean_dec(v_unused_4390_);
v_unused_4391_ = lean_ctor_get(v_l_3920_, 1);
lean_dec(v_unused_4391_);
v_unused_4392_ = lean_ctor_get(v_l_3920_, 0);
lean_dec(v_unused_4392_);
v___x_4363_ = v_l_3920_;
v_isShared_4364_ = v_isSharedCheck_4387_;
goto v_resetjp_4362_;
}
else
{
lean_dec(v_l_3920_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4387_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
if (lean_obj_tag(v_r_4104_) == 0)
{
lean_object* v_k_4365_; lean_object* v_v_4366_; lean_object* v_size_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4372_; 
v_k_4365_ = lean_ctor_get(v_d_4271_, 0);
lean_inc(v_k_4365_);
v_v_4366_ = lean_ctor_get(v_d_4271_, 1);
lean_inc(v_v_4366_);
lean_dec_ref(v_d_4271_);
v_size_4367_ = lean_ctor_get(v_r_4104_, 0);
v___x_4368_ = lean_unsigned_to_nat(1u);
v___x_4369_ = lean_nat_add(v___x_4368_, v_size_4100_);
lean_dec(v_size_4100_);
v___x_4370_ = lean_nat_add(v___x_4368_, v_size_4367_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 4, v_tree_4272_);
lean_ctor_set(v___x_4269_, 3, v_r_4104_);
lean_ctor_set(v___x_4269_, 2, v_v_4366_);
lean_ctor_set(v___x_4269_, 1, v_k_4365_);
lean_ctor_set(v___x_4269_, 0, v___x_4370_);
v___x_4372_ = v___x_4269_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___x_4370_);
lean_ctor_set(v_reuseFailAlloc_4376_, 1, v_k_4365_);
lean_ctor_set(v_reuseFailAlloc_4376_, 2, v_v_4366_);
lean_ctor_set(v_reuseFailAlloc_4376_, 3, v_r_4104_);
lean_ctor_set(v_reuseFailAlloc_4376_, 4, v_tree_4272_);
v___x_4372_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
lean_object* v___x_4374_; 
if (v_isShared_4364_ == 0)
{
lean_ctor_set(v___x_4363_, 4, v___x_4372_);
lean_ctor_set(v___x_4363_, 0, v___x_4369_);
v___x_4374_ = v___x_4363_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4369_);
lean_ctor_set(v_reuseFailAlloc_4375_, 1, v_k_4101_);
lean_ctor_set(v_reuseFailAlloc_4375_, 2, v_v_4102_);
lean_ctor_set(v_reuseFailAlloc_4375_, 3, v_l_4103_);
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
else
{
lean_object* v_k_4377_; lean_object* v_v_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4382_; 
lean_dec(v_size_4100_);
v_k_4377_ = lean_ctor_get(v_d_4271_, 0);
lean_inc(v_k_4377_);
v_v_4378_ = lean_ctor_get(v_d_4271_, 1);
lean_inc(v_v_4378_);
lean_dec_ref(v_d_4271_);
v___x_4379_ = lean_unsigned_to_nat(3u);
v___x_4380_ = lean_unsigned_to_nat(1u);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 4, v_r_4104_);
lean_ctor_set(v___x_4269_, 3, v_r_4104_);
lean_ctor_set(v___x_4269_, 2, v_v_4378_);
lean_ctor_set(v___x_4269_, 1, v_k_4377_);
lean_ctor_set(v___x_4269_, 0, v___x_4380_);
v___x_4382_ = v___x_4269_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4380_);
lean_ctor_set(v_reuseFailAlloc_4386_, 1, v_k_4377_);
lean_ctor_set(v_reuseFailAlloc_4386_, 2, v_v_4378_);
lean_ctor_set(v_reuseFailAlloc_4386_, 3, v_r_4104_);
lean_ctor_set(v_reuseFailAlloc_4386_, 4, v_r_4104_);
v___x_4382_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
lean_object* v___x_4384_; 
if (v_isShared_4364_ == 0)
{
lean_ctor_set(v___x_4363_, 4, v___x_4382_);
lean_ctor_set(v___x_4363_, 0, v___x_4379_);
v___x_4384_ = v___x_4363_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4379_);
lean_ctor_set(v_reuseFailAlloc_4385_, 1, v_k_4101_);
lean_ctor_set(v_reuseFailAlloc_4385_, 2, v_v_4102_);
lean_ctor_set(v_reuseFailAlloc_4385_, 3, v_l_4103_);
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
else
{
if (lean_obj_tag(v_r_4104_) == 0)
{
lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4418_; 
lean_inc(v_l_4103_);
lean_inc(v_v_4102_);
lean_inc(v_k_4101_);
v_isSharedCheck_4418_ = !lean_is_exclusive(v_l_3920_);
if (v_isSharedCheck_4418_ == 0)
{
lean_object* v_unused_4419_; lean_object* v_unused_4420_; lean_object* v_unused_4421_; lean_object* v_unused_4422_; lean_object* v_unused_4423_; 
v_unused_4419_ = lean_ctor_get(v_l_3920_, 4);
lean_dec(v_unused_4419_);
v_unused_4420_ = lean_ctor_get(v_l_3920_, 3);
lean_dec(v_unused_4420_);
v_unused_4421_ = lean_ctor_get(v_l_3920_, 2);
lean_dec(v_unused_4421_);
v_unused_4422_ = lean_ctor_get(v_l_3920_, 1);
lean_dec(v_unused_4422_);
v_unused_4423_ = lean_ctor_get(v_l_3920_, 0);
lean_dec(v_unused_4423_);
v___x_4394_ = v_l_3920_;
v_isShared_4395_ = v_isSharedCheck_4418_;
goto v_resetjp_4393_;
}
else
{
lean_dec(v_l_3920_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4418_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v_k_4396_; lean_object* v_v_4397_; lean_object* v_k_4398_; lean_object* v_v_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4414_; 
v_k_4396_ = lean_ctor_get(v_d_4271_, 0);
lean_inc(v_k_4396_);
v_v_4397_ = lean_ctor_get(v_d_4271_, 1);
lean_inc(v_v_4397_);
lean_dec_ref(v_d_4271_);
v_k_4398_ = lean_ctor_get(v_r_4104_, 1);
v_v_4399_ = lean_ctor_get(v_r_4104_, 2);
v_isSharedCheck_4414_ = !lean_is_exclusive(v_r_4104_);
if (v_isSharedCheck_4414_ == 0)
{
lean_object* v_unused_4415_; lean_object* v_unused_4416_; lean_object* v_unused_4417_; 
v_unused_4415_ = lean_ctor_get(v_r_4104_, 4);
lean_dec(v_unused_4415_);
v_unused_4416_ = lean_ctor_get(v_r_4104_, 3);
lean_dec(v_unused_4416_);
v_unused_4417_ = lean_ctor_get(v_r_4104_, 0);
lean_dec(v_unused_4417_);
v___x_4401_ = v_r_4104_;
v_isShared_4402_ = v_isSharedCheck_4414_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_v_4399_);
lean_inc(v_k_4398_);
lean_dec(v_r_4104_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4414_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4406_; 
v___x_4403_ = lean_unsigned_to_nat(3u);
v___x_4404_ = lean_unsigned_to_nat(1u);
if (v_isShared_4402_ == 0)
{
lean_ctor_set(v___x_4401_, 4, v_l_4103_);
lean_ctor_set(v___x_4401_, 3, v_l_4103_);
lean_ctor_set(v___x_4401_, 2, v_v_4102_);
lean_ctor_set(v___x_4401_, 1, v_k_4101_);
lean_ctor_set(v___x_4401_, 0, v___x_4404_);
v___x_4406_ = v___x_4401_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4404_);
lean_ctor_set(v_reuseFailAlloc_4413_, 1, v_k_4101_);
lean_ctor_set(v_reuseFailAlloc_4413_, 2, v_v_4102_);
lean_ctor_set(v_reuseFailAlloc_4413_, 3, v_l_4103_);
lean_ctor_set(v_reuseFailAlloc_4413_, 4, v_l_4103_);
v___x_4406_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
lean_object* v___x_4408_; 
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 4, v_l_4103_);
lean_ctor_set(v___x_4269_, 3, v_l_4103_);
lean_ctor_set(v___x_4269_, 2, v_v_4397_);
lean_ctor_set(v___x_4269_, 1, v_k_4396_);
lean_ctor_set(v___x_4269_, 0, v___x_4404_);
v___x_4408_ = v___x_4269_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4404_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v_k_4396_);
lean_ctor_set(v_reuseFailAlloc_4412_, 2, v_v_4397_);
lean_ctor_set(v_reuseFailAlloc_4412_, 3, v_l_4103_);
lean_ctor_set(v_reuseFailAlloc_4412_, 4, v_l_4103_);
v___x_4408_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
lean_object* v___x_4410_; 
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 4, v___x_4408_);
lean_ctor_set(v___x_4394_, 3, v___x_4406_);
lean_ctor_set(v___x_4394_, 2, v_v_4399_);
lean_ctor_set(v___x_4394_, 1, v_k_4398_);
lean_ctor_set(v___x_4394_, 0, v___x_4403_);
v___x_4410_ = v___x_4394_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4403_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v_k_4398_);
lean_ctor_set(v_reuseFailAlloc_4411_, 2, v_v_4399_);
lean_ctor_set(v_reuseFailAlloc_4411_, 3, v___x_4406_);
lean_ctor_set(v_reuseFailAlloc_4411_, 4, v___x_4408_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
}
}
}
}
else
{
lean_object* v_k_4424_; lean_object* v_v_4425_; lean_object* v___x_4426_; lean_object* v___x_4428_; 
v_k_4424_ = lean_ctor_get(v_d_4271_, 0);
lean_inc(v_k_4424_);
v_v_4425_ = lean_ctor_get(v_d_4271_, 1);
lean_inc(v_v_4425_);
lean_dec_ref(v_d_4271_);
v___x_4426_ = lean_unsigned_to_nat(2u);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 4, v_r_4104_);
lean_ctor_set(v___x_4269_, 3, v_l_3920_);
lean_ctor_set(v___x_4269_, 2, v_v_4425_);
lean_ctor_set(v___x_4269_, 1, v_k_4424_);
lean_ctor_set(v___x_4269_, 0, v___x_4426_);
v___x_4428_ = v___x_4269_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4426_);
lean_ctor_set(v_reuseFailAlloc_4429_, 1, v_k_4424_);
lean_ctor_set(v_reuseFailAlloc_4429_, 2, v_v_4425_);
lean_ctor_set(v_reuseFailAlloc_4429_, 3, v_l_3920_);
lean_ctor_set(v_reuseFailAlloc_4429_, 4, v_r_4104_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
}
}
}
else
{
return v_l_3920_;
}
}
else
{
return v_r_3921_;
}
}
default: 
{
lean_object* v___x_4436_; 
v___x_4436_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_3915_, v_k_3916_, v_r_3921_);
if (lean_obj_tag(v___x_4436_) == 0)
{
if (lean_obj_tag(v_l_3920_) == 0)
{
lean_object* v_size_4437_; lean_object* v_size_4438_; lean_object* v_k_4439_; lean_object* v_v_4440_; lean_object* v_l_4441_; lean_object* v_r_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; uint8_t v___x_4445_; 
v_size_4437_ = lean_ctor_get(v___x_4436_, 0);
lean_inc(v_size_4437_);
v_size_4438_ = lean_ctor_get(v_l_3920_, 0);
v_k_4439_ = lean_ctor_get(v_l_3920_, 1);
v_v_4440_ = lean_ctor_get(v_l_3920_, 2);
v_l_4441_ = lean_ctor_get(v_l_3920_, 3);
v_r_4442_ = lean_ctor_get(v_l_3920_, 4);
lean_inc(v_r_4442_);
v___x_4443_ = lean_unsigned_to_nat(3u);
v___x_4444_ = lean_nat_mul(v___x_4443_, v_size_4437_);
v___x_4445_ = lean_nat_dec_lt(v___x_4444_, v_size_4438_);
lean_dec(v___x_4444_);
if (v___x_4445_ == 0)
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4450_; 
lean_dec(v_r_4442_);
v___x_4446_ = lean_unsigned_to_nat(1u);
v___x_4447_ = lean_nat_add(v___x_4446_, v_size_4438_);
v___x_4448_ = lean_nat_add(v___x_4447_, v_size_4437_);
lean_dec(v_size_4437_);
lean_dec(v___x_4447_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v___x_4436_);
lean_ctor_set(v___x_3923_, 0, v___x_4448_);
v___x_4450_ = v___x_3923_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4448_);
lean_ctor_set(v_reuseFailAlloc_4451_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4451_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4451_, 3, v_l_3920_);
lean_ctor_set(v_reuseFailAlloc_4451_, 4, v___x_4436_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
else
{
lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4523_; 
lean_inc(v_l_4441_);
lean_inc(v_v_4440_);
lean_inc(v_k_4439_);
lean_inc(v_size_4438_);
v_isSharedCheck_4523_ = !lean_is_exclusive(v_l_3920_);
if (v_isSharedCheck_4523_ == 0)
{
lean_object* v_unused_4524_; lean_object* v_unused_4525_; lean_object* v_unused_4526_; lean_object* v_unused_4527_; lean_object* v_unused_4528_; 
v_unused_4524_ = lean_ctor_get(v_l_3920_, 4);
lean_dec(v_unused_4524_);
v_unused_4525_ = lean_ctor_get(v_l_3920_, 3);
lean_dec(v_unused_4525_);
v_unused_4526_ = lean_ctor_get(v_l_3920_, 2);
lean_dec(v_unused_4526_);
v_unused_4527_ = lean_ctor_get(v_l_3920_, 1);
lean_dec(v_unused_4527_);
v_unused_4528_ = lean_ctor_get(v_l_3920_, 0);
lean_dec(v_unused_4528_);
v___x_4453_ = v_l_3920_;
v_isShared_4454_ = v_isSharedCheck_4523_;
goto v_resetjp_4452_;
}
else
{
lean_dec(v_l_3920_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4523_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
if (lean_obj_tag(v_l_4441_) == 0)
{
if (lean_obj_tag(v_r_4442_) == 0)
{
lean_object* v_size_4455_; lean_object* v_size_4456_; lean_object* v_k_4457_; lean_object* v_v_4458_; lean_object* v_l_4459_; lean_object* v_r_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; uint8_t v___x_4463_; 
v_size_4455_ = lean_ctor_get(v_l_4441_, 0);
v_size_4456_ = lean_ctor_get(v_r_4442_, 0);
v_k_4457_ = lean_ctor_get(v_r_4442_, 1);
v_v_4458_ = lean_ctor_get(v_r_4442_, 2);
v_l_4459_ = lean_ctor_get(v_r_4442_, 3);
v_r_4460_ = lean_ctor_get(v_r_4442_, 4);
v___x_4461_ = lean_unsigned_to_nat(2u);
v___x_4462_ = lean_nat_mul(v___x_4461_, v_size_4455_);
v___x_4463_ = lean_nat_dec_lt(v_size_4456_, v___x_4462_);
lean_dec(v___x_4462_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4493_; 
lean_inc(v_r_4460_);
lean_inc(v_l_4459_);
lean_inc(v_v_4458_);
lean_inc(v_k_4457_);
v_isSharedCheck_4493_ = !lean_is_exclusive(v_r_4442_);
if (v_isSharedCheck_4493_ == 0)
{
lean_object* v_unused_4494_; lean_object* v_unused_4495_; lean_object* v_unused_4496_; lean_object* v_unused_4497_; lean_object* v_unused_4498_; 
v_unused_4494_ = lean_ctor_get(v_r_4442_, 4);
lean_dec(v_unused_4494_);
v_unused_4495_ = lean_ctor_get(v_r_4442_, 3);
lean_dec(v_unused_4495_);
v_unused_4496_ = lean_ctor_get(v_r_4442_, 2);
lean_dec(v_unused_4496_);
v_unused_4497_ = lean_ctor_get(v_r_4442_, 1);
lean_dec(v_unused_4497_);
v_unused_4498_ = lean_ctor_get(v_r_4442_, 0);
lean_dec(v_unused_4498_);
v___x_4465_ = v_r_4442_;
v_isShared_4466_ = v_isSharedCheck_4493_;
goto v_resetjp_4464_;
}
else
{
lean_dec(v_r_4442_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4493_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___x_4481_; lean_object* v___y_4483_; 
v___x_4467_ = lean_unsigned_to_nat(1u);
v___x_4468_ = lean_nat_add(v___x_4467_, v_size_4438_);
lean_dec(v_size_4438_);
v___x_4469_ = lean_nat_add(v___x_4468_, v_size_4437_);
lean_dec(v___x_4468_);
v___x_4481_ = lean_nat_add(v___x_4467_, v_size_4455_);
if (lean_obj_tag(v_l_4459_) == 0)
{
lean_object* v_size_4491_; 
v_size_4491_ = lean_ctor_get(v_l_4459_, 0);
lean_inc(v_size_4491_);
v___y_4483_ = v_size_4491_;
goto v___jp_4482_;
}
else
{
lean_object* v___x_4492_; 
v___x_4492_ = lean_unsigned_to_nat(0u);
v___y_4483_ = v___x_4492_;
goto v___jp_4482_;
}
v___jp_4470_:
{
lean_object* v___x_4474_; lean_object* v___x_4476_; 
v___x_4474_ = lean_nat_add(v___y_4472_, v___y_4473_);
lean_dec(v___y_4473_);
lean_dec(v___y_4472_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 4, v___x_4436_);
lean_ctor_set(v___x_4465_, 3, v_r_4460_);
lean_ctor_set(v___x_4465_, 2, v_v_3919_);
lean_ctor_set(v___x_4465_, 1, v_k_3918_);
lean_ctor_set(v___x_4465_, 0, v___x_4474_);
v___x_4476_ = v___x_4465_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4474_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4480_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4480_, 3, v_r_4460_);
lean_ctor_set(v_reuseFailAlloc_4480_, 4, v___x_4436_);
v___x_4476_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4478_; 
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 4, v___x_4476_);
lean_ctor_set(v___x_4453_, 3, v___y_4471_);
lean_ctor_set(v___x_4453_, 2, v_v_4458_);
lean_ctor_set(v___x_4453_, 1, v_k_4457_);
lean_ctor_set(v___x_4453_, 0, v___x_4469_);
v___x_4478_ = v___x_4453_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4469_);
lean_ctor_set(v_reuseFailAlloc_4479_, 1, v_k_4457_);
lean_ctor_set(v_reuseFailAlloc_4479_, 2, v_v_4458_);
lean_ctor_set(v_reuseFailAlloc_4479_, 3, v___y_4471_);
lean_ctor_set(v_reuseFailAlloc_4479_, 4, v___x_4476_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
v___jp_4482_:
{
lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4484_ = lean_nat_add(v___x_4481_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec(v___x_4481_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v_l_4459_);
lean_ctor_set(v___x_3923_, 3, v_l_4441_);
lean_ctor_set(v___x_3923_, 2, v_v_4440_);
lean_ctor_set(v___x_3923_, 1, v_k_4439_);
lean_ctor_set(v___x_3923_, 0, v___x_4484_);
v___x_4486_ = v___x_3923_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4484_);
lean_ctor_set(v_reuseFailAlloc_4490_, 1, v_k_4439_);
lean_ctor_set(v_reuseFailAlloc_4490_, 2, v_v_4440_);
lean_ctor_set(v_reuseFailAlloc_4490_, 3, v_l_4441_);
lean_ctor_set(v_reuseFailAlloc_4490_, 4, v_l_4459_);
v___x_4486_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; 
v___x_4487_ = lean_nat_add(v___x_4467_, v_size_4437_);
lean_dec(v_size_4437_);
if (lean_obj_tag(v_r_4460_) == 0)
{
lean_object* v_size_4488_; 
v_size_4488_ = lean_ctor_get(v_r_4460_, 0);
lean_inc(v_size_4488_);
v___y_4471_ = v___x_4486_;
v___y_4472_ = v___x_4487_;
v___y_4473_ = v_size_4488_;
goto v___jp_4470_;
}
else
{
lean_object* v___x_4489_; 
v___x_4489_ = lean_unsigned_to_nat(0u);
v___y_4471_ = v___x_4486_;
v___y_4472_ = v___x_4487_;
v___y_4473_ = v___x_4489_;
goto v___jp_4470_;
}
}
}
}
}
else
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4505_; 
lean_del_object(v___x_3923_);
v___x_4499_ = lean_unsigned_to_nat(1u);
v___x_4500_ = lean_nat_add(v___x_4499_, v_size_4438_);
lean_dec(v_size_4438_);
v___x_4501_ = lean_nat_add(v___x_4500_, v_size_4437_);
lean_dec(v___x_4500_);
v___x_4502_ = lean_nat_add(v___x_4499_, v_size_4437_);
lean_dec(v_size_4437_);
v___x_4503_ = lean_nat_add(v___x_4502_, v_size_4456_);
lean_dec(v___x_4502_);
lean_inc_ref(v___x_4436_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 4, v___x_4436_);
lean_ctor_set(v___x_4453_, 3, v_r_4442_);
lean_ctor_set(v___x_4453_, 2, v_v_3919_);
lean_ctor_set(v___x_4453_, 1, v_k_3918_);
lean_ctor_set(v___x_4453_, 0, v___x_4503_);
v___x_4505_ = v___x_4453_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4503_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4518_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4518_, 3, v_r_4442_);
lean_ctor_set(v_reuseFailAlloc_4518_, 4, v___x_4436_);
v___x_4505_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4512_ == 0)
{
lean_object* v_unused_4513_; lean_object* v_unused_4514_; lean_object* v_unused_4515_; lean_object* v_unused_4516_; lean_object* v_unused_4517_; 
v_unused_4513_ = lean_ctor_get(v___x_4436_, 4);
lean_dec(v_unused_4513_);
v_unused_4514_ = lean_ctor_get(v___x_4436_, 3);
lean_dec(v_unused_4514_);
v_unused_4515_ = lean_ctor_get(v___x_4436_, 2);
lean_dec(v_unused_4515_);
v_unused_4516_ = lean_ctor_get(v___x_4436_, 1);
lean_dec(v_unused_4516_);
v_unused_4517_ = lean_ctor_get(v___x_4436_, 0);
lean_dec(v_unused_4517_);
v___x_4507_ = v___x_4436_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_dec(v___x_4436_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
lean_ctor_set(v___x_4507_, 4, v___x_4505_);
lean_ctor_set(v___x_4507_, 3, v_l_4441_);
lean_ctor_set(v___x_4507_, 2, v_v_4440_);
lean_ctor_set(v___x_4507_, 1, v_k_4439_);
lean_ctor_set(v___x_4507_, 0, v___x_4501_);
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4501_);
lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_k_4439_);
lean_ctor_set(v_reuseFailAlloc_4511_, 2, v_v_4440_);
lean_ctor_set(v_reuseFailAlloc_4511_, 3, v_l_4441_);
lean_ctor_set(v_reuseFailAlloc_4511_, 4, v___x_4505_);
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
lean_object* v___x_4519_; lean_object* v___x_4520_; 
lean_dec_ref(v_l_4441_);
lean_del_object(v___x_4453_);
lean_dec(v_v_4440_);
lean_dec(v_k_4439_);
lean_dec(v_size_4438_);
lean_dec(v_size_4437_);
lean_dec_ref(v___x_4436_);
lean_del_object(v___x_3923_);
lean_dec(v_v_3919_);
lean_dec(v_k_3918_);
v___x_4519_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__3);
v___x_4520_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4519_);
return v___x_4520_;
}
}
else
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
lean_del_object(v___x_4453_);
lean_dec(v_r_4442_);
lean_dec(v_v_4440_);
lean_dec(v_k_4439_);
lean_dec(v_size_4438_);
lean_dec(v_size_4437_);
lean_dec_ref(v___x_4436_);
lean_del_object(v___x_3923_);
lean_dec(v_v_3919_);
lean_dec(v_k_3918_);
v___x_4521_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___closed__4);
v___x_4522_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_spec__2___redArg(v___x_4521_);
return v___x_4522_;
}
}
}
}
else
{
lean_object* v_size_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4533_; 
v_size_4529_ = lean_ctor_get(v___x_4436_, 0);
lean_inc(v_size_4529_);
v___x_4530_ = lean_unsigned_to_nat(1u);
v___x_4531_ = lean_nat_add(v___x_4530_, v_size_4529_);
lean_dec(v_size_4529_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v___x_4436_);
lean_ctor_set(v___x_3923_, 0, v___x_4531_);
v___x_4533_ = v___x_3923_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v___x_4531_);
lean_ctor_set(v_reuseFailAlloc_4534_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4534_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4534_, 3, v_l_3920_);
lean_ctor_set(v_reuseFailAlloc_4534_, 4, v___x_4436_);
v___x_4533_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
return v___x_4533_;
}
}
}
else
{
if (lean_obj_tag(v_l_3920_) == 0)
{
lean_object* v_l_4535_; 
v_l_4535_ = lean_ctor_get(v_l_3920_, 3);
if (lean_obj_tag(v_l_4535_) == 0)
{
lean_object* v_r_4536_; 
lean_inc_ref(v_l_4535_);
v_r_4536_ = lean_ctor_get(v_l_3920_, 4);
lean_inc(v_r_4536_);
if (lean_obj_tag(v_r_4536_) == 0)
{
lean_object* v_size_4537_; lean_object* v_k_4538_; lean_object* v_v_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4553_; 
v_size_4537_ = lean_ctor_get(v_l_3920_, 0);
v_k_4538_ = lean_ctor_get(v_l_3920_, 1);
v_v_4539_ = lean_ctor_get(v_l_3920_, 2);
v_isSharedCheck_4553_ = !lean_is_exclusive(v_l_3920_);
if (v_isSharedCheck_4553_ == 0)
{
lean_object* v_unused_4554_; lean_object* v_unused_4555_; 
v_unused_4554_ = lean_ctor_get(v_l_3920_, 4);
lean_dec(v_unused_4554_);
v_unused_4555_ = lean_ctor_get(v_l_3920_, 3);
lean_dec(v_unused_4555_);
v___x_4541_ = v_l_3920_;
v_isShared_4542_ = v_isSharedCheck_4553_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_v_4539_);
lean_inc(v_k_4538_);
lean_inc(v_size_4537_);
lean_dec(v_l_3920_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4553_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v_size_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4548_; 
v_size_4543_ = lean_ctor_get(v_r_4536_, 0);
v___x_4544_ = lean_unsigned_to_nat(1u);
v___x_4545_ = lean_nat_add(v___x_4544_, v_size_4537_);
lean_dec(v_size_4537_);
v___x_4546_ = lean_nat_add(v___x_4544_, v_size_4543_);
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 4, v___x_4436_);
lean_ctor_set(v___x_4541_, 3, v_r_4536_);
lean_ctor_set(v___x_4541_, 2, v_v_3919_);
lean_ctor_set(v___x_4541_, 1, v_k_3918_);
lean_ctor_set(v___x_4541_, 0, v___x_4546_);
v___x_4548_ = v___x_4541_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4546_);
lean_ctor_set(v_reuseFailAlloc_4552_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4552_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4552_, 3, v_r_4536_);
lean_ctor_set(v_reuseFailAlloc_4552_, 4, v___x_4436_);
v___x_4548_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
lean_object* v___x_4550_; 
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v___x_4548_);
lean_ctor_set(v___x_3923_, 3, v_l_4535_);
lean_ctor_set(v___x_3923_, 2, v_v_4539_);
lean_ctor_set(v___x_3923_, 1, v_k_4538_);
lean_ctor_set(v___x_3923_, 0, v___x_4545_);
v___x_4550_ = v___x_3923_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4545_);
lean_ctor_set(v_reuseFailAlloc_4551_, 1, v_k_4538_);
lean_ctor_set(v_reuseFailAlloc_4551_, 2, v_v_4539_);
lean_ctor_set(v_reuseFailAlloc_4551_, 3, v_l_4535_);
lean_ctor_set(v_reuseFailAlloc_4551_, 4, v___x_4548_);
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
lean_object* v_k_4556_; lean_object* v_v_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4569_; 
v_k_4556_ = lean_ctor_get(v_l_3920_, 1);
v_v_4557_ = lean_ctor_get(v_l_3920_, 2);
v_isSharedCheck_4569_ = !lean_is_exclusive(v_l_3920_);
if (v_isSharedCheck_4569_ == 0)
{
lean_object* v_unused_4570_; lean_object* v_unused_4571_; lean_object* v_unused_4572_; 
v_unused_4570_ = lean_ctor_get(v_l_3920_, 4);
lean_dec(v_unused_4570_);
v_unused_4571_ = lean_ctor_get(v_l_3920_, 3);
lean_dec(v_unused_4571_);
v_unused_4572_ = lean_ctor_get(v_l_3920_, 0);
lean_dec(v_unused_4572_);
v___x_4559_ = v_l_3920_;
v_isShared_4560_ = v_isSharedCheck_4569_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_v_4557_);
lean_inc(v_k_4556_);
lean_dec(v_l_3920_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4569_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4564_; 
v___x_4561_ = lean_unsigned_to_nat(3u);
v___x_4562_ = lean_unsigned_to_nat(1u);
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 3, v_r_4536_);
lean_ctor_set(v___x_4559_, 2, v_v_3919_);
lean_ctor_set(v___x_4559_, 1, v_k_3918_);
lean_ctor_set(v___x_4559_, 0, v___x_4562_);
v___x_4564_ = v___x_4559_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4562_);
lean_ctor_set(v_reuseFailAlloc_4568_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4568_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4568_, 3, v_r_4536_);
lean_ctor_set(v_reuseFailAlloc_4568_, 4, v_r_4536_);
v___x_4564_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
lean_object* v___x_4566_; 
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v___x_4564_);
lean_ctor_set(v___x_3923_, 3, v_l_4535_);
lean_ctor_set(v___x_3923_, 2, v_v_4557_);
lean_ctor_set(v___x_3923_, 1, v_k_4556_);
lean_ctor_set(v___x_3923_, 0, v___x_4561_);
v___x_4566_ = v___x_3923_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v___x_4561_);
lean_ctor_set(v_reuseFailAlloc_4567_, 1, v_k_4556_);
lean_ctor_set(v_reuseFailAlloc_4567_, 2, v_v_4557_);
lean_ctor_set(v_reuseFailAlloc_4567_, 3, v_l_4535_);
lean_ctor_set(v_reuseFailAlloc_4567_, 4, v___x_4564_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
}
else
{
lean_object* v_r_4573_; 
v_r_4573_ = lean_ctor_get(v_l_3920_, 4);
lean_inc(v_r_4573_);
if (lean_obj_tag(v_r_4573_) == 0)
{
lean_object* v_k_4574_; lean_object* v_v_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4599_; 
lean_inc(v_l_4535_);
v_k_4574_ = lean_ctor_get(v_l_3920_, 1);
v_v_4575_ = lean_ctor_get(v_l_3920_, 2);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_l_3920_);
if (v_isSharedCheck_4599_ == 0)
{
lean_object* v_unused_4600_; lean_object* v_unused_4601_; lean_object* v_unused_4602_; 
v_unused_4600_ = lean_ctor_get(v_l_3920_, 4);
lean_dec(v_unused_4600_);
v_unused_4601_ = lean_ctor_get(v_l_3920_, 3);
lean_dec(v_unused_4601_);
v_unused_4602_ = lean_ctor_get(v_l_3920_, 0);
lean_dec(v_unused_4602_);
v___x_4577_ = v_l_3920_;
v_isShared_4578_ = v_isSharedCheck_4599_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_v_4575_);
lean_inc(v_k_4574_);
lean_dec(v_l_3920_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4599_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v_k_4579_; lean_object* v_v_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4595_; 
v_k_4579_ = lean_ctor_get(v_r_4573_, 1);
v_v_4580_ = lean_ctor_get(v_r_4573_, 2);
v_isSharedCheck_4595_ = !lean_is_exclusive(v_r_4573_);
if (v_isSharedCheck_4595_ == 0)
{
lean_object* v_unused_4596_; lean_object* v_unused_4597_; lean_object* v_unused_4598_; 
v_unused_4596_ = lean_ctor_get(v_r_4573_, 4);
lean_dec(v_unused_4596_);
v_unused_4597_ = lean_ctor_get(v_r_4573_, 3);
lean_dec(v_unused_4597_);
v_unused_4598_ = lean_ctor_get(v_r_4573_, 0);
lean_dec(v_unused_4598_);
v___x_4582_ = v_r_4573_;
v_isShared_4583_ = v_isSharedCheck_4595_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_v_4580_);
lean_inc(v_k_4579_);
lean_dec(v_r_4573_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4595_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4587_; 
v___x_4584_ = lean_unsigned_to_nat(3u);
v___x_4585_ = lean_unsigned_to_nat(1u);
if (v_isShared_4583_ == 0)
{
lean_ctor_set(v___x_4582_, 4, v_l_4535_);
lean_ctor_set(v___x_4582_, 3, v_l_4535_);
lean_ctor_set(v___x_4582_, 2, v_v_4575_);
lean_ctor_set(v___x_4582_, 1, v_k_4574_);
lean_ctor_set(v___x_4582_, 0, v___x_4585_);
v___x_4587_ = v___x_4582_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4585_);
lean_ctor_set(v_reuseFailAlloc_4594_, 1, v_k_4574_);
lean_ctor_set(v_reuseFailAlloc_4594_, 2, v_v_4575_);
lean_ctor_set(v_reuseFailAlloc_4594_, 3, v_l_4535_);
lean_ctor_set(v_reuseFailAlloc_4594_, 4, v_l_4535_);
v___x_4587_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
lean_object* v___x_4589_; 
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 4, v_l_4535_);
lean_ctor_set(v___x_4577_, 2, v_v_3919_);
lean_ctor_set(v___x_4577_, 1, v_k_3918_);
lean_ctor_set(v___x_4577_, 0, v___x_4585_);
v___x_4589_ = v___x_4577_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4585_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4593_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4593_, 3, v_l_4535_);
lean_ctor_set(v_reuseFailAlloc_4593_, 4, v_l_4535_);
v___x_4589_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
lean_object* v___x_4591_; 
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v___x_4589_);
lean_ctor_set(v___x_3923_, 3, v___x_4587_);
lean_ctor_set(v___x_3923_, 2, v_v_4580_);
lean_ctor_set(v___x_3923_, 1, v_k_4579_);
lean_ctor_set(v___x_3923_, 0, v___x_4584_);
v___x_4591_ = v___x_3923_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4584_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v_k_4579_);
lean_ctor_set(v_reuseFailAlloc_4592_, 2, v_v_4580_);
lean_ctor_set(v_reuseFailAlloc_4592_, 3, v___x_4587_);
lean_ctor_set(v_reuseFailAlloc_4592_, 4, v___x_4589_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
}
}
}
else
{
lean_object* v___x_4603_; lean_object* v___x_4605_; 
v___x_4603_ = lean_unsigned_to_nat(2u);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v_r_4573_);
lean_ctor_set(v___x_3923_, 0, v___x_4603_);
v___x_4605_ = v___x_3923_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4603_);
lean_ctor_set(v_reuseFailAlloc_4606_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4606_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4606_, 3, v_l_3920_);
lean_ctor_set(v_reuseFailAlloc_4606_, 4, v_r_4573_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
else
{
lean_object* v___x_4607_; lean_object* v___x_4609_; 
v___x_4607_ = lean_unsigned_to_nat(1u);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v_l_3920_);
lean_ctor_set(v___x_3923_, 0, v___x_4607_);
v___x_4609_ = v___x_3923_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4607_);
lean_ctor_set(v_reuseFailAlloc_4610_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_4610_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_4610_, 3, v_l_3920_);
lean_ctor_set(v_reuseFailAlloc_4610_, 4, v_l_3920_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_3916_);
lean_dec_ref(v_cmp_3915_);
return v_t_3917_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(lean_object* v_cmp_4613_, lean_object* v_init_4614_, lean_object* v_x_4615_){
_start:
{
if (lean_obj_tag(v_x_4615_) == 0)
{
lean_object* v_k_4616_; lean_object* v_l_4617_; lean_object* v_r_4618_; lean_object* v___x_4619_; lean_object* v_a_4620_; lean_object* v_r_4621_; 
v_k_4616_ = lean_ctor_get(v_x_4615_, 1);
lean_inc(v_k_4616_);
v_l_4617_ = lean_ctor_get(v_x_4615_, 3);
lean_inc(v_l_4617_);
v_r_4618_ = lean_ctor_get(v_x_4615_, 4);
lean_inc(v_r_4618_);
lean_dec_ref(v_x_4615_);
lean_inc_ref(v_cmp_4613_);
v___x_4619_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4613_, v_init_4614_, v_l_4617_);
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4620_);
lean_dec_ref(v___x_4619_);
lean_inc_ref(v_cmp_4613_);
v_r_4621_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4613_, v_k_4616_, v_a_4620_);
v_init_4614_ = v_r_4621_;
v_x_4615_ = v_r_4618_;
goto _start;
}
else
{
lean_object* v___x_4623_; 
lean_dec_ref(v_cmp_4613_);
v___x_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4623_, 0, v_init_4614_);
return v___x_4623_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(lean_object* v_cmp_4624_, lean_object* v_t_u2081_4625_, lean_object* v_t_u2082_4626_){
_start:
{
lean_object* v___y_4628_; lean_object* v___y_4629_; lean_object* v___y_4635_; 
if (lean_obj_tag(v_t_u2081_4625_) == 0)
{
lean_object* v_size_4638_; 
v_size_4638_ = lean_ctor_get(v_t_u2081_4625_, 0);
lean_inc(v_size_4638_);
v___y_4635_ = v_size_4638_;
goto v___jp_4634_;
}
else
{
lean_object* v___x_4639_; 
v___x_4639_ = lean_unsigned_to_nat(0u);
v___y_4635_ = v___x_4639_;
goto v___jp_4634_;
}
v___jp_4627_:
{
uint8_t v___x_4630_; 
v___x_4630_ = lean_nat_dec_le(v___y_4628_, v___y_4629_);
lean_dec(v___y_4629_);
lean_dec(v___y_4628_);
if (v___x_4630_ == 0)
{
lean_object* v___x_4631_; lean_object* v_a_4632_; 
v___x_4631_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4624_, v_t_u2081_4625_, v_t_u2082_4626_);
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc(v_a_4632_);
lean_dec_ref(v___x_4631_);
return v_a_4632_;
}
else
{
lean_object* v___x_4633_; 
v___x_4633_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4624_, v_t_u2082_4626_, v_t_u2081_4625_);
return v___x_4633_;
}
}
v___jp_4634_:
{
if (lean_obj_tag(v_t_u2082_4626_) == 0)
{
lean_object* v_size_4636_; 
v_size_4636_ = lean_ctor_get(v_t_u2082_4626_, 0);
lean_inc(v_size_4636_);
v___y_4628_ = v___y_4635_;
v___y_4629_ = v_size_4636_;
goto v___jp_4627_;
}
else
{
lean_object* v___x_4637_; 
v___x_4637_ = lean_unsigned_to_nat(0u);
v___y_4628_ = v___y_4635_;
v___y_4629_ = v___x_4637_;
goto v___jp_4627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff___redArg(lean_object* v_cmp_4640_, lean_object* v_t_u2081_4641_, lean_object* v_t_u2082_4642_){
_start:
{
lean_object* v___x_4643_; 
v___x_4643_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4640_, v_t_u2081_4641_, v_t_u2082_4642_);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff(lean_object* v_00_u03b1_4644_, lean_object* v_00_u03b2_4645_, lean_object* v_cmp_4646_, lean_object* v_t_u2081_4647_, lean_object* v_t_u2082_4648_){
_start:
{
lean_object* v___x_4649_; 
v___x_4649_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4646_, v_t_u2081_4647_, v_t_u2082_4648_);
return v___x_4649_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0(lean_object* v_00_u03b1_4650_, lean_object* v_cmp_4651_, lean_object* v_00_u03b2_4652_, lean_object* v_t_u2081_4653_, lean_object* v_t_u2082_4654_){
_start:
{
lean_object* v___x_4655_; 
v___x_4655_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4651_, v_t_u2081_4653_, v_t_u2082_4654_);
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0(lean_object* v_00_u03b1_4656_, lean_object* v_cmp_4657_, lean_object* v_00_u03b2_4658_, lean_object* v_k_4659_, lean_object* v_t_4660_){
_start:
{
lean_object* v___x_4661_; 
v___x_4661_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4657_, v_k_4659_, v_t_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1(lean_object* v_00_u03b1_4662_, lean_object* v_00_u03b2_4663_, lean_object* v_cmp_4664_, lean_object* v_init_4665_, lean_object* v_x_4666_){
_start:
{
lean_object* v___x_4667_; 
v___x_4667_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4664_, v_init_4665_, v_x_4666_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2(lean_object* v_00_u03b1_4668_, lean_object* v_00_u03b2_4669_, lean_object* v_cmp_4670_, lean_object* v_t_u2082_4671_, lean_object* v_t_4672_){
_start:
{
lean_object* v___x_4673_; 
v___x_4673_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4670_, v_t_u2082_4671_, v_t_4672_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff___redArg(lean_object* v_cmp_4674_){
_start:
{
lean_object* v___x_4675_; 
v___x_4675_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_4675_, 0, lean_box(0));
lean_closure_set(v___x_4675_, 1, lean_box(0));
lean_closure_set(v___x_4675_, 2, v_cmp_4674_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff(lean_object* v_00_u03b1_4676_, lean_object* v_00_u03b2_4677_, lean_object* v_cmp_4678_){
_start:
{
lean_object* v___x_4679_; 
v___x_4679_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_4679_, 0, lean_box(0));
lean_closure_set(v___x_4679_, 1, lean_box(0));
lean_closure_set(v___x_4679_, 2, v_cmp_4678_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_4680_, lean_object* v_a_4681_, lean_object* v_____s_4682_){
_start:
{
lean_object* v_r_4683_; lean_object* v___x_4684_; 
v_r_4683_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_4680_, v_a_4681_, v_____s_4682_);
v___x_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4684_, 0, v_r_4683_);
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg(lean_object* v_cmp_4685_, lean_object* v_inst_4686_, lean_object* v_t_4687_, lean_object* v_l_4688_){
_start:
{
lean_object* v___f_4689_; lean_object* v___x_4690_; 
v___f_4689_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4689_, 0, v_cmp_4685_);
v___x_4690_ = lean_apply_4(v_inst_4686_, lean_box(0), v_l_4688_, v_t_4687_, v___f_4689_);
return v___x_4690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany(lean_object* v_00_u03b1_4691_, lean_object* v_00_u03b2_4692_, lean_object* v_cmp_4693_, lean_object* v_00_u03c1_4694_, lean_object* v_inst_4695_, lean_object* v_t_4696_, lean_object* v_l_4697_){
_start:
{
lean_object* v___f_4698_; lean_object* v___x_4699_; 
v___f_4698_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4698_, 0, v_cmp_4693_);
v___x_4699_ = lean_apply_4(v_inst_4695_, lean_box(0), v_l_4697_, v_t_4696_, v___f_4698_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0(lean_object* v_cmp_4700_, lean_object* v_x_4701_, lean_object* v_____s_4702_){
_start:
{
lean_object* v_fst_4703_; lean_object* v_snd_4704_; lean_object* v_r_4705_; lean_object* v___x_4706_; 
v_fst_4703_ = lean_ctor_get(v_x_4701_, 0);
lean_inc(v_fst_4703_);
v_snd_4704_ = lean_ctor_get(v_x_4701_, 1);
lean_inc(v_snd_4704_);
lean_dec_ref(v_x_4701_);
v_r_4705_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_4700_, v_fst_4703_, v_snd_4704_, v_____s_4702_);
v___x_4706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4706_, 0, v_r_4705_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg(lean_object* v_cmp_4707_, lean_object* v_inst_4708_, lean_object* v_t_4709_, lean_object* v_l_4710_){
_start:
{
lean_object* v___f_4711_; lean_object* v___x_4712_; 
v___f_4711_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4711_, 0, v_cmp_4707_);
v___x_4712_ = lean_apply_4(v_inst_4708_, lean_box(0), v_l_4710_, v_t_4709_, v___f_4711_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany(lean_object* v_00_u03b1_4713_, lean_object* v_cmp_4714_, lean_object* v_00_u03b2_4715_, lean_object* v_00_u03c1_4716_, lean_object* v_inst_4717_, lean_object* v_t_4718_, lean_object* v_l_4719_){
_start:
{
lean_object* v___f_4720_; lean_object* v___x_4721_; 
v___f_4720_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4720_, 0, v_cmp_4714_);
v___x_4721_ = lean_apply_4(v_inst_4717_, lean_box(0), v_l_4719_, v_t_4718_, v___f_4720_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_4722_, lean_object* v_a_4723_, lean_object* v_____s_4724_){
_start:
{
uint8_t v___x_4725_; 
lean_inc(v_____s_4724_);
lean_inc(v_a_4723_);
lean_inc_ref(v_cmp_4722_);
v___x_4725_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4722_, v_a_4723_, v_____s_4724_);
if (v___x_4725_ == 0)
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4726_ = lean_box(0);
v___x_4727_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_4722_, v_a_4723_, v___x_4726_, v_____s_4724_);
v___x_4728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4727_);
return v___x_4728_;
}
else
{
lean_object* v___x_4729_; 
lean_dec(v_a_4723_);
lean_dec_ref(v_cmp_4722_);
v___x_4729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4729_, 0, v_____s_4724_);
return v___x_4729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_4730_, lean_object* v_inst_4731_, lean_object* v_t_4732_, lean_object* v_l_4733_){
_start:
{
lean_object* v___f_4734_; lean_object* v___x_4735_; 
v___f_4734_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4734_, 0, v_cmp_4730_);
v___x_4735_ = lean_apply_4(v_inst_4731_, lean_box(0), v_l_4733_, v_t_4732_, v___f_4734_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_4736_, lean_object* v_cmp_4737_, lean_object* v_00_u03c1_4738_, lean_object* v_inst_4739_, lean_object* v_t_4740_, lean_object* v_l_4741_){
_start:
{
lean_object* v___f_4742_; lean_object* v___x_4743_; 
v___f_4742_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4742_, 0, v_cmp_4737_);
v___x_4743_ = lean_apply_4(v_inst_4739_, lean_box(0), v_l_4741_, v_t_4740_, v___f_4742_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(lean_object* v___f_4747_, lean_object* v___x_4748_, lean_object* v_m_4749_, lean_object* v_prec_4750_){
_start:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4751_ = ((lean_object*)(l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__1));
v___x_4752_ = lean_box(0);
v___x_4753_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_4754_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_4753_, v___f_4747_, v___x_4752_, v_m_4749_);
v___x_4755_ = l_List_repr___redArg(v___x_4748_, v___x_4754_);
v___x_4756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4751_);
lean_ctor_set(v___x_4756_, 1, v___x_4755_);
v___x_4757_ = l_Repr_addAppParen(v___x_4756_, v_prec_4750_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_4758_, lean_object* v___x_4759_, lean_object* v_m_4760_, lean_object* v_prec_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(v___f_4758_, v___x_4759_, v_m_4760_, v_prec_4761_);
lean_dec(v_prec_4761_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg(lean_object* v_inst_4763_, lean_object* v_inst_4764_){
_start:
{
lean_object* v___f_4765_; lean_object* v___x_4766_; lean_object* v___f_4767_; 
v___f_4765_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_4766_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_4766_, 0, lean_box(0));
lean_closure_set(v___x_4766_, 1, lean_box(0));
lean_closure_set(v___x_4766_, 2, v_inst_4763_);
lean_closure_set(v___x_4766_, 3, v_inst_4764_);
v___f_4767_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4767_, 0, v___f_4765_);
lean_closure_set(v___f_4767_, 1, v___x_4766_);
return v___f_4767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr(lean_object* v_00_u03b1_4768_, lean_object* v_00_u03b2_4769_, lean_object* v_cmp_4770_, lean_object* v_inst_4771_, lean_object* v_inst_4772_){
_start:
{
lean_object* v___x_4773_; 
v___x_4773_ = l_Std_DTreeMap_Raw_instRepr___redArg(v_inst_4771_, v_inst_4772_);
return v___x_4773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___boxed(lean_object* v_00_u03b1_4774_, lean_object* v_00_u03b2_4775_, lean_object* v_cmp_4776_, lean_object* v_inst_4777_, lean_object* v_inst_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l_Std_DTreeMap_Raw_instRepr(v_00_u03b1_4774_, v_00_u03b2_4775_, v_cmp_4776_, v_inst_4777_, v_inst_4778_);
lean_dec_ref(v_cmp_4776_);
return v_res_4779_;
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
