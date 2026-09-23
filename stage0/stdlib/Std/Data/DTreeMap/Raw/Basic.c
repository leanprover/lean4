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
lean_object* l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__1___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__1___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__1___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__1___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_DTreeMap_instCoeTypeForall__1___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__1(lean_object* v_00_u03b1_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__12(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__10));
v___x_34_ = l_Lean_mkAtom(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__13(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__12, &l_Std_DTreeMap_Raw___auto__1___closed__12_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__12);
v___x_36_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_37_ = lean_array_push(v___x_36_, v___x_35_);
return v___x_37_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__15(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__14));
v___x_40_ = lean_string_utf8_byte_size(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__16(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_41_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__15, &l_Std_DTreeMap_Raw___auto__1___closed__15_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__15);
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__14));
v___x_44_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
lean_ctor_set(v___x_44_, 2, v___x_41_);
return v___x_44_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__18(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_47_ = lean_box(0);
v___x_48_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__17));
v___x_49_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__16, &l_Std_DTreeMap_Raw___auto__1___closed__16_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__16);
v___x_50_ = lean_box(2);
v___x_51_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_49_);
lean_ctor_set(v___x_51_, 2, v___x_48_);
lean_ctor_set(v___x_51_, 3, v___x_47_);
return v___x_51_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__19(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__18, &l_Std_DTreeMap_Raw___auto__1___closed__18_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__18);
v___x_53_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__13, &l_Std_DTreeMap_Raw___auto__1___closed__13_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__13);
v___x_54_ = lean_array_push(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__20(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__19, &l_Std_DTreeMap_Raw___auto__1___closed__19_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__19);
v___x_56_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__11));
v___x_57_ = lean_box(2);
v___x_58_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___x_56_);
lean_ctor_set(v___x_58_, 2, v___x_55_);
return v___x_58_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__21(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__20, &l_Std_DTreeMap_Raw___auto__1___closed__20_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__20);
v___x_60_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_61_ = lean_array_push(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__22(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__21, &l_Std_DTreeMap_Raw___auto__1___closed__21_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__21);
v___x_63_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__9));
v___x_64_ = lean_box(2);
v___x_65_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
lean_ctor_set(v___x_65_, 2, v___x_62_);
return v___x_65_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__23(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__22, &l_Std_DTreeMap_Raw___auto__1___closed__22_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__22);
v___x_67_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_68_ = lean_array_push(v___x_67_, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__24(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__23, &l_Std_DTreeMap_Raw___auto__1___closed__23_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__23);
v___x_70_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__7));
v___x_71_ = lean_box(2);
v___x_72_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
lean_ctor_set(v___x_72_, 2, v___x_69_);
return v___x_72_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__25(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__24, &l_Std_DTreeMap_Raw___auto__1___closed__24_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__24);
v___x_74_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_75_ = lean_array_push(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__26(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
v___x_77_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__4));
v___x_78_ = lean_box(2);
v___x_79_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_76_);
return v___x_79_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1(void){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner___redArg(){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(0);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner___redArg___boxed(lean_object* v___dummy_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_DTreeMap_Raw_instCoeWFWFInner___redArg();
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_cmp_87_, lean_object* v_t_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(0);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner___boxed(lean_object* v_00_u03b1_90_, lean_object* v_00_u03b2_91_, lean_object* v_cmp_92_, lean_object* v_t_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_DTreeMap_Raw_instCoeWFWFInner(v_00_u03b1_90_, v_00_u03b2_91_, v_cmp_92_, v_t_93_);
lean_dec(v_t_93_);
lean_dec_ref(v_cmp_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___redArg(){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(1);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___redArg___boxed(lean_object* v___dummy_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_DTreeMap_Raw_empty___redArg();
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_cmp_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(1);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___boxed(lean_object* v_00_u03b1_103_, lean_object* v_00_u03b2_104_, lean_object* v_cmp_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_DTreeMap_Raw_empty(v_00_u03b1_103_, v_00_u03b2_104_, v_cmp_105_);
lean_dec_ref(v_cmp_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_box(1);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_DTreeMap_Raw_instEmptyCollection___redArg();
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_cmp_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(1);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___boxed(lean_object* v_00_u03b1_115_, lean_object* v_00_u03b2_116_, lean_object* v_cmp_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_DTreeMap_Raw_instEmptyCollection(v_00_u03b1_115_, v_00_u03b2_116_, v_cmp_117_);
lean_dec_ref(v_cmp_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_box(1);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_DTreeMap_Raw_instInhabited___redArg();
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_cmp_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(1);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited___boxed(lean_object* v_00_u03b1_127_, lean_object* v_00_u03b2_128_, lean_object* v_cmp_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_DTreeMap_Raw_instInhabited(v_00_u03b1_127_, v_00_u03b2_128_, v_cmp_129_);
lean_dec_ref(v_cmp_129_);
return v_res_130_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__3));
v___x_171_ = l_String_toRawSubstring_x27(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1(lean_object* v_x_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_190_);
v___x_194_ = l_Lean_Syntax_isOfKind(v_x_190_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v_x_190_);
v___x_195_ = lean_box(1);
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_192_);
return v___x_196_;
}
else
{
lean_object* v_quotContext_197_; lean_object* v_currMacroScope_198_; lean_object* v_ref_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_quotContext_197_ = lean_ctor_get(v_a_191_, 1);
v_currMacroScope_198_ = lean_ctor_get(v_a_191_, 2);
v_ref_199_ = lean_ctor_get(v_a_191_, 5);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = l_Lean_Syntax_getArg(v_x_190_, v___x_200_);
v___x_202_ = lean_unsigned_to_nat(2u);
v___x_203_ = l_Lean_Syntax_getArg(v_x_190_, v___x_202_);
lean_dec(v_x_190_);
v___x_204_ = 0;
v___x_205_ = l_Lean_SourceInfo_fromRef(v_ref_199_, v___x_204_);
v___x_206_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2));
v___x_207_ = lean_obj_once(&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4, &l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4_once, _init_l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4);
v___x_208_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_198_);
lean_inc(v_quotContext_197_);
v___x_209_ = l_Lean_addMacroScope(v_quotContext_197_, v___x_208_, v_currMacroScope_198_);
v___x_210_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__10));
lean_inc_n(v___x_205_, 2);
v___x_211_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_211_, 0, v___x_205_);
lean_ctor_set(v___x_211_, 1, v___x_207_);
lean_ctor_set(v___x_211_, 2, v___x_209_);
lean_ctor_set(v___x_211_, 3, v___x_210_);
v___x_212_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__9));
v___x_213_ = l_Lean_Syntax_node2(v___x_205_, v___x_212_, v___x_201_, v___x_203_);
v___x_214_ = l_Lean_Syntax_node2(v___x_205_, v___x_206_, v___x_211_, v___x_213_);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v_a_192_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___boxed(lean_object* v_x_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1(v_x_216_, v_a_217_, v_a_218_);
lean_dec_ref(v_a_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1(lean_object* v_x_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2));
lean_inc(v_x_223_);
v___x_227_ = l_Lean_Syntax_isOfKind(v_x_223_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v_x_223_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_a_225_);
return v___x_229_;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = l_Lean_Syntax_getArg(v_x_223_, v___x_230_);
v___x_232_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_231_);
v___x_233_ = l_Lean_Syntax_isOfKind(v___x_231_, v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v___x_231_);
lean_dec(v_x_223_);
v___x_234_ = lean_box(0);
v___x_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v_a_225_);
return v___x_235_;
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = l_Lean_Syntax_getArg(v_x_223_, v___x_236_);
lean_dec(v_x_223_);
v___x_238_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_237_);
v___x_239_ = l_Lean_Syntax_matchesNull(v___x_237_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v___x_237_);
lean_dec(v___x_231_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v_a_225_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_ref_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_242_ = l_Lean_Syntax_getArg(v___x_237_, v___x_230_);
v___x_243_ = l_Lean_Syntax_getArg(v___x_237_, v___x_236_);
lean_dec(v___x_237_);
v_ref_244_ = l_Lean_replaceRef(v___x_231_, v_a_224_);
lean_dec(v___x_231_);
v___x_245_ = 0;
v___x_246_ = l_Lean_SourceInfo_fromRef(v_ref_244_, v___x_245_);
lean_dec(v_ref_244_);
v___x_247_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__4));
v___x_248_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_246_);
v___x_249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_246_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = l_Lean_Syntax_node3(v___x_246_, v___x_247_, v___x_242_, v___x_249_, v___x_243_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v_a_225_);
return v___x_251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___boxed(lean_object* v_x_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1(v_x_252_, v_a_253_, v_a_254_);
lean_dec(v_a_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insert___redArg(lean_object* v_cmp_256_, lean_object* v_t_257_, lean_object* v_a_258_, lean_object* v_b_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_256_, v_a_258_, v_b_259_, v_t_257_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insert(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_cmp_263_, lean_object* v_t_264_, lean_object* v_a_265_, lean_object* v_b_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_263_, v_a_265_, v_b_266_, v_t_264_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0(lean_object* v_cmp_268_, lean_object* v_e_269_){
_start:
{
lean_object* v_fst_270_; lean_object* v_snd_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_fst_270_ = lean_ctor_get(v_e_269_, 0);
lean_inc(v_fst_270_);
v_snd_271_ = lean_ctor_get(v_e_269_, 1);
lean_inc(v_snd_271_);
lean_dec_ref(v_e_269_);
v___x_272_ = lean_box(1);
v___x_273_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_268_, v_fst_270_, v_snd_271_, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma___redArg(lean_object* v_cmp_274_){
_start:
{
lean_object* v___f_275_; 
v___f_275_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_275_, 0, v_cmp_274_);
return v___f_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma(lean_object* v_00_u03b1_276_, lean_object* v_00_u03b2_277_, lean_object* v_cmp_278_){
_start:
{
lean_object* v___f_279_; 
v___f_279_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_279_, 0, v_cmp_278_);
return v___f_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0(lean_object* v_cmp_280_, lean_object* v_e_281_, lean_object* v_s_282_){
_start:
{
lean_object* v_fst_283_; lean_object* v_snd_284_; lean_object* v___x_285_; 
v_fst_283_ = lean_ctor_get(v_e_281_, 0);
lean_inc(v_fst_283_);
v_snd_284_ = lean_ctor_get(v_e_281_, 1);
lean_inc(v_snd_284_);
lean_dec_ref(v_e_281_);
v___x_285_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_280_, v_fst_283_, v_snd_284_, v_s_282_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma___redArg(lean_object* v_cmp_286_){
_start:
{
lean_object* v___f_287_; 
v___f_287_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_287_, 0, v_cmp_286_);
return v___f_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma(lean_object* v_00_u03b1_288_, lean_object* v_00_u03b2_289_, lean_object* v_cmp_290_){
_start:
{
lean_object* v___f_291_; 
v___f_291_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_291_, 0, v_cmp_290_);
return v___f_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertIfNew___redArg(lean_object* v_cmp_292_, lean_object* v_t_293_, lean_object* v_a_294_, lean_object* v_b_295_){
_start:
{
uint8_t v___x_296_; 
lean_inc(v_t_293_);
lean_inc(v_a_294_);
lean_inc_ref(v_cmp_292_);
v___x_296_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_292_, v_a_294_, v_t_293_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_292_, v_a_294_, v_b_295_, v_t_293_);
return v___x_297_;
}
else
{
lean_dec(v_b_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_cmp_292_);
return v_t_293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertIfNew(lean_object* v_00_u03b1_298_, lean_object* v_00_u03b2_299_, lean_object* v_cmp_300_, lean_object* v_t_301_, lean_object* v_a_302_, lean_object* v_b_303_){
_start:
{
uint8_t v___x_304_; 
lean_inc(v_t_301_);
lean_inc(v_a_302_);
lean_inc_ref(v_cmp_300_);
v___x_304_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_300_, v_a_302_, v_t_301_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_300_, v_a_302_, v_b_303_, v_t_301_);
return v___x_305_;
}
else
{
lean_dec(v_b_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_cmp_300_);
return v_t_301_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsert___redArg(lean_object* v_cmp_306_, lean_object* v_t_307_, lean_object* v_a_308_, lean_object* v_b_309_){
_start:
{
lean_object* v_sz_310_; lean_object* v_m_311_; lean_object* v___y_313_; 
v_sz_310_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_307_);
v_m_311_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_306_, v_a_308_, v_b_309_, v_t_307_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsert(lean_object* v_00_u03b1_319_, lean_object* v_00_u03b2_320_, lean_object* v_cmp_321_, lean_object* v_t_322_, lean_object* v_a_323_, lean_object* v_b_324_){
_start:
{
lean_object* v_sz_325_; lean_object* v_m_326_; lean_object* v___y_328_; 
v_sz_325_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_322_);
v_m_326_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_321_, v_a_323_, v_b_324_, v_t_322_);
if (lean_obj_tag(v_m_326_) == 0)
{
lean_object* v_size_332_; 
v_size_332_ = lean_ctor_get(v_m_326_, 0);
lean_inc(v_size_332_);
v___y_328_ = v_size_332_;
goto v___jp_327_;
}
else
{
lean_object* v___x_333_; 
v___x_333_ = lean_unsigned_to_nat(0u);
v___y_328_ = v___x_333_;
goto v___jp_327_;
}
v___jp_327_:
{
uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_nat_dec_eq(v_sz_325_, v___y_328_);
lean_dec(v___y_328_);
lean_dec(v_sz_325_);
v___x_330_ = lean_box(v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v_m_326_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_cmp_334_, lean_object* v_t_335_, lean_object* v_a_336_, lean_object* v_b_337_){
_start:
{
uint8_t v___x_338_; 
lean_inc(v_t_335_);
lean_inc(v_a_336_);
lean_inc_ref(v_cmp_334_);
v___x_338_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_334_, v_a_336_, v_t_335_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_334_, v_a_336_, v_b_337_, v_t_335_);
v___x_340_ = lean_box(v___x_338_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v_b_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_cmp_334_);
v___x_342_ = lean_box(v___x_338_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_t_335_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_, lean_object* v_cmp_346_, lean_object* v_t_347_, lean_object* v_a_348_, lean_object* v_b_349_){
_start:
{
uint8_t v___x_350_; 
lean_inc(v_t_347_);
lean_inc(v_a_348_);
lean_inc_ref(v_cmp_346_);
v___x_350_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_346_, v_a_348_, v_t_347_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_346_, v_a_348_, v_b_349_, v_t_347_);
v___x_352_ = lean_box(v___x_350_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v_b_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_cmp_346_);
v___x_354_ = lean_box(v___x_350_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v_t_347_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_356_, lean_object* v_t_357_, lean_object* v_a_358_, lean_object* v_b_359_){
_start:
{
lean_object* v___x_360_; 
lean_inc(v_a_358_);
lean_inc(v_t_357_);
lean_inc_ref(v_cmp_356_);
v___x_360_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_356_, v_t_357_, v_a_358_);
if (lean_obj_tag(v___x_360_) == 0)
{
uint8_t v___x_361_; 
lean_inc(v_t_357_);
lean_inc(v_a_358_);
lean_inc_ref(v_cmp_356_);
v___x_361_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_356_, v_a_358_, v_t_357_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_356_, v_a_358_, v_b_359_, v_t_357_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_360_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; 
lean_dec(v_b_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_cmp_356_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_360_);
lean_ctor_set(v___x_364_, 1, v_t_357_);
return v___x_364_;
}
}
else
{
lean_object* v___x_365_; 
lean_dec(v_b_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_cmp_356_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_360_);
lean_ctor_set(v___x_365_, 1, v_t_357_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_366_, lean_object* v_00_u03b2_367_, lean_object* v_cmp_368_, lean_object* v_inst_369_, lean_object* v_t_370_, lean_object* v_a_371_, lean_object* v_b_372_){
_start:
{
lean_object* v___x_373_; 
lean_inc(v_a_371_);
lean_inc(v_t_370_);
lean_inc_ref(v_cmp_368_);
v___x_373_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_368_, v_t_370_, v_a_371_);
if (lean_obj_tag(v___x_373_) == 0)
{
uint8_t v___x_374_; 
lean_inc(v_t_370_);
lean_inc(v_a_371_);
lean_inc_ref(v_cmp_368_);
v___x_374_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_368_, v_a_371_, v_t_370_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_368_, v_a_371_, v_b_372_, v_t_370_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_373_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; 
lean_dec(v_b_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_cmp_368_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_373_);
lean_ctor_set(v___x_377_, 1, v_t_370_);
return v___x_377_;
}
}
else
{
lean_object* v___x_378_; 
lean_dec(v_b_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_cmp_368_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_373_);
lean_ctor_set(v___x_378_, 1, v_t_370_);
return v___x_378_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_contains___redArg(lean_object* v_cmp_379_, lean_object* v_t_380_, lean_object* v_a_381_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_379_, v_a_381_, v_t_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_contains___redArg___boxed(lean_object* v_cmp_383_, lean_object* v_t_384_, lean_object* v_a_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_Std_DTreeMap_Raw_contains___redArg(v_cmp_383_, v_t_384_, v_a_385_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_contains(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_cmp_390_, lean_object* v_t_391_, lean_object* v_a_392_){
_start:
{
uint8_t v___x_393_; 
v___x_393_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_390_, v_a_392_, v_t_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_contains___boxed(lean_object* v_00_u03b1_394_, lean_object* v_00_u03b2_395_, lean_object* v_cmp_396_, lean_object* v_t_397_, lean_object* v_a_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = l_Std_DTreeMap_Raw_contains(v_00_u03b1_394_, v_00_u03b2_395_, v_cmp_396_, v_t_397_, v_a_398_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___redArg(){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lean_box(0);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___redArg___boxed(lean_object* v___dummy_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Std_DTreeMap_Raw_instMembership___redArg();
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership(lean_object* v_00_u03b1_405_, lean_object* v_00_u03b2_406_, lean_object* v_cmp_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___boxed(lean_object* v_00_u03b1_409_, lean_object* v_00_u03b2_410_, lean_object* v_cmp_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_DTreeMap_Raw_instMembership(v_00_u03b1_409_, v_00_u03b2_410_, v_cmp_411_);
lean_dec_ref(v_cmp_411_);
return v_res_412_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableMem___redArg(lean_object* v_cmp_413_, lean_object* v_t_414_, lean_object* v_a_415_){
_start:
{
uint8_t v___x_416_; 
v___x_416_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_413_, v_a_415_, v_t_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_417_, lean_object* v_t_418_, lean_object* v_a_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_Std_DTreeMap_Raw_instDecidableMem___redArg(v_cmp_417_, v_t_418_, v_a_419_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableMem(lean_object* v_00_u03b1_422_, lean_object* v_00_u03b2_423_, lean_object* v_cmp_424_, lean_object* v_t_425_, lean_object* v_a_426_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_424_, v_a_426_, v_t_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_428_, lean_object* v_00_u03b2_429_, lean_object* v_cmp_430_, lean_object* v_t_431_, lean_object* v_a_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Std_DTreeMap_Raw_instDecidableMem(v_00_u03b1_428_, v_00_u03b2_429_, v_cmp_430_, v_t_431_, v_a_432_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___redArg(lean_object* v_t_435_){
_start:
{
if (lean_obj_tag(v_t_435_) == 0)
{
lean_object* v_size_436_; 
v_size_436_ = lean_ctor_get(v_t_435_, 0);
lean_inc(v_size_436_);
return v_size_436_;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = lean_unsigned_to_nat(0u);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___redArg___boxed(lean_object* v_t_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_DTreeMap_Raw_size___redArg(v_t_438_);
lean_dec(v_t_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size(lean_object* v_00_u03b1_440_, lean_object* v_00_u03b2_441_, lean_object* v_cmp_442_, lean_object* v_t_443_){
_start:
{
if (lean_obj_tag(v_t_443_) == 0)
{
lean_object* v_size_444_; 
v_size_444_ = lean_ctor_get(v_t_443_, 0);
lean_inc(v_size_444_);
return v_size_444_;
}
else
{
lean_object* v___x_445_; 
v___x_445_ = lean_unsigned_to_nat(0u);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___boxed(lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_cmp_448_, lean_object* v_t_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_DTreeMap_Raw_size(v_00_u03b1_446_, v_00_u03b2_447_, v_cmp_448_, v_t_449_);
lean_dec(v_t_449_);
lean_dec_ref(v_cmp_448_);
return v_res_450_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_isEmpty___redArg(lean_object* v_t_451_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_isEmpty___redArg___boxed(lean_object* v_t_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Std_DTreeMap_Raw_isEmpty___redArg(v_t_454_);
lean_dec(v_t_454_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_isEmpty(lean_object* v_00_u03b1_457_, lean_object* v_00_u03b2_458_, lean_object* v_cmp_459_, lean_object* v_t_460_){
_start:
{
if (lean_obj_tag(v_t_460_) == 0)
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = 1;
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_463_, lean_object* v_00_u03b2_464_, lean_object* v_cmp_465_, lean_object* v_t_466_){
_start:
{
uint8_t v_res_467_; lean_object* v_r_468_; 
v_res_467_ = l_Std_DTreeMap_Raw_isEmpty(v_00_u03b1_463_, v_00_u03b2_464_, v_cmp_465_, v_t_466_);
lean_dec(v_t_466_);
lean_dec_ref(v_cmp_465_);
v_r_468_ = lean_box(v_res_467_);
return v_r_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_erase___redArg(lean_object* v_cmp_469_, lean_object* v_t_470_, lean_object* v_a_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_469_, v_a_471_, v_t_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_erase(lean_object* v_00_u03b1_473_, lean_object* v_00_u03b2_474_, lean_object* v_cmp_475_, lean_object* v_t_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_475_, v_a_477_, v_t_476_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x3f___redArg(lean_object* v_cmp_479_, lean_object* v_t_480_, lean_object* v_a_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_479_, v_t_480_, v_a_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x3f(lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_cmp_485_, lean_object* v_inst_486_, lean_object* v_t_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_485_, v_t_487_, v_a_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get___redArg(lean_object* v_cmp_490_, lean_object* v_t_491_, lean_object* v_a_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_490_, v_t_491_, v_a_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_cmp_496_, lean_object* v_inst_497_, lean_object* v_t_498_, lean_object* v_a_499_, lean_object* v_h_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_496_, v_t_498_, v_a_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___redArg(lean_object* v_cmp_502_, lean_object* v_t_503_, lean_object* v_a_504_, lean_object* v_inst_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_502_, v_t_503_, v_a_504_, v_inst_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___redArg___boxed(lean_object* v_cmp_507_, lean_object* v_t_508_, lean_object* v_a_509_, lean_object* v_inst_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_DTreeMap_Raw_get_x21___redArg(v_cmp_507_, v_t_508_, v_a_509_, v_inst_510_);
lean_dec(v_inst_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21(lean_object* v_00_u03b1_512_, lean_object* v_00_u03b2_513_, lean_object* v_cmp_514_, lean_object* v_inst_515_, lean_object* v_t_516_, lean_object* v_a_517_, lean_object* v_inst_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_514_, v_t_516_, v_a_517_, v_inst_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_cmp_522_, lean_object* v_inst_523_, lean_object* v_t_524_, lean_object* v_a_525_, lean_object* v_inst_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_DTreeMap_Raw_get_x21(v_00_u03b1_520_, v_00_u03b2_521_, v_cmp_522_, v_inst_523_, v_t_524_, v_a_525_, v_inst_526_);
lean_dec(v_inst_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg(lean_object* v_cmp_528_, lean_object* v_t_529_, lean_object* v_a_530_, lean_object* v_fallback_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_528_, v_t_529_, v_a_530_, v_fallback_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg___boxed(lean_object* v_cmp_533_, lean_object* v_t_534_, lean_object* v_a_535_, lean_object* v_fallback_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_DTreeMap_Raw_getD___redArg(v_cmp_533_, v_t_534_, v_a_535_, v_fallback_536_);
lean_dec(v_fallback_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD(lean_object* v_00_u03b1_538_, lean_object* v_00_u03b2_539_, lean_object* v_cmp_540_, lean_object* v_inst_541_, lean_object* v_t_542_, lean_object* v_a_543_, lean_object* v_fallback_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_540_, v_t_542_, v_a_543_, v_fallback_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___boxed(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_cmp_548_, lean_object* v_inst_549_, lean_object* v_t_550_, lean_object* v_a_551_, lean_object* v_fallback_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_DTreeMap_Raw_getD(v_00_u03b1_546_, v_00_u03b2_547_, v_cmp_548_, v_inst_549_, v_t_550_, v_a_551_, v_fallback_552_);
lean_dec(v_fallback_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f___redArg(lean_object* v_cmp_554_, lean_object* v_t_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_554_, v_t_555_, v_a_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f(lean_object* v_00_u03b1_558_, lean_object* v_00_u03b2_559_, lean_object* v_cmp_560_, lean_object* v_t_561_, lean_object* v_a_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_560_, v_t_561_, v_a_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry___redArg(lean_object* v_cmp_564_, lean_object* v_t_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_564_, v_t_565_, v_a_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry(lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_cmp_570_, lean_object* v_inst_571_, lean_object* v_t_572_, lean_object* v_a_573_, lean_object* v_h_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_570_, v_t_572_, v_a_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___redArg(lean_object* v_cmp_576_, lean_object* v_inst_577_, lean_object* v_t_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_576_, v_inst_577_, v_t_578_, v_a_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___redArg___boxed(lean_object* v_cmp_581_, lean_object* v_inst_582_, lean_object* v_t_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DTreeMap_Raw_getEntry_x21___redArg(v_cmp_581_, v_inst_582_, v_t_583_, v_a_584_);
lean_dec_ref(v_inst_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21(lean_object* v_00_u03b1_586_, lean_object* v_00_u03b2_587_, lean_object* v_cmp_588_, lean_object* v_inst_589_, lean_object* v_t_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_588_, v_inst_589_, v_t_590_, v_a_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___boxed(lean_object* v_00_u03b1_593_, lean_object* v_00_u03b2_594_, lean_object* v_cmp_595_, lean_object* v_inst_596_, lean_object* v_t_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_DTreeMap_Raw_getEntry_x21(v_00_u03b1_593_, v_00_u03b2_594_, v_cmp_595_, v_inst_596_, v_t_597_, v_a_598_);
lean_dec_ref(v_inst_596_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg(lean_object* v_cmp_600_, lean_object* v_t_601_, lean_object* v_a_602_, lean_object* v_fallback_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_600_, v_t_601_, v_a_602_, v_fallback_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg___boxed(lean_object* v_cmp_605_, lean_object* v_t_606_, lean_object* v_a_607_, lean_object* v_fallback_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_DTreeMap_Raw_getEntryD___redArg(v_cmp_605_, v_t_606_, v_a_607_, v_fallback_608_);
lean_dec_ref(v_fallback_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD(lean_object* v_00_u03b1_610_, lean_object* v_00_u03b2_611_, lean_object* v_cmp_612_, lean_object* v_t_613_, lean_object* v_a_614_, lean_object* v_fallback_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_612_, v_t_613_, v_a_614_, v_fallback_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___boxed(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_cmp_619_, lean_object* v_t_620_, lean_object* v_a_621_, lean_object* v_fallback_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_DTreeMap_Raw_getEntryD(v_00_u03b1_617_, v_00_u03b2_618_, v_cmp_619_, v_t_620_, v_a_621_, v_fallback_622_);
lean_dec_ref(v_fallback_622_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f___redArg(lean_object* v_cmp_624_, lean_object* v_t_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_624_, v_t_625_, v_a_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f(lean_object* v_00_u03b1_628_, lean_object* v_00_u03b2_629_, lean_object* v_cmp_630_, lean_object* v_t_631_, lean_object* v_a_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_630_, v_t_631_, v_a_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey___redArg(lean_object* v_cmp_634_, lean_object* v_t_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_634_, v_t_635_, v_a_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey(lean_object* v_00_u03b1_638_, lean_object* v_00_u03b2_639_, lean_object* v_cmp_640_, lean_object* v_t_641_, lean_object* v_a_642_, lean_object* v_h_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_640_, v_t_641_, v_a_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___redArg(lean_object* v_cmp_645_, lean_object* v_inst_646_, lean_object* v_t_647_, lean_object* v_a_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_645_, v_t_647_, v_a_648_, v_inst_646_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___redArg___boxed(lean_object* v_cmp_650_, lean_object* v_inst_651_, lean_object* v_t_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_DTreeMap_Raw_getKey_x21___redArg(v_cmp_650_, v_inst_651_, v_t_652_, v_a_653_);
lean_dec(v_inst_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21(lean_object* v_00_u03b1_655_, lean_object* v_00_u03b2_656_, lean_object* v_cmp_657_, lean_object* v_inst_658_, lean_object* v_t_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_657_, v_t_659_, v_a_660_, v_inst_658_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_cmp_664_, lean_object* v_inst_665_, lean_object* v_t_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_DTreeMap_Raw_getKey_x21(v_00_u03b1_662_, v_00_u03b2_663_, v_cmp_664_, v_inst_665_, v_t_666_, v_a_667_);
lean_dec(v_inst_665_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___redArg(lean_object* v_cmp_669_, lean_object* v_t_670_, lean_object* v_a_671_, lean_object* v_fallback_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_669_, v_t_670_, v_a_671_, v_fallback_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___redArg___boxed(lean_object* v_cmp_674_, lean_object* v_t_675_, lean_object* v_a_676_, lean_object* v_fallback_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_DTreeMap_Raw_getKeyD___redArg(v_cmp_674_, v_t_675_, v_a_676_, v_fallback_677_);
lean_dec(v_fallback_677_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD(lean_object* v_00_u03b1_679_, lean_object* v_00_u03b2_680_, lean_object* v_cmp_681_, lean_object* v_t_682_, lean_object* v_a_683_, lean_object* v_fallback_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_681_, v_t_682_, v_a_683_, v_fallback_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_686_, lean_object* v_00_u03b2_687_, lean_object* v_cmp_688_, lean_object* v_t_689_, lean_object* v_a_690_, lean_object* v_fallback_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Std_DTreeMap_Raw_getKeyD(v_00_u03b1_686_, v_00_u03b2_687_, v_cmp_688_, v_t_689_, v_a_690_, v_fallback_691_);
lean_dec(v_fallback_691_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___redArg(lean_object* v_t_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___redArg___boxed(lean_object* v_t_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Std_DTreeMap_Raw_minEntry_x3f___redArg(v_t_695_);
lean_dec(v_t_695_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f(lean_object* v_00_u03b1_697_, lean_object* v_00_u03b2_698_, lean_object* v_cmp_699_, lean_object* v_t_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___boxed(lean_object* v_00_u03b1_702_, lean_object* v_00_u03b2_703_, lean_object* v_cmp_704_, lean_object* v_t_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_DTreeMap_Raw_minEntry_x3f(v_00_u03b1_702_, v_00_u03b2_703_, v_cmp_704_, v_t_705_);
lean_dec(v_t_705_);
lean_dec_ref(v_cmp_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___redArg(lean_object* v_inst_707_, lean_object* v_t_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_707_, v_t_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___redArg___boxed(lean_object* v_inst_710_, lean_object* v_t_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_DTreeMap_Raw_minEntry_x21___redArg(v_inst_710_, v_t_711_);
lean_dec(v_t_711_);
lean_dec_ref(v_inst_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21(lean_object* v_00_u03b1_713_, lean_object* v_00_u03b2_714_, lean_object* v_cmp_715_, lean_object* v_inst_716_, lean_object* v_t_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_716_, v_t_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___boxed(lean_object* v_00_u03b1_719_, lean_object* v_00_u03b2_720_, lean_object* v_cmp_721_, lean_object* v_inst_722_, lean_object* v_t_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Std_DTreeMap_Raw_minEntry_x21(v_00_u03b1_719_, v_00_u03b2_720_, v_cmp_721_, v_inst_722_, v_t_723_);
lean_dec(v_t_723_);
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_cmp_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___redArg(lean_object* v_t_725_, lean_object* v_fallback_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_725_, v_fallback_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___redArg___boxed(lean_object* v_t_728_, lean_object* v_fallback_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_DTreeMap_Raw_minEntryD___redArg(v_t_728_, v_fallback_729_);
lean_dec_ref(v_fallback_729_);
lean_dec(v_t_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD(lean_object* v_00_u03b1_731_, lean_object* v_00_u03b2_732_, lean_object* v_cmp_733_, lean_object* v_t_734_, lean_object* v_fallback_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_734_, v_fallback_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___boxed(lean_object* v_00_u03b1_737_, lean_object* v_00_u03b2_738_, lean_object* v_cmp_739_, lean_object* v_t_740_, lean_object* v_fallback_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Std_DTreeMap_Raw_minEntryD(v_00_u03b1_737_, v_00_u03b2_738_, v_cmp_739_, v_t_740_, v_fallback_741_);
lean_dec_ref(v_fallback_741_);
lean_dec(v_t_740_);
lean_dec_ref(v_cmp_739_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___redArg(lean_object* v_t_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___redArg___boxed(lean_object* v_t_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Std_DTreeMap_Raw_maxEntry_x3f___redArg(v_t_745_);
lean_dec(v_t_745_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f(lean_object* v_00_u03b1_747_, lean_object* v_00_u03b2_748_, lean_object* v_cmp_749_, lean_object* v_t_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___boxed(lean_object* v_00_u03b1_752_, lean_object* v_00_u03b2_753_, lean_object* v_cmp_754_, lean_object* v_t_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_DTreeMap_Raw_maxEntry_x3f(v_00_u03b1_752_, v_00_u03b2_753_, v_cmp_754_, v_t_755_);
lean_dec(v_t_755_);
lean_dec_ref(v_cmp_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___redArg(lean_object* v_inst_757_, lean_object* v_t_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_757_, v_t_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___redArg___boxed(lean_object* v_inst_760_, lean_object* v_t_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Std_DTreeMap_Raw_maxEntry_x21___redArg(v_inst_760_, v_t_761_);
lean_dec(v_t_761_);
lean_dec_ref(v_inst_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21(lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_cmp_765_, lean_object* v_inst_766_, lean_object* v_t_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_766_, v_t_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___boxed(lean_object* v_00_u03b1_769_, lean_object* v_00_u03b2_770_, lean_object* v_cmp_771_, lean_object* v_inst_772_, lean_object* v_t_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_DTreeMap_Raw_maxEntry_x21(v_00_u03b1_769_, v_00_u03b2_770_, v_cmp_771_, v_inst_772_, v_t_773_);
lean_dec(v_t_773_);
lean_dec_ref(v_inst_772_);
lean_dec_ref(v_cmp_771_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___redArg(lean_object* v_t_775_, lean_object* v_fallback_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_775_, v_fallback_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___redArg___boxed(lean_object* v_t_778_, lean_object* v_fallback_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_DTreeMap_Raw_maxEntryD___redArg(v_t_778_, v_fallback_779_);
lean_dec_ref(v_fallback_779_);
lean_dec(v_t_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD(lean_object* v_00_u03b1_781_, lean_object* v_00_u03b2_782_, lean_object* v_cmp_783_, lean_object* v_t_784_, lean_object* v_fallback_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_784_, v_fallback_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___boxed(lean_object* v_00_u03b1_787_, lean_object* v_00_u03b2_788_, lean_object* v_cmp_789_, lean_object* v_t_790_, lean_object* v_fallback_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_DTreeMap_Raw_maxEntryD(v_00_u03b1_787_, v_00_u03b2_788_, v_cmp_789_, v_t_790_, v_fallback_791_);
lean_dec_ref(v_fallback_791_);
lean_dec(v_t_790_);
lean_dec_ref(v_cmp_789_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___redArg(lean_object* v_t_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___redArg___boxed(lean_object* v_t_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Std_DTreeMap_Raw_minKey_x3f___redArg(v_t_795_);
lean_dec(v_t_795_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f(lean_object* v_00_u03b1_797_, lean_object* v_00_u03b2_798_, lean_object* v_cmp_799_, lean_object* v_t_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___boxed(lean_object* v_00_u03b1_802_, lean_object* v_00_u03b2_803_, lean_object* v_cmp_804_, lean_object* v_t_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_DTreeMap_Raw_minKey_x3f(v_00_u03b1_802_, v_00_u03b2_803_, v_cmp_804_, v_t_805_);
lean_dec(v_t_805_);
lean_dec_ref(v_cmp_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___redArg(lean_object* v_t_807_, lean_object* v_fallback_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_807_, v_fallback_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___redArg___boxed(lean_object* v_t_810_, lean_object* v_fallback_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_DTreeMap_Raw_minKeyD___redArg(v_t_810_, v_fallback_811_);
lean_dec(v_fallback_811_);
lean_dec(v_t_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD(lean_object* v_00_u03b1_813_, lean_object* v_00_u03b2_814_, lean_object* v_cmp_815_, lean_object* v_t_816_, lean_object* v_fallback_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_816_, v_fallback_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___boxed(lean_object* v_00_u03b1_819_, lean_object* v_00_u03b2_820_, lean_object* v_cmp_821_, lean_object* v_t_822_, lean_object* v_fallback_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_DTreeMap_Raw_minKeyD(v_00_u03b1_819_, v_00_u03b2_820_, v_cmp_821_, v_t_822_, v_fallback_823_);
lean_dec(v_fallback_823_);
lean_dec(v_t_822_);
lean_dec_ref(v_cmp_821_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___redArg(lean_object* v_inst_825_, lean_object* v_t_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_825_, v_t_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___redArg___boxed(lean_object* v_inst_828_, lean_object* v_t_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_DTreeMap_Raw_minKey_x21___redArg(v_inst_828_, v_t_829_);
lean_dec(v_t_829_);
lean_dec(v_inst_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21(lean_object* v_00_u03b1_831_, lean_object* v_00_u03b2_832_, lean_object* v_cmp_833_, lean_object* v_inst_834_, lean_object* v_t_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_834_, v_t_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___boxed(lean_object* v_00_u03b1_837_, lean_object* v_00_u03b2_838_, lean_object* v_cmp_839_, lean_object* v_inst_840_, lean_object* v_t_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_DTreeMap_Raw_minKey_x21(v_00_u03b1_837_, v_00_u03b2_838_, v_cmp_839_, v_inst_840_, v_t_841_);
lean_dec(v_t_841_);
lean_dec(v_inst_840_);
lean_dec_ref(v_cmp_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___redArg(lean_object* v_t_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___redArg___boxed(lean_object* v_t_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Std_DTreeMap_Raw_maxKey_x3f___redArg(v_t_845_);
lean_dec(v_t_845_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f(lean_object* v_00_u03b1_847_, lean_object* v_00_u03b2_848_, lean_object* v_cmp_849_, lean_object* v_t_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___boxed(lean_object* v_00_u03b1_852_, lean_object* v_00_u03b2_853_, lean_object* v_cmp_854_, lean_object* v_t_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DTreeMap_Raw_maxKey_x3f(v_00_u03b1_852_, v_00_u03b2_853_, v_cmp_854_, v_t_855_);
lean_dec(v_t_855_);
lean_dec_ref(v_cmp_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___redArg(lean_object* v_inst_857_, lean_object* v_t_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_857_, v_t_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___redArg___boxed(lean_object* v_inst_860_, lean_object* v_t_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_DTreeMap_Raw_maxKey_x21___redArg(v_inst_860_, v_t_861_);
lean_dec(v_t_861_);
lean_dec(v_inst_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21(lean_object* v_00_u03b1_863_, lean_object* v_00_u03b2_864_, lean_object* v_cmp_865_, lean_object* v_inst_866_, lean_object* v_t_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_866_, v_t_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___boxed(lean_object* v_00_u03b1_869_, lean_object* v_00_u03b2_870_, lean_object* v_cmp_871_, lean_object* v_inst_872_, lean_object* v_t_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Std_DTreeMap_Raw_maxKey_x21(v_00_u03b1_869_, v_00_u03b2_870_, v_cmp_871_, v_inst_872_, v_t_873_);
lean_dec(v_t_873_);
lean_dec(v_inst_872_);
lean_dec_ref(v_cmp_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___redArg(lean_object* v_t_875_, lean_object* v_fallback_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_875_, v_fallback_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___redArg___boxed(lean_object* v_t_878_, lean_object* v_fallback_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Std_DTreeMap_Raw_maxKeyD___redArg(v_t_878_, v_fallback_879_);
lean_dec(v_fallback_879_);
lean_dec(v_t_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_cmp_883_, lean_object* v_t_884_, lean_object* v_fallback_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_884_, v_fallback_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___boxed(lean_object* v_00_u03b1_887_, lean_object* v_00_u03b2_888_, lean_object* v_cmp_889_, lean_object* v_t_890_, lean_object* v_fallback_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_DTreeMap_Raw_maxKeyD(v_00_u03b1_887_, v_00_u03b2_888_, v_cmp_889_, v_t_890_, v_fallback_891_);
lean_dec(v_fallback_891_);
lean_dec(v_t_890_);
lean_dec_ref(v_cmp_889_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg(lean_object* v_t_893_, lean_object* v_n_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_893_, v_n_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_896_, lean_object* v_n_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg(v_t_896_, v_n_897_);
lean_dec(v_t_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f(lean_object* v_00_u03b1_899_, lean_object* v_00_u03b2_900_, lean_object* v_cmp_901_, lean_object* v_t_902_, lean_object* v_n_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_902_, v_n_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_905_, lean_object* v_00_u03b2_906_, lean_object* v_cmp_907_, lean_object* v_t_908_, lean_object* v_n_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Std_DTreeMap_Raw_entryAtIdx_x3f(v_00_u03b1_905_, v_00_u03b2_906_, v_cmp_907_, v_t_908_, v_n_909_);
lean_dec(v_t_908_);
lean_dec_ref(v_cmp_907_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg(lean_object* v_inst_911_, lean_object* v_t_912_, lean_object* v_n_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_911_, v_t_912_, v_n_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_915_, lean_object* v_t_916_, lean_object* v_n_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg(v_inst_915_, v_t_916_, v_n_917_);
lean_dec(v_t_916_);
lean_dec_ref(v_inst_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21(lean_object* v_00_u03b1_919_, lean_object* v_00_u03b2_920_, lean_object* v_cmp_921_, lean_object* v_inst_922_, lean_object* v_t_923_, lean_object* v_n_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_922_, v_t_923_, v_n_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_926_, lean_object* v_00_u03b2_927_, lean_object* v_cmp_928_, lean_object* v_inst_929_, lean_object* v_t_930_, lean_object* v_n_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Std_DTreeMap_Raw_entryAtIdx_x21(v_00_u03b1_926_, v_00_u03b2_927_, v_cmp_928_, v_inst_929_, v_t_930_, v_n_931_);
lean_dec(v_t_930_);
lean_dec_ref(v_inst_929_);
lean_dec_ref(v_cmp_928_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___redArg(lean_object* v_t_933_, lean_object* v_n_934_, lean_object* v_fallback_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_933_, v_n_934_, v_fallback_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___redArg___boxed(lean_object* v_t_937_, lean_object* v_n_938_, lean_object* v_fallback_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Std_DTreeMap_Raw_entryAtIdxD___redArg(v_t_937_, v_n_938_, v_fallback_939_);
lean_dec_ref(v_fallback_939_);
lean_dec(v_t_937_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD(lean_object* v_00_u03b1_941_, lean_object* v_00_u03b2_942_, lean_object* v_cmp_943_, lean_object* v_t_944_, lean_object* v_n_945_, lean_object* v_fallback_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_944_, v_n_945_, v_fallback_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___boxed(lean_object* v_00_u03b1_948_, lean_object* v_00_u03b2_949_, lean_object* v_cmp_950_, lean_object* v_t_951_, lean_object* v_n_952_, lean_object* v_fallback_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_DTreeMap_Raw_entryAtIdxD(v_00_u03b1_948_, v_00_u03b2_949_, v_cmp_950_, v_t_951_, v_n_952_, v_fallback_953_);
lean_dec_ref(v_fallback_953_);
lean_dec(v_t_951_);
lean_dec_ref(v_cmp_950_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg(lean_object* v_t_955_, lean_object* v_n_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_955_, v_n_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_958_, lean_object* v_n_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg(v_t_958_, v_n_959_);
lean_dec(v_t_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f(lean_object* v_00_u03b1_961_, lean_object* v_00_u03b2_962_, lean_object* v_cmp_963_, lean_object* v_t_964_, lean_object* v_n_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_964_, v_n_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_967_, lean_object* v_00_u03b2_968_, lean_object* v_cmp_969_, lean_object* v_t_970_, lean_object* v_n_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Std_DTreeMap_Raw_keyAtIdx_x3f(v_00_u03b1_967_, v_00_u03b2_968_, v_cmp_969_, v_t_970_, v_n_971_);
lean_dec(v_t_970_);
lean_dec_ref(v_cmp_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg(lean_object* v_inst_973_, lean_object* v_t_974_, lean_object* v_n_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_973_, v_t_974_, v_n_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_977_, lean_object* v_t_978_, lean_object* v_n_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg(v_inst_977_, v_t_978_, v_n_979_);
lean_dec(v_t_978_);
lean_dec(v_inst_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21(lean_object* v_00_u03b1_981_, lean_object* v_00_u03b2_982_, lean_object* v_cmp_983_, lean_object* v_inst_984_, lean_object* v_t_985_, lean_object* v_n_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_984_, v_t_985_, v_n_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_988_, lean_object* v_00_u03b2_989_, lean_object* v_cmp_990_, lean_object* v_inst_991_, lean_object* v_t_992_, lean_object* v_n_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Std_DTreeMap_Raw_keyAtIdx_x21(v_00_u03b1_988_, v_00_u03b2_989_, v_cmp_990_, v_inst_991_, v_t_992_, v_n_993_);
lean_dec(v_t_992_);
lean_dec(v_inst_991_);
lean_dec_ref(v_cmp_990_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___redArg(lean_object* v_t_995_, lean_object* v_n_996_, lean_object* v_fallback_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_995_, v_n_996_, v_fallback_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___redArg___boxed(lean_object* v_t_999_, lean_object* v_n_1000_, lean_object* v_fallback_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Std_DTreeMap_Raw_keyAtIdxD___redArg(v_t_999_, v_n_1000_, v_fallback_1001_);
lean_dec(v_fallback_1001_);
lean_dec(v_t_999_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD(lean_object* v_00_u03b1_1003_, lean_object* v_00_u03b2_1004_, lean_object* v_cmp_1005_, lean_object* v_t_1006_, lean_object* v_n_1007_, lean_object* v_fallback_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1006_, v_n_1007_, v_fallback_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___boxed(lean_object* v_00_u03b1_1010_, lean_object* v_00_u03b2_1011_, lean_object* v_cmp_1012_, lean_object* v_t_1013_, lean_object* v_n_1014_, lean_object* v_fallback_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Std_DTreeMap_Raw_keyAtIdxD(v_00_u03b1_1010_, v_00_u03b2_1011_, v_cmp_1012_, v_t_1013_, v_n_1014_, v_fallback_1015_);
lean_dec(v_fallback_1015_);
lean_dec(v_t_1013_);
lean_dec_ref(v_cmp_1012_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x3f___redArg(lean_object* v_cmp_1017_, lean_object* v_t_1018_, lean_object* v_k_1019_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1017_, v_k_1019_, v___x_1020_, v_t_1018_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x3f(lean_object* v_00_u03b1_1022_, lean_object* v_00_u03b2_1023_, lean_object* v_cmp_1024_, lean_object* v_t_1025_, lean_object* v_k_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1024_, v_k_1026_, v___x_1027_, v_t_1025_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x3f___redArg(lean_object* v_cmp_1029_, lean_object* v_t_1030_, lean_object* v_k_1031_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1029_, v_k_1031_, v___x_1032_, v_t_1030_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x3f(lean_object* v_00_u03b1_1034_, lean_object* v_00_u03b2_1035_, lean_object* v_cmp_1036_, lean_object* v_t_1037_, lean_object* v_k_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1036_, v_k_1038_, v___x_1039_, v_t_1037_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x3f___redArg(lean_object* v_cmp_1041_, lean_object* v_t_1042_, lean_object* v_k_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1041_, v_k_1043_, v___x_1044_, v_t_1042_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x3f(lean_object* v_00_u03b1_1046_, lean_object* v_00_u03b2_1047_, lean_object* v_cmp_1048_, lean_object* v_t_1049_, lean_object* v_k_1050_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1048_, v_k_1050_, v___x_1051_, v_t_1049_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x3f___redArg(lean_object* v_cmp_1053_, lean_object* v_t_1054_, lean_object* v_k_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1053_, v_k_1055_, v___x_1056_, v_t_1054_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x3f(lean_object* v_00_u03b1_1058_, lean_object* v_00_u03b2_1059_, lean_object* v_cmp_1060_, lean_object* v_t_1061_, lean_object* v_k_1062_){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1060_, v_k_1062_, v___x_1063_, v_t_1061_);
return v___x_1064_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1068_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__2));
v___x_1069_ = lean_unsigned_to_nat(14u);
v___x_1070_ = lean_unsigned_to_nat(22u);
v___x_1071_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__1));
v___x_1072_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__0));
v___x_1073_ = l_mkPanicMessageWithDecl(v___x_1072_, v___x_1071_, v___x_1070_, v___x_1069_, v___x_1068_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg(lean_object* v_cmp_1074_, lean_object* v_inst_1075_, lean_object* v_t_1076_, lean_object* v_k_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_box(0);
v___x_1079_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1074_, v_k_1077_, v___x_1078_, v_t_1076_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1081_ = l_panic___redArg(v_inst_1075_, v___x_1080_);
return v___x_1081_;
}
else
{
lean_object* v_val_1082_; 
v_val_1082_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_val_1082_);
lean_dec_ref_known(v___x_1079_, 1);
return v_val_1082_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1083_, lean_object* v_inst_1084_, lean_object* v_t_1085_, lean_object* v_k_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Std_DTreeMap_Raw_getEntryGE_x21___redArg(v_cmp_1083_, v_inst_1084_, v_t_1085_, v_k_1086_);
lean_dec_ref(v_inst_1084_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21(lean_object* v_00_u03b1_1088_, lean_object* v_00_u03b2_1089_, lean_object* v_cmp_1090_, lean_object* v_inst_1091_, lean_object* v_t_1092_, lean_object* v_k_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_box(0);
v___x_1095_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1090_, v_k_1093_, v___x_1094_, v_t_1092_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1097_ = l_panic___redArg(v_inst_1091_, v___x_1096_);
return v___x_1097_;
}
else
{
lean_object* v_val_1098_; 
v_val_1098_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_val_1098_);
lean_dec_ref_known(v___x_1095_, 1);
return v_val_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1099_, lean_object* v_00_u03b2_1100_, lean_object* v_cmp_1101_, lean_object* v_inst_1102_, lean_object* v_t_1103_, lean_object* v_k_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std_DTreeMap_Raw_getEntryGE_x21(v_00_u03b1_1099_, v_00_u03b2_1100_, v_cmp_1101_, v_inst_1102_, v_t_1103_, v_k_1104_);
lean_dec_ref(v_inst_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___redArg(lean_object* v_cmp_1106_, lean_object* v_inst_1107_, lean_object* v_t_1108_, lean_object* v_k_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1106_, v_k_1109_, v___x_1110_, v_t_1108_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1113_ = l_panic___redArg(v_inst_1107_, v___x_1112_);
return v___x_1113_;
}
else
{
lean_object* v_val_1114_; 
v_val_1114_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v___x_1111_, 1);
return v_val_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1115_, lean_object* v_inst_1116_, lean_object* v_t_1117_, lean_object* v_k_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Std_DTreeMap_Raw_getEntryGT_x21___redArg(v_cmp_1115_, v_inst_1116_, v_t_1117_, v_k_1118_);
lean_dec_ref(v_inst_1116_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21(lean_object* v_00_u03b1_1120_, lean_object* v_00_u03b2_1121_, lean_object* v_cmp_1122_, lean_object* v_inst_1123_, lean_object* v_t_1124_, lean_object* v_k_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1122_, v_k_1125_, v___x_1126_, v_t_1124_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1129_ = l_panic___redArg(v_inst_1123_, v___x_1128_);
return v___x_1129_;
}
else
{
lean_object* v_val_1130_; 
v_val_1130_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_val_1130_);
lean_dec_ref_known(v___x_1127_, 1);
return v_val_1130_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1131_, lean_object* v_00_u03b2_1132_, lean_object* v_cmp_1133_, lean_object* v_inst_1134_, lean_object* v_t_1135_, lean_object* v_k_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_DTreeMap_Raw_getEntryGT_x21(v_00_u03b1_1131_, v_00_u03b2_1132_, v_cmp_1133_, v_inst_1134_, v_t_1135_, v_k_1136_);
lean_dec_ref(v_inst_1134_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___redArg(lean_object* v_cmp_1138_, lean_object* v_inst_1139_, lean_object* v_t_1140_, lean_object* v_k_1141_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_box(0);
v___x_1143_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1138_, v_k_1141_, v___x_1142_, v_t_1140_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1145_ = l_panic___redArg(v_inst_1139_, v___x_1144_);
return v___x_1145_;
}
else
{
lean_object* v_val_1146_; 
v_val_1146_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_val_1146_);
lean_dec_ref_known(v___x_1143_, 1);
return v_val_1146_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1147_, lean_object* v_inst_1148_, lean_object* v_t_1149_, lean_object* v_k_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Std_DTreeMap_Raw_getEntryLE_x21___redArg(v_cmp_1147_, v_inst_1148_, v_t_1149_, v_k_1150_);
lean_dec_ref(v_inst_1148_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21(lean_object* v_00_u03b1_1152_, lean_object* v_00_u03b2_1153_, lean_object* v_cmp_1154_, lean_object* v_inst_1155_, lean_object* v_t_1156_, lean_object* v_k_1157_){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_box(0);
v___x_1159_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1154_, v_k_1157_, v___x_1158_, v_t_1156_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1161_ = l_panic___redArg(v_inst_1155_, v___x_1160_);
return v___x_1161_;
}
else
{
lean_object* v_val_1162_; 
v_val_1162_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_val_1162_);
lean_dec_ref_known(v___x_1159_, 1);
return v_val_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1163_, lean_object* v_00_u03b2_1164_, lean_object* v_cmp_1165_, lean_object* v_inst_1166_, lean_object* v_t_1167_, lean_object* v_k_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Std_DTreeMap_Raw_getEntryLE_x21(v_00_u03b1_1163_, v_00_u03b2_1164_, v_cmp_1165_, v_inst_1166_, v_t_1167_, v_k_1168_);
lean_dec_ref(v_inst_1166_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___redArg(lean_object* v_cmp_1170_, lean_object* v_inst_1171_, lean_object* v_t_1172_, lean_object* v_k_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_box(0);
v___x_1175_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1170_, v_k_1173_, v___x_1174_, v_t_1172_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1177_ = l_panic___redArg(v_inst_1171_, v___x_1176_);
return v___x_1177_;
}
else
{
lean_object* v_val_1178_; 
v_val_1178_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_val_1178_);
lean_dec_ref_known(v___x_1175_, 1);
return v_val_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1179_, lean_object* v_inst_1180_, lean_object* v_t_1181_, lean_object* v_k_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Std_DTreeMap_Raw_getEntryLT_x21___redArg(v_cmp_1179_, v_inst_1180_, v_t_1181_, v_k_1182_);
lean_dec_ref(v_inst_1180_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21(lean_object* v_00_u03b1_1184_, lean_object* v_00_u03b2_1185_, lean_object* v_cmp_1186_, lean_object* v_inst_1187_, lean_object* v_t_1188_, lean_object* v_k_1189_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_box(0);
v___x_1191_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1186_, v_k_1189_, v___x_1190_, v_t_1188_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1193_ = l_panic___redArg(v_inst_1187_, v___x_1192_);
return v___x_1193_;
}
else
{
lean_object* v_val_1194_; 
v_val_1194_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_val_1194_);
lean_dec_ref_known(v___x_1191_, 1);
return v_val_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1195_, lean_object* v_00_u03b2_1196_, lean_object* v_cmp_1197_, lean_object* v_inst_1198_, lean_object* v_t_1199_, lean_object* v_k_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_DTreeMap_Raw_getEntryLT_x21(v_00_u03b1_1195_, v_00_u03b2_1196_, v_cmp_1197_, v_inst_1198_, v_t_1199_, v_k_1200_);
lean_dec_ref(v_inst_1198_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___redArg(lean_object* v_cmp_1202_, lean_object* v_t_1203_, lean_object* v_k_1204_, lean_object* v_fallback_1205_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_box(0);
v___x_1207_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1202_, v_k_1204_, v___x_1206_, v_t_1203_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_inc_ref(v_fallback_1205_);
return v_fallback_1205_;
}
else
{
lean_object* v_val_1208_; 
v_val_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_val_1208_);
lean_dec_ref_known(v___x_1207_, 1);
return v_val_1208_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___redArg___boxed(lean_object* v_cmp_1209_, lean_object* v_t_1210_, lean_object* v_k_1211_, lean_object* v_fallback_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Std_DTreeMap_Raw_getEntryGED___redArg(v_cmp_1209_, v_t_1210_, v_k_1211_, v_fallback_1212_);
lean_dec_ref(v_fallback_1212_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED(lean_object* v_00_u03b1_1214_, lean_object* v_00_u03b2_1215_, lean_object* v_cmp_1216_, lean_object* v_t_1217_, lean_object* v_k_1218_, lean_object* v_fallback_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1216_, v_k_1218_, v___x_1220_, v_t_1217_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_inc_ref(v_fallback_1219_);
return v_fallback_1219_;
}
else
{
lean_object* v_val_1222_; 
v_val_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_val_1222_);
lean_dec_ref_known(v___x_1221_, 1);
return v_val_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___boxed(lean_object* v_00_u03b1_1223_, lean_object* v_00_u03b2_1224_, lean_object* v_cmp_1225_, lean_object* v_t_1226_, lean_object* v_k_1227_, lean_object* v_fallback_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Std_DTreeMap_Raw_getEntryGED(v_00_u03b1_1223_, v_00_u03b2_1224_, v_cmp_1225_, v_t_1226_, v_k_1227_, v_fallback_1228_);
lean_dec_ref(v_fallback_1228_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___redArg(lean_object* v_cmp_1230_, lean_object* v_t_1231_, lean_object* v_k_1232_, lean_object* v_fallback_1233_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_box(0);
v___x_1235_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1230_, v_k_1232_, v___x_1234_, v_t_1231_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_inc_ref(v_fallback_1233_);
return v_fallback_1233_;
}
else
{
lean_object* v_val_1236_; 
v_val_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_val_1236_);
lean_dec_ref_known(v___x_1235_, 1);
return v_val_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___redArg___boxed(lean_object* v_cmp_1237_, lean_object* v_t_1238_, lean_object* v_k_1239_, lean_object* v_fallback_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Std_DTreeMap_Raw_getEntryGTD___redArg(v_cmp_1237_, v_t_1238_, v_k_1239_, v_fallback_1240_);
lean_dec_ref(v_fallback_1240_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD(lean_object* v_00_u03b1_1242_, lean_object* v_00_u03b2_1243_, lean_object* v_cmp_1244_, lean_object* v_t_1245_, lean_object* v_k_1246_, lean_object* v_fallback_1247_){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1244_, v_k_1246_, v___x_1248_, v_t_1245_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_inc_ref(v_fallback_1247_);
return v_fallback_1247_;
}
else
{
lean_object* v_val_1250_; 
v_val_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_val_1250_);
lean_dec_ref_known(v___x_1249_, 1);
return v_val_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___boxed(lean_object* v_00_u03b1_1251_, lean_object* v_00_u03b2_1252_, lean_object* v_cmp_1253_, lean_object* v_t_1254_, lean_object* v_k_1255_, lean_object* v_fallback_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Std_DTreeMap_Raw_getEntryGTD(v_00_u03b1_1251_, v_00_u03b2_1252_, v_cmp_1253_, v_t_1254_, v_k_1255_, v_fallback_1256_);
lean_dec_ref(v_fallback_1256_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___redArg(lean_object* v_cmp_1258_, lean_object* v_t_1259_, lean_object* v_k_1260_, lean_object* v_fallback_1261_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_box(0);
v___x_1263_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1258_, v_k_1260_, v___x_1262_, v_t_1259_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_inc_ref(v_fallback_1261_);
return v_fallback_1261_;
}
else
{
lean_object* v_val_1264_; 
v_val_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_val_1264_);
lean_dec_ref_known(v___x_1263_, 1);
return v_val_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___redArg___boxed(lean_object* v_cmp_1265_, lean_object* v_t_1266_, lean_object* v_k_1267_, lean_object* v_fallback_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Std_DTreeMap_Raw_getEntryLED___redArg(v_cmp_1265_, v_t_1266_, v_k_1267_, v_fallback_1268_);
lean_dec_ref(v_fallback_1268_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED(lean_object* v_00_u03b1_1270_, lean_object* v_00_u03b2_1271_, lean_object* v_cmp_1272_, lean_object* v_t_1273_, lean_object* v_k_1274_, lean_object* v_fallback_1275_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_box(0);
v___x_1277_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1272_, v_k_1274_, v___x_1276_, v_t_1273_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_inc_ref(v_fallback_1275_);
return v_fallback_1275_;
}
else
{
lean_object* v_val_1278_; 
v_val_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_val_1278_);
lean_dec_ref_known(v___x_1277_, 1);
return v_val_1278_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___boxed(lean_object* v_00_u03b1_1279_, lean_object* v_00_u03b2_1280_, lean_object* v_cmp_1281_, lean_object* v_t_1282_, lean_object* v_k_1283_, lean_object* v_fallback_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Std_DTreeMap_Raw_getEntryLED(v_00_u03b1_1279_, v_00_u03b2_1280_, v_cmp_1281_, v_t_1282_, v_k_1283_, v_fallback_1284_);
lean_dec_ref(v_fallback_1284_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___redArg(lean_object* v_cmp_1286_, lean_object* v_t_1287_, lean_object* v_k_1288_, lean_object* v_fallback_1289_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_box(0);
v___x_1291_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1286_, v_k_1288_, v___x_1290_, v_t_1287_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___redArg___boxed(lean_object* v_cmp_1293_, lean_object* v_t_1294_, lean_object* v_k_1295_, lean_object* v_fallback_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Std_DTreeMap_Raw_getEntryLTD___redArg(v_cmp_1293_, v_t_1294_, v_k_1295_, v_fallback_1296_);
lean_dec_ref(v_fallback_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD(lean_object* v_00_u03b1_1298_, lean_object* v_00_u03b2_1299_, lean_object* v_cmp_1300_, lean_object* v_t_1301_, lean_object* v_k_1302_, lean_object* v_fallback_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1300_, v_k_1302_, v___x_1304_, v_t_1301_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_00_u03b2_1308_, lean_object* v_cmp_1309_, lean_object* v_t_1310_, lean_object* v_k_1311_, lean_object* v_fallback_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Std_DTreeMap_Raw_getEntryLTD(v_00_u03b1_1307_, v_00_u03b2_1308_, v_cmp_1309_, v_t_1310_, v_k_1311_, v_fallback_1312_);
lean_dec_ref(v_fallback_1312_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x3f___redArg(lean_object* v_cmp_1314_, lean_object* v_t_1315_, lean_object* v_k_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_box(0);
v___x_1318_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1314_, v_k_1316_, v___x_1317_, v_t_1315_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x3f(lean_object* v_00_u03b1_1319_, lean_object* v_00_u03b2_1320_, lean_object* v_cmp_1321_, lean_object* v_t_1322_, lean_object* v_k_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1321_, v_k_1323_, v___x_1324_, v_t_1322_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x3f___redArg(lean_object* v_cmp_1326_, lean_object* v_t_1327_, lean_object* v_k_1328_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_box(0);
v___x_1330_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1326_, v_k_1328_, v___x_1329_, v_t_1327_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x3f(lean_object* v_00_u03b1_1331_, lean_object* v_00_u03b2_1332_, lean_object* v_cmp_1333_, lean_object* v_t_1334_, lean_object* v_k_1335_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1333_, v_k_1335_, v___x_1336_, v_t_1334_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x3f___redArg(lean_object* v_cmp_1338_, lean_object* v_t_1339_, lean_object* v_k_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_box(0);
v___x_1342_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1338_, v_k_1340_, v___x_1341_, v_t_1339_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x3f(lean_object* v_00_u03b1_1343_, lean_object* v_00_u03b2_1344_, lean_object* v_cmp_1345_, lean_object* v_t_1346_, lean_object* v_k_1347_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_box(0);
v___x_1349_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1345_, v_k_1347_, v___x_1348_, v_t_1346_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x3f___redArg(lean_object* v_cmp_1350_, lean_object* v_t_1351_, lean_object* v_k_1352_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_box(0);
v___x_1354_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1350_, v_k_1352_, v___x_1353_, v_t_1351_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x3f(lean_object* v_00_u03b1_1355_, lean_object* v_00_u03b2_1356_, lean_object* v_cmp_1357_, lean_object* v_t_1358_, lean_object* v_k_1359_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_box(0);
v___x_1361_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1357_, v_k_1359_, v___x_1360_, v_t_1358_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___redArg(lean_object* v_cmp_1362_, lean_object* v_inst_1363_, lean_object* v_t_1364_, lean_object* v_k_1365_){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_box(0);
v___x_1367_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1362_, v_k_1365_, v___x_1366_, v_t_1364_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1369_ = l_panic___redArg(v_inst_1363_, v___x_1368_);
return v___x_1369_;
}
else
{
lean_object* v_val_1370_; 
v_val_1370_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v___x_1367_, 1);
return v_val_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1371_, lean_object* v_inst_1372_, lean_object* v_t_1373_, lean_object* v_k_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Std_DTreeMap_Raw_getKeyGE_x21___redArg(v_cmp_1371_, v_inst_1372_, v_t_1373_, v_k_1374_);
lean_dec(v_inst_1372_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21(lean_object* v_00_u03b1_1376_, lean_object* v_00_u03b2_1377_, lean_object* v_cmp_1378_, lean_object* v_inst_1379_, lean_object* v_t_1380_, lean_object* v_k_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1378_, v_k_1381_, v___x_1382_, v_t_1380_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1385_ = l_panic___redArg(v_inst_1379_, v___x_1384_);
return v___x_1385_;
}
else
{
lean_object* v_val_1386_; 
v_val_1386_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_val_1386_);
lean_dec_ref_known(v___x_1383_, 1);
return v_val_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1387_, lean_object* v_00_u03b2_1388_, lean_object* v_cmp_1389_, lean_object* v_inst_1390_, lean_object* v_t_1391_, lean_object* v_k_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Std_DTreeMap_Raw_getKeyGE_x21(v_00_u03b1_1387_, v_00_u03b2_1388_, v_cmp_1389_, v_inst_1390_, v_t_1391_, v_k_1392_);
lean_dec(v_inst_1390_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___redArg(lean_object* v_cmp_1394_, lean_object* v_inst_1395_, lean_object* v_t_1396_, lean_object* v_k_1397_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_box(0);
v___x_1399_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1394_, v_k_1397_, v___x_1398_, v_t_1396_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1401_ = l_panic___redArg(v_inst_1395_, v___x_1400_);
return v___x_1401_;
}
else
{
lean_object* v_val_1402_; 
v_val_1402_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v___x_1399_, 1);
return v_val_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1403_, lean_object* v_inst_1404_, lean_object* v_t_1405_, lean_object* v_k_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Std_DTreeMap_Raw_getKeyGT_x21___redArg(v_cmp_1403_, v_inst_1404_, v_t_1405_, v_k_1406_);
lean_dec(v_inst_1404_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21(lean_object* v_00_u03b1_1408_, lean_object* v_00_u03b2_1409_, lean_object* v_cmp_1410_, lean_object* v_inst_1411_, lean_object* v_t_1412_, lean_object* v_k_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1410_, v_k_1413_, v___x_1414_, v_t_1412_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1417_ = l_panic___redArg(v_inst_1411_, v___x_1416_);
return v___x_1417_;
}
else
{
lean_object* v_val_1418_; 
v_val_1418_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_val_1418_);
lean_dec_ref_known(v___x_1415_, 1);
return v_val_1418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1419_, lean_object* v_00_u03b2_1420_, lean_object* v_cmp_1421_, lean_object* v_inst_1422_, lean_object* v_t_1423_, lean_object* v_k_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Std_DTreeMap_Raw_getKeyGT_x21(v_00_u03b1_1419_, v_00_u03b2_1420_, v_cmp_1421_, v_inst_1422_, v_t_1423_, v_k_1424_);
lean_dec(v_inst_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___redArg(lean_object* v_cmp_1426_, lean_object* v_inst_1427_, lean_object* v_t_1428_, lean_object* v_k_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1426_, v_k_1429_, v___x_1430_, v_t_1428_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1433_ = l_panic___redArg(v_inst_1427_, v___x_1432_);
return v___x_1433_;
}
else
{
lean_object* v_val_1434_; 
v_val_1434_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_val_1434_);
lean_dec_ref_known(v___x_1431_, 1);
return v_val_1434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1435_, lean_object* v_inst_1436_, lean_object* v_t_1437_, lean_object* v_k_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Std_DTreeMap_Raw_getKeyLE_x21___redArg(v_cmp_1435_, v_inst_1436_, v_t_1437_, v_k_1438_);
lean_dec(v_inst_1436_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21(lean_object* v_00_u03b1_1440_, lean_object* v_00_u03b2_1441_, lean_object* v_cmp_1442_, lean_object* v_inst_1443_, lean_object* v_t_1444_, lean_object* v_k_1445_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_box(0);
v___x_1447_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1442_, v_k_1445_, v___x_1446_, v_t_1444_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1449_ = l_panic___redArg(v_inst_1443_, v___x_1448_);
return v___x_1449_;
}
else
{
lean_object* v_val_1450_; 
v_val_1450_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_val_1450_);
lean_dec_ref_known(v___x_1447_, 1);
return v_val_1450_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_00_u03b2_1452_, lean_object* v_cmp_1453_, lean_object* v_inst_1454_, lean_object* v_t_1455_, lean_object* v_k_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Std_DTreeMap_Raw_getKeyLE_x21(v_00_u03b1_1451_, v_00_u03b2_1452_, v_cmp_1453_, v_inst_1454_, v_t_1455_, v_k_1456_);
lean_dec(v_inst_1454_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___redArg(lean_object* v_cmp_1458_, lean_object* v_inst_1459_, lean_object* v_t_1460_, lean_object* v_k_1461_){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_box(0);
v___x_1463_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1458_, v_k_1461_, v___x_1462_, v_t_1460_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1465_ = l_panic___redArg(v_inst_1459_, v___x_1464_);
return v___x_1465_;
}
else
{
lean_object* v_val_1466_; 
v_val_1466_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_val_1466_);
lean_dec_ref_known(v___x_1463_, 1);
return v_val_1466_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1467_, lean_object* v_inst_1468_, lean_object* v_t_1469_, lean_object* v_k_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Std_DTreeMap_Raw_getKeyLT_x21___redArg(v_cmp_1467_, v_inst_1468_, v_t_1469_, v_k_1470_);
lean_dec(v_inst_1468_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21(lean_object* v_00_u03b1_1472_, lean_object* v_00_u03b2_1473_, lean_object* v_cmp_1474_, lean_object* v_inst_1475_, lean_object* v_t_1476_, lean_object* v_k_1477_){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_box(0);
v___x_1479_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1474_, v_k_1477_, v___x_1478_, v_t_1476_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1481_ = l_panic___redArg(v_inst_1475_, v___x_1480_);
return v___x_1481_;
}
else
{
lean_object* v_val_1482_; 
v_val_1482_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_val_1482_);
lean_dec_ref_known(v___x_1479_, 1);
return v_val_1482_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_00_u03b2_1484_, lean_object* v_cmp_1485_, lean_object* v_inst_1486_, lean_object* v_t_1487_, lean_object* v_k_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Std_DTreeMap_Raw_getKeyLT_x21(v_00_u03b1_1483_, v_00_u03b2_1484_, v_cmp_1485_, v_inst_1486_, v_t_1487_, v_k_1488_);
lean_dec(v_inst_1486_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___redArg(lean_object* v_cmp_1490_, lean_object* v_t_1491_, lean_object* v_k_1492_, lean_object* v_fallback_1493_){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_box(0);
v___x_1495_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1490_, v_k_1492_, v___x_1494_, v_t_1491_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_inc(v_fallback_1493_);
return v_fallback_1493_;
}
else
{
lean_object* v_val_1496_; 
v_val_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_val_1496_);
lean_dec_ref_known(v___x_1495_, 1);
return v_val_1496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___redArg___boxed(lean_object* v_cmp_1497_, lean_object* v_t_1498_, lean_object* v_k_1499_, lean_object* v_fallback_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Std_DTreeMap_Raw_getKeyGED___redArg(v_cmp_1497_, v_t_1498_, v_k_1499_, v_fallback_1500_);
lean_dec(v_fallback_1500_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED(lean_object* v_00_u03b1_1502_, lean_object* v_00_u03b2_1503_, lean_object* v_cmp_1504_, lean_object* v_t_1505_, lean_object* v_k_1506_, lean_object* v_fallback_1507_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_box(0);
v___x_1509_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1504_, v_k_1506_, v___x_1508_, v_t_1505_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_inc(v_fallback_1507_);
return v_fallback_1507_;
}
else
{
lean_object* v_val_1510_; 
v_val_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_val_1510_);
lean_dec_ref_known(v___x_1509_, 1);
return v_val_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___boxed(lean_object* v_00_u03b1_1511_, lean_object* v_00_u03b2_1512_, lean_object* v_cmp_1513_, lean_object* v_t_1514_, lean_object* v_k_1515_, lean_object* v_fallback_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Std_DTreeMap_Raw_getKeyGED(v_00_u03b1_1511_, v_00_u03b2_1512_, v_cmp_1513_, v_t_1514_, v_k_1515_, v_fallback_1516_);
lean_dec(v_fallback_1516_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___redArg(lean_object* v_cmp_1518_, lean_object* v_t_1519_, lean_object* v_k_1520_, lean_object* v_fallback_1521_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_box(0);
v___x_1523_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1518_, v_k_1520_, v___x_1522_, v_t_1519_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_inc(v_fallback_1521_);
return v_fallback_1521_;
}
else
{
lean_object* v_val_1524_; 
v_val_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_val_1524_);
lean_dec_ref_known(v___x_1523_, 1);
return v_val_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___redArg___boxed(lean_object* v_cmp_1525_, lean_object* v_t_1526_, lean_object* v_k_1527_, lean_object* v_fallback_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Std_DTreeMap_Raw_getKeyGTD___redArg(v_cmp_1525_, v_t_1526_, v_k_1527_, v_fallback_1528_);
lean_dec(v_fallback_1528_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD(lean_object* v_00_u03b1_1530_, lean_object* v_00_u03b2_1531_, lean_object* v_cmp_1532_, lean_object* v_t_1533_, lean_object* v_k_1534_, lean_object* v_fallback_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_box(0);
v___x_1537_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1532_, v_k_1534_, v___x_1536_, v_t_1533_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_inc(v_fallback_1535_);
return v_fallback_1535_;
}
else
{
lean_object* v_val_1538_; 
v_val_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_val_1538_);
lean_dec_ref_known(v___x_1537_, 1);
return v_val_1538_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___boxed(lean_object* v_00_u03b1_1539_, lean_object* v_00_u03b2_1540_, lean_object* v_cmp_1541_, lean_object* v_t_1542_, lean_object* v_k_1543_, lean_object* v_fallback_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Std_DTreeMap_Raw_getKeyGTD(v_00_u03b1_1539_, v_00_u03b2_1540_, v_cmp_1541_, v_t_1542_, v_k_1543_, v_fallback_1544_);
lean_dec(v_fallback_1544_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___redArg(lean_object* v_cmp_1546_, lean_object* v_t_1547_, lean_object* v_k_1548_, lean_object* v_fallback_1549_){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_box(0);
v___x_1551_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1546_, v_k_1548_, v___x_1550_, v_t_1547_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_inc(v_fallback_1549_);
return v_fallback_1549_;
}
else
{
lean_object* v_val_1552_; 
v_val_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1551_, 1);
return v_val_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___redArg___boxed(lean_object* v_cmp_1553_, lean_object* v_t_1554_, lean_object* v_k_1555_, lean_object* v_fallback_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Std_DTreeMap_Raw_getKeyLED___redArg(v_cmp_1553_, v_t_1554_, v_k_1555_, v_fallback_1556_);
lean_dec(v_fallback_1556_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED(lean_object* v_00_u03b1_1558_, lean_object* v_00_u03b2_1559_, lean_object* v_cmp_1560_, lean_object* v_t_1561_, lean_object* v_k_1562_, lean_object* v_fallback_1563_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_box(0);
v___x_1565_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1560_, v_k_1562_, v___x_1564_, v_t_1561_);
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
lean_dec_ref_known(v___x_1565_, 1);
return v_val_1566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___boxed(lean_object* v_00_u03b1_1567_, lean_object* v_00_u03b2_1568_, lean_object* v_cmp_1569_, lean_object* v_t_1570_, lean_object* v_k_1571_, lean_object* v_fallback_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Std_DTreeMap_Raw_getKeyLED(v_00_u03b1_1567_, v_00_u03b2_1568_, v_cmp_1569_, v_t_1570_, v_k_1571_, v_fallback_1572_);
lean_dec(v_fallback_1572_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___redArg(lean_object* v_cmp_1574_, lean_object* v_t_1575_, lean_object* v_k_1576_, lean_object* v_fallback_1577_){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_box(0);
v___x_1579_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1574_, v_k_1576_, v___x_1578_, v_t_1575_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___redArg___boxed(lean_object* v_cmp_1581_, lean_object* v_t_1582_, lean_object* v_k_1583_, lean_object* v_fallback_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Std_DTreeMap_Raw_getKeyLTD___redArg(v_cmp_1581_, v_t_1582_, v_k_1583_, v_fallback_1584_);
lean_dec(v_fallback_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD(lean_object* v_00_u03b1_1586_, lean_object* v_00_u03b2_1587_, lean_object* v_cmp_1588_, lean_object* v_t_1589_, lean_object* v_k_1590_, lean_object* v_fallback_1591_){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_box(0);
v___x_1593_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1588_, v_k_1590_, v___x_1592_, v_t_1589_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___boxed(lean_object* v_00_u03b1_1595_, lean_object* v_00_u03b2_1596_, lean_object* v_cmp_1597_, lean_object* v_t_1598_, lean_object* v_k_1599_, lean_object* v_fallback_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Std_DTreeMap_Raw_getKeyLTD(v_00_u03b1_1595_, v_00_u03b2_1596_, v_cmp_1597_, v_t_1598_, v_k_1599_, v_fallback_1600_);
lean_dec(v_fallback_1600_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1602_, lean_object* v_t_1603_, lean_object* v_a_1604_, lean_object* v_b_1605_){
_start:
{
lean_object* v___x_1606_; 
lean_inc(v_a_1604_);
lean_inc(v_t_1603_);
lean_inc_ref(v_cmp_1602_);
v___x_1606_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1602_, v_t_1603_, v_a_1604_);
if (lean_obj_tag(v___x_1606_) == 0)
{
uint8_t v___x_1607_; 
lean_inc(v_t_1603_);
lean_inc(v_a_1604_);
lean_inc_ref(v_cmp_1602_);
v___x_1607_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1602_, v_a_1604_, v_t_1603_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1602_, v_a_1604_, v_b_1605_, v_t_1603_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1606_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; 
lean_dec(v_b_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_cmp_1602_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1606_);
lean_ctor_set(v___x_1610_, 1, v_t_1603_);
return v___x_1610_;
}
}
else
{
lean_object* v___x_1611_; 
lean_dec(v_b_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_cmp_1602_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1606_);
lean_ctor_set(v___x_1611_, 1, v_t_1603_);
return v___x_1611_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1612_, lean_object* v_cmp_1613_, lean_object* v_00_u03b2_1614_, lean_object* v_t_1615_, lean_object* v_a_1616_, lean_object* v_b_1617_){
_start:
{
lean_object* v___x_1618_; 
lean_inc(v_a_1616_);
lean_inc(v_t_1615_);
lean_inc_ref(v_cmp_1613_);
v___x_1618_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1613_, v_t_1615_, v_a_1616_);
if (lean_obj_tag(v___x_1618_) == 0)
{
uint8_t v___x_1619_; 
lean_inc(v_t_1615_);
lean_inc(v_a_1616_);
lean_inc_ref(v_cmp_1613_);
v___x_1619_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1613_, v_a_1616_, v_t_1615_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1613_, v_a_1616_, v_b_1617_, v_t_1615_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1618_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; 
lean_dec(v_b_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_cmp_1613_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1618_);
lean_ctor_set(v___x_1622_, 1, v_t_1615_);
return v___x_1622_;
}
}
else
{
lean_object* v___x_1623_; 
lean_dec(v_b_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_cmp_1613_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1618_);
lean_ctor_set(v___x_1623_, 1, v_t_1615_);
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x3f___redArg(lean_object* v_cmp_1624_, lean_object* v_t_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1624_, v_t_1625_, v_a_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x3f(lean_object* v_00_u03b1_1628_, lean_object* v_cmp_1629_, lean_object* v_00_u03b2_1630_, lean_object* v_t_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1629_, v_t_1631_, v_a_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get___redArg(lean_object* v_cmp_1634_, lean_object* v_t_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1634_, v_t_1635_, v_a_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get(lean_object* v_00_u03b1_1638_, lean_object* v_cmp_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_t_1641_, lean_object* v_a_1642_, lean_object* v_h_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1639_, v_t_1641_, v_a_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___redArg(lean_object* v_cmp_1645_, lean_object* v_inst_1646_, lean_object* v_t_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1645_, v_inst_1646_, v_t_1647_, v_a_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___redArg___boxed(lean_object* v_cmp_1650_, lean_object* v_inst_1651_, lean_object* v_t_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Std_DTreeMap_Raw_Const_get_x21___redArg(v_cmp_1650_, v_inst_1651_, v_t_1652_, v_a_1653_);
lean_dec(v_inst_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21(lean_object* v_00_u03b1_1655_, lean_object* v_cmp_1656_, lean_object* v_00_u03b2_1657_, lean_object* v_inst_1658_, lean_object* v_t_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1656_, v_inst_1658_, v_t_1659_, v_a_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___boxed(lean_object* v_00_u03b1_1662_, lean_object* v_cmp_1663_, lean_object* v_00_u03b2_1664_, lean_object* v_inst_1665_, lean_object* v_t_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Std_DTreeMap_Raw_Const_get_x21(v_00_u03b1_1662_, v_cmp_1663_, v_00_u03b2_1664_, v_inst_1665_, v_t_1666_, v_a_1667_);
lean_dec(v_inst_1665_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___redArg(lean_object* v_cmp_1669_, lean_object* v_t_1670_, lean_object* v_a_1671_, lean_object* v_fallback_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1669_, v_t_1670_, v_a_1671_, v_fallback_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___redArg___boxed(lean_object* v_cmp_1674_, lean_object* v_t_1675_, lean_object* v_a_1676_, lean_object* v_fallback_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Std_DTreeMap_Raw_Const_getD___redArg(v_cmp_1674_, v_t_1675_, v_a_1676_, v_fallback_1677_);
lean_dec(v_fallback_1677_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD(lean_object* v_00_u03b1_1679_, lean_object* v_cmp_1680_, lean_object* v_00_u03b2_1681_, lean_object* v_t_1682_, lean_object* v_a_1683_, lean_object* v_fallback_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1680_, v_t_1682_, v_a_1683_, v_fallback_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___boxed(lean_object* v_00_u03b1_1686_, lean_object* v_cmp_1687_, lean_object* v_00_u03b2_1688_, lean_object* v_t_1689_, lean_object* v_a_1690_, lean_object* v_fallback_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Std_DTreeMap_Raw_Const_getD(v_00_u03b1_1686_, v_cmp_1687_, v_00_u03b2_1688_, v_t_1689_, v_a_1690_, v_fallback_1691_);
lean_dec(v_fallback_1691_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg(lean_object* v_t_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg(v_t_1695_);
lean_dec(v_t_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f(lean_object* v_00_u03b1_1697_, lean_object* v_cmp_1698_, lean_object* v_00_u03b2_1699_, lean_object* v_t_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1702_, lean_object* v_cmp_1703_, lean_object* v_00_u03b2_1704_, lean_object* v_t_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Std_DTreeMap_Raw_Const_minEntry_x3f(v_00_u03b1_1702_, v_cmp_1703_, v_00_u03b2_1704_, v_t_1705_);
lean_dec(v_t_1705_);
lean_dec_ref(v_cmp_1703_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg(lean_object* v_inst_1707_, lean_object* v_t_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1707_, v_t_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1710_, lean_object* v_t_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg(v_inst_1710_, v_t_1711_);
lean_dec(v_t_1711_);
lean_dec_ref(v_inst_1710_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21(lean_object* v_00_u03b1_1713_, lean_object* v_cmp_1714_, lean_object* v_00_u03b2_1715_, lean_object* v_inst_1716_, lean_object* v_t_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1716_, v_t_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_cmp_1720_, lean_object* v_00_u03b2_1721_, lean_object* v_inst_1722_, lean_object* v_t_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Std_DTreeMap_Raw_Const_minEntry_x21(v_00_u03b1_1719_, v_cmp_1720_, v_00_u03b2_1721_, v_inst_1722_, v_t_1723_);
lean_dec(v_t_1723_);
lean_dec_ref(v_inst_1722_);
lean_dec_ref(v_cmp_1720_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___redArg(lean_object* v_t_1725_, lean_object* v_fallback_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1725_, v_fallback_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___redArg___boxed(lean_object* v_t_1728_, lean_object* v_fallback_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Std_DTreeMap_Raw_Const_minEntryD___redArg(v_t_1728_, v_fallback_1729_);
lean_dec_ref(v_fallback_1729_);
lean_dec(v_t_1728_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD(lean_object* v_00_u03b1_1731_, lean_object* v_cmp_1732_, lean_object* v_00_u03b2_1733_, lean_object* v_t_1734_, lean_object* v_fallback_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1734_, v_fallback_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___boxed(lean_object* v_00_u03b1_1737_, lean_object* v_cmp_1738_, lean_object* v_00_u03b2_1739_, lean_object* v_t_1740_, lean_object* v_fallback_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Std_DTreeMap_Raw_Const_minEntryD(v_00_u03b1_1737_, v_cmp_1738_, v_00_u03b2_1739_, v_t_1740_, v_fallback_1741_);
lean_dec_ref(v_fallback_1741_);
lean_dec(v_t_1740_);
lean_dec_ref(v_cmp_1738_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg(lean_object* v_t_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg(v_t_1745_);
lean_dec(v_t_1745_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f(lean_object* v_00_u03b1_1747_, lean_object* v_cmp_1748_, lean_object* v_00_u03b2_1749_, lean_object* v_t_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1752_, lean_object* v_cmp_1753_, lean_object* v_00_u03b2_1754_, lean_object* v_t_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Std_DTreeMap_Raw_Const_maxEntry_x3f(v_00_u03b1_1752_, v_cmp_1753_, v_00_u03b2_1754_, v_t_1755_);
lean_dec(v_t_1755_);
lean_dec_ref(v_cmp_1753_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg(lean_object* v_inst_1757_, lean_object* v_t_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1757_, v_t_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_1760_, lean_object* v_t_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg(v_inst_1760_, v_t_1761_);
lean_dec(v_t_1761_);
lean_dec_ref(v_inst_1760_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21(lean_object* v_00_u03b1_1763_, lean_object* v_cmp_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_inst_1766_, lean_object* v_t_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1766_, v_t_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_1769_, lean_object* v_cmp_1770_, lean_object* v_00_u03b2_1771_, lean_object* v_inst_1772_, lean_object* v_t_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Std_DTreeMap_Raw_Const_maxEntry_x21(v_00_u03b1_1769_, v_cmp_1770_, v_00_u03b2_1771_, v_inst_1772_, v_t_1773_);
lean_dec(v_t_1773_);
lean_dec_ref(v_inst_1772_);
lean_dec_ref(v_cmp_1770_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___redArg(lean_object* v_t_1775_, lean_object* v_fallback_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1775_, v_fallback_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___redArg___boxed(lean_object* v_t_1778_, lean_object* v_fallback_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Std_DTreeMap_Raw_Const_maxEntryD___redArg(v_t_1778_, v_fallback_1779_);
lean_dec_ref(v_fallback_1779_);
lean_dec(v_t_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD(lean_object* v_00_u03b1_1781_, lean_object* v_cmp_1782_, lean_object* v_00_u03b2_1783_, lean_object* v_t_1784_, lean_object* v_fallback_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1784_, v_fallback_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___boxed(lean_object* v_00_u03b1_1787_, lean_object* v_cmp_1788_, lean_object* v_00_u03b2_1789_, lean_object* v_t_1790_, lean_object* v_fallback_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Std_DTreeMap_Raw_Const_maxEntryD(v_00_u03b1_1787_, v_cmp_1788_, v_00_u03b2_1789_, v_t_1790_, v_fallback_1791_);
lean_dec_ref(v_fallback_1791_);
lean_dec(v_t_1790_);
lean_dec_ref(v_cmp_1788_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg(lean_object* v_t_1793_, lean_object* v_n_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1793_, v_n_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_1796_, lean_object* v_n_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg(v_t_1796_, v_n_1797_);
lean_dec(v_t_1796_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_1799_, lean_object* v_cmp_1800_, lean_object* v_00_u03b2_1801_, lean_object* v_t_1802_, lean_object* v_n_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1802_, v_n_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1805_, lean_object* v_cmp_1806_, lean_object* v_00_u03b2_1807_, lean_object* v_t_1808_, lean_object* v_n_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f(v_00_u03b1_1805_, v_cmp_1806_, v_00_u03b2_1807_, v_t_1808_, v_n_1809_);
lean_dec(v_t_1808_);
lean_dec_ref(v_cmp_1806_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg(lean_object* v_inst_1811_, lean_object* v_t_1812_, lean_object* v_n_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1811_, v_t_1812_, v_n_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_1815_, lean_object* v_t_1816_, lean_object* v_n_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg(v_inst_1815_, v_t_1816_, v_n_1817_);
lean_dec(v_t_1816_);
lean_dec_ref(v_inst_1815_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21(lean_object* v_00_u03b1_1819_, lean_object* v_cmp_1820_, lean_object* v_00_u03b2_1821_, lean_object* v_inst_1822_, lean_object* v_t_1823_, lean_object* v_n_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1822_, v_t_1823_, v_n_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_1826_, lean_object* v_cmp_1827_, lean_object* v_00_u03b2_1828_, lean_object* v_inst_1829_, lean_object* v_t_1830_, lean_object* v_n_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x21(v_00_u03b1_1826_, v_cmp_1827_, v_00_u03b2_1828_, v_inst_1829_, v_t_1830_, v_n_1831_);
lean_dec(v_t_1830_);
lean_dec_ref(v_inst_1829_);
lean_dec_ref(v_cmp_1827_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg(lean_object* v_t_1833_, lean_object* v_n_1834_, lean_object* v_fallback_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1833_, v_n_1834_, v_fallback_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_1837_, lean_object* v_n_1838_, lean_object* v_fallback_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg(v_t_1837_, v_n_1838_, v_fallback_1839_);
lean_dec_ref(v_fallback_1839_);
lean_dec(v_t_1837_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD(lean_object* v_00_u03b1_1841_, lean_object* v_cmp_1842_, lean_object* v_00_u03b2_1843_, lean_object* v_t_1844_, lean_object* v_n_1845_, lean_object* v_fallback_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1844_, v_n_1845_, v_fallback_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_cmp_1849_, lean_object* v_00_u03b2_1850_, lean_object* v_t_1851_, lean_object* v_n_1852_, lean_object* v_fallback_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Std_DTreeMap_Raw_Const_entryAtIdxD(v_00_u03b1_1848_, v_cmp_1849_, v_00_u03b2_1850_, v_t_1851_, v_n_1852_, v_fallback_1853_);
lean_dec_ref(v_fallback_1853_);
lean_dec(v_t_1851_);
lean_dec_ref(v_cmp_1849_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_1855_, lean_object* v_t_1856_, lean_object* v_k_1857_){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = lean_box(0);
v___x_1859_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1855_, v_k_1857_, v___x_1858_, v_t_1856_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x3f(lean_object* v_00_u03b1_1860_, lean_object* v_cmp_1861_, lean_object* v_00_u03b2_1862_, lean_object* v_t_1863_, lean_object* v_k_1864_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_box(0);
v___x_1866_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1861_, v_k_1864_, v___x_1865_, v_t_1863_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_1867_, lean_object* v_t_1868_, lean_object* v_k_1869_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_box(0);
v___x_1871_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1867_, v_k_1869_, v___x_1870_, v_t_1868_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x3f(lean_object* v_00_u03b1_1872_, lean_object* v_cmp_1873_, lean_object* v_00_u03b2_1874_, lean_object* v_t_1875_, lean_object* v_k_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_box(0);
v___x_1878_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1873_, v_k_1876_, v___x_1877_, v_t_1875_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_1879_, lean_object* v_t_1880_, lean_object* v_k_1881_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_box(0);
v___x_1883_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1879_, v_k_1881_, v___x_1882_, v_t_1880_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x3f(lean_object* v_00_u03b1_1884_, lean_object* v_cmp_1885_, lean_object* v_00_u03b2_1886_, lean_object* v_t_1887_, lean_object* v_k_1888_){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_box(0);
v___x_1890_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1885_, v_k_1888_, v___x_1889_, v_t_1887_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_1891_, lean_object* v_t_1892_, lean_object* v_k_1893_){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_box(0);
v___x_1895_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1891_, v_k_1893_, v___x_1894_, v_t_1892_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x3f(lean_object* v_00_u03b1_1896_, lean_object* v_cmp_1897_, lean_object* v_00_u03b2_1898_, lean_object* v_t_1899_, lean_object* v_k_1900_){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_box(0);
v___x_1902_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1897_, v_k_1900_, v___x_1901_, v_t_1899_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg(lean_object* v_cmp_1903_, lean_object* v_inst_1904_, lean_object* v_t_1905_, lean_object* v_k_1906_){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_box(0);
v___x_1908_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1903_, v_k_1906_, v___x_1907_, v_t_1905_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1910_ = l_panic___redArg(v_inst_1904_, v___x_1909_);
return v___x_1910_;
}
else
{
lean_object* v_val_1911_; 
v_val_1911_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_val_1911_);
lean_dec_ref_known(v___x_1908_, 1);
return v_val_1911_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1912_, lean_object* v_inst_1913_, lean_object* v_t_1914_, lean_object* v_k_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg(v_cmp_1912_, v_inst_1913_, v_t_1914_, v_k_1915_);
lean_dec_ref(v_inst_1913_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21(lean_object* v_00_u03b1_1917_, lean_object* v_cmp_1918_, lean_object* v_00_u03b2_1919_, lean_object* v_inst_1920_, lean_object* v_t_1921_, lean_object* v_k_1922_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_box(0);
v___x_1924_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1918_, v_k_1922_, v___x_1923_, v_t_1921_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1926_ = l_panic___redArg(v_inst_1920_, v___x_1925_);
return v___x_1926_;
}
else
{
lean_object* v_val_1927_; 
v_val_1927_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_val_1927_);
lean_dec_ref_known(v___x_1924_, 1);
return v_val_1927_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1928_, lean_object* v_cmp_1929_, lean_object* v_00_u03b2_1930_, lean_object* v_inst_1931_, lean_object* v_t_1932_, lean_object* v_k_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Std_DTreeMap_Raw_Const_getEntryGE_x21(v_00_u03b1_1928_, v_cmp_1929_, v_00_u03b2_1930_, v_inst_1931_, v_t_1932_, v_k_1933_);
lean_dec_ref(v_inst_1931_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg(lean_object* v_cmp_1935_, lean_object* v_inst_1936_, lean_object* v_t_1937_, lean_object* v_k_1938_){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_box(0);
v___x_1940_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1935_, v_k_1938_, v___x_1939_, v_t_1937_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1942_ = l_panic___redArg(v_inst_1936_, v___x_1941_);
return v___x_1942_;
}
else
{
lean_object* v_val_1943_; 
v_val_1943_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_val_1943_);
lean_dec_ref_known(v___x_1940_, 1);
return v_val_1943_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1944_, lean_object* v_inst_1945_, lean_object* v_t_1946_, lean_object* v_k_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg(v_cmp_1944_, v_inst_1945_, v_t_1946_, v_k_1947_);
lean_dec_ref(v_inst_1945_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21(lean_object* v_00_u03b1_1949_, lean_object* v_cmp_1950_, lean_object* v_00_u03b2_1951_, lean_object* v_inst_1952_, lean_object* v_t_1953_, lean_object* v_k_1954_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_box(0);
v___x_1956_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1950_, v_k_1954_, v___x_1955_, v_t_1953_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1958_ = l_panic___redArg(v_inst_1952_, v___x_1957_);
return v___x_1958_;
}
else
{
lean_object* v_val_1959_; 
v_val_1959_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_val_1959_);
lean_dec_ref_known(v___x_1956_, 1);
return v_val_1959_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1960_, lean_object* v_cmp_1961_, lean_object* v_00_u03b2_1962_, lean_object* v_inst_1963_, lean_object* v_t_1964_, lean_object* v_k_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Std_DTreeMap_Raw_Const_getEntryGT_x21(v_00_u03b1_1960_, v_cmp_1961_, v_00_u03b2_1962_, v_inst_1963_, v_t_1964_, v_k_1965_);
lean_dec_ref(v_inst_1963_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg(lean_object* v_cmp_1967_, lean_object* v_inst_1968_, lean_object* v_t_1969_, lean_object* v_k_1970_){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_box(0);
v___x_1972_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1967_, v_k_1970_, v___x_1971_, v_t_1969_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1974_ = l_panic___redArg(v_inst_1968_, v___x_1973_);
return v___x_1974_;
}
else
{
lean_object* v_val_1975_; 
v_val_1975_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_val_1975_);
lean_dec_ref_known(v___x_1972_, 1);
return v_val_1975_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1976_, lean_object* v_inst_1977_, lean_object* v_t_1978_, lean_object* v_k_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg(v_cmp_1976_, v_inst_1977_, v_t_1978_, v_k_1979_);
lean_dec_ref(v_inst_1977_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21(lean_object* v_00_u03b1_1981_, lean_object* v_cmp_1982_, lean_object* v_00_u03b2_1983_, lean_object* v_inst_1984_, lean_object* v_t_1985_, lean_object* v_k_1986_){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_box(0);
v___x_1988_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1982_, v_k_1986_, v___x_1987_, v_t_1985_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1990_ = l_panic___redArg(v_inst_1984_, v___x_1989_);
return v___x_1990_;
}
else
{
lean_object* v_val_1991_; 
v_val_1991_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_val_1991_);
lean_dec_ref_known(v___x_1988_, 1);
return v_val_1991_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1992_, lean_object* v_cmp_1993_, lean_object* v_00_u03b2_1994_, lean_object* v_inst_1995_, lean_object* v_t_1996_, lean_object* v_k_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Std_DTreeMap_Raw_Const_getEntryLE_x21(v_00_u03b1_1992_, v_cmp_1993_, v_00_u03b2_1994_, v_inst_1995_, v_t_1996_, v_k_1997_);
lean_dec_ref(v_inst_1995_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg(lean_object* v_cmp_1999_, lean_object* v_inst_2000_, lean_object* v_t_2001_, lean_object* v_k_2002_){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_box(0);
v___x_2004_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1999_, v_k_2002_, v___x_2003_, v_t_2001_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_2006_ = l_panic___redArg(v_inst_2000_, v___x_2005_);
return v___x_2006_;
}
else
{
lean_object* v_val_2007_; 
v_val_2007_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_val_2007_);
lean_dec_ref_known(v___x_2004_, 1);
return v_val_2007_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_2008_, lean_object* v_inst_2009_, lean_object* v_t_2010_, lean_object* v_k_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg(v_cmp_2008_, v_inst_2009_, v_t_2010_, v_k_2011_);
lean_dec_ref(v_inst_2009_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21(lean_object* v_00_u03b1_2013_, lean_object* v_cmp_2014_, lean_object* v_00_u03b2_2015_, lean_object* v_inst_2016_, lean_object* v_t_2017_, lean_object* v_k_2018_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_box(0);
v___x_2020_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2014_, v_k_2018_, v___x_2019_, v_t_2017_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_2022_ = l_panic___redArg(v_inst_2016_, v___x_2021_);
return v___x_2022_;
}
else
{
lean_object* v_val_2023_; 
v_val_2023_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_val_2023_);
lean_dec_ref_known(v___x_2020_, 1);
return v_val_2023_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2024_, lean_object* v_cmp_2025_, lean_object* v_00_u03b2_2026_, lean_object* v_inst_2027_, lean_object* v_t_2028_, lean_object* v_k_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Std_DTreeMap_Raw_Const_getEntryLT_x21(v_00_u03b1_2024_, v_cmp_2025_, v_00_u03b2_2026_, v_inst_2027_, v_t_2028_, v_k_2029_);
lean_dec_ref(v_inst_2027_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___redArg(lean_object* v_cmp_2031_, lean_object* v_t_2032_, lean_object* v_k_2033_, lean_object* v_fallback_2034_){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = lean_box(0);
v___x_2036_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2031_, v_k_2033_, v___x_2035_, v_t_2032_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_inc_ref(v_fallback_2034_);
return v_fallback_2034_;
}
else
{
lean_object* v_val_2037_; 
v_val_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_val_2037_);
lean_dec_ref_known(v___x_2036_, 1);
return v_val_2037_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2038_, lean_object* v_t_2039_, lean_object* v_k_2040_, lean_object* v_fallback_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Std_DTreeMap_Raw_Const_getEntryGED___redArg(v_cmp_2038_, v_t_2039_, v_k_2040_, v_fallback_2041_);
lean_dec_ref(v_fallback_2041_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED(lean_object* v_00_u03b1_2043_, lean_object* v_cmp_2044_, lean_object* v_00_u03b2_2045_, lean_object* v_t_2046_, lean_object* v_k_2047_, lean_object* v_fallback_2048_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = lean_box(0);
v___x_2050_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2044_, v_k_2047_, v___x_2049_, v_t_2046_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_inc_ref(v_fallback_2048_);
return v_fallback_2048_;
}
else
{
lean_object* v_val_2051_; 
v_val_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_val_2051_);
lean_dec_ref_known(v___x_2050_, 1);
return v_val_2051_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2052_, lean_object* v_cmp_2053_, lean_object* v_00_u03b2_2054_, lean_object* v_t_2055_, lean_object* v_k_2056_, lean_object* v_fallback_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Std_DTreeMap_Raw_Const_getEntryGED(v_00_u03b1_2052_, v_cmp_2053_, v_00_u03b2_2054_, v_t_2055_, v_k_2056_, v_fallback_2057_);
lean_dec_ref(v_fallback_2057_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg(lean_object* v_cmp_2059_, lean_object* v_t_2060_, lean_object* v_k_2061_, lean_object* v_fallback_2062_){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = lean_box(0);
v___x_2064_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2059_, v_k_2061_, v___x_2063_, v_t_2060_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_inc_ref(v_fallback_2062_);
return v_fallback_2062_;
}
else
{
lean_object* v_val_2065_; 
v_val_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_val_2065_);
lean_dec_ref_known(v___x_2064_, 1);
return v_val_2065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2066_, lean_object* v_t_2067_, lean_object* v_k_2068_, lean_object* v_fallback_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg(v_cmp_2066_, v_t_2067_, v_k_2068_, v_fallback_2069_);
lean_dec_ref(v_fallback_2069_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD(lean_object* v_00_u03b1_2071_, lean_object* v_cmp_2072_, lean_object* v_00_u03b2_2073_, lean_object* v_t_2074_, lean_object* v_k_2075_, lean_object* v_fallback_2076_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_box(0);
v___x_2078_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2072_, v_k_2075_, v___x_2077_, v_t_2074_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_inc_ref(v_fallback_2076_);
return v_fallback_2076_;
}
else
{
lean_object* v_val_2079_; 
v_val_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_val_2079_);
lean_dec_ref_known(v___x_2078_, 1);
return v_val_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2080_, lean_object* v_cmp_2081_, lean_object* v_00_u03b2_2082_, lean_object* v_t_2083_, lean_object* v_k_2084_, lean_object* v_fallback_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Std_DTreeMap_Raw_Const_getEntryGTD(v_00_u03b1_2080_, v_cmp_2081_, v_00_u03b2_2082_, v_t_2083_, v_k_2084_, v_fallback_2085_);
lean_dec_ref(v_fallback_2085_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___redArg(lean_object* v_cmp_2087_, lean_object* v_t_2088_, lean_object* v_k_2089_, lean_object* v_fallback_2090_){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2087_, v_k_2089_, v___x_2091_, v_t_2088_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_inc_ref(v_fallback_2090_);
return v_fallback_2090_;
}
else
{
lean_object* v_val_2093_; 
v_val_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_val_2093_);
lean_dec_ref_known(v___x_2092_, 1);
return v_val_2093_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2094_, lean_object* v_t_2095_, lean_object* v_k_2096_, lean_object* v_fallback_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Std_DTreeMap_Raw_Const_getEntryLED___redArg(v_cmp_2094_, v_t_2095_, v_k_2096_, v_fallback_2097_);
lean_dec_ref(v_fallback_2097_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED(lean_object* v_00_u03b1_2099_, lean_object* v_cmp_2100_, lean_object* v_00_u03b2_2101_, lean_object* v_t_2102_, lean_object* v_k_2103_, lean_object* v_fallback_2104_){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2100_, v_k_2103_, v___x_2105_, v_t_2102_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_inc_ref(v_fallback_2104_);
return v_fallback_2104_;
}
else
{
lean_object* v_val_2107_; 
v_val_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_val_2107_);
lean_dec_ref_known(v___x_2106_, 1);
return v_val_2107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2108_, lean_object* v_cmp_2109_, lean_object* v_00_u03b2_2110_, lean_object* v_t_2111_, lean_object* v_k_2112_, lean_object* v_fallback_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Std_DTreeMap_Raw_Const_getEntryLED(v_00_u03b1_2108_, v_cmp_2109_, v_00_u03b2_2110_, v_t_2111_, v_k_2112_, v_fallback_2113_);
lean_dec_ref(v_fallback_2113_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg(lean_object* v_cmp_2115_, lean_object* v_t_2116_, lean_object* v_k_2117_, lean_object* v_fallback_2118_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_box(0);
v___x_2120_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2115_, v_k_2117_, v___x_2119_, v_t_2116_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_inc_ref(v_fallback_2118_);
return v_fallback_2118_;
}
else
{
lean_object* v_val_2121_; 
v_val_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_val_2121_);
lean_dec_ref_known(v___x_2120_, 1);
return v_val_2121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2122_, lean_object* v_t_2123_, lean_object* v_k_2124_, lean_object* v_fallback_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg(v_cmp_2122_, v_t_2123_, v_k_2124_, v_fallback_2125_);
lean_dec_ref(v_fallback_2125_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD(lean_object* v_00_u03b1_2127_, lean_object* v_cmp_2128_, lean_object* v_00_u03b2_2129_, lean_object* v_t_2130_, lean_object* v_k_2131_, lean_object* v_fallback_2132_){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = lean_box(0);
v___x_2134_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2128_, v_k_2131_, v___x_2133_, v_t_2130_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_inc_ref(v_fallback_2132_);
return v_fallback_2132_;
}
else
{
lean_object* v_val_2135_; 
v_val_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_val_2135_);
lean_dec_ref_known(v___x_2134_, 1);
return v_val_2135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2136_, lean_object* v_cmp_2137_, lean_object* v_00_u03b2_2138_, lean_object* v_t_2139_, lean_object* v_k_2140_, lean_object* v_fallback_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Std_DTreeMap_Raw_Const_getEntryLTD(v_00_u03b1_2136_, v_cmp_2137_, v_00_u03b2_2138_, v_t_2139_, v_k_2140_, v_fallback_2141_);
lean_dec_ref(v_fallback_2141_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter___redArg(lean_object* v_f_2143_, lean_object* v_t_2144_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_2143_, v_t_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter(lean_object* v_00_u03b1_2146_, lean_object* v_00_u03b2_2147_, lean_object* v_cmp_2148_, lean_object* v_f_2149_, lean_object* v_t_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_2149_, v_t_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter___boxed(lean_object* v_00_u03b1_2152_, lean_object* v_00_u03b2_2153_, lean_object* v_cmp_2154_, lean_object* v_f_2155_, lean_object* v_t_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Std_DTreeMap_Raw_filter(v_00_u03b1_2152_, v_00_u03b2_2153_, v_cmp_2154_, v_f_2155_, v_t_2156_);
lean_dec_ref(v_cmp_2154_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM___redArg(lean_object* v_inst_2158_, lean_object* v_f_2159_, lean_object* v_init_2160_, lean_object* v_t_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2158_, v_f_2159_, v_init_2160_, v_t_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM(lean_object* v_00_u03b1_2163_, lean_object* v_00_u03b2_2164_, lean_object* v_cmp_2165_, lean_object* v_00_u03b4_2166_, lean_object* v_m_2167_, lean_object* v_inst_2168_, lean_object* v_f_2169_, lean_object* v_init_2170_, lean_object* v_t_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2168_, v_f_2169_, v_init_2170_, v_t_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM___boxed(lean_object* v_00_u03b1_2173_, lean_object* v_00_u03b2_2174_, lean_object* v_cmp_2175_, lean_object* v_00_u03b4_2176_, lean_object* v_m_2177_, lean_object* v_inst_2178_, lean_object* v_f_2179_, lean_object* v_init_2180_, lean_object* v_t_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Std_DTreeMap_Raw_foldlM(v_00_u03b1_2173_, v_00_u03b2_2174_, v_cmp_2175_, v_00_u03b4_2176_, v_m_2177_, v_inst_2178_, v_f_2179_, v_init_2180_, v_t_2181_);
lean_dec_ref(v_cmp_2175_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl___redArg(lean_object* v_f_2183_, lean_object* v_init_2184_, lean_object* v_t_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2183_, v_init_2184_, v_t_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl(lean_object* v_00_u03b1_2187_, lean_object* v_00_u03b2_2188_, lean_object* v_cmp_2189_, lean_object* v_00_u03b4_2190_, lean_object* v_f_2191_, lean_object* v_init_2192_, lean_object* v_t_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2191_, v_init_2192_, v_t_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl___boxed(lean_object* v_00_u03b1_2195_, lean_object* v_00_u03b2_2196_, lean_object* v_cmp_2197_, lean_object* v_00_u03b4_2198_, lean_object* v_f_2199_, lean_object* v_init_2200_, lean_object* v_t_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Std_DTreeMap_Raw_foldl(v_00_u03b1_2195_, v_00_u03b2_2196_, v_cmp_2197_, v_00_u03b4_2198_, v_f_2199_, v_init_2200_, v_t_2201_);
lean_dec_ref(v_cmp_2197_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM___redArg(lean_object* v_inst_2203_, lean_object* v_f_2204_, lean_object* v_init_2205_, lean_object* v_t_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2203_, v_f_2204_, v_init_2205_, v_t_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM(lean_object* v_00_u03b1_2208_, lean_object* v_00_u03b2_2209_, lean_object* v_cmp_2210_, lean_object* v_00_u03b4_2211_, lean_object* v_m_2212_, lean_object* v_inst_2213_, lean_object* v_f_2214_, lean_object* v_init_2215_, lean_object* v_t_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2213_, v_f_2214_, v_init_2215_, v_t_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM___boxed(lean_object* v_00_u03b1_2218_, lean_object* v_00_u03b2_2219_, lean_object* v_cmp_2220_, lean_object* v_00_u03b4_2221_, lean_object* v_m_2222_, lean_object* v_inst_2223_, lean_object* v_f_2224_, lean_object* v_init_2225_, lean_object* v_t_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Std_DTreeMap_Raw_foldrM(v_00_u03b1_2218_, v_00_u03b2_2219_, v_cmp_2220_, v_00_u03b4_2221_, v_m_2222_, v_inst_2223_, v_f_2224_, v_init_2225_, v_t_2226_);
lean_dec_ref(v_cmp_2220_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___redArg___lam__0(lean_object* v_f_2228_, lean_object* v_x1_2229_, lean_object* v_x2_2230_, lean_object* v_x3_2231_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_apply_3(v_f_2228_, v_x1_2229_, v_x2_2230_, v_x3_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___redArg(lean_object* v_f_2252_, lean_object* v_init_2253_, lean_object* v_t_2254_){
_start:
{
lean_object* v___f_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___f_2255_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2255_, 0, v_f_2252_);
v___x_2256_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2257_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2256_, v___f_2255_, v_init_2253_, v_t_2254_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr(lean_object* v_00_u03b1_2258_, lean_object* v_00_u03b2_2259_, lean_object* v_cmp_2260_, lean_object* v_00_u03b4_2261_, lean_object* v_f_2262_, lean_object* v_init_2263_, lean_object* v_t_2264_){
_start:
{
lean_object* v___f_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___f_2265_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2265_, 0, v_f_2262_);
v___x_2266_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2267_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2266_, v___f_2265_, v_init_2263_, v_t_2264_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___boxed(lean_object* v_00_u03b1_2268_, lean_object* v_00_u03b2_2269_, lean_object* v_cmp_2270_, lean_object* v_00_u03b4_2271_, lean_object* v_f_2272_, lean_object* v_init_2273_, lean_object* v_t_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Std_DTreeMap_Raw_foldr(v_00_u03b1_2268_, v_00_u03b2_2269_, v_cmp_2270_, v_00_u03b4_2271_, v_f_2272_, v_init_2273_, v_t_2274_);
lean_dec_ref(v_cmp_2270_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition___redArg___lam__0(lean_object* v_f_2276_, lean_object* v_cmp_2277_, lean_object* v_x_2278_, lean_object* v_a_2279_, lean_object* v_b_2280_){
_start:
{
lean_object* v_fst_2281_; lean_object* v_snd_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2296_; 
v_fst_2281_ = lean_ctor_get(v_x_2278_, 0);
v_snd_2282_ = lean_ctor_get(v_x_2278_, 1);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_x_2278_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2284_ = v_x_2278_;
v_isShared_2285_ = v_isSharedCheck_2296_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_snd_2282_);
lean_inc(v_fst_2281_);
lean_dec(v_x_2278_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2296_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; uint8_t v___x_2287_; 
lean_inc(v_b_2280_);
lean_inc(v_a_2279_);
v___x_2286_ = lean_apply_2(v_f_2276_, v_a_2279_, v_b_2280_);
v___x_2287_ = lean_unbox(v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2288_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2277_, v_a_2279_, v_b_2280_, v_snd_2282_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 1, v___x_2288_);
v___x_2290_ = v___x_2284_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_fst_2281_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2292_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2277_, v_a_2279_, v_b_2280_, v_fst_2281_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2292_);
v___x_2294_ = v___x_2284_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v_snd_2282_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition___redArg(lean_object* v_cmp_2299_, lean_object* v_f_2300_, lean_object* v_t_2301_){
_start:
{
lean_object* v___f_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___f_2302_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2302_, 0, v_f_2300_);
lean_closure_set(v___f_2302_, 1, v_cmp_2299_);
v___x_2303_ = ((lean_object*)(l_Std_DTreeMap_Raw_partition___redArg___closed__0));
v___x_2304_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2302_, v___x_2303_, v_t_2301_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition(lean_object* v_00_u03b1_2305_, lean_object* v_00_u03b2_2306_, lean_object* v_cmp_2307_, lean_object* v_f_2308_, lean_object* v_t_2309_){
_start:
{
lean_object* v___f_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___f_2310_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2310_, 0, v_f_2308_);
lean_closure_set(v___f_2310_, 1, v_cmp_2307_);
v___x_2311_ = ((lean_object*)(l_Std_DTreeMap_Raw_partition___redArg___closed__0));
v___x_2312_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2310_, v___x_2311_, v_t_2309_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___redArg___lam__0(lean_object* v_f_2313_, lean_object* v_x_2314_, lean_object* v_k_2315_, lean_object* v_v_2316_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_apply_2(v_f_2313_, v_k_2315_, v_v_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___redArg(lean_object* v_inst_2318_, lean_object* v_f_2319_, lean_object* v_t_2320_){
_start:
{
lean_object* v___f_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___f_2321_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2321_, 0, v_f_2319_);
v___x_2322_ = lean_box(0);
v___x_2323_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2318_, v___f_2321_, v___x_2322_, v_t_2320_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM(lean_object* v_00_u03b1_2324_, lean_object* v_00_u03b2_2325_, lean_object* v_cmp_2326_, lean_object* v_m_2327_, lean_object* v_inst_2328_, lean_object* v_f_2329_, lean_object* v_t_2330_){
_start:
{
lean_object* v___f_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___f_2331_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2331_, 0, v_f_2329_);
v___x_2332_ = lean_box(0);
v___x_2333_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2328_, v___f_2331_, v___x_2332_, v_t_2330_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___boxed(lean_object* v_00_u03b1_2334_, lean_object* v_00_u03b2_2335_, lean_object* v_cmp_2336_, lean_object* v_m_2337_, lean_object* v_inst_2338_, lean_object* v_f_2339_, lean_object* v_t_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Std_DTreeMap_Raw_forM(v_00_u03b1_2334_, v_00_u03b2_2335_, v_cmp_2336_, v_m_2337_, v_inst_2338_, v_f_2339_, v_t_2340_);
lean_dec_ref(v_cmp_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___redArg___lam__0(lean_object* v_toPure_2342_, lean_object* v_____do__lift_2343_){
_start:
{
lean_object* v_a_2344_; lean_object* v___x_2345_; 
v_a_2344_ = lean_ctor_get(v_____do__lift_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref(v_____do__lift_2343_);
v___x_2345_ = lean_apply_2(v_toPure_2342_, lean_box(0), v_a_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___redArg(lean_object* v_inst_2346_, lean_object* v_f_2347_, lean_object* v_init_2348_, lean_object* v_t_2349_){
_start:
{
lean_object* v_toApplicative_2350_; lean_object* v_toBind_2351_; lean_object* v_toPure_2352_; lean_object* v___x_2353_; lean_object* v___f_2354_; lean_object* v___x_2355_; 
v_toApplicative_2350_ = lean_ctor_get(v_inst_2346_, 0);
v_toBind_2351_ = lean_ctor_get(v_inst_2346_, 1);
lean_inc(v_toBind_2351_);
v_toPure_2352_ = lean_ctor_get(v_toApplicative_2350_, 1);
lean_inc(v_toPure_2352_);
v___x_2353_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2346_, v_f_2347_, v_init_2348_, v_t_2349_);
v___f_2354_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2354_, 0, v_toPure_2352_);
v___x_2355_ = lean_apply_4(v_toBind_2351_, lean_box(0), lean_box(0), v___x_2353_, v___f_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn(lean_object* v_00_u03b1_2356_, lean_object* v_00_u03b2_2357_, lean_object* v_cmp_2358_, lean_object* v_00_u03b4_2359_, lean_object* v_m_2360_, lean_object* v_inst_2361_, lean_object* v_f_2362_, lean_object* v_init_2363_, lean_object* v_t_2364_){
_start:
{
lean_object* v_toApplicative_2365_; lean_object* v_toBind_2366_; lean_object* v_toPure_2367_; lean_object* v___x_2368_; lean_object* v___f_2369_; lean_object* v___x_2370_; 
v_toApplicative_2365_ = lean_ctor_get(v_inst_2361_, 0);
v_toBind_2366_ = lean_ctor_get(v_inst_2361_, 1);
lean_inc(v_toBind_2366_);
v_toPure_2367_ = lean_ctor_get(v_toApplicative_2365_, 1);
lean_inc(v_toPure_2367_);
v___x_2368_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2361_, v_f_2362_, v_init_2363_, v_t_2364_);
v___f_2369_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2369_, 0, v_toPure_2367_);
v___x_2370_ = lean_apply_4(v_toBind_2366_, lean_box(0), lean_box(0), v___x_2368_, v___f_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___boxed(lean_object* v_00_u03b1_2371_, lean_object* v_00_u03b2_2372_, lean_object* v_cmp_2373_, lean_object* v_00_u03b4_2374_, lean_object* v_m_2375_, lean_object* v_inst_2376_, lean_object* v_f_2377_, lean_object* v_init_2378_, lean_object* v_t_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Std_DTreeMap_Raw_forIn(v_00_u03b1_2371_, v_00_u03b2_2372_, v_cmp_2373_, v_00_u03b4_2374_, v_m_2375_, v_inst_2376_, v_f_2377_, v_init_2378_, v_t_2379_);
lean_dec_ref(v_cmp_2373_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_2381_, lean_object* v_x_2382_, lean_object* v_k_2383_, lean_object* v_v_2384_){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2385_, 0, v_k_2383_);
lean_ctor_set(v___x_2385_, 1, v_v_2384_);
v___x_2386_ = lean_apply_1(v_f_2381_, v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1(lean_object* v_inst_2387_, lean_object* v_t_2388_, lean_object* v_f_2389_){
_start:
{
lean_object* v___f_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___f_2390_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2390_, 0, v_f_2389_);
v___x_2391_ = lean_box(0);
v___x_2392_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2387_, v___f_2390_, v___x_2391_, v_t_2388_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg(lean_object* v_inst_2393_){
_start:
{
lean_object* v___f_2394_; 
v___f_2394_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2394_, 0, v_inst_2393_);
return v___f_2394_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad(lean_object* v_00_u03b1_2395_, lean_object* v_00_u03b2_2396_, lean_object* v_cmp_2397_, lean_object* v_m_2398_, lean_object* v_inst_2399_){
_start:
{
lean_object* v___f_2400_; 
v___f_2400_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2400_, 0, v_inst_2399_);
return v___f_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___boxed(lean_object* v_00_u03b1_2401_, lean_object* v_00_u03b2_2402_, lean_object* v_cmp_2403_, lean_object* v_m_2404_, lean_object* v_inst_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Std_DTreeMap_Raw_instForMSigmaOfMonad(v_00_u03b1_2401_, v_00_u03b2_2402_, v_cmp_2403_, v_m_2404_, v_inst_2405_);
lean_dec_ref(v_cmp_2403_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_2407_, lean_object* v_a_2408_, lean_object* v_b_2409_, lean_object* v_acc_2410_){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v_a_2408_);
lean_ctor_set(v___x_2411_, 1, v_b_2409_);
v___x_2412_ = lean_apply_2(v_f_2407_, v___x_2411_, v_acc_2410_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_2413_, lean_object* v_00_u03b2_2414_, lean_object* v_t_2415_, lean_object* v_init_2416_, lean_object* v_f_2417_){
_start:
{
lean_object* v_toApplicative_2418_; lean_object* v_toBind_2419_; lean_object* v_toPure_2420_; lean_object* v___f_2421_; lean_object* v___x_2422_; lean_object* v___f_2423_; lean_object* v___x_2424_; 
v_toApplicative_2418_ = lean_ctor_get(v_inst_2413_, 0);
v_toBind_2419_ = lean_ctor_get(v_inst_2413_, 1);
lean_inc(v_toBind_2419_);
v_toPure_2420_ = lean_ctor_get(v_toApplicative_2418_, 1);
lean_inc(v_toPure_2420_);
v___f_2421_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2421_, 0, v_f_2417_);
v___x_2422_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2413_, v___f_2421_, v_init_2416_, v_t_2415_);
v___f_2423_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2423_, 0, v_toPure_2420_);
v___x_2424_ = lean_apply_4(v_toBind_2419_, lean_box(0), lean_box(0), v___x_2422_, v___f_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg(lean_object* v_inst_2425_){
_start:
{
lean_object* v___f_2426_; 
v___f_2426_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2426_, 0, v_inst_2425_);
return v___f_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad(lean_object* v_00_u03b1_2427_, lean_object* v_00_u03b2_2428_, lean_object* v_cmp_2429_, lean_object* v_m_2430_, lean_object* v_inst_2431_){
_start:
{
lean_object* v___f_2432_; 
v___f_2432_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2432_, 0, v_inst_2431_);
return v___f_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___boxed(lean_object* v_00_u03b1_2433_, lean_object* v_00_u03b2_2434_, lean_object* v_cmp_2435_, lean_object* v_m_2436_, lean_object* v_inst_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Std_DTreeMap_Raw_instForInSigmaOfMonad(v_00_u03b1_2433_, v_00_u03b2_2434_, v_cmp_2435_, v_m_2436_, v_inst_2437_);
lean_dec_ref(v_cmp_2435_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2439_, lean_object* v_x_2440_, lean_object* v_k_2441_, lean_object* v_v_2442_){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2443_, 0, v_k_2441_);
lean_ctor_set(v___x_2443_, 1, v_v_2442_);
v___x_2444_ = lean_apply_1(v_f_2439_, v___x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___redArg(lean_object* v_inst_2445_, lean_object* v_f_2446_, lean_object* v_t_2447_){
_start:
{
lean_object* v___f_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___f_2448_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2448_, 0, v_f_2446_);
v___x_2449_ = lean_box(0);
v___x_2450_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2445_, v___f_2448_, v___x_2449_, v_t_2447_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried(lean_object* v_00_u03b1_2451_, lean_object* v_cmp_2452_, lean_object* v_m_2453_, lean_object* v_inst_2454_, lean_object* v_00_u03b2_2455_, lean_object* v_f_2456_, lean_object* v_t_2457_){
_start:
{
lean_object* v___f_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___f_2458_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2458_, 0, v_f_2456_);
v___x_2459_ = lean_box(0);
v___x_2460_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2454_, v___f_2458_, v___x_2459_, v_t_2457_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2461_, lean_object* v_cmp_2462_, lean_object* v_m_2463_, lean_object* v_inst_2464_, lean_object* v_00_u03b2_2465_, lean_object* v_f_2466_, lean_object* v_t_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Std_DTreeMap_Raw_Const_forMUncurried(v_00_u03b1_2461_, v_cmp_2462_, v_m_2463_, v_inst_2464_, v_00_u03b2_2465_, v_f_2466_, v_t_2467_);
lean_dec_ref(v_cmp_2462_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2469_, lean_object* v_a_2470_, lean_object* v_b_2471_, lean_object* v_d_2472_){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v_a_2470_);
lean_ctor_set(v___x_2473_, 1, v_b_2471_);
v___x_2474_ = lean_apply_2(v_f_2469_, v___x_2473_, v_d_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___redArg(lean_object* v_inst_2475_, lean_object* v_f_2476_, lean_object* v_init_2477_, lean_object* v_t_2478_){
_start:
{
lean_object* v_toApplicative_2479_; lean_object* v_toBind_2480_; lean_object* v_toPure_2481_; lean_object* v___f_2482_; lean_object* v___x_2483_; lean_object* v___f_2484_; lean_object* v___x_2485_; 
v_toApplicative_2479_ = lean_ctor_get(v_inst_2475_, 0);
v_toBind_2480_ = lean_ctor_get(v_inst_2475_, 1);
lean_inc(v_toBind_2480_);
v_toPure_2481_ = lean_ctor_get(v_toApplicative_2479_, 1);
lean_inc(v_toPure_2481_);
v___f_2482_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2482_, 0, v_f_2476_);
v___x_2483_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2475_, v___f_2482_, v_init_2477_, v_t_2478_);
v___f_2484_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2484_, 0, v_toPure_2481_);
v___x_2485_ = lean_apply_4(v_toBind_2480_, lean_box(0), lean_box(0), v___x_2483_, v___f_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried(lean_object* v_00_u03b1_2486_, lean_object* v_cmp_2487_, lean_object* v_00_u03b4_2488_, lean_object* v_m_2489_, lean_object* v_inst_2490_, lean_object* v_00_u03b2_2491_, lean_object* v_f_2492_, lean_object* v_init_2493_, lean_object* v_t_2494_){
_start:
{
lean_object* v_toApplicative_2495_; lean_object* v_toBind_2496_; lean_object* v_toPure_2497_; lean_object* v___f_2498_; lean_object* v___x_2499_; lean_object* v___f_2500_; lean_object* v___x_2501_; 
v_toApplicative_2495_ = lean_ctor_get(v_inst_2490_, 0);
v_toBind_2496_ = lean_ctor_get(v_inst_2490_, 1);
lean_inc(v_toBind_2496_);
v_toPure_2497_ = lean_ctor_get(v_toApplicative_2495_, 1);
lean_inc(v_toPure_2497_);
v___f_2498_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2498_, 0, v_f_2492_);
v___x_2499_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2490_, v___f_2498_, v_init_2493_, v_t_2494_);
v___f_2500_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2500_, 0, v_toPure_2497_);
v___x_2501_ = lean_apply_4(v_toBind_2496_, lean_box(0), lean_box(0), v___x_2499_, v___f_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2502_, lean_object* v_cmp_2503_, lean_object* v_00_u03b4_2504_, lean_object* v_m_2505_, lean_object* v_inst_2506_, lean_object* v_00_u03b2_2507_, lean_object* v_f_2508_, lean_object* v_init_2509_, lean_object* v_t_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Std_DTreeMap_Raw_Const_forInUncurried(v_00_u03b1_2502_, v_cmp_2503_, v_00_u03b4_2504_, v_m_2505_, v_inst_2506_, v_00_u03b2_2507_, v_f_2508_, v_init_2509_, v_t_2510_);
lean_dec_ref(v_cmp_2503_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___lam__0(lean_object* v_p_2512_, lean_object* v___x_2513_, lean_object* v___x_2514_, lean_object* v_a_2515_, lean_object* v_b_2516_, lean_object* v_acc_2517_){
_start:
{
lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2518_ = lean_apply_2(v_p_2512_, v_a_2515_, v_b_2516_);
v___x_2519_ = lean_unbox(v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2513_);
return v___x_2520_;
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec_ref(v___x_2513_);
v___x_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2518_);
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v___x_2514_);
v___x_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
return v___x_2523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_2524_, lean_object* v___x_2525_, lean_object* v___x_2526_, lean_object* v_a_2527_, lean_object* v_b_2528_, lean_object* v_acc_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Std_DTreeMap_Raw_any___redArg___lam__0(v_p_2524_, v___x_2525_, v___x_2526_, v_a_2527_, v_b_2528_, v_acc_2529_);
lean_dec_ref(v_acc_2529_);
return v_res_2530_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_any___redArg(lean_object* v_t_2534_, lean_object* v_p_2535_){
_start:
{
lean_object* v___y_2537_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___f_2545_; lean_object* v___x_2546_; lean_object* v_a_2547_; 
v___x_2542_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2543_ = lean_box(0);
v___x_2544_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2545_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2545_, 0, v_p_2535_);
lean_closure_set(v___f_2545_, 1, v___x_2544_);
lean_closure_set(v___f_2545_, 2, v___x_2543_);
v___x_2546_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2542_, v___f_2545_, v___x_2544_, v_t_2534_);
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec(v___x_2546_);
v___y_2537_ = v_a_2547_;
goto v___jp_2536_;
v___jp_2536_:
{
lean_object* v_fst_2538_; 
v_fst_2538_ = lean_ctor_get(v___y_2537_, 0);
lean_inc(v_fst_2538_);
lean_dec_ref(v___y_2537_);
if (lean_obj_tag(v_fst_2538_) == 0)
{
uint8_t v___x_2539_; 
v___x_2539_ = 0;
return v___x_2539_;
}
else
{
lean_object* v_val_2540_; uint8_t v___x_2541_; 
v_val_2540_ = lean_ctor_get(v_fst_2538_, 0);
lean_inc(v_val_2540_);
lean_dec_ref_known(v_fst_2538_, 1);
v___x_2541_ = lean_unbox(v_val_2540_);
lean_dec(v_val_2540_);
return v___x_2541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___boxed(lean_object* v_t_2548_, lean_object* v_p_2549_){
_start:
{
uint8_t v_res_2550_; lean_object* v_r_2551_; 
v_res_2550_ = l_Std_DTreeMap_Raw_any___redArg(v_t_2548_, v_p_2549_);
v_r_2551_ = lean_box(v_res_2550_);
return v_r_2551_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_any(lean_object* v_00_u03b1_2552_, lean_object* v_00_u03b2_2553_, lean_object* v_cmp_2554_, lean_object* v_t_2555_, lean_object* v_p_2556_){
_start:
{
lean_object* v___y_2558_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___f_2566_; lean_object* v___x_2567_; lean_object* v_a_2568_; 
v___x_2563_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2564_ = lean_box(0);
v___x_2565_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2566_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2566_, 0, v_p_2556_);
lean_closure_set(v___f_2566_, 1, v___x_2565_);
lean_closure_set(v___f_2566_, 2, v___x_2564_);
v___x_2567_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2563_, v___f_2566_, v___x_2565_, v_t_2555_);
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___y_2558_ = v_a_2568_;
goto v___jp_2557_;
v___jp_2557_:
{
lean_object* v_fst_2559_; 
v_fst_2559_ = lean_ctor_get(v___y_2558_, 0);
lean_inc(v_fst_2559_);
lean_dec_ref(v___y_2558_);
if (lean_obj_tag(v_fst_2559_) == 0)
{
uint8_t v___x_2560_; 
v___x_2560_ = 0;
return v___x_2560_;
}
else
{
lean_object* v_val_2561_; uint8_t v___x_2562_; 
v_val_2561_ = lean_ctor_get(v_fst_2559_, 0);
lean_inc(v_val_2561_);
lean_dec_ref_known(v_fst_2559_, 1);
v___x_2562_ = lean_unbox(v_val_2561_);
lean_dec(v_val_2561_);
return v___x_2562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___boxed(lean_object* v_00_u03b1_2569_, lean_object* v_00_u03b2_2570_, lean_object* v_cmp_2571_, lean_object* v_t_2572_, lean_object* v_p_2573_){
_start:
{
uint8_t v_res_2574_; lean_object* v_r_2575_; 
v_res_2574_ = l_Std_DTreeMap_Raw_any(v_00_u03b1_2569_, v_00_u03b2_2570_, v_cmp_2571_, v_t_2572_, v_p_2573_);
lean_dec_ref(v_cmp_2571_);
v_r_2575_ = lean_box(v_res_2574_);
return v_r_2575_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___lam__0(lean_object* v_p_2576_, lean_object* v___x_2577_, lean_object* v___x_2578_, lean_object* v_a_2579_, lean_object* v_b_2580_, lean_object* v_acc_2581_){
_start:
{
lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2582_ = lean_apply_2(v_p_2576_, v_a_2579_, v_b_2580_);
v___x_2583_ = lean_unbox(v___x_2582_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_dec_ref(v___x_2578_);
v___x_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set(v___x_2585_, 1, v___x_2577_);
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2578_);
return v___x_2587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_2588_, lean_object* v___x_2589_, lean_object* v___x_2590_, lean_object* v_a_2591_, lean_object* v_b_2592_, lean_object* v_acc_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Std_DTreeMap_Raw_all___redArg___lam__0(v_p_2588_, v___x_2589_, v___x_2590_, v_a_2591_, v_b_2592_, v_acc_2593_);
lean_dec_ref(v_acc_2593_);
return v_res_2594_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_all___redArg(lean_object* v_t_2595_, lean_object* v_p_2596_){
_start:
{
lean_object* v___y_2598_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___f_2606_; lean_object* v___x_2607_; lean_object* v_a_2608_; 
v___x_2603_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2604_ = lean_box(0);
v___x_2605_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2606_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2606_, 0, v_p_2596_);
lean_closure_set(v___f_2606_, 1, v___x_2604_);
lean_closure_set(v___f_2606_, 2, v___x_2605_);
v___x_2607_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2603_, v___f_2606_, v___x_2605_, v_t_2595_);
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___y_2598_ = v_a_2608_;
goto v___jp_2597_;
v___jp_2597_:
{
lean_object* v_fst_2599_; 
v_fst_2599_ = lean_ctor_get(v___y_2598_, 0);
lean_inc(v_fst_2599_);
lean_dec_ref(v___y_2598_);
if (lean_obj_tag(v_fst_2599_) == 0)
{
uint8_t v___x_2600_; 
v___x_2600_ = 1;
return v___x_2600_;
}
else
{
lean_object* v_val_2601_; uint8_t v___x_2602_; 
v_val_2601_ = lean_ctor_get(v_fst_2599_, 0);
lean_inc(v_val_2601_);
lean_dec_ref_known(v_fst_2599_, 1);
v___x_2602_ = lean_unbox(v_val_2601_);
lean_dec(v_val_2601_);
return v___x_2602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___boxed(lean_object* v_t_2609_, lean_object* v_p_2610_){
_start:
{
uint8_t v_res_2611_; lean_object* v_r_2612_; 
v_res_2611_ = l_Std_DTreeMap_Raw_all___redArg(v_t_2609_, v_p_2610_);
v_r_2612_ = lean_box(v_res_2611_);
return v_r_2612_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_all(lean_object* v_00_u03b1_2613_, lean_object* v_00_u03b2_2614_, lean_object* v_cmp_2615_, lean_object* v_t_2616_, lean_object* v_p_2617_){
_start:
{
lean_object* v___y_2619_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___f_2627_; lean_object* v___x_2628_; lean_object* v_a_2629_; 
v___x_2624_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2625_ = lean_box(0);
v___x_2626_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2627_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2627_, 0, v_p_2617_);
lean_closure_set(v___f_2627_, 1, v___x_2625_);
lean_closure_set(v___f_2627_, 2, v___x_2626_);
v___x_2628_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2624_, v___f_2627_, v___x_2626_, v_t_2616_);
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___y_2619_ = v_a_2629_;
goto v___jp_2618_;
v___jp_2618_:
{
lean_object* v_fst_2620_; 
v_fst_2620_ = lean_ctor_get(v___y_2619_, 0);
lean_inc(v_fst_2620_);
lean_dec_ref(v___y_2619_);
if (lean_obj_tag(v_fst_2620_) == 0)
{
uint8_t v___x_2621_; 
v___x_2621_ = 1;
return v___x_2621_;
}
else
{
lean_object* v_val_2622_; uint8_t v___x_2623_; 
v_val_2622_ = lean_ctor_get(v_fst_2620_, 0);
lean_inc(v_val_2622_);
lean_dec_ref_known(v_fst_2620_, 1);
v___x_2623_ = lean_unbox(v_val_2622_);
lean_dec(v_val_2622_);
return v___x_2623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___boxed(lean_object* v_00_u03b1_2630_, lean_object* v_00_u03b2_2631_, lean_object* v_cmp_2632_, lean_object* v_t_2633_, lean_object* v_p_2634_){
_start:
{
uint8_t v_res_2635_; lean_object* v_r_2636_; 
v_res_2635_ = l_Std_DTreeMap_Raw_all(v_00_u03b1_2630_, v_00_u03b2_2631_, v_cmp_2632_, v_t_2633_, v_p_2634_);
lean_dec_ref(v_cmp_2632_);
v_r_2636_ = lean_box(v_res_2635_);
return v_r_2636_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg___lam__0(lean_object* v_x1_2637_, lean_object* v_x2_2638_, lean_object* v_x3_2639_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2640_, 0, v_x1_2637_);
lean_ctor_set(v___x_2640_, 1, v_x3_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_x1_2641_, lean_object* v_x2_2642_, lean_object* v_x3_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Std_DTreeMap_Raw_keys___redArg___lam__0(v_x1_2641_, v_x2_2642_, v_x3_2643_);
lean_dec(v_x2_2642_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg(lean_object* v_t_2646_){
_start:
{
lean_object* v___f_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___f_2647_ = ((lean_object*)(l_Std_DTreeMap_Raw_keys___redArg___closed__0));
v___x_2648_ = lean_box(0);
v___x_2649_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2650_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2649_, v___f_2647_, v___x_2648_, v_t_2646_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys(lean_object* v_00_u03b1_2651_, lean_object* v_00_u03b2_2652_, lean_object* v_cmp_2653_, lean_object* v_t_2654_){
_start:
{
lean_object* v___f_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___f_2655_ = ((lean_object*)(l_Std_DTreeMap_Raw_keys___redArg___closed__0));
v___x_2656_ = lean_box(0);
v___x_2657_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2658_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2657_, v___f_2655_, v___x_2656_, v_t_2654_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___boxed(lean_object* v_00_u03b1_2659_, lean_object* v_00_u03b2_2660_, lean_object* v_cmp_2661_, lean_object* v_t_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Std_DTreeMap_Raw_keys(v_00_u03b1_2659_, v_00_u03b2_2660_, v_cmp_2661_, v_t_2662_);
lean_dec_ref(v_cmp_2661_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___lam__0(lean_object* v_l_2664_, lean_object* v_k_2665_, lean_object* v_x_2666_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = lean_array_push(v_l_2664_, v_k_2665_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_l_2668_, lean_object* v_k_2669_, lean_object* v_x_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Std_DTreeMap_Raw_keysArray___redArg___lam__0(v_l_2668_, v_k_2669_, v_x_2670_);
lean_dec(v_x_2670_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg(lean_object* v_t_2673_){
_start:
{
lean_object* v___f_2674_; lean_object* v___y_2676_; 
v___f_2674_ = ((lean_object*)(l_Std_DTreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2673_) == 0)
{
lean_object* v_size_2679_; 
v_size_2679_ = lean_ctor_get(v_t_2673_, 0);
lean_inc(v_size_2679_);
v___y_2676_ = v_size_2679_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2680_; 
v___x_2680_ = lean_unsigned_to_nat(0u);
v___y_2676_ = v___x_2680_;
goto v___jp_2675_;
}
v___jp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = lean_mk_empty_array_with_capacity(v___y_2676_);
lean_dec(v___y_2676_);
v___x_2678_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2674_, v___x_2677_, v_t_2673_);
return v___x_2678_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray(lean_object* v_00_u03b1_2681_, lean_object* v_00_u03b2_2682_, lean_object* v_cmp_2683_, lean_object* v_t_2684_){
_start:
{
lean_object* v___f_2685_; lean_object* v___y_2687_; 
v___f_2685_ = ((lean_object*)(l_Std_DTreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2684_) == 0)
{
lean_object* v_size_2690_; 
v_size_2690_ = lean_ctor_get(v_t_2684_, 0);
lean_inc(v_size_2690_);
v___y_2687_ = v_size_2690_;
goto v___jp_2686_;
}
else
{
lean_object* v___x_2691_; 
v___x_2691_ = lean_unsigned_to_nat(0u);
v___y_2687_ = v___x_2691_;
goto v___jp_2686_;
}
v___jp_2686_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_mk_empty_array_with_capacity(v___y_2687_);
lean_dec(v___y_2687_);
v___x_2689_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2685_, v___x_2688_, v_t_2684_);
return v___x_2689_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___boxed(lean_object* v_00_u03b1_2692_, lean_object* v_00_u03b2_2693_, lean_object* v_cmp_2694_, lean_object* v_t_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Std_DTreeMap_Raw_keysArray(v_00_u03b1_2692_, v_00_u03b2_2693_, v_cmp_2694_, v_t_2695_);
lean_dec_ref(v_cmp_2694_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg___lam__0(lean_object* v_x1_2697_, lean_object* v_x2_2698_, lean_object* v_x3_2699_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2700_, 0, v_x2_2698_);
lean_ctor_set(v___x_2700_, 1, v_x3_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg___lam__0___boxed(lean_object* v_x1_2701_, lean_object* v_x2_2702_, lean_object* v_x3_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Std_DTreeMap_Raw_values___redArg___lam__0(v_x1_2701_, v_x2_2702_, v_x3_2703_);
lean_dec(v_x1_2701_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg(lean_object* v_t_2706_){
_start:
{
lean_object* v___f_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___f_2707_ = ((lean_object*)(l_Std_DTreeMap_Raw_values___redArg___closed__0));
v___x_2708_ = lean_box(0);
v___x_2709_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2710_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2709_, v___f_2707_, v___x_2708_, v_t_2706_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values(lean_object* v_00_u03b1_2711_, lean_object* v_cmp_2712_, lean_object* v_00_u03b2_2713_, lean_object* v_t_2714_){
_start:
{
lean_object* v___f_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___f_2715_ = ((lean_object*)(l_Std_DTreeMap_Raw_values___redArg___closed__0));
v___x_2716_ = lean_box(0);
v___x_2717_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2718_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2717_, v___f_2715_, v___x_2716_, v_t_2714_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___boxed(lean_object* v_00_u03b1_2719_, lean_object* v_cmp_2720_, lean_object* v_00_u03b2_2721_, lean_object* v_t_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Std_DTreeMap_Raw_values(v_00_u03b1_2719_, v_cmp_2720_, v_00_u03b2_2721_, v_t_2722_);
lean_dec_ref(v_cmp_2720_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0(lean_object* v_l_2724_, lean_object* v_x_2725_, lean_object* v_v_2726_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_array_push(v_l_2724_, v_v_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2728_, lean_object* v_x_2729_, lean_object* v_v_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0(v_l_2728_, v_x_2729_, v_v_2730_);
lean_dec(v_x_2729_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg(lean_object* v_t_2733_){
_start:
{
lean_object* v___f_2734_; lean_object* v___y_2736_; 
v___f_2734_ = ((lean_object*)(l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2733_) == 0)
{
lean_object* v_size_2739_; 
v_size_2739_ = lean_ctor_get(v_t_2733_, 0);
lean_inc(v_size_2739_);
v___y_2736_ = v_size_2739_;
goto v___jp_2735_;
}
else
{
lean_object* v___x_2740_; 
v___x_2740_ = lean_unsigned_to_nat(0u);
v___y_2736_ = v___x_2740_;
goto v___jp_2735_;
}
v___jp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_mk_empty_array_with_capacity(v___y_2736_);
lean_dec(v___y_2736_);
v___x_2738_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2734_, v___x_2737_, v_t_2733_);
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray(lean_object* v_00_u03b1_2741_, lean_object* v_cmp_2742_, lean_object* v_00_u03b2_2743_, lean_object* v_t_2744_){
_start:
{
lean_object* v___f_2745_; lean_object* v___y_2747_; 
v___f_2745_ = ((lean_object*)(l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2744_) == 0)
{
lean_object* v_size_2750_; 
v_size_2750_ = lean_ctor_get(v_t_2744_, 0);
lean_inc(v_size_2750_);
v___y_2747_ = v_size_2750_;
goto v___jp_2746_;
}
else
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_unsigned_to_nat(0u);
v___y_2747_ = v___x_2751_;
goto v___jp_2746_;
}
v___jp_2746_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = lean_mk_empty_array_with_capacity(v___y_2747_);
lean_dec(v___y_2747_);
v___x_2749_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2745_, v___x_2748_, v_t_2744_);
return v___x_2749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___boxed(lean_object* v_00_u03b1_2752_, lean_object* v_cmp_2753_, lean_object* v_00_u03b2_2754_, lean_object* v_t_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Std_DTreeMap_Raw_valuesArray(v_00_u03b1_2752_, v_cmp_2753_, v_00_u03b2_2754_, v_t_2755_);
lean_dec_ref(v_cmp_2753_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___redArg___lam__0(lean_object* v_x1_2757_, lean_object* v_x2_2758_, lean_object* v_x3_2759_){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v_x1_2757_);
lean_ctor_set(v___x_2760_, 1, v_x2_2758_);
v___x_2761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
lean_ctor_set(v___x_2761_, 1, v_x3_2759_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___redArg(lean_object* v_t_2763_){
_start:
{
lean_object* v___f_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___f_2764_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_2765_ = lean_box(0);
v___x_2766_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2767_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2766_, v___f_2764_, v___x_2765_, v_t_2763_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList(lean_object* v_00_u03b1_2768_, lean_object* v_00_u03b2_2769_, lean_object* v_cmp_2770_, lean_object* v_t_2771_){
_start:
{
lean_object* v___f_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___f_2772_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_2773_ = lean_box(0);
v___x_2774_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2775_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2774_, v___f_2772_, v___x_2773_, v_t_2771_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___boxed(lean_object* v_00_u03b1_2776_, lean_object* v_00_u03b2_2777_, lean_object* v_cmp_2778_, lean_object* v_t_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Std_DTreeMap_Raw_toList(v_00_u03b1_2776_, v_00_u03b2_2777_, v_cmp_2778_, v_t_2779_);
lean_dec_ref(v_cmp_2778_);
return v_res_2780_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg___lam__0(lean_object* v_cmp_2782_, lean_object* v_a_2783_, lean_object* v_x_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_fst_2786_; lean_object* v_snd_2787_; lean_object* v_r_2788_; lean_object* v___x_2789_; 
v_fst_2786_ = lean_ctor_get(v_a_2783_, 0);
lean_inc(v_fst_2786_);
v_snd_2787_ = lean_ctor_get(v_a_2783_, 1);
lean_inc(v_snd_2787_);
lean_dec_ref(v_a_2783_);
v_r_2788_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2782_, v_fst_2786_, v_snd_2787_, v___y_2785_);
v___x_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2789_, 0, v_r_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg(lean_object* v_l_2790_, lean_object* v_cmp_2791_){
_start:
{
lean_object* v___f_2792_; lean_object* v___x_2793_; lean_object* v_r_2794_; lean_object* v___x_2795_; 
v___f_2792_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2792_, 0, v_cmp_2791_);
v___x_2793_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2794_ = lean_box(1);
v___x_2795_ = l_List_forIn_x27_loop___redArg(v___x_2793_, v___f_2792_, v_l_2790_, v_r_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg___boxed(lean_object* v_l_2796_, lean_object* v_cmp_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Std_DTreeMap_Raw_ofList___redArg(v_l_2796_, v_cmp_2797_);
lean_dec(v_l_2796_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList(lean_object* v_00_u03b1_2799_, lean_object* v_00_u03b2_2800_, lean_object* v_l_2801_, lean_object* v_cmp_2802_){
_start:
{
lean_object* v___f_2803_; lean_object* v___x_2804_; lean_object* v_r_2805_; lean_object* v___x_2806_; 
v___f_2803_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2803_, 0, v_cmp_2802_);
v___x_2804_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2805_ = lean_box(1);
v___x_2806_ = l_List_forIn_x27_loop___redArg(v___x_2804_, v___f_2803_, v_l_2801_, v_r_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___boxed(lean_object* v_00_u03b1_2807_, lean_object* v_00_u03b2_2808_, lean_object* v_l_2809_, lean_object* v_cmp_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Std_DTreeMap_Raw_ofList(v_00_u03b1_2807_, v_00_u03b2_2808_, v_l_2809_, v_cmp_2810_);
lean_dec(v_l_2809_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg___lam__0(lean_object* v_l_2812_, lean_object* v_k_2813_, lean_object* v_v_2814_){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v_k_2813_);
lean_ctor_set(v___x_2815_, 1, v_v_2814_);
v___x_2816_ = lean_array_push(v_l_2812_, v___x_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg(lean_object* v_t_2818_){
_start:
{
lean_object* v___f_2819_; lean_object* v___y_2821_; 
v___f_2819_ = ((lean_object*)(l_Std_DTreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2818_) == 0)
{
lean_object* v_size_2824_; 
v_size_2824_ = lean_ctor_get(v_t_2818_, 0);
lean_inc(v_size_2824_);
v___y_2821_ = v_size_2824_;
goto v___jp_2820_;
}
else
{
lean_object* v___x_2825_; 
v___x_2825_ = lean_unsigned_to_nat(0u);
v___y_2821_ = v___x_2825_;
goto v___jp_2820_;
}
v___jp_2820_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = lean_mk_empty_array_with_capacity(v___y_2821_);
lean_dec(v___y_2821_);
v___x_2823_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2819_, v___x_2822_, v_t_2818_);
return v___x_2823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray(lean_object* v_00_u03b1_2826_, lean_object* v_00_u03b2_2827_, lean_object* v_cmp_2828_, lean_object* v_t_2829_){
_start:
{
lean_object* v___f_2830_; lean_object* v___y_2832_; 
v___f_2830_ = ((lean_object*)(l_Std_DTreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2829_) == 0)
{
lean_object* v_size_2835_; 
v_size_2835_ = lean_ctor_get(v_t_2829_, 0);
lean_inc(v_size_2835_);
v___y_2832_ = v_size_2835_;
goto v___jp_2831_;
}
else
{
lean_object* v___x_2836_; 
v___x_2836_ = lean_unsigned_to_nat(0u);
v___y_2832_ = v___x_2836_;
goto v___jp_2831_;
}
v___jp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_mk_empty_array_with_capacity(v___y_2832_);
lean_dec(v___y_2832_);
v___x_2834_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2830_, v___x_2833_, v_t_2829_);
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___boxed(lean_object* v_00_u03b1_2837_, lean_object* v_00_u03b2_2838_, lean_object* v_cmp_2839_, lean_object* v_t_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Std_DTreeMap_Raw_toArray(v_00_u03b1_2837_, v_00_u03b2_2838_, v_cmp_2839_, v_t_2840_);
lean_dec_ref(v_cmp_2839_);
return v_res_2841_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray___redArg(lean_object* v_a_2843_, lean_object* v_cmp_2844_){
_start:
{
lean_object* v___f_2845_; lean_object* v___x_2846_; lean_object* v_r_2847_; size_t v_sz_2848_; size_t v___x_2849_; lean_object* v___x_2850_; 
v___f_2845_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2845_, 0, v_cmp_2844_);
v___x_2846_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2847_ = lean_box(1);
v_sz_2848_ = lean_array_size(v_a_2843_);
v___x_2849_ = ((size_t)0ULL);
v___x_2850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2846_, v_a_2843_, v___f_2845_, v_sz_2848_, v___x_2849_, v_r_2847_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray(lean_object* v_00_u03b1_2851_, lean_object* v_00_u03b2_2852_, lean_object* v_a_2853_, lean_object* v_cmp_2854_){
_start:
{
lean_object* v___f_2855_; lean_object* v___x_2856_; lean_object* v_r_2857_; size_t v_sz_2858_; size_t v___x_2859_; lean_object* v___x_2860_; 
v___f_2855_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2855_, 0, v_cmp_2854_);
v___x_2856_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2857_ = lean_box(1);
v_sz_2858_ = lean_array_size(v_a_2853_);
v___x_2859_ = ((size_t)0ULL);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2856_, v_a_2853_, v___f_2855_, v_sz_2858_, v___x_2859_, v_r_2857_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify___redArg(lean_object* v_cmp_2861_, lean_object* v_t_2862_, lean_object* v_a_2863_, lean_object* v_f_2864_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2861_, v_a_2863_, v_f_2864_, v_t_2862_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify(lean_object* v_00_u03b1_2866_, lean_object* v_00_u03b2_2867_, lean_object* v_cmp_2868_, lean_object* v_inst_2869_, lean_object* v_t_2870_, lean_object* v_a_2871_, lean_object* v_f_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2868_, v_a_2871_, v_f_2872_, v_t_2870_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter___redArg(lean_object* v_cmp_2874_, lean_object* v_t_2875_, lean_object* v_a_2876_, lean_object* v_f_2877_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2874_, v_a_2876_, v_f_2877_, v_t_2875_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter(lean_object* v_00_u03b1_2879_, lean_object* v_00_u03b2_2880_, lean_object* v_cmp_2881_, lean_object* v_inst_2882_, lean_object* v_t_2883_, lean_object* v_a_2884_, lean_object* v_f_2885_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2881_, v_a_2884_, v_f_2885_, v_t_2883_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2887_, lean_object* v_mergeFn_2888_, lean_object* v_a_2889_, lean_object* v_x_2890_){
_start:
{
if (lean_obj_tag(v_x_2890_) == 0)
{
lean_object* v___x_2891_; 
lean_dec(v_a_2889_);
lean_dec(v_mergeFn_2888_);
v___x_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2891_, 0, v_b_u2082_2887_);
return v___x_2891_;
}
else
{
lean_object* v_val_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2900_; 
v_val_2892_ = lean_ctor_get(v_x_2890_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_x_2890_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2894_ = v_x_2890_;
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_val_2892_);
lean_dec(v_x_2890_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2896_ = lean_apply_3(v_mergeFn_2888_, v_a_2889_, v_val_2892_, v_b_u2082_2887_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2896_);
v___x_2898_ = v___x_2894_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2901_, lean_object* v_cmp_2902_, lean_object* v_t_2903_, lean_object* v_a_2904_, lean_object* v_b_u2082_2905_){
_start:
{
lean_object* v___f_2906_; lean_object* v___x_2907_; 
lean_inc(v_a_2904_);
v___f_2906_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2906_, 0, v_b_u2082_2905_);
lean_closure_set(v___f_2906_, 1, v_mergeFn_2901_);
lean_closure_set(v___f_2906_, 2, v_a_2904_);
v___x_2907_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2902_, v_a_2904_, v___f_2906_, v_t_2903_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg(lean_object* v_cmp_2908_, lean_object* v_mergeFn_2909_, lean_object* v_t_u2081_2910_, lean_object* v_t_u2082_2911_){
_start:
{
lean_object* v___f_2912_; lean_object* v___x_2913_; 
v___f_2912_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2912_, 0, v_mergeFn_2909_);
lean_closure_set(v___f_2912_, 1, v_cmp_2908_);
v___x_2913_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2912_, v_t_u2081_2910_, v_t_u2082_2911_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith(lean_object* v_00_u03b1_2914_, lean_object* v_00_u03b2_2915_, lean_object* v_cmp_2916_, lean_object* v_inst_2917_, lean_object* v_mergeFn_2918_, lean_object* v_t_u2081_2919_, lean_object* v_t_u2082_2920_){
_start:
{
lean_object* v___f_2921_; lean_object* v___x_2922_; 
v___f_2921_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2921_, 0, v_mergeFn_2918_);
lean_closure_set(v___f_2921_, 1, v_cmp_2916_);
v___x_2922_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2921_, v_t_u2081_2919_, v_t_u2082_2920_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg___lam__0(lean_object* v_x1_2923_, lean_object* v_x2_2924_, lean_object* v_x3_2925_){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2926_, 0, v_x1_2923_);
lean_ctor_set(v___x_2926_, 1, v_x2_2924_);
v___x_2927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
lean_ctor_set(v___x_2927_, 1, v_x3_2925_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg(lean_object* v_t_2929_){
_start:
{
lean_object* v___f_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___f_2930_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0));
v___x_2931_ = lean_box(0);
v___x_2932_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2933_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2932_, v___f_2930_, v___x_2931_, v_t_2929_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList(lean_object* v_00_u03b1_2934_, lean_object* v_cmp_2935_, lean_object* v_00_u03b2_2936_, lean_object* v_t_2937_){
_start:
{
lean_object* v___f_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___f_2938_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0));
v___x_2939_ = lean_box(0);
v___x_2940_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2941_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2940_, v___f_2938_, v___x_2939_, v_t_2937_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___boxed(lean_object* v_00_u03b1_2942_, lean_object* v_cmp_2943_, lean_object* v_00_u03b2_2944_, lean_object* v_t_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Std_DTreeMap_Raw_Const_toList(v_00_u03b1_2942_, v_cmp_2943_, v_00_u03b2_2944_, v_t_2945_);
lean_dec_ref(v_cmp_2943_);
return v_res_2946_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0(lean_object* v_cmp_2948_, lean_object* v_a_2949_, lean_object* v_x_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v_fst_2952_; lean_object* v_snd_2953_; lean_object* v_r_2954_; lean_object* v___x_2955_; 
v_fst_2952_ = lean_ctor_get(v_a_2949_, 0);
lean_inc(v_fst_2952_);
v_snd_2953_ = lean_ctor_get(v_a_2949_, 1);
lean_inc(v_snd_2953_);
lean_dec_ref(v_a_2949_);
v_r_2954_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2948_, v_fst_2952_, v_snd_2953_, v___y_2951_);
v___x_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2955_, 0, v_r_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg(lean_object* v_l_2956_, lean_object* v_cmp_2957_){
_start:
{
lean_object* v___f_2958_; lean_object* v___x_2959_; lean_object* v_r_2960_; lean_object* v___x_2961_; 
v___f_2958_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2958_, 0, v_cmp_2957_);
v___x_2959_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2960_ = lean_box(1);
v___x_2961_ = l_List_forIn_x27_loop___redArg(v___x_2959_, v___f_2958_, v_l_2956_, v_r_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg___boxed(lean_object* v_l_2962_, lean_object* v_cmp_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Std_DTreeMap_Raw_Const_ofList___redArg(v_l_2962_, v_cmp_2963_);
lean_dec(v_l_2962_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList(lean_object* v_00_u03b1_2965_, lean_object* v_00_u03b2_2966_, lean_object* v_l_2967_, lean_object* v_cmp_2968_){
_start:
{
lean_object* v___f_2969_; lean_object* v___x_2970_; lean_object* v_r_2971_; lean_object* v___x_2972_; 
v___f_2969_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2969_, 0, v_cmp_2968_);
v___x_2970_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2971_ = lean_box(1);
v___x_2972_ = l_List_forIn_x27_loop___redArg(v___x_2970_, v___f_2969_, v_l_2967_, v_r_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___boxed(lean_object* v_00_u03b1_2973_, lean_object* v_00_u03b2_2974_, lean_object* v_l_2975_, lean_object* v_cmp_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Std_DTreeMap_Raw_Const_ofList(v_00_u03b1_2973_, v_00_u03b2_2974_, v_l_2975_, v_cmp_2976_);
lean_dec(v_l_2975_);
return v_res_2977_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_2979_, lean_object* v_a_2980_, lean_object* v_x_2981_, lean_object* v___y_2982_){
_start:
{
uint8_t v___x_2983_; 
lean_inc(v___y_2982_);
lean_inc(v_a_2980_);
lean_inc_ref(v_cmp_2979_);
v___x_2983_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2979_, v_a_2980_, v___y_2982_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = lean_box(0);
v___x_2985_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2979_, v_a_2980_, v___x_2984_, v___y_2982_);
v___x_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
return v___x_2986_;
}
else
{
lean_object* v___x_2987_; 
lean_dec(v_a_2980_);
lean_dec_ref(v_cmp_2979_);
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___y_2982_);
return v___x_2987_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg(lean_object* v_l_2988_, lean_object* v_cmp_2989_){
_start:
{
lean_object* v___f_2990_; lean_object* v___x_2991_; lean_object* v_r_2992_; lean_object* v___x_2993_; 
v___f_2990_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2990_, 0, v_cmp_2989_);
v___x_2991_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2992_ = lean_box(1);
v___x_2993_ = l_List_forIn_x27_loop___redArg(v___x_2991_, v___f_2990_, v_l_2988_, v_r_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___boxed(lean_object* v_l_2994_, lean_object* v_cmp_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Std_DTreeMap_Raw_Const_unitOfList___redArg(v_l_2994_, v_cmp_2995_);
lean_dec(v_l_2994_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList(lean_object* v_00_u03b1_2997_, lean_object* v_l_2998_, lean_object* v_cmp_2999_){
_start:
{
lean_object* v___f_3000_; lean_object* v___x_3001_; lean_object* v_r_3002_; lean_object* v___x_3003_; 
v___f_3000_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3000_, 0, v_cmp_2999_);
v___x_3001_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3002_ = lean_box(1);
v___x_3003_ = l_List_forIn_x27_loop___redArg(v___x_3001_, v___f_3000_, v_l_2998_, v_r_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___boxed(lean_object* v_00_u03b1_3004_, lean_object* v_l_3005_, lean_object* v_cmp_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Std_DTreeMap_Raw_Const_unitOfList(v_00_u03b1_3004_, v_l_3005_, v_cmp_3006_);
lean_dec(v_l_3005_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg___lam__0(lean_object* v_l_3008_, lean_object* v_k_3009_, lean_object* v_v_3010_){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3011_, 0, v_k_3009_);
lean_ctor_set(v___x_3011_, 1, v_v_3010_);
v___x_3012_ = lean_array_push(v_l_3008_, v___x_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg(lean_object* v_t_3014_){
_start:
{
lean_object* v___f_3015_; lean_object* v___y_3017_; 
v___f_3015_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3014_) == 0)
{
lean_object* v_size_3020_; 
v_size_3020_ = lean_ctor_get(v_t_3014_, 0);
lean_inc(v_size_3020_);
v___y_3017_ = v_size_3020_;
goto v___jp_3016_;
}
else
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_unsigned_to_nat(0u);
v___y_3017_ = v___x_3021_;
goto v___jp_3016_;
}
v___jp_3016_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_mk_empty_array_with_capacity(v___y_3017_);
lean_dec(v___y_3017_);
v___x_3019_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3015_, v___x_3018_, v_t_3014_);
return v___x_3019_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray(lean_object* v_00_u03b1_3022_, lean_object* v_cmp_3023_, lean_object* v_00_u03b2_3024_, lean_object* v_t_3025_){
_start:
{
lean_object* v___f_3026_; lean_object* v___y_3028_; 
v___f_3026_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3025_) == 0)
{
lean_object* v_size_3031_; 
v_size_3031_ = lean_ctor_get(v_t_3025_, 0);
lean_inc(v_size_3031_);
v___y_3028_ = v_size_3031_;
goto v___jp_3027_;
}
else
{
lean_object* v___x_3032_; 
v___x_3032_ = lean_unsigned_to_nat(0u);
v___y_3028_ = v___x_3032_;
goto v___jp_3027_;
}
v___jp_3027_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = lean_mk_empty_array_with_capacity(v___y_3028_);
lean_dec(v___y_3028_);
v___x_3030_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3026_, v___x_3029_, v_t_3025_);
return v___x_3030_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___boxed(lean_object* v_00_u03b1_3033_, lean_object* v_cmp_3034_, lean_object* v_00_u03b2_3035_, lean_object* v_t_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Std_DTreeMap_Raw_Const_toArray(v_00_u03b1_3033_, v_cmp_3034_, v_00_u03b2_3035_, v_t_3036_);
lean_dec_ref(v_cmp_3034_);
return v_res_3037_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray___redArg(lean_object* v_a_3039_, lean_object* v_cmp_3040_){
_start:
{
lean_object* v___f_3041_; lean_object* v___x_3042_; lean_object* v_r_3043_; size_t v_sz_3044_; size_t v___x_3045_; lean_object* v___x_3046_; 
v___f_3041_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3041_, 0, v_cmp_3040_);
v___x_3042_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3043_ = lean_box(1);
v_sz_3044_ = lean_array_size(v_a_3039_);
v___x_3045_ = ((size_t)0ULL);
v___x_3046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3042_, v_a_3039_, v___f_3041_, v_sz_3044_, v___x_3045_, v_r_3043_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray(lean_object* v_00_u03b1_3047_, lean_object* v_00_u03b2_3048_, lean_object* v_a_3049_, lean_object* v_cmp_3050_){
_start:
{
lean_object* v___f_3051_; lean_object* v___x_3052_; lean_object* v_r_3053_; size_t v_sz_3054_; size_t v___x_3055_; lean_object* v___x_3056_; 
v___f_3051_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3051_, 0, v_cmp_3050_);
v___x_3052_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3053_ = lean_box(1);
v_sz_3054_ = lean_array_size(v_a_3049_);
v___x_3055_ = ((size_t)0ULL);
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3052_, v_a_3049_, v___f_3051_, v_sz_3054_, v___x_3055_, v_r_3053_);
return v___x_3056_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__26, &l_Std_DTreeMap_Raw___auto__1___closed__26_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__26);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray___redArg(lean_object* v_a_3058_, lean_object* v_cmp_3059_){
_start:
{
lean_object* v___f_3060_; lean_object* v___x_3061_; lean_object* v_r_3062_; size_t v_sz_3063_; size_t v___x_3064_; lean_object* v___x_3065_; 
v___f_3060_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3060_, 0, v_cmp_3059_);
v___x_3061_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3062_ = lean_box(1);
v_sz_3063_ = lean_array_size(v_a_3058_);
v___x_3064_ = ((size_t)0ULL);
v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3061_, v_a_3058_, v___f_3060_, v_sz_3063_, v___x_3064_, v_r_3062_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray(lean_object* v_00_u03b1_3066_, lean_object* v_a_3067_, lean_object* v_cmp_3068_){
_start:
{
lean_object* v___f_3069_; lean_object* v___x_3070_; lean_object* v_r_3071_; size_t v_sz_3072_; size_t v___x_3073_; lean_object* v___x_3074_; 
v___f_3069_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3069_, 0, v_cmp_3068_);
v___x_3070_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3071_ = lean_box(1);
v_sz_3072_ = lean_array_size(v_a_3067_);
v___x_3073_ = ((size_t)0ULL);
v___x_3074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3070_, v_a_3067_, v___f_3069_, v_sz_3072_, v___x_3073_, v_r_3071_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify___redArg(lean_object* v_cmp_3075_, lean_object* v_t_3076_, lean_object* v_a_3077_, lean_object* v_f_3078_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3075_, v_a_3077_, v_f_3078_, v_t_3076_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify(lean_object* v_00_u03b1_3080_, lean_object* v_cmp_3081_, lean_object* v_00_u03b2_3082_, lean_object* v_t_3083_, lean_object* v_a_3084_, lean_object* v_f_3085_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3081_, v_a_3084_, v_f_3085_, v_t_3083_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter___redArg(lean_object* v_cmp_3087_, lean_object* v_t_3088_, lean_object* v_a_3089_, lean_object* v_f_3090_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3087_, v_a_3089_, v_f_3090_, v_t_3088_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter(lean_object* v_00_u03b1_3092_, lean_object* v_cmp_3093_, lean_object* v_00_u03b2_3094_, lean_object* v_t_3095_, lean_object* v_a_3096_, lean_object* v_f_3097_){
_start:
{
lean_object* v___x_3098_; 
v___x_3098_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3093_, v_a_3096_, v_f_3097_, v_t_3095_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3099_, lean_object* v_cmp_3100_, lean_object* v_t_3101_, lean_object* v_a_3102_, lean_object* v_b_u2082_3103_){
_start:
{
lean_object* v___f_3104_; lean_object* v___x_3105_; 
lean_inc(v_a_3102_);
v___f_3104_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3104_, 0, v_b_u2082_3103_);
lean_closure_set(v___f_3104_, 1, v_mergeFn_3099_);
lean_closure_set(v___f_3104_, 2, v_a_3102_);
v___x_3105_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3100_, v_a_3102_, v___f_3104_, v_t_3101_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg(lean_object* v_cmp_3106_, lean_object* v_mergeFn_3107_, lean_object* v_t_u2081_3108_, lean_object* v_t_u2082_3109_){
_start:
{
lean_object* v___f_3110_; lean_object* v___x_3111_; 
v___f_3110_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3110_, 0, v_mergeFn_3107_);
lean_closure_set(v___f_3110_, 1, v_cmp_3106_);
v___x_3111_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3110_, v_t_u2081_3108_, v_t_u2082_3109_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith(lean_object* v_00_u03b1_3112_, lean_object* v_cmp_3113_, lean_object* v_00_u03b2_3114_, lean_object* v_mergeFn_3115_, lean_object* v_t_u2081_3116_, lean_object* v_t_u2082_3117_){
_start:
{
lean_object* v___f_3118_; lean_object* v___x_3119_; 
v___f_3118_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3118_, 0, v_mergeFn_3115_);
lean_closure_set(v___f_3118_, 1, v_cmp_3113_);
v___x_3119_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3118_, v_t_u2081_3116_, v_t_u2082_3117_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_3120_, lean_object* v_x_3121_, lean_object* v_____s_3122_){
_start:
{
lean_object* v_fst_3123_; lean_object* v_snd_3124_; lean_object* v_r_3125_; lean_object* v___x_3126_; 
v_fst_3123_ = lean_ctor_get(v_x_3121_, 0);
lean_inc(v_fst_3123_);
v_snd_3124_ = lean_ctor_get(v_x_3121_, 1);
lean_inc(v_snd_3124_);
lean_dec_ref(v_x_3121_);
v_r_3125_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_3120_, v_fst_3123_, v_snd_3124_, v_____s_3122_);
v___x_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3126_, 0, v_r_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg(lean_object* v_cmp_3127_, lean_object* v_inst_3128_, lean_object* v_t_3129_, lean_object* v_l_3130_){
_start:
{
lean_object* v___f_3131_; lean_object* v___x_3132_; 
v___f_3131_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3131_, 0, v_cmp_3127_);
v___x_3132_ = lean_apply_4(v_inst_3128_, lean_box(0), v_l_3130_, v_t_3129_, v___f_3131_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany(lean_object* v_00_u03b1_3133_, lean_object* v_00_u03b2_3134_, lean_object* v_cmp_3135_, lean_object* v_00_u03c1_3136_, lean_object* v_inst_3137_, lean_object* v_t_3138_, lean_object* v_l_3139_){
_start:
{
lean_object* v___f_3140_; lean_object* v___x_3141_; 
v___f_3140_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3140_, 0, v_cmp_3135_);
v___x_3141_ = lean_apply_4(v_inst_3137_, lean_box(0), v_l_3139_, v_t_3138_, v___f_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3142_){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = lean_box(1);
v___x_3144_ = lean_panic_fn_borrowed(v___x_3143_, v_msg_3142_);
return v___x_3144_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3148_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__2));
v___x_3149_ = lean_unsigned_to_nat(35u);
v___x_3150_ = lean_unsigned_to_nat(182u);
v___x_3151_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__1));
v___x_3152_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0));
v___x_3153_ = l_mkPanicMessageWithDecl(v___x_3152_, v___x_3151_, v___x_3150_, v___x_3149_, v___x_3148_);
return v___x_3153_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3154_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__2));
v___x_3155_ = lean_unsigned_to_nat(21u);
v___x_3156_ = lean_unsigned_to_nat(183u);
v___x_3157_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__1));
v___x_3158_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0));
v___x_3159_ = l_mkPanicMessageWithDecl(v___x_3158_, v___x_3157_, v___x_3156_, v___x_3155_, v___x_3154_);
return v___x_3159_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3162_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__6));
v___x_3163_ = lean_unsigned_to_nat(35u);
v___x_3164_ = lean_unsigned_to_nat(276u);
v___x_3165_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__5));
v___x_3166_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0));
v___x_3167_ = l_mkPanicMessageWithDecl(v___x_3166_, v___x_3165_, v___x_3164_, v___x_3163_, v___x_3162_);
return v___x_3167_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3168_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__6));
v___x_3169_ = lean_unsigned_to_nat(21u);
v___x_3170_ = lean_unsigned_to_nat(277u);
v___x_3171_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__5));
v___x_3172_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0));
v___x_3173_ = l_mkPanicMessageWithDecl(v___x_3172_, v___x_3171_, v___x_3170_, v___x_3169_, v___x_3168_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(lean_object* v_cmp_3174_, lean_object* v_k_3175_, lean_object* v_v_3176_, lean_object* v_t_3177_){
_start:
{
if (lean_obj_tag(v_t_3177_) == 0)
{
lean_object* v_size_3178_; lean_object* v_k_3179_; lean_object* v_v_3180_; lean_object* v_l_3181_; lean_object* v_r_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3539_; 
v_size_3178_ = lean_ctor_get(v_t_3177_, 0);
v_k_3179_ = lean_ctor_get(v_t_3177_, 1);
v_v_3180_ = lean_ctor_get(v_t_3177_, 2);
v_l_3181_ = lean_ctor_get(v_t_3177_, 3);
v_r_3182_ = lean_ctor_get(v_t_3177_, 4);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_t_3177_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3184_ = v_t_3177_;
v_isShared_3185_ = v_isSharedCheck_3539_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_r_3182_);
lean_inc(v_l_3181_);
lean_inc(v_v_3180_);
lean_inc(v_k_3179_);
lean_inc(v_size_3178_);
lean_dec(v_t_3177_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3539_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3186_; uint8_t v___x_3187_; 
lean_inc_ref(v_cmp_3174_);
lean_inc(v_k_3179_);
lean_inc(v_k_3175_);
v___x_3186_ = lean_apply_2(v_cmp_3174_, v_k_3175_, v_k_3179_);
v___x_3187_ = lean_unbox(v___x_3186_);
switch(v___x_3187_)
{
case 0:
{
lean_object* v___x_3188_; 
lean_dec(v_size_3178_);
v___x_3188_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3174_, v_k_3175_, v_v_3176_, v_l_3181_);
if (lean_obj_tag(v_r_3182_) == 0)
{
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_size_3189_; lean_object* v_size_3190_; lean_object* v_k_3191_; lean_object* v_v_3192_; lean_object* v_l_3193_; lean_object* v_r_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; uint8_t v___x_3197_; 
v_size_3189_ = lean_ctor_get(v_r_3182_, 0);
v_size_3190_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_size_3190_);
v_k_3191_ = lean_ctor_get(v___x_3188_, 1);
lean_inc(v_k_3191_);
v_v_3192_ = lean_ctor_get(v___x_3188_, 2);
lean_inc(v_v_3192_);
v_l_3193_ = lean_ctor_get(v___x_3188_, 3);
lean_inc(v_l_3193_);
v_r_3194_ = lean_ctor_get(v___x_3188_, 4);
lean_inc(v_r_3194_);
v___x_3195_ = lean_unsigned_to_nat(3u);
v___x_3196_ = lean_nat_mul(v___x_3195_, v_size_3189_);
v___x_3197_ = lean_nat_dec_lt(v___x_3196_, v_size_3190_);
lean_dec(v___x_3196_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
lean_dec(v_r_3194_);
lean_dec(v_l_3193_);
lean_dec(v_v_3192_);
lean_dec(v_k_3191_);
v___x_3198_ = lean_unsigned_to_nat(1u);
v___x_3199_ = lean_nat_add(v___x_3198_, v_size_3190_);
lean_dec(v_size_3190_);
v___x_3200_ = lean_nat_add(v___x_3199_, v_size_3189_);
lean_dec(v___x_3199_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 3, v___x_3188_);
lean_ctor_set(v___x_3184_, 0, v___x_3200_);
v___x_3202_ = v___x_3184_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3203_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3203_, 3, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3203_, 4, v_r_3182_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
else
{
lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3275_; 
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3275_ == 0)
{
lean_object* v_unused_3276_; lean_object* v_unused_3277_; lean_object* v_unused_3278_; lean_object* v_unused_3279_; lean_object* v_unused_3280_; 
v_unused_3276_ = lean_ctor_get(v___x_3188_, 4);
lean_dec(v_unused_3276_);
v_unused_3277_ = lean_ctor_get(v___x_3188_, 3);
lean_dec(v_unused_3277_);
v_unused_3278_ = lean_ctor_get(v___x_3188_, 2);
lean_dec(v_unused_3278_);
v_unused_3279_ = lean_ctor_get(v___x_3188_, 1);
lean_dec(v_unused_3279_);
v_unused_3280_ = lean_ctor_get(v___x_3188_, 0);
lean_dec(v_unused_3280_);
v___x_3205_ = v___x_3188_;
v_isShared_3206_ = v_isSharedCheck_3275_;
goto v_resetjp_3204_;
}
else
{
lean_dec(v___x_3188_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3275_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
if (lean_obj_tag(v_l_3193_) == 0)
{
if (lean_obj_tag(v_r_3194_) == 0)
{
lean_object* v_size_3207_; lean_object* v_size_3208_; lean_object* v_k_3209_; lean_object* v_v_3210_; lean_object* v_l_3211_; lean_object* v_r_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; 
v_size_3207_ = lean_ctor_get(v_l_3193_, 0);
v_size_3208_ = lean_ctor_get(v_r_3194_, 0);
v_k_3209_ = lean_ctor_get(v_r_3194_, 1);
v_v_3210_ = lean_ctor_get(v_r_3194_, 2);
v_l_3211_ = lean_ctor_get(v_r_3194_, 3);
v_r_3212_ = lean_ctor_get(v_r_3194_, 4);
v___x_3213_ = lean_unsigned_to_nat(2u);
v___x_3214_ = lean_nat_mul(v___x_3213_, v_size_3207_);
v___x_3215_ = lean_nat_dec_lt(v_size_3208_, v___x_3214_);
lean_dec(v___x_3214_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3245_; 
lean_inc(v_r_3212_);
lean_inc(v_l_3211_);
lean_inc(v_v_3210_);
lean_inc(v_k_3209_);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_r_3194_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; lean_object* v_unused_3247_; lean_object* v_unused_3248_; lean_object* v_unused_3249_; lean_object* v_unused_3250_; 
v_unused_3246_ = lean_ctor_get(v_r_3194_, 4);
lean_dec(v_unused_3246_);
v_unused_3247_ = lean_ctor_get(v_r_3194_, 3);
lean_dec(v_unused_3247_);
v_unused_3248_ = lean_ctor_get(v_r_3194_, 2);
lean_dec(v_unused_3248_);
v_unused_3249_ = lean_ctor_get(v_r_3194_, 1);
lean_dec(v_unused_3249_);
v_unused_3250_ = lean_ctor_get(v_r_3194_, 0);
lean_dec(v_unused_3250_);
v___x_3217_ = v_r_3194_;
v_isShared_3218_ = v_isSharedCheck_3245_;
goto v_resetjp_3216_;
}
else
{
lean_dec(v_r_3194_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3245_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___x_3233_; lean_object* v___y_3235_; 
v___x_3219_ = lean_unsigned_to_nat(1u);
v___x_3220_ = lean_nat_add(v___x_3219_, v_size_3190_);
lean_dec(v_size_3190_);
v___x_3221_ = lean_nat_add(v___x_3220_, v_size_3189_);
lean_dec(v___x_3220_);
v___x_3233_ = lean_nat_add(v___x_3219_, v_size_3207_);
if (lean_obj_tag(v_l_3211_) == 0)
{
lean_object* v_size_3243_; 
v_size_3243_ = lean_ctor_get(v_l_3211_, 0);
lean_inc(v_size_3243_);
v___y_3235_ = v_size_3243_;
goto v___jp_3234_;
}
else
{
lean_object* v___x_3244_; 
v___x_3244_ = lean_unsigned_to_nat(0u);
v___y_3235_ = v___x_3244_;
goto v___jp_3234_;
}
v___jp_3222_:
{
lean_object* v___x_3226_; lean_object* v___x_3228_; 
v___x_3226_ = lean_nat_add(v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec(v___y_3224_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 4, v_r_3182_);
lean_ctor_set(v___x_3217_, 3, v_r_3212_);
lean_ctor_set(v___x_3217_, 2, v_v_3180_);
lean_ctor_set(v___x_3217_, 1, v_k_3179_);
lean_ctor_set(v___x_3217_, 0, v___x_3226_);
v___x_3228_ = v___x_3217_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3226_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3232_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3232_, 3, v_r_3212_);
lean_ctor_set(v_reuseFailAlloc_3232_, 4, v_r_3182_);
v___x_3228_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3230_; 
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 4, v___x_3228_);
lean_ctor_set(v___x_3205_, 3, v___y_3223_);
lean_ctor_set(v___x_3205_, 2, v_v_3210_);
lean_ctor_set(v___x_3205_, 1, v_k_3209_);
lean_ctor_set(v___x_3205_, 0, v___x_3221_);
v___x_3230_ = v___x_3205_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_k_3209_);
lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_v_3210_);
lean_ctor_set(v_reuseFailAlloc_3231_, 3, v___y_3223_);
lean_ctor_set(v_reuseFailAlloc_3231_, 4, v___x_3228_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
v___jp_3234_:
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3236_ = lean_nat_add(v___x_3233_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec(v___x_3233_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v_l_3211_);
lean_ctor_set(v___x_3184_, 3, v_l_3193_);
lean_ctor_set(v___x_3184_, 2, v_v_3192_);
lean_ctor_set(v___x_3184_, 1, v_k_3191_);
lean_ctor_set(v___x_3184_, 0, v___x_3236_);
v___x_3238_ = v___x_3184_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v_k_3191_);
lean_ctor_set(v_reuseFailAlloc_3242_, 2, v_v_3192_);
lean_ctor_set(v_reuseFailAlloc_3242_, 3, v_l_3193_);
lean_ctor_set(v_reuseFailAlloc_3242_, 4, v_l_3211_);
v___x_3238_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_nat_add(v___x_3219_, v_size_3189_);
if (lean_obj_tag(v_r_3212_) == 0)
{
lean_object* v_size_3240_; 
v_size_3240_ = lean_ctor_get(v_r_3212_, 0);
lean_inc(v_size_3240_);
v___y_3223_ = v___x_3238_;
v___y_3224_ = v___x_3239_;
v___y_3225_ = v_size_3240_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_unsigned_to_nat(0u);
v___y_3223_ = v___x_3238_;
v___y_3224_ = v___x_3239_;
v___y_3225_ = v___x_3241_;
goto v___jp_3222_;
}
}
}
}
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
lean_del_object(v___x_3184_);
v___x_3251_ = lean_unsigned_to_nat(1u);
v___x_3252_ = lean_nat_add(v___x_3251_, v_size_3190_);
lean_dec(v_size_3190_);
v___x_3253_ = lean_nat_add(v___x_3252_, v_size_3189_);
lean_dec(v___x_3252_);
v___x_3254_ = lean_nat_add(v___x_3251_, v_size_3189_);
v___x_3255_ = lean_nat_add(v___x_3254_, v_size_3208_);
lean_dec(v___x_3254_);
lean_inc_ref(v_r_3182_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 4, v_r_3182_);
lean_ctor_set(v___x_3205_, 3, v_r_3194_);
lean_ctor_set(v___x_3205_, 2, v_v_3180_);
lean_ctor_set(v___x_3205_, 1, v_k_3179_);
lean_ctor_set(v___x_3205_, 0, v___x_3255_);
v___x_3257_ = v___x_3205_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3270_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3270_, 3, v_r_3194_);
lean_ctor_set(v_reuseFailAlloc_3270_, 4, v_r_3182_);
v___x_3257_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
v_isSharedCheck_3264_ = !lean_is_exclusive(v_r_3182_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; lean_object* v_unused_3266_; lean_object* v_unused_3267_; lean_object* v_unused_3268_; lean_object* v_unused_3269_; 
v_unused_3265_ = lean_ctor_get(v_r_3182_, 4);
lean_dec(v_unused_3265_);
v_unused_3266_ = lean_ctor_get(v_r_3182_, 3);
lean_dec(v_unused_3266_);
v_unused_3267_ = lean_ctor_get(v_r_3182_, 2);
lean_dec(v_unused_3267_);
v_unused_3268_ = lean_ctor_get(v_r_3182_, 1);
lean_dec(v_unused_3268_);
v_unused_3269_ = lean_ctor_get(v_r_3182_, 0);
lean_dec(v_unused_3269_);
v___x_3259_ = v_r_3182_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_dec(v_r_3182_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 4, v___x_3257_);
lean_ctor_set(v___x_3259_, 3, v_l_3193_);
lean_ctor_set(v___x_3259_, 2, v_v_3192_);
lean_ctor_set(v___x_3259_, 1, v_k_3191_);
lean_ctor_set(v___x_3259_, 0, v___x_3253_);
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3253_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_k_3191_);
lean_ctor_set(v_reuseFailAlloc_3263_, 2, v_v_3192_);
lean_ctor_set(v_reuseFailAlloc_3263_, 3, v_l_3193_);
lean_ctor_set(v_reuseFailAlloc_3263_, 4, v___x_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_dec_ref_known(v_l_3193_, 5);
lean_del_object(v___x_3205_);
lean_dec(v_v_3192_);
lean_dec(v_k_3191_);
lean_dec(v_size_3190_);
lean_dec_ref_known(v_r_3182_, 5);
lean_del_object(v___x_3184_);
lean_dec(v_v_3180_);
lean_dec(v_k_3179_);
v___x_3271_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3);
v___x_3272_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_3271_);
return v___x_3272_;
}
}
else
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
lean_del_object(v___x_3205_);
lean_dec(v_r_3194_);
lean_dec(v_v_3192_);
lean_dec(v_k_3191_);
lean_dec(v_size_3190_);
lean_dec_ref_known(v_r_3182_, 5);
lean_del_object(v___x_3184_);
lean_dec(v_v_3180_);
lean_dec(v_k_3179_);
v___x_3273_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4);
v___x_3274_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_3273_);
return v___x_3274_;
}
}
}
}
else
{
lean_object* v_size_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3285_; 
v_size_3281_ = lean_ctor_get(v_r_3182_, 0);
v___x_3282_ = lean_unsigned_to_nat(1u);
v___x_3283_ = lean_nat_add(v___x_3282_, v_size_3281_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 3, v___x_3188_);
lean_ctor_set(v___x_3184_, 0, v___x_3283_);
v___x_3285_ = v___x_3184_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3283_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3286_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3286_, 3, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3286_, 4, v_r_3182_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
else
{
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_l_3287_; 
v_l_3287_ = lean_ctor_get(v___x_3188_, 3);
lean_inc(v_l_3287_);
if (lean_obj_tag(v_l_3287_) == 0)
{
lean_object* v_r_3288_; 
v_r_3288_ = lean_ctor_get(v___x_3188_, 4);
lean_inc(v_r_3288_);
if (lean_obj_tag(v_r_3288_) == 0)
{
lean_object* v_size_3289_; lean_object* v_k_3290_; lean_object* v_v_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3305_; 
v_size_3289_ = lean_ctor_get(v___x_3188_, 0);
v_k_3290_ = lean_ctor_get(v___x_3188_, 1);
v_v_3291_ = lean_ctor_get(v___x_3188_, 2);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3305_ == 0)
{
lean_object* v_unused_3306_; lean_object* v_unused_3307_; 
v_unused_3306_ = lean_ctor_get(v___x_3188_, 4);
lean_dec(v_unused_3306_);
v_unused_3307_ = lean_ctor_get(v___x_3188_, 3);
lean_dec(v_unused_3307_);
v___x_3293_ = v___x_3188_;
v_isShared_3294_ = v_isSharedCheck_3305_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_v_3291_);
lean_inc(v_k_3290_);
lean_inc(v_size_3289_);
lean_dec(v___x_3188_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3305_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v_size_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
v_size_3295_ = lean_ctor_get(v_r_3288_, 0);
v___x_3296_ = lean_unsigned_to_nat(1u);
v___x_3297_ = lean_nat_add(v___x_3296_, v_size_3289_);
lean_dec(v_size_3289_);
v___x_3298_ = lean_nat_add(v___x_3296_, v_size_3295_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v_r_3182_);
lean_ctor_set(v___x_3293_, 3, v_r_3288_);
lean_ctor_set(v___x_3293_, 2, v_v_3180_);
lean_ctor_set(v___x_3293_, 1, v_k_3179_);
lean_ctor_set(v___x_3293_, 0, v___x_3298_);
v___x_3300_ = v___x_3293_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3298_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_r_3288_);
lean_ctor_set(v_reuseFailAlloc_3304_, 4, v_r_3182_);
v___x_3300_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
lean_object* v___x_3302_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v___x_3300_);
lean_ctor_set(v___x_3184_, 3, v_l_3287_);
lean_ctor_set(v___x_3184_, 2, v_v_3291_);
lean_ctor_set(v___x_3184_, 1, v_k_3290_);
lean_ctor_set(v___x_3184_, 0, v___x_3297_);
v___x_3302_ = v___x_3184_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v_k_3290_);
lean_ctor_set(v_reuseFailAlloc_3303_, 2, v_v_3291_);
lean_ctor_set(v_reuseFailAlloc_3303_, 3, v_l_3287_);
lean_ctor_set(v_reuseFailAlloc_3303_, 4, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
else
{
lean_object* v_k_3308_; lean_object* v_v_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3321_; 
v_k_3308_ = lean_ctor_get(v___x_3188_, 1);
v_v_3309_ = lean_ctor_get(v___x_3188_, 2);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3321_ == 0)
{
lean_object* v_unused_3322_; lean_object* v_unused_3323_; lean_object* v_unused_3324_; 
v_unused_3322_ = lean_ctor_get(v___x_3188_, 4);
lean_dec(v_unused_3322_);
v_unused_3323_ = lean_ctor_get(v___x_3188_, 3);
lean_dec(v_unused_3323_);
v_unused_3324_ = lean_ctor_get(v___x_3188_, 0);
lean_dec(v_unused_3324_);
v___x_3311_ = v___x_3188_;
v_isShared_3312_ = v_isSharedCheck_3321_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_v_3309_);
lean_inc(v_k_3308_);
lean_dec(v___x_3188_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3321_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3316_; 
v___x_3313_ = lean_unsigned_to_nat(3u);
v___x_3314_ = lean_unsigned_to_nat(1u);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 3, v_r_3288_);
lean_ctor_set(v___x_3311_, 2, v_v_3180_);
lean_ctor_set(v___x_3311_, 1, v_k_3179_);
lean_ctor_set(v___x_3311_, 0, v___x_3314_);
v___x_3316_ = v___x_3311_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3314_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3320_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3320_, 3, v_r_3288_);
lean_ctor_set(v_reuseFailAlloc_3320_, 4, v_r_3288_);
v___x_3316_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3318_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v___x_3316_);
lean_ctor_set(v___x_3184_, 3, v_l_3287_);
lean_ctor_set(v___x_3184_, 2, v_v_3309_);
lean_ctor_set(v___x_3184_, 1, v_k_3308_);
lean_ctor_set(v___x_3184_, 0, v___x_3313_);
v___x_3318_ = v___x_3184_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_k_3308_);
lean_ctor_set(v_reuseFailAlloc_3319_, 2, v_v_3309_);
lean_ctor_set(v_reuseFailAlloc_3319_, 3, v_l_3287_);
lean_ctor_set(v_reuseFailAlloc_3319_, 4, v___x_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
else
{
lean_object* v_r_3325_; 
v_r_3325_ = lean_ctor_get(v___x_3188_, 4);
lean_inc(v_r_3325_);
if (lean_obj_tag(v_r_3325_) == 0)
{
lean_object* v_k_3326_; lean_object* v_v_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3351_; 
v_k_3326_ = lean_ctor_get(v___x_3188_, 1);
v_v_3327_ = lean_ctor_get(v___x_3188_, 2);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3351_ == 0)
{
lean_object* v_unused_3352_; lean_object* v_unused_3353_; lean_object* v_unused_3354_; 
v_unused_3352_ = lean_ctor_get(v___x_3188_, 4);
lean_dec(v_unused_3352_);
v_unused_3353_ = lean_ctor_get(v___x_3188_, 3);
lean_dec(v_unused_3353_);
v_unused_3354_ = lean_ctor_get(v___x_3188_, 0);
lean_dec(v_unused_3354_);
v___x_3329_ = v___x_3188_;
v_isShared_3330_ = v_isSharedCheck_3351_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_v_3327_);
lean_inc(v_k_3326_);
lean_dec(v___x_3188_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3351_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v_k_3331_; lean_object* v_v_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3347_; 
v_k_3331_ = lean_ctor_get(v_r_3325_, 1);
v_v_3332_ = lean_ctor_get(v_r_3325_, 2);
v_isSharedCheck_3347_ = !lean_is_exclusive(v_r_3325_);
if (v_isSharedCheck_3347_ == 0)
{
lean_object* v_unused_3348_; lean_object* v_unused_3349_; lean_object* v_unused_3350_; 
v_unused_3348_ = lean_ctor_get(v_r_3325_, 4);
lean_dec(v_unused_3348_);
v_unused_3349_ = lean_ctor_get(v_r_3325_, 3);
lean_dec(v_unused_3349_);
v_unused_3350_ = lean_ctor_get(v_r_3325_, 0);
lean_dec(v_unused_3350_);
v___x_3334_ = v_r_3325_;
v_isShared_3335_ = v_isSharedCheck_3347_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_v_3332_);
lean_inc(v_k_3331_);
lean_dec(v_r_3325_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3347_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3336_ = lean_unsigned_to_nat(3u);
v___x_3337_ = lean_unsigned_to_nat(1u);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 4, v_l_3287_);
lean_ctor_set(v___x_3334_, 3, v_l_3287_);
lean_ctor_set(v___x_3334_, 2, v_v_3327_);
lean_ctor_set(v___x_3334_, 1, v_k_3326_);
lean_ctor_set(v___x_3334_, 0, v___x_3337_);
v___x_3339_ = v___x_3334_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3346_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3346_, 3, v_l_3287_);
lean_ctor_set(v_reuseFailAlloc_3346_, 4, v_l_3287_);
v___x_3339_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
lean_object* v___x_3341_; 
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 4, v_l_3287_);
lean_ctor_set(v___x_3329_, 2, v_v_3180_);
lean_ctor_set(v___x_3329_, 1, v_k_3179_);
lean_ctor_set(v___x_3329_, 0, v___x_3337_);
v___x_3341_ = v___x_3329_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3345_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3345_, 3, v_l_3287_);
lean_ctor_set(v_reuseFailAlloc_3345_, 4, v_l_3287_);
v___x_3341_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3343_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v___x_3341_);
lean_ctor_set(v___x_3184_, 3, v___x_3339_);
lean_ctor_set(v___x_3184_, 2, v_v_3332_);
lean_ctor_set(v___x_3184_, 1, v_k_3331_);
lean_ctor_set(v___x_3184_, 0, v___x_3336_);
v___x_3343_ = v___x_3184_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3344_, 1, v_k_3331_);
lean_ctor_set(v_reuseFailAlloc_3344_, 2, v_v_3332_);
lean_ctor_set(v_reuseFailAlloc_3344_, 3, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3344_, 4, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3357_; 
v___x_3355_ = lean_unsigned_to_nat(2u);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v_r_3325_);
lean_ctor_set(v___x_3184_, 3, v___x_3188_);
lean_ctor_set(v___x_3184_, 0, v___x_3355_);
v___x_3357_ = v___x_3184_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3355_);
lean_ctor_set(v_reuseFailAlloc_3358_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3358_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3358_, 3, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3358_, 4, v_r_3325_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3361_; 
v___x_3359_ = lean_unsigned_to_nat(1u);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v___x_3188_);
lean_ctor_set(v___x_3184_, 3, v___x_3188_);
lean_ctor_set(v___x_3184_, 0, v___x_3359_);
v___x_3361_ = v___x_3184_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3359_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3362_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3362_, 3, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3362_, 4, v___x_3188_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
case 1:
{
lean_object* v___x_3364_; 
lean_dec(v_v_3180_);
lean_dec(v_k_3179_);
lean_dec_ref(v_cmp_3174_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 2, v_v_3176_);
lean_ctor_set(v___x_3184_, 1, v_k_3175_);
v___x_3364_ = v___x_3184_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_size_3178_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v_k_3175_);
lean_ctor_set(v_reuseFailAlloc_3365_, 2, v_v_3176_);
lean_ctor_set(v_reuseFailAlloc_3365_, 3, v_l_3181_);
lean_ctor_set(v_reuseFailAlloc_3365_, 4, v_r_3182_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
default: 
{
lean_object* v___x_3366_; 
lean_dec(v_size_3178_);
v___x_3366_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3174_, v_k_3175_, v_v_3176_, v_r_3182_);
if (lean_obj_tag(v_l_3181_) == 0)
{
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_size_3367_; lean_object* v_size_3368_; lean_object* v_k_3369_; lean_object* v_v_3370_; lean_object* v_l_3371_; lean_object* v_r_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; 
v_size_3367_ = lean_ctor_get(v_l_3181_, 0);
v_size_3368_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_size_3368_);
v_k_3369_ = lean_ctor_get(v___x_3366_, 1);
lean_inc(v_k_3369_);
v_v_3370_ = lean_ctor_get(v___x_3366_, 2);
lean_inc(v_v_3370_);
v_l_3371_ = lean_ctor_get(v___x_3366_, 3);
lean_inc(v_l_3371_);
v_r_3372_ = lean_ctor_get(v___x_3366_, 4);
lean_inc(v_r_3372_);
v___x_3373_ = lean_unsigned_to_nat(3u);
v___x_3374_ = lean_nat_mul(v___x_3373_, v_size_3367_);
v___x_3375_ = lean_nat_dec_lt(v___x_3374_, v_size_3368_);
lean_dec(v___x_3374_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3380_; 
lean_dec(v_r_3372_);
lean_dec(v_l_3371_);
lean_dec(v_v_3370_);
lean_dec(v_k_3369_);
v___x_3376_ = lean_unsigned_to_nat(1u);
v___x_3377_ = lean_nat_add(v___x_3376_, v_size_3367_);
v___x_3378_ = lean_nat_add(v___x_3377_, v_size_3368_);
lean_dec(v_size_3368_);
lean_dec(v___x_3377_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v___x_3366_);
lean_ctor_set(v___x_3184_, 0, v___x_3378_);
v___x_3380_ = v___x_3184_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3381_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3381_, 3, v_l_3181_);
lean_ctor_set(v_reuseFailAlloc_3381_, 4, v___x_3366_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
else
{
lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3451_; 
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3451_ == 0)
{
lean_object* v_unused_3452_; lean_object* v_unused_3453_; lean_object* v_unused_3454_; lean_object* v_unused_3455_; lean_object* v_unused_3456_; 
v_unused_3452_ = lean_ctor_get(v___x_3366_, 4);
lean_dec(v_unused_3452_);
v_unused_3453_ = lean_ctor_get(v___x_3366_, 3);
lean_dec(v_unused_3453_);
v_unused_3454_ = lean_ctor_get(v___x_3366_, 2);
lean_dec(v_unused_3454_);
v_unused_3455_ = lean_ctor_get(v___x_3366_, 1);
lean_dec(v_unused_3455_);
v_unused_3456_ = lean_ctor_get(v___x_3366_, 0);
lean_dec(v_unused_3456_);
v___x_3383_ = v___x_3366_;
v_isShared_3384_ = v_isSharedCheck_3451_;
goto v_resetjp_3382_;
}
else
{
lean_dec(v___x_3366_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3451_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
if (lean_obj_tag(v_l_3371_) == 0)
{
if (lean_obj_tag(v_r_3372_) == 0)
{
lean_object* v_size_3385_; lean_object* v_k_3386_; lean_object* v_v_3387_; lean_object* v_l_3388_; lean_object* v_r_3389_; lean_object* v_size_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
v_size_3385_ = lean_ctor_get(v_l_3371_, 0);
v_k_3386_ = lean_ctor_get(v_l_3371_, 1);
v_v_3387_ = lean_ctor_get(v_l_3371_, 2);
v_l_3388_ = lean_ctor_get(v_l_3371_, 3);
v_r_3389_ = lean_ctor_get(v_l_3371_, 4);
v_size_3390_ = lean_ctor_get(v_r_3372_, 0);
v___x_3391_ = lean_unsigned_to_nat(2u);
v___x_3392_ = lean_nat_mul(v___x_3391_, v_size_3390_);
v___x_3393_ = lean_nat_dec_lt(v_size_3385_, v___x_3392_);
lean_dec(v___x_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3422_; 
lean_inc(v_r_3389_);
lean_inc(v_l_3388_);
lean_inc(v_v_3387_);
lean_inc(v_k_3386_);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_l_3371_);
if (v_isSharedCheck_3422_ == 0)
{
lean_object* v_unused_3423_; lean_object* v_unused_3424_; lean_object* v_unused_3425_; lean_object* v_unused_3426_; lean_object* v_unused_3427_; 
v_unused_3423_ = lean_ctor_get(v_l_3371_, 4);
lean_dec(v_unused_3423_);
v_unused_3424_ = lean_ctor_get(v_l_3371_, 3);
lean_dec(v_unused_3424_);
v_unused_3425_ = lean_ctor_get(v_l_3371_, 2);
lean_dec(v_unused_3425_);
v_unused_3426_ = lean_ctor_get(v_l_3371_, 1);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v_l_3371_, 0);
lean_dec(v_unused_3427_);
v___x_3395_ = v_l_3371_;
v_isShared_3396_ = v_isSharedCheck_3422_;
goto v_resetjp_3394_;
}
else
{
lean_dec(v_l_3371_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3422_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3412_; 
v___x_3397_ = lean_unsigned_to_nat(1u);
v___x_3398_ = lean_nat_add(v___x_3397_, v_size_3367_);
v___x_3399_ = lean_nat_add(v___x_3398_, v_size_3368_);
lean_dec(v_size_3368_);
if (lean_obj_tag(v_l_3388_) == 0)
{
lean_object* v_size_3420_; 
v_size_3420_ = lean_ctor_get(v_l_3388_, 0);
lean_inc(v_size_3420_);
v___y_3412_ = v_size_3420_;
goto v___jp_3411_;
}
else
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_unsigned_to_nat(0u);
v___y_3412_ = v___x_3421_;
goto v___jp_3411_;
}
v___jp_3400_:
{
lean_object* v___x_3404_; lean_object* v___x_3406_; 
v___x_3404_ = lean_nat_add(v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec(v___y_3402_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 4, v_r_3372_);
lean_ctor_set(v___x_3395_, 3, v_r_3389_);
lean_ctor_set(v___x_3395_, 2, v_v_3370_);
lean_ctor_set(v___x_3395_, 1, v_k_3369_);
lean_ctor_set(v___x_3395_, 0, v___x_3404_);
v___x_3406_ = v___x_3395_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3404_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_k_3369_);
lean_ctor_set(v_reuseFailAlloc_3410_, 2, v_v_3370_);
lean_ctor_set(v_reuseFailAlloc_3410_, 3, v_r_3389_);
lean_ctor_set(v_reuseFailAlloc_3410_, 4, v_r_3372_);
v___x_3406_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3408_; 
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 4, v___x_3406_);
lean_ctor_set(v___x_3383_, 3, v___y_3401_);
lean_ctor_set(v___x_3383_, 2, v_v_3387_);
lean_ctor_set(v___x_3383_, 1, v_k_3386_);
lean_ctor_set(v___x_3383_, 0, v___x_3399_);
v___x_3408_ = v___x_3383_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_k_3386_);
lean_ctor_set(v_reuseFailAlloc_3409_, 2, v_v_3387_);
lean_ctor_set(v_reuseFailAlloc_3409_, 3, v___y_3401_);
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
v___jp_3411_:
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3413_ = lean_nat_add(v___x_3398_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec(v___x_3398_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v_l_3388_);
lean_ctor_set(v___x_3184_, 0, v___x_3413_);
v___x_3415_ = v___x_3184_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3413_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3419_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3419_, 3, v_l_3181_);
lean_ctor_set(v_reuseFailAlloc_3419_, 4, v_l_3388_);
v___x_3415_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_nat_add(v___x_3397_, v_size_3390_);
if (lean_obj_tag(v_r_3389_) == 0)
{
lean_object* v_size_3417_; 
v_size_3417_ = lean_ctor_get(v_r_3389_, 0);
lean_inc(v_size_3417_);
v___y_3401_ = v___x_3415_;
v___y_3402_ = v___x_3416_;
v___y_3403_ = v_size_3417_;
goto v___jp_3400_;
}
else
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_unsigned_to_nat(0u);
v___y_3401_ = v___x_3415_;
v___y_3402_ = v___x_3416_;
v___y_3403_ = v___x_3418_;
goto v___jp_3400_;
}
}
}
}
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3433_; 
lean_del_object(v___x_3184_);
v___x_3428_ = lean_unsigned_to_nat(1u);
v___x_3429_ = lean_nat_add(v___x_3428_, v_size_3367_);
v___x_3430_ = lean_nat_add(v___x_3429_, v_size_3368_);
lean_dec(v_size_3368_);
v___x_3431_ = lean_nat_add(v___x_3429_, v_size_3385_);
lean_dec(v___x_3429_);
lean_inc_ref(v_l_3181_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 4, v_l_3371_);
lean_ctor_set(v___x_3383_, 3, v_l_3181_);
lean_ctor_set(v___x_3383_, 2, v_v_3180_);
lean_ctor_set(v___x_3383_, 1, v_k_3179_);
lean_ctor_set(v___x_3383_, 0, v___x_3431_);
v___x_3433_ = v___x_3383_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3446_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3446_, 3, v_l_3181_);
lean_ctor_set(v_reuseFailAlloc_3446_, 4, v_l_3371_);
v___x_3433_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
v_isSharedCheck_3440_ = !lean_is_exclusive(v_l_3181_);
if (v_isSharedCheck_3440_ == 0)
{
lean_object* v_unused_3441_; lean_object* v_unused_3442_; lean_object* v_unused_3443_; lean_object* v_unused_3444_; lean_object* v_unused_3445_; 
v_unused_3441_ = lean_ctor_get(v_l_3181_, 4);
lean_dec(v_unused_3441_);
v_unused_3442_ = lean_ctor_get(v_l_3181_, 3);
lean_dec(v_unused_3442_);
v_unused_3443_ = lean_ctor_get(v_l_3181_, 2);
lean_dec(v_unused_3443_);
v_unused_3444_ = lean_ctor_get(v_l_3181_, 1);
lean_dec(v_unused_3444_);
v_unused_3445_ = lean_ctor_get(v_l_3181_, 0);
lean_dec(v_unused_3445_);
v___x_3435_ = v_l_3181_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_dec(v_l_3181_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 4, v_r_3372_);
lean_ctor_set(v___x_3435_, 3, v___x_3433_);
lean_ctor_set(v___x_3435_, 2, v_v_3370_);
lean_ctor_set(v___x_3435_, 1, v_k_3369_);
lean_ctor_set(v___x_3435_, 0, v___x_3430_);
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3430_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_k_3369_);
lean_ctor_set(v_reuseFailAlloc_3439_, 2, v_v_3370_);
lean_ctor_set(v_reuseFailAlloc_3439_, 3, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3439_, 4, v_r_3372_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
}
else
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_dec_ref_known(v_l_3371_, 5);
lean_del_object(v___x_3383_);
lean_dec(v_v_3370_);
lean_dec(v_k_3369_);
lean_dec(v_size_3368_);
lean_dec_ref_known(v_l_3181_, 5);
lean_del_object(v___x_3184_);
lean_dec(v_v_3180_);
lean_dec(v_k_3179_);
v___x_3447_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7);
v___x_3448_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_3447_);
return v___x_3448_;
}
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
lean_del_object(v___x_3383_);
lean_dec(v_r_3372_);
lean_dec(v_v_3370_);
lean_dec(v_k_3369_);
lean_dec(v_size_3368_);
lean_dec_ref_known(v_l_3181_, 5);
lean_del_object(v___x_3184_);
lean_dec(v_v_3180_);
lean_dec(v_k_3179_);
v___x_3449_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8);
v___x_3450_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_3449_);
return v___x_3450_;
}
}
}
}
else
{
lean_object* v_size_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v_size_3457_ = lean_ctor_get(v_l_3181_, 0);
v___x_3458_ = lean_unsigned_to_nat(1u);
v___x_3459_ = lean_nat_add(v___x_3458_, v_size_3457_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v___x_3366_);
lean_ctor_set(v___x_3184_, 0, v___x_3459_);
v___x_3461_ = v___x_3184_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3462_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3462_, 3, v_l_3181_);
lean_ctor_set(v_reuseFailAlloc_3462_, 4, v___x_3366_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
else
{
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_l_3463_; 
v_l_3463_ = lean_ctor_get(v___x_3366_, 3);
lean_inc(v_l_3463_);
if (lean_obj_tag(v_l_3463_) == 0)
{
lean_object* v_r_3464_; 
v_r_3464_ = lean_ctor_get(v___x_3366_, 4);
lean_inc(v_r_3464_);
if (lean_obj_tag(v_r_3464_) == 0)
{
lean_object* v_size_3465_; lean_object* v_k_3466_; lean_object* v_v_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3481_; 
v_size_3465_ = lean_ctor_get(v___x_3366_, 0);
v_k_3466_ = lean_ctor_get(v___x_3366_, 1);
v_v_3467_ = lean_ctor_get(v___x_3366_, 2);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; lean_object* v_unused_3483_; 
v_unused_3482_ = lean_ctor_get(v___x_3366_, 4);
lean_dec(v_unused_3482_);
v_unused_3483_ = lean_ctor_get(v___x_3366_, 3);
lean_dec(v_unused_3483_);
v___x_3469_ = v___x_3366_;
v_isShared_3470_ = v_isSharedCheck_3481_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_v_3467_);
lean_inc(v_k_3466_);
lean_inc(v_size_3465_);
lean_dec(v___x_3366_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3481_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v_size_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
v_size_3471_ = lean_ctor_get(v_l_3463_, 0);
v___x_3472_ = lean_unsigned_to_nat(1u);
v___x_3473_ = lean_nat_add(v___x_3472_, v_size_3465_);
lean_dec(v_size_3465_);
v___x_3474_ = lean_nat_add(v___x_3472_, v_size_3471_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 4, v_l_3463_);
lean_ctor_set(v___x_3469_, 3, v_l_3181_);
lean_ctor_set(v___x_3469_, 2, v_v_3180_);
lean_ctor_set(v___x_3469_, 1, v_k_3179_);
lean_ctor_set(v___x_3469_, 0, v___x_3474_);
v___x_3476_ = v___x_3469_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3480_, 3, v_l_3181_);
lean_ctor_set(v_reuseFailAlloc_3480_, 4, v_l_3463_);
v___x_3476_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3478_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v_r_3464_);
lean_ctor_set(v___x_3184_, 3, v___x_3476_);
lean_ctor_set(v___x_3184_, 2, v_v_3467_);
lean_ctor_set(v___x_3184_, 1, v_k_3466_);
lean_ctor_set(v___x_3184_, 0, v___x_3473_);
v___x_3478_ = v___x_3184_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_k_3466_);
lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_v_3467_);
lean_ctor_set(v_reuseFailAlloc_3479_, 3, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3479_, 4, v_r_3464_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
lean_object* v_k_3484_; lean_object* v_v_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3509_; 
v_k_3484_ = lean_ctor_get(v___x_3366_, 1);
v_v_3485_ = lean_ctor_get(v___x_3366_, 2);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3509_ == 0)
{
lean_object* v_unused_3510_; lean_object* v_unused_3511_; lean_object* v_unused_3512_; 
v_unused_3510_ = lean_ctor_get(v___x_3366_, 4);
lean_dec(v_unused_3510_);
v_unused_3511_ = lean_ctor_get(v___x_3366_, 3);
lean_dec(v_unused_3511_);
v_unused_3512_ = lean_ctor_get(v___x_3366_, 0);
lean_dec(v_unused_3512_);
v___x_3487_ = v___x_3366_;
v_isShared_3488_ = v_isSharedCheck_3509_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_v_3485_);
lean_inc(v_k_3484_);
lean_dec(v___x_3366_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3509_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v_k_3489_; lean_object* v_v_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3505_; 
v_k_3489_ = lean_ctor_get(v_l_3463_, 1);
v_v_3490_ = lean_ctor_get(v_l_3463_, 2);
v_isSharedCheck_3505_ = !lean_is_exclusive(v_l_3463_);
if (v_isSharedCheck_3505_ == 0)
{
lean_object* v_unused_3506_; lean_object* v_unused_3507_; lean_object* v_unused_3508_; 
v_unused_3506_ = lean_ctor_get(v_l_3463_, 4);
lean_dec(v_unused_3506_);
v_unused_3507_ = lean_ctor_get(v_l_3463_, 3);
lean_dec(v_unused_3507_);
v_unused_3508_ = lean_ctor_get(v_l_3463_, 0);
lean_dec(v_unused_3508_);
v___x_3492_ = v_l_3463_;
v_isShared_3493_ = v_isSharedCheck_3505_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_v_3490_);
lean_inc(v_k_3489_);
lean_dec(v_l_3463_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3505_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3494_ = lean_unsigned_to_nat(3u);
v___x_3495_ = lean_unsigned_to_nat(1u);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 4, v_r_3464_);
lean_ctor_set(v___x_3492_, 3, v_r_3464_);
lean_ctor_set(v___x_3492_, 2, v_v_3180_);
lean_ctor_set(v___x_3492_, 1, v_k_3179_);
lean_ctor_set(v___x_3492_, 0, v___x_3495_);
v___x_3497_ = v___x_3492_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3504_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3504_, 3, v_r_3464_);
lean_ctor_set(v_reuseFailAlloc_3504_, 4, v_r_3464_);
v___x_3497_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3499_; 
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 3, v_r_3464_);
lean_ctor_set(v___x_3487_, 0, v___x_3495_);
v___x_3499_ = v___x_3487_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_k_3484_);
lean_ctor_set(v_reuseFailAlloc_3503_, 2, v_v_3485_);
lean_ctor_set(v_reuseFailAlloc_3503_, 3, v_r_3464_);
lean_ctor_set(v_reuseFailAlloc_3503_, 4, v_r_3464_);
v___x_3499_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3501_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v___x_3499_);
lean_ctor_set(v___x_3184_, 3, v___x_3497_);
lean_ctor_set(v___x_3184_, 2, v_v_3490_);
lean_ctor_set(v___x_3184_, 1, v_k_3489_);
lean_ctor_set(v___x_3184_, 0, v___x_3494_);
v___x_3501_ = v___x_3184_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3494_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_k_3489_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v_v_3490_);
lean_ctor_set(v_reuseFailAlloc_3502_, 3, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3502_, 4, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3513_; 
v_r_3513_ = lean_ctor_get(v___x_3366_, 4);
lean_inc(v_r_3513_);
if (lean_obj_tag(v_r_3513_) == 0)
{
lean_object* v_k_3514_; lean_object* v_v_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3527_; 
v_k_3514_ = lean_ctor_get(v___x_3366_, 1);
v_v_3515_ = lean_ctor_get(v___x_3366_, 2);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3527_ == 0)
{
lean_object* v_unused_3528_; lean_object* v_unused_3529_; lean_object* v_unused_3530_; 
v_unused_3528_ = lean_ctor_get(v___x_3366_, 4);
lean_dec(v_unused_3528_);
v_unused_3529_ = lean_ctor_get(v___x_3366_, 3);
lean_dec(v_unused_3529_);
v_unused_3530_ = lean_ctor_get(v___x_3366_, 0);
lean_dec(v_unused_3530_);
v___x_3517_ = v___x_3366_;
v_isShared_3518_ = v_isSharedCheck_3527_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_v_3515_);
lean_inc(v_k_3514_);
lean_dec(v___x_3366_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3527_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3522_; 
v___x_3519_ = lean_unsigned_to_nat(3u);
v___x_3520_ = lean_unsigned_to_nat(1u);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 4, v_l_3463_);
lean_ctor_set(v___x_3517_, 2, v_v_3180_);
lean_ctor_set(v___x_3517_, 1, v_k_3179_);
lean_ctor_set(v___x_3517_, 0, v___x_3520_);
v___x_3522_ = v___x_3517_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3526_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3526_, 3, v_l_3463_);
lean_ctor_set(v_reuseFailAlloc_3526_, 4, v_l_3463_);
v___x_3522_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3524_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v_r_3513_);
lean_ctor_set(v___x_3184_, 3, v___x_3522_);
lean_ctor_set(v___x_3184_, 2, v_v_3515_);
lean_ctor_set(v___x_3184_, 1, v_k_3514_);
lean_ctor_set(v___x_3184_, 0, v___x_3519_);
v___x_3524_ = v___x_3184_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_k_3514_);
lean_ctor_set(v_reuseFailAlloc_3525_, 2, v_v_3515_);
lean_ctor_set(v_reuseFailAlloc_3525_, 3, v___x_3522_);
lean_ctor_set(v_reuseFailAlloc_3525_, 4, v_r_3513_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3533_; 
v___x_3531_ = lean_unsigned_to_nat(2u);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v___x_3366_);
lean_ctor_set(v___x_3184_, 3, v_r_3513_);
lean_ctor_set(v___x_3184_, 0, v___x_3531_);
v___x_3533_ = v___x_3184_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3534_, 3, v_r_3513_);
lean_ctor_set(v_reuseFailAlloc_3534_, 4, v___x_3366_);
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
lean_object* v___x_3535_; lean_object* v___x_3537_; 
v___x_3535_ = lean_unsigned_to_nat(1u);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v___x_3366_);
lean_ctor_set(v___x_3184_, 3, v___x_3366_);
lean_ctor_set(v___x_3184_, 0, v___x_3535_);
v___x_3537_ = v___x_3184_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3538_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3538_, 3, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3538_, 4, v___x_3366_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
lean_dec_ref(v_cmp_3174_);
v___x_3540_ = lean_unsigned_to_nat(1u);
v___x_3541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
lean_ctor_set(v___x_3541_, 1, v_k_3175_);
lean_ctor_set(v___x_3541_, 2, v_v_3176_);
lean_ctor_set(v___x_3541_, 3, v_t_3177_);
lean_ctor_set(v___x_3541_, 4, v_t_3177_);
return v___x_3541_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(lean_object* v_cmp_3542_, lean_object* v_init_3543_, lean_object* v_x_3544_){
_start:
{
if (lean_obj_tag(v_x_3544_) == 0)
{
lean_object* v_k_3545_; lean_object* v_v_3546_; lean_object* v_l_3547_; lean_object* v_r_3548_; lean_object* v___x_3549_; lean_object* v_a_3550_; lean_object* v_r_3551_; 
v_k_3545_ = lean_ctor_get(v_x_3544_, 1);
lean_inc(v_k_3545_);
v_v_3546_ = lean_ctor_get(v_x_3544_, 2);
lean_inc(v_v_3546_);
v_l_3547_ = lean_ctor_get(v_x_3544_, 3);
lean_inc(v_l_3547_);
v_r_3548_ = lean_ctor_get(v_x_3544_, 4);
lean_inc(v_r_3548_);
lean_dec_ref_known(v_x_3544_, 5);
lean_inc_ref_n(v_cmp_3542_, 2);
v___x_3549_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3542_, v_init_3543_, v_l_3547_);
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref(v___x_3549_);
v_r_3551_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3542_, v_k_3545_, v_v_3546_, v_a_3550_);
v_init_3543_ = v_r_3551_;
v_x_3544_ = v_r_3548_;
goto _start;
}
else
{
lean_object* v___x_3553_; 
lean_dec_ref(v_cmp_3542_);
v___x_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3553_, 0, v_init_3543_);
return v___x_3553_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(lean_object* v_cmp_3554_, lean_object* v_k_3555_, lean_object* v_t_3556_){
_start:
{
if (lean_obj_tag(v_t_3556_) == 0)
{
lean_object* v_k_3557_; lean_object* v_l_3558_; lean_object* v_r_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
v_k_3557_ = lean_ctor_get(v_t_3556_, 1);
lean_inc(v_k_3557_);
v_l_3558_ = lean_ctor_get(v_t_3556_, 3);
lean_inc(v_l_3558_);
v_r_3559_ = lean_ctor_get(v_t_3556_, 4);
lean_inc(v_r_3559_);
lean_dec_ref_known(v_t_3556_, 5);
lean_inc_ref(v_cmp_3554_);
lean_inc(v_k_3555_);
v___x_3560_ = lean_apply_2(v_cmp_3554_, v_k_3555_, v_k_3557_);
v___x_3561_ = lean_unbox(v___x_3560_);
switch(v___x_3561_)
{
case 0:
{
lean_dec(v_r_3559_);
v_t_3556_ = v_l_3558_;
goto _start;
}
case 1:
{
uint8_t v___x_3563_; 
lean_dec(v_r_3559_);
lean_dec(v_l_3558_);
lean_dec(v_k_3555_);
lean_dec_ref(v_cmp_3554_);
v___x_3563_ = 1;
return v___x_3563_;
}
default: 
{
lean_dec(v_l_3558_);
v_t_3556_ = v_r_3559_;
goto _start;
}
}
}
else
{
uint8_t v___x_3565_; 
lean_dec(v_k_3555_);
lean_dec_ref(v_cmp_3554_);
v___x_3565_ = 0;
return v___x_3565_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_3566_, lean_object* v_k_3567_, lean_object* v_t_3568_){
_start:
{
uint8_t v_res_3569_; lean_object* v_r_3570_; 
v_res_3569_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3566_, v_k_3567_, v_t_3568_);
v_r_3570_ = lean_box(v_res_3569_);
return v_r_3570_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(lean_object* v_cmp_3571_, lean_object* v_init_3572_, lean_object* v_x_3573_){
_start:
{
if (lean_obj_tag(v_x_3573_) == 0)
{
lean_object* v_k_3574_; lean_object* v_v_3575_; lean_object* v_l_3576_; lean_object* v_r_3577_; lean_object* v___x_3578_; lean_object* v_a_3579_; uint8_t v___x_3580_; 
v_k_3574_ = lean_ctor_get(v_x_3573_, 1);
lean_inc_n(v_k_3574_, 2);
v_v_3575_ = lean_ctor_get(v_x_3573_, 2);
lean_inc(v_v_3575_);
v_l_3576_ = lean_ctor_get(v_x_3573_, 3);
lean_inc(v_l_3576_);
v_r_3577_ = lean_ctor_get(v_x_3573_, 4);
lean_inc(v_r_3577_);
lean_dec_ref_known(v_x_3573_, 5);
lean_inc_ref_n(v_cmp_3571_, 2);
v___x_3578_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3571_, v_init_3572_, v_l_3576_);
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc_n(v_a_3579_, 2);
lean_dec_ref(v___x_3578_);
v___x_3580_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3571_, v_k_3574_, v_a_3579_);
if (v___x_3580_ == 0)
{
lean_object* v___x_3581_; 
lean_inc_ref(v_cmp_3571_);
v___x_3581_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3571_, v_k_3574_, v_v_3575_, v_a_3579_);
v_init_3572_ = v___x_3581_;
v_x_3573_ = v_r_3577_;
goto _start;
}
else
{
lean_dec(v_v_3575_);
lean_dec(v_k_3574_);
v_init_3572_ = v_a_3579_;
v_x_3573_ = v_r_3577_;
goto _start;
}
}
else
{
lean_object* v___x_3584_; 
lean_dec_ref(v_cmp_3571_);
v___x_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3584_, 0, v_init_3572_);
return v___x_3584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(lean_object* v_cmp_3585_, lean_object* v_t_u2081_3586_, lean_object* v_t_u2082_3587_){
_start:
{
lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3597_; 
if (lean_obj_tag(v_t_u2081_3586_) == 0)
{
lean_object* v_size_3600_; 
v_size_3600_ = lean_ctor_get(v_t_u2081_3586_, 0);
lean_inc(v_size_3600_);
v___y_3597_ = v_size_3600_;
goto v___jp_3596_;
}
else
{
lean_object* v___x_3601_; 
v___x_3601_ = lean_unsigned_to_nat(0u);
v___y_3597_ = v___x_3601_;
goto v___jp_3596_;
}
v___jp_3588_:
{
uint8_t v___x_3591_; 
v___x_3591_ = lean_nat_dec_le(v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec(v___y_3589_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v_a_3593_; 
v___x_3592_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3585_, v_t_u2081_3586_, v_t_u2082_3587_);
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref(v___x_3592_);
return v_a_3593_;
}
else
{
lean_object* v___x_3594_; lean_object* v_a_3595_; 
v___x_3594_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3585_, v_t_u2082_3587_, v_t_u2081_3586_);
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref(v___x_3594_);
return v_a_3595_;
}
}
v___jp_3596_:
{
if (lean_obj_tag(v_t_u2082_3587_) == 0)
{
lean_object* v_size_3598_; 
v_size_3598_ = lean_ctor_get(v_t_u2082_3587_, 0);
lean_inc(v_size_3598_);
v___y_3589_ = v___y_3597_;
v___y_3590_ = v_size_3598_;
goto v___jp_3588_;
}
else
{
lean_object* v___x_3599_; 
v___x_3599_ = lean_unsigned_to_nat(0u);
v___y_3589_ = v___y_3597_;
v___y_3590_ = v___x_3599_;
goto v___jp_3588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union___redArg(lean_object* v_cmp_3602_, lean_object* v_t_u2081_3603_, lean_object* v_t_u2082_3604_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3602_, v_t_u2081_3603_, v_t_u2082_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union(lean_object* v_00_u03b1_3606_, lean_object* v_00_u03b2_3607_, lean_object* v_cmp_3608_, lean_object* v_t_u2081_3609_, lean_object* v_t_u2082_3610_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3608_, v_t_u2081_3609_, v_t_u2082_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0(lean_object* v_00_u03b1_3612_, lean_object* v_cmp_3613_, lean_object* v_00_u03b2_3614_, lean_object* v_t_u2081_3615_, lean_object* v_t_u2082_3616_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3613_, v_t_u2081_3615_, v_t_u2082_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3618_, lean_object* v_00_u03b2_3619_, lean_object* v_msg_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v_msg_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0(lean_object* v_00_u03b1_3622_, lean_object* v_cmp_3623_, lean_object* v_00_u03b2_3624_, lean_object* v_k_3625_, lean_object* v_v_3626_, lean_object* v_t_3627_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3623_, v_k_3625_, v_v_3626_, v_t_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1(lean_object* v_00_u03b1_3629_, lean_object* v_cmp_3630_, lean_object* v_00_u03b2_3631_, lean_object* v_k_3632_, lean_object* v_t_3633_){
_start:
{
uint8_t v___x_3634_; 
v___x_3634_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3630_, v_k_3632_, v_t_3633_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3635_, lean_object* v_cmp_3636_, lean_object* v_00_u03b2_3637_, lean_object* v_k_3638_, lean_object* v_t_3639_){
_start:
{
uint8_t v_res_3640_; lean_object* v_r_3641_; 
v_res_3640_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1(v_00_u03b1_3635_, v_cmp_3636_, v_00_u03b2_3637_, v_k_3638_, v_t_3639_);
v_r_3641_ = lean_box(v_res_3640_);
return v_r_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2(lean_object* v_00_u03b1_3642_, lean_object* v_00_u03b2_3643_, lean_object* v_cmp_3644_, lean_object* v_init_3645_, lean_object* v_x_3646_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3644_, v_init_3645_, v_x_3646_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3(lean_object* v_00_u03b1_3648_, lean_object* v_00_u03b2_3649_, lean_object* v_cmp_3650_, lean_object* v_init_3651_, lean_object* v_x_3652_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3650_, v_init_3651_, v_x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion___redArg(lean_object* v_cmp_3654_){
_start:
{
lean_object* v___x_3655_; 
v___x_3655_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_3655_, 0, lean_box(0));
lean_closure_set(v___x_3655_, 1, lean_box(0));
lean_closure_set(v___x_3655_, 2, v_cmp_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion(lean_object* v_00_u03b1_3656_, lean_object* v_00_u03b2_3657_, lean_object* v_cmp_3658_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_3659_, 0, lean_box(0));
lean_closure_set(v___x_3659_, 1, lean_box(0));
lean_closure_set(v___x_3659_, 2, v_cmp_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(lean_object* v_cmp_3660_, lean_object* v_k_3661_, lean_object* v_v_3662_, lean_object* v_t_3663_){
_start:
{
if (lean_obj_tag(v_t_3663_) == 0)
{
lean_object* v_size_3664_; lean_object* v_k_3665_; lean_object* v_v_3666_; lean_object* v_l_3667_; lean_object* v_r_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3949_; 
v_size_3664_ = lean_ctor_get(v_t_3663_, 0);
v_k_3665_ = lean_ctor_get(v_t_3663_, 1);
v_v_3666_ = lean_ctor_get(v_t_3663_, 2);
v_l_3667_ = lean_ctor_get(v_t_3663_, 3);
v_r_3668_ = lean_ctor_get(v_t_3663_, 4);
v_isSharedCheck_3949_ = !lean_is_exclusive(v_t_3663_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3670_ = v_t_3663_;
v_isShared_3671_ = v_isSharedCheck_3949_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_r_3668_);
lean_inc(v_l_3667_);
lean_inc(v_v_3666_);
lean_inc(v_k_3665_);
lean_inc(v_size_3664_);
lean_dec(v_t_3663_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3949_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3672_; uint8_t v___x_3673_; 
lean_inc_ref(v_cmp_3660_);
lean_inc(v_k_3665_);
lean_inc(v_k_3661_);
v___x_3672_ = lean_apply_2(v_cmp_3660_, v_k_3661_, v_k_3665_);
v___x_3673_ = lean_unbox(v___x_3672_);
switch(v___x_3673_)
{
case 0:
{
lean_object* v_impl_3674_; lean_object* v___x_3675_; 
lean_dec(v_size_3664_);
v_impl_3674_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3660_, v_k_3661_, v_v_3662_, v_l_3667_);
v___x_3675_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3668_) == 0)
{
lean_object* v_size_3676_; lean_object* v_size_3677_; lean_object* v_k_3678_; lean_object* v_v_3679_; lean_object* v_l_3680_; lean_object* v_r_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v_size_3676_ = lean_ctor_get(v_r_3668_, 0);
v_size_3677_ = lean_ctor_get(v_impl_3674_, 0);
lean_inc(v_size_3677_);
v_k_3678_ = lean_ctor_get(v_impl_3674_, 1);
lean_inc(v_k_3678_);
v_v_3679_ = lean_ctor_get(v_impl_3674_, 2);
lean_inc(v_v_3679_);
v_l_3680_ = lean_ctor_get(v_impl_3674_, 3);
lean_inc(v_l_3680_);
v_r_3681_ = lean_ctor_get(v_impl_3674_, 4);
lean_inc(v_r_3681_);
v___x_3682_ = lean_unsigned_to_nat(3u);
v___x_3683_ = lean_nat_mul(v___x_3682_, v_size_3676_);
v___x_3684_ = lean_nat_dec_lt(v___x_3683_, v_size_3677_);
lean_dec(v___x_3683_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3688_; 
lean_dec(v_r_3681_);
lean_dec(v_l_3680_);
lean_dec(v_v_3679_);
lean_dec(v_k_3678_);
v___x_3685_ = lean_nat_add(v___x_3675_, v_size_3677_);
lean_dec(v_size_3677_);
v___x_3686_ = lean_nat_add(v___x_3685_, v_size_3676_);
lean_dec(v___x_3685_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 3, v_impl_3674_);
lean_ctor_set(v___x_3670_, 0, v___x_3686_);
v___x_3688_ = v___x_3670_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3689_, 3, v_impl_3674_);
lean_ctor_set(v_reuseFailAlloc_3689_, 4, v_r_3668_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
else
{
lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3755_; 
v_isSharedCheck_3755_ = !lean_is_exclusive(v_impl_3674_);
if (v_isSharedCheck_3755_ == 0)
{
lean_object* v_unused_3756_; lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; lean_object* v_unused_3760_; 
v_unused_3756_ = lean_ctor_get(v_impl_3674_, 4);
lean_dec(v_unused_3756_);
v_unused_3757_ = lean_ctor_get(v_impl_3674_, 3);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_impl_3674_, 2);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_impl_3674_, 1);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_impl_3674_, 0);
lean_dec(v_unused_3760_);
v___x_3691_ = v_impl_3674_;
v_isShared_3692_ = v_isSharedCheck_3755_;
goto v_resetjp_3690_;
}
else
{
lean_dec(v_impl_3674_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3755_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v_size_3693_; lean_object* v_size_3694_; lean_object* v_k_3695_; lean_object* v_v_3696_; lean_object* v_l_3697_; lean_object* v_r_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; uint8_t v___x_3701_; 
v_size_3693_ = lean_ctor_get(v_l_3680_, 0);
v_size_3694_ = lean_ctor_get(v_r_3681_, 0);
v_k_3695_ = lean_ctor_get(v_r_3681_, 1);
v_v_3696_ = lean_ctor_get(v_r_3681_, 2);
v_l_3697_ = lean_ctor_get(v_r_3681_, 3);
v_r_3698_ = lean_ctor_get(v_r_3681_, 4);
v___x_3699_ = lean_unsigned_to_nat(2u);
v___x_3700_ = lean_nat_mul(v___x_3699_, v_size_3693_);
v___x_3701_ = lean_nat_dec_lt(v_size_3694_, v___x_3700_);
lean_dec(v___x_3700_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3730_; 
lean_inc(v_r_3698_);
lean_inc(v_l_3697_);
lean_inc(v_v_3696_);
lean_inc(v_k_3695_);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_r_3681_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; 
v_unused_3731_ = lean_ctor_get(v_r_3681_, 4);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_r_3681_, 3);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_r_3681_, 2);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_r_3681_, 1);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_r_3681_, 0);
lean_dec(v_unused_3735_);
v___x_3703_ = v_r_3681_;
v_isShared_3704_ = v_isSharedCheck_3730_;
goto v_resetjp_3702_;
}
else
{
lean_dec(v_r_3681_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3730_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___x_3718_; lean_object* v___y_3720_; 
v___x_3705_ = lean_nat_add(v___x_3675_, v_size_3677_);
lean_dec(v_size_3677_);
v___x_3706_ = lean_nat_add(v___x_3705_, v_size_3676_);
lean_dec(v___x_3705_);
v___x_3718_ = lean_nat_add(v___x_3675_, v_size_3693_);
if (lean_obj_tag(v_l_3697_) == 0)
{
lean_object* v_size_3728_; 
v_size_3728_ = lean_ctor_get(v_l_3697_, 0);
lean_inc(v_size_3728_);
v___y_3720_ = v_size_3728_;
goto v___jp_3719_;
}
else
{
lean_object* v___x_3729_; 
v___x_3729_ = lean_unsigned_to_nat(0u);
v___y_3720_ = v___x_3729_;
goto v___jp_3719_;
}
v___jp_3707_:
{
lean_object* v___x_3711_; lean_object* v___x_3713_; 
v___x_3711_ = lean_nat_add(v___y_3709_, v___y_3710_);
lean_dec(v___y_3710_);
lean_dec(v___y_3709_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 4, v_r_3668_);
lean_ctor_set(v___x_3703_, 3, v_r_3698_);
lean_ctor_set(v___x_3703_, 2, v_v_3666_);
lean_ctor_set(v___x_3703_, 1, v_k_3665_);
lean_ctor_set(v___x_3703_, 0, v___x_3711_);
v___x_3713_ = v___x_3703_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3711_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3717_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3717_, 3, v_r_3698_);
lean_ctor_set(v_reuseFailAlloc_3717_, 4, v_r_3668_);
v___x_3713_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
lean_object* v___x_3715_; 
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 4, v___x_3713_);
lean_ctor_set(v___x_3691_, 3, v___y_3708_);
lean_ctor_set(v___x_3691_, 2, v_v_3696_);
lean_ctor_set(v___x_3691_, 1, v_k_3695_);
lean_ctor_set(v___x_3691_, 0, v___x_3706_);
v___x_3715_ = v___x_3691_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3706_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_k_3695_);
lean_ctor_set(v_reuseFailAlloc_3716_, 2, v_v_3696_);
lean_ctor_set(v_reuseFailAlloc_3716_, 3, v___y_3708_);
lean_ctor_set(v_reuseFailAlloc_3716_, 4, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
v___jp_3719_:
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3721_ = lean_nat_add(v___x_3718_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec(v___x_3718_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 4, v_l_3697_);
lean_ctor_set(v___x_3670_, 3, v_l_3680_);
lean_ctor_set(v___x_3670_, 2, v_v_3679_);
lean_ctor_set(v___x_3670_, 1, v_k_3678_);
lean_ctor_set(v___x_3670_, 0, v___x_3721_);
v___x_3723_ = v___x_3670_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_k_3678_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v_v_3679_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v_l_3680_);
lean_ctor_set(v_reuseFailAlloc_3727_, 4, v_l_3697_);
v___x_3723_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_nat_add(v___x_3675_, v_size_3676_);
if (lean_obj_tag(v_r_3698_) == 0)
{
lean_object* v_size_3725_; 
v_size_3725_ = lean_ctor_get(v_r_3698_, 0);
lean_inc(v_size_3725_);
v___y_3708_ = v___x_3723_;
v___y_3709_ = v___x_3724_;
v___y_3710_ = v_size_3725_;
goto v___jp_3707_;
}
else
{
lean_object* v___x_3726_; 
v___x_3726_ = lean_unsigned_to_nat(0u);
v___y_3708_ = v___x_3723_;
v___y_3709_ = v___x_3724_;
v___y_3710_ = v___x_3726_;
goto v___jp_3707_;
}
}
}
}
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3741_; 
lean_del_object(v___x_3670_);
v___x_3736_ = lean_nat_add(v___x_3675_, v_size_3677_);
lean_dec(v_size_3677_);
v___x_3737_ = lean_nat_add(v___x_3736_, v_size_3676_);
lean_dec(v___x_3736_);
v___x_3738_ = lean_nat_add(v___x_3675_, v_size_3676_);
v___x_3739_ = lean_nat_add(v___x_3738_, v_size_3694_);
lean_dec(v___x_3738_);
lean_inc_ref(v_r_3668_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 4, v_r_3668_);
lean_ctor_set(v___x_3691_, 3, v_r_3681_);
lean_ctor_set(v___x_3691_, 2, v_v_3666_);
lean_ctor_set(v___x_3691_, 1, v_k_3665_);
lean_ctor_set(v___x_3691_, 0, v___x_3739_);
v___x_3741_ = v___x_3691_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3754_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3754_, 3, v_r_3681_);
lean_ctor_set(v_reuseFailAlloc_3754_, 4, v_r_3668_);
v___x_3741_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
v_isSharedCheck_3748_ = !lean_is_exclusive(v_r_3668_);
if (v_isSharedCheck_3748_ == 0)
{
lean_object* v_unused_3749_; lean_object* v_unused_3750_; lean_object* v_unused_3751_; lean_object* v_unused_3752_; lean_object* v_unused_3753_; 
v_unused_3749_ = lean_ctor_get(v_r_3668_, 4);
lean_dec(v_unused_3749_);
v_unused_3750_ = lean_ctor_get(v_r_3668_, 3);
lean_dec(v_unused_3750_);
v_unused_3751_ = lean_ctor_get(v_r_3668_, 2);
lean_dec(v_unused_3751_);
v_unused_3752_ = lean_ctor_get(v_r_3668_, 1);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_r_3668_, 0);
lean_dec(v_unused_3753_);
v___x_3743_ = v_r_3668_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_dec(v_r_3668_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 4, v___x_3741_);
lean_ctor_set(v___x_3743_, 3, v_l_3680_);
lean_ctor_set(v___x_3743_, 2, v_v_3679_);
lean_ctor_set(v___x_3743_, 1, v_k_3678_);
lean_ctor_set(v___x_3743_, 0, v___x_3737_);
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_k_3678_);
lean_ctor_set(v_reuseFailAlloc_3747_, 2, v_v_3679_);
lean_ctor_set(v_reuseFailAlloc_3747_, 3, v_l_3680_);
lean_ctor_set(v_reuseFailAlloc_3747_, 4, v___x_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3761_; 
v_l_3761_ = lean_ctor_get(v_impl_3674_, 3);
lean_inc(v_l_3761_);
if (lean_obj_tag(v_l_3761_) == 0)
{
lean_object* v_r_3762_; lean_object* v_k_3763_; lean_object* v_v_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3775_; 
v_r_3762_ = lean_ctor_get(v_impl_3674_, 4);
v_k_3763_ = lean_ctor_get(v_impl_3674_, 1);
v_v_3764_ = lean_ctor_get(v_impl_3674_, 2);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_impl_3674_);
if (v_isSharedCheck_3775_ == 0)
{
lean_object* v_unused_3776_; lean_object* v_unused_3777_; 
v_unused_3776_ = lean_ctor_get(v_impl_3674_, 3);
lean_dec(v_unused_3776_);
v_unused_3777_ = lean_ctor_get(v_impl_3674_, 0);
lean_dec(v_unused_3777_);
v___x_3766_ = v_impl_3674_;
v_isShared_3767_ = v_isSharedCheck_3775_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_r_3762_);
lean_inc(v_v_3764_);
lean_inc(v_k_3763_);
lean_dec(v_impl_3674_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3775_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3768_; lean_object* v___x_3770_; 
v___x_3768_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3762_);
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 3, v_r_3762_);
lean_ctor_set(v___x_3766_, 2, v_v_3666_);
lean_ctor_set(v___x_3766_, 1, v_k_3665_);
lean_ctor_set(v___x_3766_, 0, v___x_3675_);
v___x_3770_ = v___x_3766_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3675_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3774_, 3, v_r_3762_);
lean_ctor_set(v_reuseFailAlloc_3774_, 4, v_r_3762_);
v___x_3770_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
lean_object* v___x_3772_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 4, v___x_3770_);
lean_ctor_set(v___x_3670_, 3, v_l_3761_);
lean_ctor_set(v___x_3670_, 2, v_v_3764_);
lean_ctor_set(v___x_3670_, 1, v_k_3763_);
lean_ctor_set(v___x_3670_, 0, v___x_3768_);
v___x_3772_ = v___x_3670_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3773_, 1, v_k_3763_);
lean_ctor_set(v_reuseFailAlloc_3773_, 2, v_v_3764_);
lean_ctor_set(v_reuseFailAlloc_3773_, 3, v_l_3761_);
lean_ctor_set(v_reuseFailAlloc_3773_, 4, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v_r_3778_; 
v_r_3778_ = lean_ctor_get(v_impl_3674_, 4);
lean_inc(v_r_3778_);
if (lean_obj_tag(v_r_3778_) == 0)
{
lean_object* v_k_3779_; lean_object* v_v_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3803_; 
v_k_3779_ = lean_ctor_get(v_impl_3674_, 1);
v_v_3780_ = lean_ctor_get(v_impl_3674_, 2);
v_isSharedCheck_3803_ = !lean_is_exclusive(v_impl_3674_);
if (v_isSharedCheck_3803_ == 0)
{
lean_object* v_unused_3804_; lean_object* v_unused_3805_; lean_object* v_unused_3806_; 
v_unused_3804_ = lean_ctor_get(v_impl_3674_, 4);
lean_dec(v_unused_3804_);
v_unused_3805_ = lean_ctor_get(v_impl_3674_, 3);
lean_dec(v_unused_3805_);
v_unused_3806_ = lean_ctor_get(v_impl_3674_, 0);
lean_dec(v_unused_3806_);
v___x_3782_ = v_impl_3674_;
v_isShared_3783_ = v_isSharedCheck_3803_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_v_3780_);
lean_inc(v_k_3779_);
lean_dec(v_impl_3674_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3803_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v_k_3784_; lean_object* v_v_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3799_; 
v_k_3784_ = lean_ctor_get(v_r_3778_, 1);
v_v_3785_ = lean_ctor_get(v_r_3778_, 2);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_r_3778_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; lean_object* v_unused_3801_; lean_object* v_unused_3802_; 
v_unused_3800_ = lean_ctor_get(v_r_3778_, 4);
lean_dec(v_unused_3800_);
v_unused_3801_ = lean_ctor_get(v_r_3778_, 3);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v_r_3778_, 0);
lean_dec(v_unused_3802_);
v___x_3787_ = v_r_3778_;
v_isShared_3788_ = v_isSharedCheck_3799_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_v_3785_);
lean_inc(v_k_3784_);
lean_dec(v_r_3778_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3799_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3789_; lean_object* v___x_3791_; 
v___x_3789_ = lean_unsigned_to_nat(3u);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 4, v_l_3761_);
lean_ctor_set(v___x_3787_, 3, v_l_3761_);
lean_ctor_set(v___x_3787_, 2, v_v_3780_);
lean_ctor_set(v___x_3787_, 1, v_k_3779_);
lean_ctor_set(v___x_3787_, 0, v___x_3675_);
v___x_3791_ = v___x_3787_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3675_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_k_3779_);
lean_ctor_set(v_reuseFailAlloc_3798_, 2, v_v_3780_);
lean_ctor_set(v_reuseFailAlloc_3798_, 3, v_l_3761_);
lean_ctor_set(v_reuseFailAlloc_3798_, 4, v_l_3761_);
v___x_3791_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
lean_object* v___x_3793_; 
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 4, v_l_3761_);
lean_ctor_set(v___x_3782_, 2, v_v_3666_);
lean_ctor_set(v___x_3782_, 1, v_k_3665_);
lean_ctor_set(v___x_3782_, 0, v___x_3675_);
v___x_3793_ = v___x_3782_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3675_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3797_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3797_, 3, v_l_3761_);
lean_ctor_set(v_reuseFailAlloc_3797_, 4, v_l_3761_);
v___x_3793_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
lean_object* v___x_3795_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 4, v___x_3793_);
lean_ctor_set(v___x_3670_, 3, v___x_3791_);
lean_ctor_set(v___x_3670_, 2, v_v_3785_);
lean_ctor_set(v___x_3670_, 1, v_k_3784_);
lean_ctor_set(v___x_3670_, 0, v___x_3789_);
v___x_3795_ = v___x_3670_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_k_3784_);
lean_ctor_set(v_reuseFailAlloc_3796_, 2, v_v_3785_);
lean_ctor_set(v_reuseFailAlloc_3796_, 3, v___x_3791_);
lean_ctor_set(v_reuseFailAlloc_3796_, 4, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3807_ = lean_unsigned_to_nat(2u);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 4, v_r_3778_);
lean_ctor_set(v___x_3670_, 3, v_impl_3674_);
lean_ctor_set(v___x_3670_, 0, v___x_3807_);
v___x_3809_ = v___x_3670_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3810_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3810_, 3, v_impl_3674_);
lean_ctor_set(v_reuseFailAlloc_3810_, 4, v_r_3778_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3812_; 
lean_dec(v_v_3666_);
lean_dec(v_k_3665_);
lean_dec_ref(v_cmp_3660_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 2, v_v_3662_);
lean_ctor_set(v___x_3670_, 1, v_k_3661_);
v___x_3812_ = v___x_3670_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_size_3664_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_k_3661_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v_v_3662_);
lean_ctor_set(v_reuseFailAlloc_3813_, 3, v_l_3667_);
lean_ctor_set(v_reuseFailAlloc_3813_, 4, v_r_3668_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
default: 
{
lean_object* v_impl_3814_; lean_object* v___x_3815_; 
lean_dec(v_size_3664_);
v_impl_3814_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3660_, v_k_3661_, v_v_3662_, v_r_3668_);
v___x_3815_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3667_) == 0)
{
lean_object* v_size_3816_; lean_object* v_size_3817_; lean_object* v_k_3818_; lean_object* v_v_3819_; lean_object* v_l_3820_; lean_object* v_r_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
v_size_3816_ = lean_ctor_get(v_l_3667_, 0);
v_size_3817_ = lean_ctor_get(v_impl_3814_, 0);
lean_inc(v_size_3817_);
v_k_3818_ = lean_ctor_get(v_impl_3814_, 1);
lean_inc(v_k_3818_);
v_v_3819_ = lean_ctor_get(v_impl_3814_, 2);
lean_inc(v_v_3819_);
v_l_3820_ = lean_ctor_get(v_impl_3814_, 3);
lean_inc(v_l_3820_);
v_r_3821_ = lean_ctor_get(v_impl_3814_, 4);
lean_inc(v_r_3821_);
v___x_3822_ = lean_unsigned_to_nat(3u);
v___x_3823_ = lean_nat_mul(v___x_3822_, v_size_3816_);
v___x_3824_ = lean_nat_dec_lt(v___x_3823_, v_size_3817_);
lean_dec(v___x_3823_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3828_; 
lean_dec(v_r_3821_);
lean_dec(v_l_3820_);
lean_dec(v_v_3819_);
lean_dec(v_k_3818_);
v___x_3825_ = lean_nat_add(v___x_3815_, v_size_3816_);
v___x_3826_ = lean_nat_add(v___x_3825_, v_size_3817_);
lean_dec(v_size_3817_);
lean_dec(v___x_3825_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 4, v_impl_3814_);
lean_ctor_set(v___x_3670_, 0, v___x_3826_);
v___x_3828_ = v___x_3670_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3829_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3829_, 3, v_l_3667_);
lean_ctor_set(v_reuseFailAlloc_3829_, 4, v_impl_3814_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
else
{
lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3893_; 
v_isSharedCheck_3893_ = !lean_is_exclusive(v_impl_3814_);
if (v_isSharedCheck_3893_ == 0)
{
lean_object* v_unused_3894_; lean_object* v_unused_3895_; lean_object* v_unused_3896_; lean_object* v_unused_3897_; lean_object* v_unused_3898_; 
v_unused_3894_ = lean_ctor_get(v_impl_3814_, 4);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_impl_3814_, 3);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_impl_3814_, 2);
lean_dec(v_unused_3896_);
v_unused_3897_ = lean_ctor_get(v_impl_3814_, 1);
lean_dec(v_unused_3897_);
v_unused_3898_ = lean_ctor_get(v_impl_3814_, 0);
lean_dec(v_unused_3898_);
v___x_3831_ = v_impl_3814_;
v_isShared_3832_ = v_isSharedCheck_3893_;
goto v_resetjp_3830_;
}
else
{
lean_dec(v_impl_3814_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3893_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v_size_3833_; lean_object* v_k_3834_; lean_object* v_v_3835_; lean_object* v_l_3836_; lean_object* v_r_3837_; lean_object* v_size_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; 
v_size_3833_ = lean_ctor_get(v_l_3820_, 0);
v_k_3834_ = lean_ctor_get(v_l_3820_, 1);
v_v_3835_ = lean_ctor_get(v_l_3820_, 2);
v_l_3836_ = lean_ctor_get(v_l_3820_, 3);
v_r_3837_ = lean_ctor_get(v_l_3820_, 4);
v_size_3838_ = lean_ctor_get(v_r_3821_, 0);
v___x_3839_ = lean_unsigned_to_nat(2u);
v___x_3840_ = lean_nat_mul(v___x_3839_, v_size_3838_);
v___x_3841_ = lean_nat_dec_lt(v_size_3833_, v___x_3840_);
lean_dec(v___x_3840_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3869_; 
lean_inc(v_r_3837_);
lean_inc(v_l_3836_);
lean_inc(v_v_3835_);
lean_inc(v_k_3834_);
v_isSharedCheck_3869_ = !lean_is_exclusive(v_l_3820_);
if (v_isSharedCheck_3869_ == 0)
{
lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; lean_object* v_unused_3873_; lean_object* v_unused_3874_; 
v_unused_3870_ = lean_ctor_get(v_l_3820_, 4);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_l_3820_, 3);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_l_3820_, 2);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_l_3820_, 1);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_l_3820_, 0);
lean_dec(v_unused_3874_);
v___x_3843_ = v_l_3820_;
v_isShared_3844_ = v_isSharedCheck_3869_;
goto v_resetjp_3842_;
}
else
{
lean_dec(v_l_3820_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3869_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3859_; 
v___x_3845_ = lean_nat_add(v___x_3815_, v_size_3816_);
v___x_3846_ = lean_nat_add(v___x_3845_, v_size_3817_);
lean_dec(v_size_3817_);
if (lean_obj_tag(v_l_3836_) == 0)
{
lean_object* v_size_3867_; 
v_size_3867_ = lean_ctor_get(v_l_3836_, 0);
lean_inc(v_size_3867_);
v___y_3859_ = v_size_3867_;
goto v___jp_3858_;
}
else
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_unsigned_to_nat(0u);
v___y_3859_ = v___x_3868_;
goto v___jp_3858_;
}
v___jp_3847_:
{
lean_object* v___x_3851_; lean_object* v___x_3853_; 
v___x_3851_ = lean_nat_add(v___y_3849_, v___y_3850_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 4, v_r_3821_);
lean_ctor_set(v___x_3843_, 3, v_r_3837_);
lean_ctor_set(v___x_3843_, 2, v_v_3819_);
lean_ctor_set(v___x_3843_, 1, v_k_3818_);
lean_ctor_set(v___x_3843_, 0, v___x_3851_);
v___x_3853_ = v___x_3843_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v_k_3818_);
lean_ctor_set(v_reuseFailAlloc_3857_, 2, v_v_3819_);
lean_ctor_set(v_reuseFailAlloc_3857_, 3, v_r_3837_);
lean_ctor_set(v_reuseFailAlloc_3857_, 4, v_r_3821_);
v___x_3853_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3855_; 
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 4, v___x_3853_);
lean_ctor_set(v___x_3831_, 3, v___y_3848_);
lean_ctor_set(v___x_3831_, 2, v_v_3835_);
lean_ctor_set(v___x_3831_, 1, v_k_3834_);
lean_ctor_set(v___x_3831_, 0, v___x_3846_);
v___x_3855_ = v___x_3831_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3846_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_k_3834_);
lean_ctor_set(v_reuseFailAlloc_3856_, 2, v_v_3835_);
lean_ctor_set(v_reuseFailAlloc_3856_, 3, v___y_3848_);
lean_ctor_set(v_reuseFailAlloc_3856_, 4, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
v___jp_3858_:
{
lean_object* v___x_3860_; lean_object* v___x_3862_; 
v___x_3860_ = lean_nat_add(v___x_3845_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec(v___x_3845_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 4, v_l_3836_);
lean_ctor_set(v___x_3670_, 0, v___x_3860_);
v___x_3862_ = v___x_3670_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3866_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3866_, 3, v_l_3667_);
lean_ctor_set(v_reuseFailAlloc_3866_, 4, v_l_3836_);
v___x_3862_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_nat_add(v___x_3815_, v_size_3838_);
if (lean_obj_tag(v_r_3837_) == 0)
{
lean_object* v_size_3864_; 
v_size_3864_ = lean_ctor_get(v_r_3837_, 0);
lean_inc(v_size_3864_);
v___y_3848_ = v___x_3862_;
v___y_3849_ = v___x_3863_;
v___y_3850_ = v_size_3864_;
goto v___jp_3847_;
}
else
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_unsigned_to_nat(0u);
v___y_3848_ = v___x_3862_;
v___y_3849_ = v___x_3863_;
v___y_3850_ = v___x_3865_;
goto v___jp_3847_;
}
}
}
}
}
else
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3879_; 
lean_del_object(v___x_3670_);
v___x_3875_ = lean_nat_add(v___x_3815_, v_size_3816_);
v___x_3876_ = lean_nat_add(v___x_3875_, v_size_3817_);
lean_dec(v_size_3817_);
v___x_3877_ = lean_nat_add(v___x_3875_, v_size_3833_);
lean_dec(v___x_3875_);
lean_inc_ref(v_l_3667_);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 4, v_l_3820_);
lean_ctor_set(v___x_3831_, 3, v_l_3667_);
lean_ctor_set(v___x_3831_, 2, v_v_3666_);
lean_ctor_set(v___x_3831_, 1, v_k_3665_);
lean_ctor_set(v___x_3831_, 0, v___x_3877_);
v___x_3879_ = v___x_3831_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3877_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3892_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3892_, 3, v_l_3667_);
lean_ctor_set(v_reuseFailAlloc_3892_, 4, v_l_3820_);
v___x_3879_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
v_isSharedCheck_3886_ = !lean_is_exclusive(v_l_3667_);
if (v_isSharedCheck_3886_ == 0)
{
lean_object* v_unused_3887_; lean_object* v_unused_3888_; lean_object* v_unused_3889_; lean_object* v_unused_3890_; lean_object* v_unused_3891_; 
v_unused_3887_ = lean_ctor_get(v_l_3667_, 4);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_l_3667_, 3);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_l_3667_, 2);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_l_3667_, 1);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_l_3667_, 0);
lean_dec(v_unused_3891_);
v___x_3881_ = v_l_3667_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_dec(v_l_3667_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 4, v_r_3821_);
lean_ctor_set(v___x_3881_, 3, v___x_3879_);
lean_ctor_set(v___x_3881_, 2, v_v_3819_);
lean_ctor_set(v___x_3881_, 1, v_k_3818_);
lean_ctor_set(v___x_3881_, 0, v___x_3876_);
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v_k_3818_);
lean_ctor_set(v_reuseFailAlloc_3885_, 2, v_v_3819_);
lean_ctor_set(v_reuseFailAlloc_3885_, 3, v___x_3879_);
lean_ctor_set(v_reuseFailAlloc_3885_, 4, v_r_3821_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3899_; 
v_l_3899_ = lean_ctor_get(v_impl_3814_, 3);
lean_inc(v_l_3899_);
if (lean_obj_tag(v_l_3899_) == 0)
{
lean_object* v_r_3900_; lean_object* v_k_3901_; lean_object* v_v_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3925_; 
v_r_3900_ = lean_ctor_get(v_impl_3814_, 4);
v_k_3901_ = lean_ctor_get(v_impl_3814_, 1);
v_v_3902_ = lean_ctor_get(v_impl_3814_, 2);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_impl_3814_);
if (v_isSharedCheck_3925_ == 0)
{
lean_object* v_unused_3926_; lean_object* v_unused_3927_; 
v_unused_3926_ = lean_ctor_get(v_impl_3814_, 3);
lean_dec(v_unused_3926_);
v_unused_3927_ = lean_ctor_get(v_impl_3814_, 0);
lean_dec(v_unused_3927_);
v___x_3904_ = v_impl_3814_;
v_isShared_3905_ = v_isSharedCheck_3925_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_r_3900_);
lean_inc(v_v_3902_);
lean_inc(v_k_3901_);
lean_dec(v_impl_3814_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3925_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v_k_3906_; lean_object* v_v_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3921_; 
v_k_3906_ = lean_ctor_get(v_l_3899_, 1);
v_v_3907_ = lean_ctor_get(v_l_3899_, 2);
v_isSharedCheck_3921_ = !lean_is_exclusive(v_l_3899_);
if (v_isSharedCheck_3921_ == 0)
{
lean_object* v_unused_3922_; lean_object* v_unused_3923_; lean_object* v_unused_3924_; 
v_unused_3922_ = lean_ctor_get(v_l_3899_, 4);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_l_3899_, 3);
lean_dec(v_unused_3923_);
v_unused_3924_ = lean_ctor_get(v_l_3899_, 0);
lean_dec(v_unused_3924_);
v___x_3909_ = v_l_3899_;
v_isShared_3910_ = v_isSharedCheck_3921_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_v_3907_);
lean_inc(v_k_3906_);
lean_dec(v_l_3899_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3921_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3911_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3900_, 2);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 4, v_r_3900_);
lean_ctor_set(v___x_3909_, 3, v_r_3900_);
lean_ctor_set(v___x_3909_, 2, v_v_3666_);
lean_ctor_set(v___x_3909_, 1, v_k_3665_);
lean_ctor_set(v___x_3909_, 0, v___x_3815_);
v___x_3913_ = v___x_3909_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3920_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3920_, 3, v_r_3900_);
lean_ctor_set(v_reuseFailAlloc_3920_, 4, v_r_3900_);
v___x_3913_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3915_; 
lean_inc(v_r_3900_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 3, v_r_3900_);
lean_ctor_set(v___x_3904_, 0, v___x_3815_);
v___x_3915_ = v___x_3904_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v_k_3901_);
lean_ctor_set(v_reuseFailAlloc_3919_, 2, v_v_3902_);
lean_ctor_set(v_reuseFailAlloc_3919_, 3, v_r_3900_);
lean_ctor_set(v_reuseFailAlloc_3919_, 4, v_r_3900_);
v___x_3915_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
lean_object* v___x_3917_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 4, v___x_3915_);
lean_ctor_set(v___x_3670_, 3, v___x_3913_);
lean_ctor_set(v___x_3670_, 2, v_v_3907_);
lean_ctor_set(v___x_3670_, 1, v_k_3906_);
lean_ctor_set(v___x_3670_, 0, v___x_3911_);
v___x_3917_ = v___x_3670_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v_k_3906_);
lean_ctor_set(v_reuseFailAlloc_3918_, 2, v_v_3907_);
lean_ctor_set(v_reuseFailAlloc_3918_, 3, v___x_3913_);
lean_ctor_set(v_reuseFailAlloc_3918_, 4, v___x_3915_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
}
}
else
{
lean_object* v_r_3928_; 
v_r_3928_ = lean_ctor_get(v_impl_3814_, 4);
lean_inc(v_r_3928_);
if (lean_obj_tag(v_r_3928_) == 0)
{
lean_object* v_k_3929_; lean_object* v_v_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3941_; 
v_k_3929_ = lean_ctor_get(v_impl_3814_, 1);
v_v_3930_ = lean_ctor_get(v_impl_3814_, 2);
v_isSharedCheck_3941_ = !lean_is_exclusive(v_impl_3814_);
if (v_isSharedCheck_3941_ == 0)
{
lean_object* v_unused_3942_; lean_object* v_unused_3943_; lean_object* v_unused_3944_; 
v_unused_3942_ = lean_ctor_get(v_impl_3814_, 4);
lean_dec(v_unused_3942_);
v_unused_3943_ = lean_ctor_get(v_impl_3814_, 3);
lean_dec(v_unused_3943_);
v_unused_3944_ = lean_ctor_get(v_impl_3814_, 0);
lean_dec(v_unused_3944_);
v___x_3932_ = v_impl_3814_;
v_isShared_3933_ = v_isSharedCheck_3941_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_v_3930_);
lean_inc(v_k_3929_);
lean_dec(v_impl_3814_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3941_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3934_; lean_object* v___x_3936_; 
v___x_3934_ = lean_unsigned_to_nat(3u);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 4, v_l_3899_);
lean_ctor_set(v___x_3932_, 2, v_v_3666_);
lean_ctor_set(v___x_3932_, 1, v_k_3665_);
lean_ctor_set(v___x_3932_, 0, v___x_3815_);
v___x_3936_ = v___x_3932_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3940_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3940_, 3, v_l_3899_);
lean_ctor_set(v_reuseFailAlloc_3940_, 4, v_l_3899_);
v___x_3936_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
lean_object* v___x_3938_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 4, v_r_3928_);
lean_ctor_set(v___x_3670_, 3, v___x_3936_);
lean_ctor_set(v___x_3670_, 2, v_v_3930_);
lean_ctor_set(v___x_3670_, 1, v_k_3929_);
lean_ctor_set(v___x_3670_, 0, v___x_3934_);
v___x_3938_ = v___x_3670_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3934_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v_k_3929_);
lean_ctor_set(v_reuseFailAlloc_3939_, 2, v_v_3930_);
lean_ctor_set(v_reuseFailAlloc_3939_, 3, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3939_, 4, v_r_3928_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
else
{
lean_object* v___x_3945_; lean_object* v___x_3947_; 
v___x_3945_ = lean_unsigned_to_nat(2u);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 4, v_impl_3814_);
lean_ctor_set(v___x_3670_, 3, v_r_3928_);
lean_ctor_set(v___x_3670_, 0, v___x_3945_);
v___x_3947_ = v___x_3670_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3948_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3948_, 3, v_r_3928_);
lean_ctor_set(v_reuseFailAlloc_3948_, 4, v_impl_3814_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
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
lean_object* v___x_3950_; lean_object* v___x_3951_; 
lean_dec_ref(v_cmp_3660_);
v___x_3950_ = lean_unsigned_to_nat(1u);
v___x_3951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
lean_ctor_set(v___x_3951_, 1, v_k_3661_);
lean_ctor_set(v___x_3951_, 2, v_v_3662_);
lean_ctor_set(v___x_3951_, 3, v_t_3663_);
lean_ctor_set(v___x_3951_, 4, v_t_3663_);
return v___x_3951_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_3952_, lean_object* v_t_3953_, lean_object* v_k_3954_){
_start:
{
if (lean_obj_tag(v_t_3953_) == 0)
{
lean_object* v_k_3955_; lean_object* v_v_3956_; lean_object* v_l_3957_; lean_object* v_r_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v_k_3955_ = lean_ctor_get(v_t_3953_, 1);
lean_inc_n(v_k_3955_, 2);
v_v_3956_ = lean_ctor_get(v_t_3953_, 2);
lean_inc(v_v_3956_);
v_l_3957_ = lean_ctor_get(v_t_3953_, 3);
lean_inc(v_l_3957_);
v_r_3958_ = lean_ctor_get(v_t_3953_, 4);
lean_inc(v_r_3958_);
lean_dec_ref_known(v_t_3953_, 5);
lean_inc_ref(v_cmp_3952_);
lean_inc(v_k_3954_);
v___x_3959_ = lean_apply_2(v_cmp_3952_, v_k_3954_, v_k_3955_);
v___x_3960_ = lean_unbox(v___x_3959_);
switch(v___x_3960_)
{
case 0:
{
lean_dec(v_r_3958_);
lean_dec(v_v_3956_);
lean_dec(v_k_3955_);
v_t_3953_ = v_l_3957_;
goto _start;
}
case 1:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
lean_dec(v_r_3958_);
lean_dec(v_l_3957_);
lean_dec(v_k_3954_);
lean_dec_ref(v_cmp_3952_);
v___x_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3962_, 0, v_k_3955_);
lean_ctor_set(v___x_3962_, 1, v_v_3956_);
v___x_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
return v___x_3963_;
}
default: 
{
lean_dec(v_l_3957_);
lean_dec(v_v_3956_);
lean_dec(v_k_3955_);
v_t_3953_ = v_r_3958_;
goto _start;
}
}
}
else
{
lean_object* v___x_3965_; 
lean_dec(v_k_3954_);
lean_dec_ref(v_cmp_3952_);
v___x_3965_ = lean_box(0);
return v___x_3965_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_cmp_3966_, lean_object* v_m_u2081_3967_, lean_object* v_init_3968_, lean_object* v_x_3969_){
_start:
{
if (lean_obj_tag(v_x_3969_) == 0)
{
lean_object* v_k_3970_; lean_object* v_l_3971_; lean_object* v_r_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v_k_3970_ = lean_ctor_get(v_x_3969_, 1);
lean_inc(v_k_3970_);
v_l_3971_ = lean_ctor_get(v_x_3969_, 3);
lean_inc(v_l_3971_);
v_r_3972_ = lean_ctor_get(v_x_3969_, 4);
lean_inc(v_r_3972_);
lean_dec_ref_known(v_x_3969_, 5);
lean_inc_n(v_m_u2081_3967_, 2);
lean_inc_ref_n(v_cmp_3966_, 2);
v___x_3973_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3966_, v_m_u2081_3967_, v_init_3968_, v_l_3971_);
v___x_3974_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3966_, v_m_u2081_3967_, v_k_3970_);
if (lean_obj_tag(v___x_3974_) == 0)
{
v_init_3968_ = v___x_3973_;
v_x_3969_ = v_r_3972_;
goto _start;
}
else
{
lean_object* v_val_3976_; lean_object* v_fst_3977_; lean_object* v_snd_3978_; lean_object* v_impl_3979_; 
v_val_3976_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_val_3976_);
lean_dec_ref_known(v___x_3974_, 1);
v_fst_3977_ = lean_ctor_get(v_val_3976_, 0);
lean_inc(v_fst_3977_);
v_snd_3978_ = lean_ctor_get(v_val_3976_, 1);
lean_inc(v_snd_3978_);
lean_dec(v_val_3976_);
lean_inc_ref(v_cmp_3966_);
v_impl_3979_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3966_, v_fst_3977_, v_snd_3978_, v___x_3973_);
v_init_3968_ = v_impl_3979_;
v_x_3969_ = v_r_3972_;
goto _start;
}
}
else
{
lean_dec(v_m_u2081_3967_);
lean_dec_ref(v_cmp_3966_);
return v_init_3968_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(lean_object* v_cmp_3981_, lean_object* v_m_u2081_3982_, lean_object* v_m_u2082_3983_){
_start:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3984_ = lean_box(1);
v___x_3985_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3981_, v_m_u2081_3982_, v___x_3984_, v_m_u2082_3983_);
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(lean_object* v_cmp_3986_, lean_object* v_m_u2082_3987_, lean_object* v_t_3988_){
_start:
{
if (lean_obj_tag(v_t_3988_) == 0)
{
lean_object* v_k_3989_; lean_object* v_v_3990_; lean_object* v_l_3991_; lean_object* v_r_3992_; uint8_t v___x_3993_; 
v_k_3989_ = lean_ctor_get(v_t_3988_, 1);
lean_inc_n(v_k_3989_, 2);
v_v_3990_ = lean_ctor_get(v_t_3988_, 2);
lean_inc(v_v_3990_);
v_l_3991_ = lean_ctor_get(v_t_3988_, 3);
lean_inc(v_l_3991_);
v_r_3992_ = lean_ctor_get(v_t_3988_, 4);
lean_inc(v_r_3992_);
lean_dec_ref_known(v_t_3988_, 5);
lean_inc(v_m_u2082_3987_);
lean_inc_ref(v_cmp_3986_);
v___x_3993_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3986_, v_k_3989_, v_m_u2082_3987_);
if (v___x_3993_ == 0)
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
lean_dec(v_v_3990_);
lean_dec(v_k_3989_);
lean_inc(v_m_u2082_3987_);
lean_inc_ref(v_cmp_3986_);
v___x_3994_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3986_, v_m_u2082_3987_, v_l_3991_);
v___x_3995_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3986_, v_m_u2082_3987_, v_r_3992_);
v___x_3996_ = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(v___x_3994_, v___x_3995_);
return v___x_3996_;
}
else
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
lean_inc(v_m_u2082_3987_);
lean_inc_ref(v_cmp_3986_);
v___x_3997_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3986_, v_m_u2082_3987_, v_l_3991_);
v___x_3998_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3986_, v_m_u2082_3987_, v_r_3992_);
v___x_3999_ = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(v_k_3989_, v_v_3990_, v___x_3997_, v___x_3998_);
return v___x_3999_;
}
}
else
{
lean_dec(v_m_u2082_3987_);
lean_dec_ref(v_cmp_3986_);
return v_t_3988_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(lean_object* v_cmp_4000_, lean_object* v_m_u2081_4001_, lean_object* v_m_u2082_4002_){
_start:
{
lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4010_; 
if (lean_obj_tag(v_m_u2081_4001_) == 0)
{
lean_object* v_size_4013_; 
v_size_4013_ = lean_ctor_get(v_m_u2081_4001_, 0);
lean_inc(v_size_4013_);
v___y_4010_ = v_size_4013_;
goto v___jp_4009_;
}
else
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_unsigned_to_nat(0u);
v___y_4010_ = v___x_4014_;
goto v___jp_4009_;
}
v___jp_4003_:
{
uint8_t v___x_4006_; 
v___x_4006_ = lean_nat_dec_le(v___y_4004_, v___y_4005_);
lean_dec(v___y_4005_);
lean_dec(v___y_4004_);
if (v___x_4006_ == 0)
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(v_cmp_4000_, v_m_u2081_4001_, v_m_u2082_4002_);
return v___x_4007_;
}
else
{
lean_object* v___x_4008_; 
v___x_4008_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_4000_, v_m_u2082_4002_, v_m_u2081_4001_);
return v___x_4008_;
}
}
v___jp_4009_:
{
if (lean_obj_tag(v_m_u2082_4002_) == 0)
{
lean_object* v_size_4011_; 
v_size_4011_ = lean_ctor_get(v_m_u2082_4002_, 0);
lean_inc(v_size_4011_);
v___y_4004_ = v___y_4010_;
v___y_4005_ = v_size_4011_;
goto v___jp_4003_;
}
else
{
lean_object* v___x_4012_; 
v___x_4012_ = lean_unsigned_to_nat(0u);
v___y_4004_ = v___y_4010_;
v___y_4005_ = v___x_4012_;
goto v___jp_4003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter___redArg(lean_object* v_cmp_4015_, lean_object* v_t_u2081_4016_, lean_object* v_t_u2082_4017_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_4015_, v_t_u2081_4016_, v_t_u2082_4017_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter(lean_object* v_00_u03b1_4019_, lean_object* v_00_u03b2_4020_, lean_object* v_cmp_4021_, lean_object* v_t_u2081_4022_, lean_object* v_t_u2082_4023_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_4021_, v_t_u2081_4022_, v_t_u2082_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0(lean_object* v_00_u03b1_4025_, lean_object* v_cmp_4026_, lean_object* v_00_u03b2_4027_, lean_object* v_m_u2081_4028_, lean_object* v_m_u2082_4029_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_4026_, v_m_u2081_4028_, v_m_u2082_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0(lean_object* v_00_u03b1_4031_, lean_object* v_cmp_4032_, lean_object* v_00_u03b2_4033_, lean_object* v_m_u2081_4034_, lean_object* v_m_u2082_4035_){
_start:
{
lean_object* v___x_4036_; 
v___x_4036_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(v_cmp_4032_, v_m_u2081_4034_, v_m_u2082_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1(lean_object* v_00_u03b1_4037_, lean_object* v_00_u03b2_4038_, lean_object* v_cmp_4039_, lean_object* v_m_u2082_4040_, lean_object* v_t_4041_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_4039_, v_m_u2082_4040_, v_t_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4043_, lean_object* v_cmp_4044_, lean_object* v_00_u03b2_4045_, lean_object* v_t_4046_, lean_object* v_k_4047_){
_start:
{
lean_object* v___x_4048_; 
v___x_4048_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(v_cmp_4044_, v_t_4046_, v_k_4047_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_4049_, lean_object* v_cmp_4050_, lean_object* v_00_u03b2_4051_, lean_object* v_k_4052_, lean_object* v_v_4053_, lean_object* v_t_4054_, lean_object* v_hl_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_4050_, v_k_4052_, v_v_4053_, v_t_4054_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3___redArg(lean_object* v_cmp_4057_, lean_object* v_m_u2081_4058_, lean_object* v_init_4059_, lean_object* v_t_4060_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4057_, v_m_u2081_4058_, v_init_4059_, v_t_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4062_, lean_object* v_00_u03b2_4063_, lean_object* v_cmp_4064_, lean_object* v_m_u2081_4065_, lean_object* v_init_4066_, lean_object* v_t_4067_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4064_, v_m_u2081_4065_, v_init_4066_, v_t_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b1_4069_, lean_object* v_00_u03b2_4070_, lean_object* v_cmp_4071_, lean_object* v_m_u2081_4072_, lean_object* v_init_4073_, lean_object* v_x_4074_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4071_, v_m_u2081_4072_, v_init_4073_, v_x_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter___redArg(lean_object* v_cmp_4076_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_4077_, 0, lean_box(0));
lean_closure_set(v___x_4077_, 1, lean_box(0));
lean_closure_set(v___x_4077_, 2, v_cmp_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter(lean_object* v_00_u03b1_4078_, lean_object* v_00_u03b2_4079_, lean_object* v_cmp_4080_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_4081_, 0, lean_box(0));
lean_closure_set(v___x_4081_, 1, lean_box(0));
lean_closure_set(v___x_4081_, 2, v_cmp_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_beq___redArg(lean_object* v_cmp_4082_, lean_object* v_inst_4083_, lean_object* v_t_u2081_4084_, lean_object* v_t_u2082_4085_){
_start:
{
uint8_t v___x_4086_; 
v___x_4086_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_4082_, v_inst_4083_, v_t_u2081_4084_, v_t_u2082_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___redArg___boxed(lean_object* v_cmp_4087_, lean_object* v_inst_4088_, lean_object* v_t_u2081_4089_, lean_object* v_t_u2082_4090_){
_start:
{
uint8_t v_res_4091_; lean_object* v_r_4092_; 
v_res_4091_ = l_Std_DTreeMap_Raw_beq___redArg(v_cmp_4087_, v_inst_4088_, v_t_u2081_4089_, v_t_u2082_4090_);
v_r_4092_ = lean_box(v_res_4091_);
return v_r_4092_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_beq(lean_object* v_00_u03b1_4093_, lean_object* v_00_u03b2_4094_, lean_object* v_cmp_4095_, lean_object* v_inst_4096_, lean_object* v_inst_4097_, lean_object* v_t_u2081_4098_, lean_object* v_t_u2082_4099_){
_start:
{
uint8_t v___x_4100_; 
v___x_4100_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_4095_, v_inst_4097_, v_t_u2081_4098_, v_t_u2082_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___boxed(lean_object* v_00_u03b1_4101_, lean_object* v_00_u03b2_4102_, lean_object* v_cmp_4103_, lean_object* v_inst_4104_, lean_object* v_inst_4105_, lean_object* v_t_u2081_4106_, lean_object* v_t_u2082_4107_){
_start:
{
uint8_t v_res_4108_; lean_object* v_r_4109_; 
v_res_4108_ = l_Std_DTreeMap_Raw_beq(v_00_u03b1_4101_, v_00_u03b2_4102_, v_cmp_4103_, v_inst_4104_, v_inst_4105_, v_t_u2081_4106_, v_t_u2082_4107_);
v_r_4109_ = lean_box(v_res_4108_);
return v_r_4109_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp___redArg(lean_object* v_cmp_4110_, lean_object* v_inst_4111_){
_start:
{
lean_object* v___x_4112_; 
v___x_4112_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_4112_, 0, lean_box(0));
lean_closure_set(v___x_4112_, 1, lean_box(0));
lean_closure_set(v___x_4112_, 2, v_cmp_4110_);
lean_closure_set(v___x_4112_, 3, lean_box(0));
lean_closure_set(v___x_4112_, 4, v_inst_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp(lean_object* v_00_u03b1_4113_, lean_object* v_00_u03b2_4114_, lean_object* v_cmp_4115_, lean_object* v_inst_4116_, lean_object* v_inst_4117_){
_start:
{
lean_object* v___x_4118_; 
v___x_4118_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_4118_, 0, lean_box(0));
lean_closure_set(v___x_4118_, 1, lean_box(0));
lean_closure_set(v___x_4118_, 2, v_cmp_4115_);
lean_closure_set(v___x_4118_, 3, lean_box(0));
lean_closure_set(v___x_4118_, 4, v_inst_4117_);
return v___x_4118_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___redArg(lean_object* v_cmp_4119_, lean_object* v_inst_4120_, lean_object* v_t_u2081_4121_, lean_object* v_t_u2082_4122_){
_start:
{
uint8_t v___x_4123_; 
v___x_4123_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_4119_, v_inst_4120_, v_t_u2081_4121_, v_t_u2082_4122_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___redArg___boxed(lean_object* v_cmp_4124_, lean_object* v_inst_4125_, lean_object* v_t_u2081_4126_, lean_object* v_t_u2082_4127_){
_start:
{
uint8_t v_res_4128_; lean_object* v_r_4129_; 
v_res_4128_ = l_Std_DTreeMap_Raw_Const_beq___redArg(v_cmp_4124_, v_inst_4125_, v_t_u2081_4126_, v_t_u2082_4127_);
v_r_4129_ = lean_box(v_res_4128_);
return v_r_4129_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq(lean_object* v_00_u03b1_4130_, lean_object* v_cmp_4131_, lean_object* v_00_u03b2_4132_, lean_object* v_inst_4133_, lean_object* v_t_u2081_4134_, lean_object* v_t_u2082_4135_){
_start:
{
uint8_t v___x_4136_; 
v___x_4136_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_4131_, v_inst_4133_, v_t_u2081_4134_, v_t_u2082_4135_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___boxed(lean_object* v_00_u03b1_4137_, lean_object* v_cmp_4138_, lean_object* v_00_u03b2_4139_, lean_object* v_inst_4140_, lean_object* v_t_u2081_4141_, lean_object* v_t_u2082_4142_){
_start:
{
uint8_t v_res_4143_; lean_object* v_r_4144_; 
v_res_4143_ = l_Std_DTreeMap_Raw_Const_beq(v_00_u03b1_4137_, v_cmp_4138_, v_00_u03b2_4139_, v_inst_4140_, v_t_u2081_4141_, v_t_u2082_4142_);
v_r_4144_ = lean_box(v_res_4143_);
return v_r_4144_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(lean_object* v_cmp_4145_, lean_object* v_t_u2082_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v_t_4149_){
_start:
{
if (lean_obj_tag(v_t_4149_) == 0)
{
lean_object* v_k_4150_; lean_object* v_v_4151_; lean_object* v_l_4152_; lean_object* v_r_4153_; uint8_t v___x_4158_; 
v_k_4150_ = lean_ctor_get(v_t_4149_, 1);
lean_inc_n(v_k_4150_, 2);
v_v_4151_ = lean_ctor_get(v_t_4149_, 2);
lean_inc(v_v_4151_);
v_l_4152_ = lean_ctor_get(v_t_4149_, 3);
lean_inc(v_l_4152_);
v_r_4153_ = lean_ctor_get(v_t_4149_, 4);
lean_inc(v_r_4153_);
lean_dec_ref_known(v_t_4149_, 5);
lean_inc(v_t_u2082_4146_);
lean_inc_ref(v_cmp_4145_);
v___x_4158_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_4145_, v_k_4150_, v_t_u2082_4146_);
if (v___x_4158_ == 0)
{
uint8_t v___x_4159_; 
v___x_4159_ = lean_nat_dec_le(v___y_4147_, v___y_4148_);
if (v___x_4159_ == 0)
{
lean_dec(v_v_4151_);
lean_dec(v_k_4150_);
goto v___jp_4154_;
}
else
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
lean_inc(v_t_u2082_4146_);
lean_inc_ref(v_cmp_4145_);
v___x_4160_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4145_, v_t_u2082_4146_, v___y_4147_, v___y_4148_, v_l_4152_);
v___x_4161_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4145_, v_t_u2082_4146_, v___y_4147_, v___y_4148_, v_r_4153_);
v___x_4162_ = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(v_k_4150_, v_v_4151_, v___x_4160_, v___x_4161_);
return v___x_4162_;
}
}
else
{
lean_dec(v_v_4151_);
lean_dec(v_k_4150_);
goto v___jp_4154_;
}
v___jp_4154_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
lean_inc(v_t_u2082_4146_);
lean_inc_ref(v_cmp_4145_);
v___x_4155_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4145_, v_t_u2082_4146_, v___y_4147_, v___y_4148_, v_l_4152_);
v___x_4156_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4145_, v_t_u2082_4146_, v___y_4147_, v___y_4148_, v_r_4153_);
v___x_4157_ = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(v___x_4155_, v___x_4156_);
return v___x_4157_;
}
}
else
{
lean_dec(v_t_u2082_4146_);
lean_dec_ref(v_cmp_4145_);
return v_t_4149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg___boxed(lean_object* v_cmp_4163_, lean_object* v_t_u2082_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v_t_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4163_, v_t_u2082_4164_, v___y_4165_, v___y_4166_, v_t_4167_);
lean_dec(v___y_4166_);
lean_dec(v___y_4165_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(lean_object* v_cmp_4169_, lean_object* v_k_4170_, lean_object* v_t_4171_){
_start:
{
if (lean_obj_tag(v_t_4171_) == 0)
{
lean_object* v_k_4172_; lean_object* v_v_4173_; lean_object* v_l_4174_; lean_object* v_r_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4865_; 
v_k_4172_ = lean_ctor_get(v_t_4171_, 1);
v_v_4173_ = lean_ctor_get(v_t_4171_, 2);
v_l_4174_ = lean_ctor_get(v_t_4171_, 3);
v_r_4175_ = lean_ctor_get(v_t_4171_, 4);
v_isSharedCheck_4865_ = !lean_is_exclusive(v_t_4171_);
if (v_isSharedCheck_4865_ == 0)
{
lean_object* v_unused_4866_; 
v_unused_4866_ = lean_ctor_get(v_t_4171_, 0);
lean_dec(v_unused_4866_);
v___x_4177_ = v_t_4171_;
v_isShared_4178_ = v_isSharedCheck_4865_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_r_4175_);
lean_inc(v_l_4174_);
lean_inc(v_v_4173_);
lean_inc(v_k_4172_);
lean_dec(v_t_4171_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4865_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4179_; uint8_t v___x_4180_; 
lean_inc_ref(v_cmp_4169_);
lean_inc(v_k_4172_);
lean_inc(v_k_4170_);
v___x_4179_ = lean_apply_2(v_cmp_4169_, v_k_4170_, v_k_4172_);
v___x_4180_ = lean_unbox(v___x_4179_);
switch(v___x_4180_)
{
case 0:
{
lean_object* v___x_4181_; 
v___x_4181_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4169_, v_k_4170_, v_l_4174_);
if (lean_obj_tag(v___x_4181_) == 0)
{
if (lean_obj_tag(v_r_4175_) == 0)
{
lean_object* v_size_4182_; lean_object* v_size_4183_; lean_object* v_k_4184_; lean_object* v_v_4185_; lean_object* v_l_4186_; lean_object* v_r_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v_size_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_size_4182_);
v_size_4183_ = lean_ctor_get(v_r_4175_, 0);
v_k_4184_ = lean_ctor_get(v_r_4175_, 1);
v_v_4185_ = lean_ctor_get(v_r_4175_, 2);
v_l_4186_ = lean_ctor_get(v_r_4175_, 3);
lean_inc(v_l_4186_);
v_r_4187_ = lean_ctor_get(v_r_4175_, 4);
v___x_4188_ = lean_unsigned_to_nat(3u);
v___x_4189_ = lean_nat_mul(v___x_4188_, v_size_4182_);
v___x_4190_ = lean_nat_dec_lt(v___x_4189_, v_size_4183_);
lean_dec(v___x_4189_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4195_; 
lean_dec(v_l_4186_);
v___x_4191_ = lean_unsigned_to_nat(1u);
v___x_4192_ = lean_nat_add(v___x_4191_, v_size_4182_);
lean_dec(v_size_4182_);
v___x_4193_ = lean_nat_add(v___x_4192_, v_size_4183_);
lean_dec(v___x_4192_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 3, v___x_4181_);
lean_ctor_set(v___x_4177_, 0, v___x_4193_);
v___x_4195_ = v___x_4177_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4193_);
lean_ctor_set(v_reuseFailAlloc_4196_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4196_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4196_, 3, v___x_4181_);
lean_ctor_set(v_reuseFailAlloc_4196_, 4, v_r_4175_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
else
{
lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4266_; 
lean_inc(v_r_4187_);
lean_inc(v_v_4185_);
lean_inc(v_k_4184_);
lean_inc(v_size_4183_);
v_isSharedCheck_4266_ = !lean_is_exclusive(v_r_4175_);
if (v_isSharedCheck_4266_ == 0)
{
lean_object* v_unused_4267_; lean_object* v_unused_4268_; lean_object* v_unused_4269_; lean_object* v_unused_4270_; lean_object* v_unused_4271_; 
v_unused_4267_ = lean_ctor_get(v_r_4175_, 4);
lean_dec(v_unused_4267_);
v_unused_4268_ = lean_ctor_get(v_r_4175_, 3);
lean_dec(v_unused_4268_);
v_unused_4269_ = lean_ctor_get(v_r_4175_, 2);
lean_dec(v_unused_4269_);
v_unused_4270_ = lean_ctor_get(v_r_4175_, 1);
lean_dec(v_unused_4270_);
v_unused_4271_ = lean_ctor_get(v_r_4175_, 0);
lean_dec(v_unused_4271_);
v___x_4198_ = v_r_4175_;
v_isShared_4199_ = v_isSharedCheck_4266_;
goto v_resetjp_4197_;
}
else
{
lean_dec(v_r_4175_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4266_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
if (lean_obj_tag(v_l_4186_) == 0)
{
if (lean_obj_tag(v_r_4187_) == 0)
{
lean_object* v_size_4200_; lean_object* v_k_4201_; lean_object* v_v_4202_; lean_object* v_l_4203_; lean_object* v_r_4204_; lean_object* v_size_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; uint8_t v___x_4208_; 
v_size_4200_ = lean_ctor_get(v_l_4186_, 0);
v_k_4201_ = lean_ctor_get(v_l_4186_, 1);
v_v_4202_ = lean_ctor_get(v_l_4186_, 2);
v_l_4203_ = lean_ctor_get(v_l_4186_, 3);
v_r_4204_ = lean_ctor_get(v_l_4186_, 4);
v_size_4205_ = lean_ctor_get(v_r_4187_, 0);
v___x_4206_ = lean_unsigned_to_nat(2u);
v___x_4207_ = lean_nat_mul(v___x_4206_, v_size_4205_);
v___x_4208_ = lean_nat_dec_lt(v_size_4200_, v___x_4207_);
lean_dec(v___x_4207_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4237_; 
lean_inc(v_r_4204_);
lean_inc(v_l_4203_);
lean_inc(v_v_4202_);
lean_inc(v_k_4201_);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_l_4186_);
if (v_isSharedCheck_4237_ == 0)
{
lean_object* v_unused_4238_; lean_object* v_unused_4239_; lean_object* v_unused_4240_; lean_object* v_unused_4241_; lean_object* v_unused_4242_; 
v_unused_4238_ = lean_ctor_get(v_l_4186_, 4);
lean_dec(v_unused_4238_);
v_unused_4239_ = lean_ctor_get(v_l_4186_, 3);
lean_dec(v_unused_4239_);
v_unused_4240_ = lean_ctor_get(v_l_4186_, 2);
lean_dec(v_unused_4240_);
v_unused_4241_ = lean_ctor_get(v_l_4186_, 1);
lean_dec(v_unused_4241_);
v_unused_4242_ = lean_ctor_get(v_l_4186_, 0);
lean_dec(v_unused_4242_);
v___x_4210_ = v_l_4186_;
v_isShared_4211_ = v_isSharedCheck_4237_;
goto v_resetjp_4209_;
}
else
{
lean_dec(v_l_4186_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4237_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4227_; 
v___x_4212_ = lean_unsigned_to_nat(1u);
v___x_4213_ = lean_nat_add(v___x_4212_, v_size_4182_);
lean_dec(v_size_4182_);
v___x_4214_ = lean_nat_add(v___x_4213_, v_size_4183_);
lean_dec(v_size_4183_);
if (lean_obj_tag(v_l_4203_) == 0)
{
lean_object* v_size_4235_; 
v_size_4235_ = lean_ctor_get(v_l_4203_, 0);
lean_inc(v_size_4235_);
v___y_4227_ = v_size_4235_;
goto v___jp_4226_;
}
else
{
lean_object* v___x_4236_; 
v___x_4236_ = lean_unsigned_to_nat(0u);
v___y_4227_ = v___x_4236_;
goto v___jp_4226_;
}
v___jp_4215_:
{
lean_object* v___x_4219_; lean_object* v___x_4221_; 
v___x_4219_ = lean_nat_add(v___y_4216_, v___y_4218_);
lean_dec(v___y_4218_);
lean_dec(v___y_4216_);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 4, v_r_4187_);
lean_ctor_set(v___x_4210_, 3, v_r_4204_);
lean_ctor_set(v___x_4210_, 2, v_v_4185_);
lean_ctor_set(v___x_4210_, 1, v_k_4184_);
lean_ctor_set(v___x_4210_, 0, v___x_4219_);
v___x_4221_ = v___x_4210_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4219_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_k_4184_);
lean_ctor_set(v_reuseFailAlloc_4225_, 2, v_v_4185_);
lean_ctor_set(v_reuseFailAlloc_4225_, 3, v_r_4204_);
lean_ctor_set(v_reuseFailAlloc_4225_, 4, v_r_4187_);
v___x_4221_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
lean_object* v___x_4223_; 
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 4, v___x_4221_);
lean_ctor_set(v___x_4198_, 3, v___y_4217_);
lean_ctor_set(v___x_4198_, 2, v_v_4202_);
lean_ctor_set(v___x_4198_, 1, v_k_4201_);
lean_ctor_set(v___x_4198_, 0, v___x_4214_);
v___x_4223_ = v___x_4198_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4214_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v_k_4201_);
lean_ctor_set(v_reuseFailAlloc_4224_, 2, v_v_4202_);
lean_ctor_set(v_reuseFailAlloc_4224_, 3, v___y_4217_);
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
v___jp_4226_:
{
lean_object* v___x_4228_; lean_object* v___x_4230_; 
v___x_4228_ = lean_nat_add(v___x_4213_, v___y_4227_);
lean_dec(v___y_4227_);
lean_dec(v___x_4213_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 4, v_l_4203_);
lean_ctor_set(v___x_4177_, 3, v___x_4181_);
lean_ctor_set(v___x_4177_, 0, v___x_4228_);
v___x_4230_ = v___x_4177_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4228_);
lean_ctor_set(v_reuseFailAlloc_4234_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4234_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4234_, 3, v___x_4181_);
lean_ctor_set(v_reuseFailAlloc_4234_, 4, v_l_4203_);
v___x_4230_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
lean_object* v___x_4231_; 
v___x_4231_ = lean_nat_add(v___x_4212_, v_size_4205_);
if (lean_obj_tag(v_r_4204_) == 0)
{
lean_object* v_size_4232_; 
v_size_4232_ = lean_ctor_get(v_r_4204_, 0);
lean_inc(v_size_4232_);
v___y_4216_ = v___x_4231_;
v___y_4217_ = v___x_4230_;
v___y_4218_ = v_size_4232_;
goto v___jp_4215_;
}
else
{
lean_object* v___x_4233_; 
v___x_4233_ = lean_unsigned_to_nat(0u);
v___y_4216_ = v___x_4231_;
v___y_4217_ = v___x_4230_;
v___y_4218_ = v___x_4233_;
goto v___jp_4215_;
}
}
}
}
}
else
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4248_; 
lean_del_object(v___x_4177_);
v___x_4243_ = lean_unsigned_to_nat(1u);
v___x_4244_ = lean_nat_add(v___x_4243_, v_size_4182_);
lean_dec(v_size_4182_);
v___x_4245_ = lean_nat_add(v___x_4244_, v_size_4183_);
lean_dec(v_size_4183_);
v___x_4246_ = lean_nat_add(v___x_4244_, v_size_4200_);
lean_dec(v___x_4244_);
lean_inc_ref(v___x_4181_);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 4, v_l_4186_);
lean_ctor_set(v___x_4198_, 3, v___x_4181_);
lean_ctor_set(v___x_4198_, 2, v_v_4173_);
lean_ctor_set(v___x_4198_, 1, v_k_4172_);
lean_ctor_set(v___x_4198_, 0, v___x_4246_);
v___x_4248_ = v___x_4198_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4246_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4261_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4261_, 3, v___x_4181_);
lean_ctor_set(v_reuseFailAlloc_4261_, 4, v_l_4186_);
v___x_4248_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4255_ == 0)
{
lean_object* v_unused_4256_; lean_object* v_unused_4257_; lean_object* v_unused_4258_; lean_object* v_unused_4259_; lean_object* v_unused_4260_; 
v_unused_4256_ = lean_ctor_get(v___x_4181_, 4);
lean_dec(v_unused_4256_);
v_unused_4257_ = lean_ctor_get(v___x_4181_, 3);
lean_dec(v_unused_4257_);
v_unused_4258_ = lean_ctor_get(v___x_4181_, 2);
lean_dec(v_unused_4258_);
v_unused_4259_ = lean_ctor_get(v___x_4181_, 1);
lean_dec(v_unused_4259_);
v_unused_4260_ = lean_ctor_get(v___x_4181_, 0);
lean_dec(v_unused_4260_);
v___x_4250_ = v___x_4181_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_dec(v___x_4181_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 4, v_r_4187_);
lean_ctor_set(v___x_4250_, 3, v___x_4248_);
lean_ctor_set(v___x_4250_, 2, v_v_4185_);
lean_ctor_set(v___x_4250_, 1, v_k_4184_);
lean_ctor_set(v___x_4250_, 0, v___x_4245_);
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4245_);
lean_ctor_set(v_reuseFailAlloc_4254_, 1, v_k_4184_);
lean_ctor_set(v_reuseFailAlloc_4254_, 2, v_v_4185_);
lean_ctor_set(v_reuseFailAlloc_4254_, 3, v___x_4248_);
lean_ctor_set(v_reuseFailAlloc_4254_, 4, v_r_4187_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
}
else
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
lean_dec_ref_known(v_l_4186_, 5);
lean_del_object(v___x_4198_);
lean_dec(v_v_4185_);
lean_dec(v_k_4184_);
lean_dec(v_size_4183_);
lean_dec(v_size_4182_);
lean_dec_ref_known(v___x_4181_, 5);
lean_del_object(v___x_4177_);
lean_dec(v_v_4173_);
lean_dec(v_k_4172_);
v___x_4262_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7);
v___x_4263_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4262_);
return v___x_4263_;
}
}
else
{
lean_object* v___x_4264_; lean_object* v___x_4265_; 
lean_del_object(v___x_4198_);
lean_dec(v_r_4187_);
lean_dec(v_v_4185_);
lean_dec(v_k_4184_);
lean_dec(v_size_4183_);
lean_dec(v_size_4182_);
lean_dec_ref_known(v___x_4181_, 5);
lean_del_object(v___x_4177_);
lean_dec(v_v_4173_);
lean_dec(v_k_4172_);
v___x_4264_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8);
v___x_4265_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4264_);
return v___x_4265_;
}
}
}
}
else
{
lean_object* v_size_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4276_; 
v_size_4272_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_size_4272_);
v___x_4273_ = lean_unsigned_to_nat(1u);
v___x_4274_ = lean_nat_add(v___x_4273_, v_size_4272_);
lean_dec(v_size_4272_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 3, v___x_4181_);
lean_ctor_set(v___x_4177_, 0, v___x_4274_);
v___x_4276_ = v___x_4177_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
lean_ctor_set(v_reuseFailAlloc_4277_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4277_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4277_, 3, v___x_4181_);
lean_ctor_set(v_reuseFailAlloc_4277_, 4, v_r_4175_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
else
{
if (lean_obj_tag(v_r_4175_) == 0)
{
lean_object* v_l_4278_; 
v_l_4278_ = lean_ctor_get(v_r_4175_, 3);
lean_inc(v_l_4278_);
if (lean_obj_tag(v_l_4278_) == 0)
{
lean_object* v_r_4279_; 
v_r_4279_ = lean_ctor_get(v_r_4175_, 4);
lean_inc(v_r_4279_);
if (lean_obj_tag(v_r_4279_) == 0)
{
lean_object* v_size_4280_; lean_object* v_k_4281_; lean_object* v_v_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4296_; 
v_size_4280_ = lean_ctor_get(v_r_4175_, 0);
v_k_4281_ = lean_ctor_get(v_r_4175_, 1);
v_v_4282_ = lean_ctor_get(v_r_4175_, 2);
v_isSharedCheck_4296_ = !lean_is_exclusive(v_r_4175_);
if (v_isSharedCheck_4296_ == 0)
{
lean_object* v_unused_4297_; lean_object* v_unused_4298_; 
v_unused_4297_ = lean_ctor_get(v_r_4175_, 4);
lean_dec(v_unused_4297_);
v_unused_4298_ = lean_ctor_get(v_r_4175_, 3);
lean_dec(v_unused_4298_);
v___x_4284_ = v_r_4175_;
v_isShared_4285_ = v_isSharedCheck_4296_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_v_4282_);
lean_inc(v_k_4281_);
lean_inc(v_size_4280_);
lean_dec(v_r_4175_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4296_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v_size_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4291_; 
v_size_4286_ = lean_ctor_get(v_l_4278_, 0);
v___x_4287_ = lean_unsigned_to_nat(1u);
v___x_4288_ = lean_nat_add(v___x_4287_, v_size_4280_);
lean_dec(v_size_4280_);
v___x_4289_ = lean_nat_add(v___x_4287_, v_size_4286_);
if (v_isShared_4285_ == 0)
{
lean_ctor_set(v___x_4284_, 4, v_l_4278_);
lean_ctor_set(v___x_4284_, 3, v___x_4181_);
lean_ctor_set(v___x_4284_, 2, v_v_4173_);
lean_ctor_set(v___x_4284_, 1, v_k_4172_);
lean_ctor_set(v___x_4284_, 0, v___x_4289_);
v___x_4291_ = v___x_4284_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4289_);
lean_ctor_set(v_reuseFailAlloc_4295_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4295_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4295_, 3, v___x_4181_);
lean_ctor_set(v_reuseFailAlloc_4295_, 4, v_l_4278_);
v___x_4291_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
lean_object* v___x_4293_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 4, v_r_4279_);
lean_ctor_set(v___x_4177_, 3, v___x_4291_);
lean_ctor_set(v___x_4177_, 2, v_v_4282_);
lean_ctor_set(v___x_4177_, 1, v_k_4281_);
lean_ctor_set(v___x_4177_, 0, v___x_4288_);
v___x_4293_ = v___x_4177_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4288_);
lean_ctor_set(v_reuseFailAlloc_4294_, 1, v_k_4281_);
lean_ctor_set(v_reuseFailAlloc_4294_, 2, v_v_4282_);
lean_ctor_set(v_reuseFailAlloc_4294_, 3, v___x_4291_);
lean_ctor_set(v_reuseFailAlloc_4294_, 4, v_r_4279_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
else
{
lean_object* v_k_4299_; lean_object* v_v_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4324_; 
v_k_4299_ = lean_ctor_get(v_r_4175_, 1);
v_v_4300_ = lean_ctor_get(v_r_4175_, 2);
v_isSharedCheck_4324_ = !lean_is_exclusive(v_r_4175_);
if (v_isSharedCheck_4324_ == 0)
{
lean_object* v_unused_4325_; lean_object* v_unused_4326_; lean_object* v_unused_4327_; 
v_unused_4325_ = lean_ctor_get(v_r_4175_, 4);
lean_dec(v_unused_4325_);
v_unused_4326_ = lean_ctor_get(v_r_4175_, 3);
lean_dec(v_unused_4326_);
v_unused_4327_ = lean_ctor_get(v_r_4175_, 0);
lean_dec(v_unused_4327_);
v___x_4302_ = v_r_4175_;
v_isShared_4303_ = v_isSharedCheck_4324_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_v_4300_);
lean_inc(v_k_4299_);
lean_dec(v_r_4175_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4324_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v_k_4304_; lean_object* v_v_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4320_; 
v_k_4304_ = lean_ctor_get(v_l_4278_, 1);
v_v_4305_ = lean_ctor_get(v_l_4278_, 2);
v_isSharedCheck_4320_ = !lean_is_exclusive(v_l_4278_);
if (v_isSharedCheck_4320_ == 0)
{
lean_object* v_unused_4321_; lean_object* v_unused_4322_; lean_object* v_unused_4323_; 
v_unused_4321_ = lean_ctor_get(v_l_4278_, 4);
lean_dec(v_unused_4321_);
v_unused_4322_ = lean_ctor_get(v_l_4278_, 3);
lean_dec(v_unused_4322_);
v_unused_4323_ = lean_ctor_get(v_l_4278_, 0);
lean_dec(v_unused_4323_);
v___x_4307_ = v_l_4278_;
v_isShared_4308_ = v_isSharedCheck_4320_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_v_4305_);
lean_inc(v_k_4304_);
lean_dec(v_l_4278_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4320_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4312_; 
v___x_4309_ = lean_unsigned_to_nat(3u);
v___x_4310_ = lean_unsigned_to_nat(1u);
if (v_isShared_4308_ == 0)
{
lean_ctor_set(v___x_4307_, 4, v_r_4279_);
lean_ctor_set(v___x_4307_, 3, v_r_4279_);
lean_ctor_set(v___x_4307_, 2, v_v_4173_);
lean_ctor_set(v___x_4307_, 1, v_k_4172_);
lean_ctor_set(v___x_4307_, 0, v___x_4310_);
v___x_4312_ = v___x_4307_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4310_);
lean_ctor_set(v_reuseFailAlloc_4319_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4319_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4319_, 3, v_r_4279_);
lean_ctor_set(v_reuseFailAlloc_4319_, 4, v_r_4279_);
v___x_4312_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
lean_object* v___x_4314_; 
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 3, v_r_4279_);
lean_ctor_set(v___x_4302_, 0, v___x_4310_);
v___x_4314_ = v___x_4302_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v___x_4310_);
lean_ctor_set(v_reuseFailAlloc_4318_, 1, v_k_4299_);
lean_ctor_set(v_reuseFailAlloc_4318_, 2, v_v_4300_);
lean_ctor_set(v_reuseFailAlloc_4318_, 3, v_r_4279_);
lean_ctor_set(v_reuseFailAlloc_4318_, 4, v_r_4279_);
v___x_4314_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
lean_object* v___x_4316_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 4, v___x_4314_);
lean_ctor_set(v___x_4177_, 3, v___x_4312_);
lean_ctor_set(v___x_4177_, 2, v_v_4305_);
lean_ctor_set(v___x_4177_, 1, v_k_4304_);
lean_ctor_set(v___x_4177_, 0, v___x_4309_);
v___x_4316_ = v___x_4177_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4309_);
lean_ctor_set(v_reuseFailAlloc_4317_, 1, v_k_4304_);
lean_ctor_set(v_reuseFailAlloc_4317_, 2, v_v_4305_);
lean_ctor_set(v_reuseFailAlloc_4317_, 3, v___x_4312_);
lean_ctor_set(v_reuseFailAlloc_4317_, 4, v___x_4314_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_4328_; 
v_r_4328_ = lean_ctor_get(v_r_4175_, 4);
lean_inc(v_r_4328_);
if (lean_obj_tag(v_r_4328_) == 0)
{
lean_object* v_k_4329_; lean_object* v_v_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4342_; 
v_k_4329_ = lean_ctor_get(v_r_4175_, 1);
v_v_4330_ = lean_ctor_get(v_r_4175_, 2);
v_isSharedCheck_4342_ = !lean_is_exclusive(v_r_4175_);
if (v_isSharedCheck_4342_ == 0)
{
lean_object* v_unused_4343_; lean_object* v_unused_4344_; lean_object* v_unused_4345_; 
v_unused_4343_ = lean_ctor_get(v_r_4175_, 4);
lean_dec(v_unused_4343_);
v_unused_4344_ = lean_ctor_get(v_r_4175_, 3);
lean_dec(v_unused_4344_);
v_unused_4345_ = lean_ctor_get(v_r_4175_, 0);
lean_dec(v_unused_4345_);
v___x_4332_ = v_r_4175_;
v_isShared_4333_ = v_isSharedCheck_4342_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_v_4330_);
lean_inc(v_k_4329_);
lean_dec(v_r_4175_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4342_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4337_; 
v___x_4334_ = lean_unsigned_to_nat(3u);
v___x_4335_ = lean_unsigned_to_nat(1u);
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 4, v_l_4278_);
lean_ctor_set(v___x_4332_, 2, v_v_4173_);
lean_ctor_set(v___x_4332_, 1, v_k_4172_);
lean_ctor_set(v___x_4332_, 0, v___x_4335_);
v___x_4337_ = v___x_4332_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v___x_4335_);
lean_ctor_set(v_reuseFailAlloc_4341_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4341_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4341_, 3, v_l_4278_);
lean_ctor_set(v_reuseFailAlloc_4341_, 4, v_l_4278_);
v___x_4337_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
lean_object* v___x_4339_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 4, v_r_4328_);
lean_ctor_set(v___x_4177_, 3, v___x_4337_);
lean_ctor_set(v___x_4177_, 2, v_v_4330_);
lean_ctor_set(v___x_4177_, 1, v_k_4329_);
lean_ctor_set(v___x_4177_, 0, v___x_4334_);
v___x_4339_ = v___x_4177_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4334_);
lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_k_4329_);
lean_ctor_set(v_reuseFailAlloc_4340_, 2, v_v_4330_);
lean_ctor_set(v_reuseFailAlloc_4340_, 3, v___x_4337_);
lean_ctor_set(v_reuseFailAlloc_4340_, 4, v_r_4328_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
else
{
lean_object* v___x_4346_; lean_object* v___x_4348_; 
v___x_4346_ = lean_unsigned_to_nat(2u);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 3, v_r_4328_);
lean_ctor_set(v___x_4177_, 0, v___x_4346_);
v___x_4348_ = v___x_4177_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4346_);
lean_ctor_set(v_reuseFailAlloc_4349_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4349_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4349_, 3, v_r_4328_);
lean_ctor_set(v_reuseFailAlloc_4349_, 4, v_r_4175_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
else
{
lean_object* v___x_4350_; lean_object* v___x_4352_; 
v___x_4350_ = lean_unsigned_to_nat(1u);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 3, v_r_4175_);
lean_ctor_set(v___x_4177_, 0, v___x_4350_);
v___x_4352_ = v___x_4177_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4350_);
lean_ctor_set(v_reuseFailAlloc_4353_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4353_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4353_, 3, v_r_4175_);
lean_ctor_set(v_reuseFailAlloc_4353_, 4, v_r_4175_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
case 1:
{
lean_del_object(v___x_4177_);
lean_dec(v_v_4173_);
lean_dec(v_k_4172_);
lean_dec(v_k_4170_);
lean_dec_ref(v_cmp_4169_);
if (lean_obj_tag(v_l_4174_) == 0)
{
if (lean_obj_tag(v_r_4175_) == 0)
{
lean_object* v_size_4354_; lean_object* v_k_4355_; lean_object* v_v_4356_; lean_object* v_l_4357_; lean_object* v_r_4358_; lean_object* v_size_4359_; lean_object* v_k_4360_; lean_object* v_v_4361_; lean_object* v_l_4362_; lean_object* v_r_4363_; uint8_t v___x_4364_; 
v_size_4354_ = lean_ctor_get(v_l_4174_, 0);
v_k_4355_ = lean_ctor_get(v_l_4174_, 1);
v_v_4356_ = lean_ctor_get(v_l_4174_, 2);
v_l_4357_ = lean_ctor_get(v_l_4174_, 3);
v_r_4358_ = lean_ctor_get(v_l_4174_, 4);
lean_inc(v_r_4358_);
v_size_4359_ = lean_ctor_get(v_r_4175_, 0);
v_k_4360_ = lean_ctor_get(v_r_4175_, 1);
v_v_4361_ = lean_ctor_get(v_r_4175_, 2);
v_l_4362_ = lean_ctor_get(v_r_4175_, 3);
lean_inc(v_l_4362_);
v_r_4363_ = lean_ctor_get(v_r_4175_, 4);
v___x_4364_ = lean_nat_dec_lt(v_size_4354_, v_size_4359_);
if (v___x_4364_ == 0)
{
lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4516_; 
lean_inc(v_l_4357_);
lean_inc(v_v_4356_);
lean_inc(v_k_4355_);
v_isSharedCheck_4516_ = !lean_is_exclusive(v_l_4174_);
if (v_isSharedCheck_4516_ == 0)
{
lean_object* v_unused_4517_; lean_object* v_unused_4518_; lean_object* v_unused_4519_; lean_object* v_unused_4520_; lean_object* v_unused_4521_; 
v_unused_4517_ = lean_ctor_get(v_l_4174_, 4);
lean_dec(v_unused_4517_);
v_unused_4518_ = lean_ctor_get(v_l_4174_, 3);
lean_dec(v_unused_4518_);
v_unused_4519_ = lean_ctor_get(v_l_4174_, 2);
lean_dec(v_unused_4519_);
v_unused_4520_ = lean_ctor_get(v_l_4174_, 1);
lean_dec(v_unused_4520_);
v_unused_4521_ = lean_ctor_get(v_l_4174_, 0);
lean_dec(v_unused_4521_);
v___x_4366_ = v_l_4174_;
v_isShared_4367_ = v_isSharedCheck_4516_;
goto v_resetjp_4365_;
}
else
{
lean_dec(v_l_4174_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4516_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v_d_4368_; lean_object* v_tree_4369_; 
v_d_4368_ = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(v_k_4355_, v_v_4356_, v_l_4357_, v_r_4358_);
v_tree_4369_ = lean_ctor_get(v_d_4368_, 2);
lean_inc(v_tree_4369_);
if (lean_obj_tag(v_tree_4369_) == 0)
{
lean_object* v_k_4370_; lean_object* v_v_4371_; lean_object* v_size_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; uint8_t v___x_4375_; 
v_k_4370_ = lean_ctor_get(v_d_4368_, 0);
lean_inc(v_k_4370_);
v_v_4371_ = lean_ctor_get(v_d_4368_, 1);
lean_inc(v_v_4371_);
lean_dec_ref(v_d_4368_);
v_size_4372_ = lean_ctor_get(v_tree_4369_, 0);
v___x_4373_ = lean_unsigned_to_nat(3u);
v___x_4374_ = lean_nat_mul(v___x_4373_, v_size_4372_);
v___x_4375_ = lean_nat_dec_lt(v___x_4374_, v_size_4359_);
lean_dec(v___x_4374_);
if (v___x_4375_ == 0)
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4380_; 
lean_dec(v_l_4362_);
v___x_4376_ = lean_unsigned_to_nat(1u);
v___x_4377_ = lean_nat_add(v___x_4376_, v_size_4372_);
v___x_4378_ = lean_nat_add(v___x_4377_, v_size_4359_);
lean_dec(v___x_4377_);
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 4, v_r_4175_);
lean_ctor_set(v___x_4366_, 3, v_tree_4369_);
lean_ctor_set(v___x_4366_, 2, v_v_4371_);
lean_ctor_set(v___x_4366_, 1, v_k_4370_);
lean_ctor_set(v___x_4366_, 0, v___x_4378_);
v___x_4380_ = v___x_4366_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4378_);
lean_ctor_set(v_reuseFailAlloc_4381_, 1, v_k_4370_);
lean_ctor_set(v_reuseFailAlloc_4381_, 2, v_v_4371_);
lean_ctor_set(v_reuseFailAlloc_4381_, 3, v_tree_4369_);
lean_ctor_set(v_reuseFailAlloc_4381_, 4, v_r_4175_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
else
{
lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4442_; 
lean_inc(v_r_4363_);
lean_inc(v_v_4361_);
lean_inc(v_k_4360_);
lean_inc(v_size_4359_);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_r_4175_);
if (v_isSharedCheck_4442_ == 0)
{
lean_object* v_unused_4443_; lean_object* v_unused_4444_; lean_object* v_unused_4445_; lean_object* v_unused_4446_; lean_object* v_unused_4447_; 
v_unused_4443_ = lean_ctor_get(v_r_4175_, 4);
lean_dec(v_unused_4443_);
v_unused_4444_ = lean_ctor_get(v_r_4175_, 3);
lean_dec(v_unused_4444_);
v_unused_4445_ = lean_ctor_get(v_r_4175_, 2);
lean_dec(v_unused_4445_);
v_unused_4446_ = lean_ctor_get(v_r_4175_, 1);
lean_dec(v_unused_4446_);
v_unused_4447_ = lean_ctor_get(v_r_4175_, 0);
lean_dec(v_unused_4447_);
v___x_4383_ = v_r_4175_;
v_isShared_4384_ = v_isSharedCheck_4442_;
goto v_resetjp_4382_;
}
else
{
lean_dec(v_r_4175_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4442_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
if (lean_obj_tag(v_l_4362_) == 0)
{
if (lean_obj_tag(v_r_4363_) == 0)
{
lean_object* v_size_4385_; lean_object* v_k_4386_; lean_object* v_v_4387_; lean_object* v_l_4388_; lean_object* v_r_4389_; lean_object* v_size_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v_size_4385_ = lean_ctor_get(v_l_4362_, 0);
v_k_4386_ = lean_ctor_get(v_l_4362_, 1);
v_v_4387_ = lean_ctor_get(v_l_4362_, 2);
v_l_4388_ = lean_ctor_get(v_l_4362_, 3);
v_r_4389_ = lean_ctor_get(v_l_4362_, 4);
v_size_4390_ = lean_ctor_get(v_r_4363_, 0);
v___x_4391_ = lean_unsigned_to_nat(2u);
v___x_4392_ = lean_nat_mul(v___x_4391_, v_size_4390_);
v___x_4393_ = lean_nat_dec_lt(v_size_4385_, v___x_4392_);
lean_dec(v___x_4392_);
if (v___x_4393_ == 0)
{
lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4422_; 
lean_inc(v_r_4389_);
lean_inc(v_l_4388_);
lean_inc(v_v_4387_);
lean_inc(v_k_4386_);
v_isSharedCheck_4422_ = !lean_is_exclusive(v_l_4362_);
if (v_isSharedCheck_4422_ == 0)
{
lean_object* v_unused_4423_; lean_object* v_unused_4424_; lean_object* v_unused_4425_; lean_object* v_unused_4426_; lean_object* v_unused_4427_; 
v_unused_4423_ = lean_ctor_get(v_l_4362_, 4);
lean_dec(v_unused_4423_);
v_unused_4424_ = lean_ctor_get(v_l_4362_, 3);
lean_dec(v_unused_4424_);
v_unused_4425_ = lean_ctor_get(v_l_4362_, 2);
lean_dec(v_unused_4425_);
v_unused_4426_ = lean_ctor_get(v_l_4362_, 1);
lean_dec(v_unused_4426_);
v_unused_4427_ = lean_ctor_get(v_l_4362_, 0);
lean_dec(v_unused_4427_);
v___x_4395_ = v_l_4362_;
v_isShared_4396_ = v_isSharedCheck_4422_;
goto v_resetjp_4394_;
}
else
{
lean_dec(v_l_4362_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4422_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4412_; 
v___x_4397_ = lean_unsigned_to_nat(1u);
v___x_4398_ = lean_nat_add(v___x_4397_, v_size_4372_);
v___x_4399_ = lean_nat_add(v___x_4398_, v_size_4359_);
lean_dec(v_size_4359_);
if (lean_obj_tag(v_l_4388_) == 0)
{
lean_object* v_size_4420_; 
v_size_4420_ = lean_ctor_get(v_l_4388_, 0);
lean_inc(v_size_4420_);
v___y_4412_ = v_size_4420_;
goto v___jp_4411_;
}
else
{
lean_object* v___x_4421_; 
v___x_4421_ = lean_unsigned_to_nat(0u);
v___y_4412_ = v___x_4421_;
goto v___jp_4411_;
}
v___jp_4400_:
{
lean_object* v___x_4404_; lean_object* v___x_4406_; 
v___x_4404_ = lean_nat_add(v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec(v___y_4402_);
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 4, v_r_4363_);
lean_ctor_set(v___x_4395_, 3, v_r_4389_);
lean_ctor_set(v___x_4395_, 2, v_v_4361_);
lean_ctor_set(v___x_4395_, 1, v_k_4360_);
lean_ctor_set(v___x_4395_, 0, v___x_4404_);
v___x_4406_ = v___x_4395_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4404_);
lean_ctor_set(v_reuseFailAlloc_4410_, 1, v_k_4360_);
lean_ctor_set(v_reuseFailAlloc_4410_, 2, v_v_4361_);
lean_ctor_set(v_reuseFailAlloc_4410_, 3, v_r_4389_);
lean_ctor_set(v_reuseFailAlloc_4410_, 4, v_r_4363_);
v___x_4406_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
lean_object* v___x_4408_; 
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 4, v___x_4406_);
lean_ctor_set(v___x_4383_, 3, v___y_4401_);
lean_ctor_set(v___x_4383_, 2, v_v_4387_);
lean_ctor_set(v___x_4383_, 1, v_k_4386_);
lean_ctor_set(v___x_4383_, 0, v___x_4399_);
v___x_4408_ = v___x_4383_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4399_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v_k_4386_);
lean_ctor_set(v_reuseFailAlloc_4409_, 2, v_v_4387_);
lean_ctor_set(v_reuseFailAlloc_4409_, 3, v___y_4401_);
lean_ctor_set(v_reuseFailAlloc_4409_, 4, v___x_4406_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
v___jp_4411_:
{
lean_object* v___x_4413_; lean_object* v___x_4415_; 
v___x_4413_ = lean_nat_add(v___x_4398_, v___y_4412_);
lean_dec(v___y_4412_);
lean_dec(v___x_4398_);
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 4, v_l_4388_);
lean_ctor_set(v___x_4366_, 3, v_tree_4369_);
lean_ctor_set(v___x_4366_, 2, v_v_4371_);
lean_ctor_set(v___x_4366_, 1, v_k_4370_);
lean_ctor_set(v___x_4366_, 0, v___x_4413_);
v___x_4415_ = v___x_4366_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4413_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v_k_4370_);
lean_ctor_set(v_reuseFailAlloc_4419_, 2, v_v_4371_);
lean_ctor_set(v_reuseFailAlloc_4419_, 3, v_tree_4369_);
lean_ctor_set(v_reuseFailAlloc_4419_, 4, v_l_4388_);
v___x_4415_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v___x_4416_; 
v___x_4416_ = lean_nat_add(v___x_4397_, v_size_4390_);
if (lean_obj_tag(v_r_4389_) == 0)
{
lean_object* v_size_4417_; 
v_size_4417_ = lean_ctor_get(v_r_4389_, 0);
lean_inc(v_size_4417_);
v___y_4401_ = v___x_4415_;
v___y_4402_ = v___x_4416_;
v___y_4403_ = v_size_4417_;
goto v___jp_4400_;
}
else
{
lean_object* v___x_4418_; 
v___x_4418_ = lean_unsigned_to_nat(0u);
v___y_4401_ = v___x_4415_;
v___y_4402_ = v___x_4416_;
v___y_4403_ = v___x_4418_;
goto v___jp_4400_;
}
}
}
}
}
else
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4433_; 
v___x_4428_ = lean_unsigned_to_nat(1u);
v___x_4429_ = lean_nat_add(v___x_4428_, v_size_4372_);
v___x_4430_ = lean_nat_add(v___x_4429_, v_size_4359_);
lean_dec(v_size_4359_);
v___x_4431_ = lean_nat_add(v___x_4429_, v_size_4385_);
lean_dec(v___x_4429_);
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 4, v_l_4362_);
lean_ctor_set(v___x_4383_, 3, v_tree_4369_);
lean_ctor_set(v___x_4383_, 2, v_v_4371_);
lean_ctor_set(v___x_4383_, 1, v_k_4370_);
lean_ctor_set(v___x_4383_, 0, v___x_4431_);
v___x_4433_ = v___x_4383_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v___x_4431_);
lean_ctor_set(v_reuseFailAlloc_4437_, 1, v_k_4370_);
lean_ctor_set(v_reuseFailAlloc_4437_, 2, v_v_4371_);
lean_ctor_set(v_reuseFailAlloc_4437_, 3, v_tree_4369_);
lean_ctor_set(v_reuseFailAlloc_4437_, 4, v_l_4362_);
v___x_4433_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
lean_object* v___x_4435_; 
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 4, v_r_4363_);
lean_ctor_set(v___x_4366_, 3, v___x_4433_);
lean_ctor_set(v___x_4366_, 2, v_v_4361_);
lean_ctor_set(v___x_4366_, 1, v_k_4360_);
lean_ctor_set(v___x_4366_, 0, v___x_4430_);
v___x_4435_ = v___x_4366_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v___x_4430_);
lean_ctor_set(v_reuseFailAlloc_4436_, 1, v_k_4360_);
lean_ctor_set(v_reuseFailAlloc_4436_, 2, v_v_4361_);
lean_ctor_set(v_reuseFailAlloc_4436_, 3, v___x_4433_);
lean_ctor_set(v_reuseFailAlloc_4436_, 4, v_r_4363_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
else
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
lean_dec_ref_known(v_l_4362_, 5);
lean_del_object(v___x_4383_);
lean_dec(v_v_4371_);
lean_dec_ref_known(v_tree_4369_, 5);
lean_dec(v_k_4370_);
lean_del_object(v___x_4366_);
lean_dec(v_v_4361_);
lean_dec(v_k_4360_);
lean_dec(v_size_4359_);
v___x_4438_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7);
v___x_4439_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4438_);
return v___x_4439_;
}
}
else
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
lean_del_object(v___x_4383_);
lean_dec(v_v_4371_);
lean_dec_ref_known(v_tree_4369_, 5);
lean_dec(v_k_4370_);
lean_del_object(v___x_4366_);
lean_dec(v_r_4363_);
lean_dec(v_v_4361_);
lean_dec(v_k_4360_);
lean_dec(v_size_4359_);
v___x_4440_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8);
v___x_4441_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4440_);
return v___x_4441_;
}
}
}
}
else
{
lean_inc(v_r_4363_);
if (lean_obj_tag(v_l_4362_) == 0)
{
lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4485_; 
lean_inc(v_v_4361_);
lean_inc(v_k_4360_);
lean_inc(v_size_4359_);
v_isSharedCheck_4485_ = !lean_is_exclusive(v_r_4175_);
if (v_isSharedCheck_4485_ == 0)
{
lean_object* v_unused_4486_; lean_object* v_unused_4487_; lean_object* v_unused_4488_; lean_object* v_unused_4489_; lean_object* v_unused_4490_; 
v_unused_4486_ = lean_ctor_get(v_r_4175_, 4);
lean_dec(v_unused_4486_);
v_unused_4487_ = lean_ctor_get(v_r_4175_, 3);
lean_dec(v_unused_4487_);
v_unused_4488_ = lean_ctor_get(v_r_4175_, 2);
lean_dec(v_unused_4488_);
v_unused_4489_ = lean_ctor_get(v_r_4175_, 1);
lean_dec(v_unused_4489_);
v_unused_4490_ = lean_ctor_get(v_r_4175_, 0);
lean_dec(v_unused_4490_);
v___x_4449_ = v_r_4175_;
v_isShared_4450_ = v_isSharedCheck_4485_;
goto v_resetjp_4448_;
}
else
{
lean_dec(v_r_4175_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4485_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
if (lean_obj_tag(v_r_4363_) == 0)
{
lean_object* v_k_4451_; lean_object* v_v_4452_; lean_object* v_size_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4458_; 
v_k_4451_ = lean_ctor_get(v_d_4368_, 0);
lean_inc(v_k_4451_);
v_v_4452_ = lean_ctor_get(v_d_4368_, 1);
lean_inc(v_v_4452_);
lean_dec_ref(v_d_4368_);
v_size_4453_ = lean_ctor_get(v_l_4362_, 0);
v___x_4454_ = lean_unsigned_to_nat(1u);
v___x_4455_ = lean_nat_add(v___x_4454_, v_size_4359_);
lean_dec(v_size_4359_);
v___x_4456_ = lean_nat_add(v___x_4454_, v_size_4453_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 4, v_l_4362_);
lean_ctor_set(v___x_4449_, 3, v_tree_4369_);
lean_ctor_set(v___x_4449_, 2, v_v_4452_);
lean_ctor_set(v___x_4449_, 1, v_k_4451_);
lean_ctor_set(v___x_4449_, 0, v___x_4456_);
v___x_4458_ = v___x_4449_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4456_);
lean_ctor_set(v_reuseFailAlloc_4462_, 1, v_k_4451_);
lean_ctor_set(v_reuseFailAlloc_4462_, 2, v_v_4452_);
lean_ctor_set(v_reuseFailAlloc_4462_, 3, v_tree_4369_);
lean_ctor_set(v_reuseFailAlloc_4462_, 4, v_l_4362_);
v___x_4458_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
lean_object* v___x_4460_; 
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 4, v_r_4363_);
lean_ctor_set(v___x_4366_, 3, v___x_4458_);
lean_ctor_set(v___x_4366_, 2, v_v_4361_);
lean_ctor_set(v___x_4366_, 1, v_k_4360_);
lean_ctor_set(v___x_4366_, 0, v___x_4455_);
v___x_4460_ = v___x_4366_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4455_);
lean_ctor_set(v_reuseFailAlloc_4461_, 1, v_k_4360_);
lean_ctor_set(v_reuseFailAlloc_4461_, 2, v_v_4361_);
lean_ctor_set(v_reuseFailAlloc_4461_, 3, v___x_4458_);
lean_ctor_set(v_reuseFailAlloc_4461_, 4, v_r_4363_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
else
{
lean_object* v_k_4463_; lean_object* v_v_4464_; lean_object* v_k_4465_; lean_object* v_v_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4481_; 
lean_dec(v_size_4359_);
v_k_4463_ = lean_ctor_get(v_d_4368_, 0);
lean_inc(v_k_4463_);
v_v_4464_ = lean_ctor_get(v_d_4368_, 1);
lean_inc(v_v_4464_);
lean_dec_ref(v_d_4368_);
v_k_4465_ = lean_ctor_get(v_l_4362_, 1);
v_v_4466_ = lean_ctor_get(v_l_4362_, 2);
v_isSharedCheck_4481_ = !lean_is_exclusive(v_l_4362_);
if (v_isSharedCheck_4481_ == 0)
{
lean_object* v_unused_4482_; lean_object* v_unused_4483_; lean_object* v_unused_4484_; 
v_unused_4482_ = lean_ctor_get(v_l_4362_, 4);
lean_dec(v_unused_4482_);
v_unused_4483_ = lean_ctor_get(v_l_4362_, 3);
lean_dec(v_unused_4483_);
v_unused_4484_ = lean_ctor_get(v_l_4362_, 0);
lean_dec(v_unused_4484_);
v___x_4468_ = v_l_4362_;
v_isShared_4469_ = v_isSharedCheck_4481_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_v_4466_);
lean_inc(v_k_4465_);
lean_dec(v_l_4362_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4481_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4473_; 
v___x_4470_ = lean_unsigned_to_nat(3u);
v___x_4471_ = lean_unsigned_to_nat(1u);
if (v_isShared_4469_ == 0)
{
lean_ctor_set(v___x_4468_, 4, v_r_4363_);
lean_ctor_set(v___x_4468_, 3, v_r_4363_);
lean_ctor_set(v___x_4468_, 2, v_v_4464_);
lean_ctor_set(v___x_4468_, 1, v_k_4463_);
lean_ctor_set(v___x_4468_, 0, v___x_4471_);
v___x_4473_ = v___x_4468_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4471_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_k_4463_);
lean_ctor_set(v_reuseFailAlloc_4480_, 2, v_v_4464_);
lean_ctor_set(v_reuseFailAlloc_4480_, 3, v_r_4363_);
lean_ctor_set(v_reuseFailAlloc_4480_, 4, v_r_4363_);
v___x_4473_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
lean_object* v___x_4475_; 
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 3, v_r_4363_);
lean_ctor_set(v___x_4449_, 0, v___x_4471_);
v___x_4475_ = v___x_4449_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4471_);
lean_ctor_set(v_reuseFailAlloc_4479_, 1, v_k_4360_);
lean_ctor_set(v_reuseFailAlloc_4479_, 2, v_v_4361_);
lean_ctor_set(v_reuseFailAlloc_4479_, 3, v_r_4363_);
lean_ctor_set(v_reuseFailAlloc_4479_, 4, v_r_4363_);
v___x_4475_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4477_; 
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 4, v___x_4475_);
lean_ctor_set(v___x_4366_, 3, v___x_4473_);
lean_ctor_set(v___x_4366_, 2, v_v_4466_);
lean_ctor_set(v___x_4366_, 1, v_k_4465_);
lean_ctor_set(v___x_4366_, 0, v___x_4470_);
v___x_4477_ = v___x_4366_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4470_);
lean_ctor_set(v_reuseFailAlloc_4478_, 1, v_k_4465_);
lean_ctor_set(v_reuseFailAlloc_4478_, 2, v_v_4466_);
lean_ctor_set(v_reuseFailAlloc_4478_, 3, v___x_4473_);
lean_ctor_set(v_reuseFailAlloc_4478_, 4, v___x_4475_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4363_) == 0)
{
lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4504_; 
lean_inc(v_v_4361_);
lean_inc(v_k_4360_);
v_isSharedCheck_4504_ = !lean_is_exclusive(v_r_4175_);
if (v_isSharedCheck_4504_ == 0)
{
lean_object* v_unused_4505_; lean_object* v_unused_4506_; lean_object* v_unused_4507_; lean_object* v_unused_4508_; lean_object* v_unused_4509_; 
v_unused_4505_ = lean_ctor_get(v_r_4175_, 4);
lean_dec(v_unused_4505_);
v_unused_4506_ = lean_ctor_get(v_r_4175_, 3);
lean_dec(v_unused_4506_);
v_unused_4507_ = lean_ctor_get(v_r_4175_, 2);
lean_dec(v_unused_4507_);
v_unused_4508_ = lean_ctor_get(v_r_4175_, 1);
lean_dec(v_unused_4508_);
v_unused_4509_ = lean_ctor_get(v_r_4175_, 0);
lean_dec(v_unused_4509_);
v___x_4492_ = v_r_4175_;
v_isShared_4493_ = v_isSharedCheck_4504_;
goto v_resetjp_4491_;
}
else
{
lean_dec(v_r_4175_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4504_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v_k_4494_; lean_object* v_v_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4499_; 
v_k_4494_ = lean_ctor_get(v_d_4368_, 0);
lean_inc(v_k_4494_);
v_v_4495_ = lean_ctor_get(v_d_4368_, 1);
lean_inc(v_v_4495_);
lean_dec_ref(v_d_4368_);
v___x_4496_ = lean_unsigned_to_nat(3u);
v___x_4497_ = lean_unsigned_to_nat(1u);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 4, v_l_4362_);
lean_ctor_set(v___x_4492_, 2, v_v_4495_);
lean_ctor_set(v___x_4492_, 1, v_k_4494_);
lean_ctor_set(v___x_4492_, 0, v___x_4497_);
v___x_4499_ = v___x_4492_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4497_);
lean_ctor_set(v_reuseFailAlloc_4503_, 1, v_k_4494_);
lean_ctor_set(v_reuseFailAlloc_4503_, 2, v_v_4495_);
lean_ctor_set(v_reuseFailAlloc_4503_, 3, v_l_4362_);
lean_ctor_set(v_reuseFailAlloc_4503_, 4, v_l_4362_);
v___x_4499_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
lean_object* v___x_4501_; 
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 4, v_r_4363_);
lean_ctor_set(v___x_4366_, 3, v___x_4499_);
lean_ctor_set(v___x_4366_, 2, v_v_4361_);
lean_ctor_set(v___x_4366_, 1, v_k_4360_);
lean_ctor_set(v___x_4366_, 0, v___x_4496_);
v___x_4501_ = v___x_4366_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4496_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_k_4360_);
lean_ctor_set(v_reuseFailAlloc_4502_, 2, v_v_4361_);
lean_ctor_set(v_reuseFailAlloc_4502_, 3, v___x_4499_);
lean_ctor_set(v_reuseFailAlloc_4502_, 4, v_r_4363_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
}
else
{
lean_object* v_k_4510_; lean_object* v_v_4511_; lean_object* v___x_4512_; lean_object* v___x_4514_; 
v_k_4510_ = lean_ctor_get(v_d_4368_, 0);
lean_inc(v_k_4510_);
v_v_4511_ = lean_ctor_get(v_d_4368_, 1);
lean_inc(v_v_4511_);
lean_dec_ref(v_d_4368_);
v___x_4512_ = lean_unsigned_to_nat(2u);
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 4, v_r_4175_);
lean_ctor_set(v___x_4366_, 3, v_r_4363_);
lean_ctor_set(v___x_4366_, 2, v_v_4511_);
lean_ctor_set(v___x_4366_, 1, v_k_4510_);
lean_ctor_set(v___x_4366_, 0, v___x_4512_);
v___x_4514_ = v___x_4366_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4512_);
lean_ctor_set(v_reuseFailAlloc_4515_, 1, v_k_4510_);
lean_ctor_set(v_reuseFailAlloc_4515_, 2, v_v_4511_);
lean_ctor_set(v_reuseFailAlloc_4515_, 3, v_r_4363_);
lean_ctor_set(v_reuseFailAlloc_4515_, 4, v_r_4175_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
}
}
else
{
lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4684_; 
lean_inc(v_r_4363_);
lean_inc(v_v_4361_);
lean_inc(v_k_4360_);
v_isSharedCheck_4684_ = !lean_is_exclusive(v_r_4175_);
if (v_isSharedCheck_4684_ == 0)
{
lean_object* v_unused_4685_; lean_object* v_unused_4686_; lean_object* v_unused_4687_; lean_object* v_unused_4688_; lean_object* v_unused_4689_; 
v_unused_4685_ = lean_ctor_get(v_r_4175_, 4);
lean_dec(v_unused_4685_);
v_unused_4686_ = lean_ctor_get(v_r_4175_, 3);
lean_dec(v_unused_4686_);
v_unused_4687_ = lean_ctor_get(v_r_4175_, 2);
lean_dec(v_unused_4687_);
v_unused_4688_ = lean_ctor_get(v_r_4175_, 1);
lean_dec(v_unused_4688_);
v_unused_4689_ = lean_ctor_get(v_r_4175_, 0);
lean_dec(v_unused_4689_);
v___x_4523_ = v_r_4175_;
v_isShared_4524_ = v_isSharedCheck_4684_;
goto v_resetjp_4522_;
}
else
{
lean_dec(v_r_4175_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4684_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v_d_4525_; lean_object* v_tree_4526_; 
v_d_4525_ = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(v_k_4360_, v_v_4361_, v_l_4362_, v_r_4363_);
v_tree_4526_ = lean_ctor_get(v_d_4525_, 2);
lean_inc(v_tree_4526_);
if (lean_obj_tag(v_tree_4526_) == 0)
{
lean_object* v_k_4527_; lean_object* v_v_4528_; lean_object* v_size_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; uint8_t v___x_4532_; 
v_k_4527_ = lean_ctor_get(v_d_4525_, 0);
lean_inc(v_k_4527_);
v_v_4528_ = lean_ctor_get(v_d_4525_, 1);
lean_inc(v_v_4528_);
lean_dec_ref(v_d_4525_);
v_size_4529_ = lean_ctor_get(v_tree_4526_, 0);
v___x_4530_ = lean_unsigned_to_nat(3u);
v___x_4531_ = lean_nat_mul(v___x_4530_, v_size_4529_);
v___x_4532_ = lean_nat_dec_lt(v___x_4531_, v_size_4354_);
lean_dec(v___x_4531_);
if (v___x_4532_ == 0)
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4537_; 
lean_dec(v_r_4358_);
v___x_4533_ = lean_unsigned_to_nat(1u);
v___x_4534_ = lean_nat_add(v___x_4533_, v_size_4354_);
v___x_4535_ = lean_nat_add(v___x_4534_, v_size_4529_);
lean_dec(v___x_4534_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 4, v_tree_4526_);
lean_ctor_set(v___x_4523_, 3, v_l_4174_);
lean_ctor_set(v___x_4523_, 2, v_v_4528_);
lean_ctor_set(v___x_4523_, 1, v_k_4527_);
lean_ctor_set(v___x_4523_, 0, v___x_4535_);
v___x_4537_ = v___x_4523_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v___x_4535_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v_k_4527_);
lean_ctor_set(v_reuseFailAlloc_4538_, 2, v_v_4528_);
lean_ctor_set(v_reuseFailAlloc_4538_, 3, v_l_4174_);
lean_ctor_set(v_reuseFailAlloc_4538_, 4, v_tree_4526_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
else
{
lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4610_; 
lean_inc(v_l_4357_);
lean_inc(v_v_4356_);
lean_inc(v_k_4355_);
lean_inc(v_size_4354_);
v_isSharedCheck_4610_ = !lean_is_exclusive(v_l_4174_);
if (v_isSharedCheck_4610_ == 0)
{
lean_object* v_unused_4611_; lean_object* v_unused_4612_; lean_object* v_unused_4613_; lean_object* v_unused_4614_; lean_object* v_unused_4615_; 
v_unused_4611_ = lean_ctor_get(v_l_4174_, 4);
lean_dec(v_unused_4611_);
v_unused_4612_ = lean_ctor_get(v_l_4174_, 3);
lean_dec(v_unused_4612_);
v_unused_4613_ = lean_ctor_get(v_l_4174_, 2);
lean_dec(v_unused_4613_);
v_unused_4614_ = lean_ctor_get(v_l_4174_, 1);
lean_dec(v_unused_4614_);
v_unused_4615_ = lean_ctor_get(v_l_4174_, 0);
lean_dec(v_unused_4615_);
v___x_4540_ = v_l_4174_;
v_isShared_4541_ = v_isSharedCheck_4610_;
goto v_resetjp_4539_;
}
else
{
lean_dec(v_l_4174_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4610_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
if (lean_obj_tag(v_l_4357_) == 0)
{
if (lean_obj_tag(v_r_4358_) == 0)
{
lean_object* v_size_4542_; lean_object* v_size_4543_; lean_object* v_k_4544_; lean_object* v_v_4545_; lean_object* v_l_4546_; lean_object* v_r_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; uint8_t v___x_4550_; 
v_size_4542_ = lean_ctor_get(v_l_4357_, 0);
v_size_4543_ = lean_ctor_get(v_r_4358_, 0);
v_k_4544_ = lean_ctor_get(v_r_4358_, 1);
v_v_4545_ = lean_ctor_get(v_r_4358_, 2);
v_l_4546_ = lean_ctor_get(v_r_4358_, 3);
v_r_4547_ = lean_ctor_get(v_r_4358_, 4);
v___x_4548_ = lean_unsigned_to_nat(2u);
v___x_4549_ = lean_nat_mul(v___x_4548_, v_size_4542_);
v___x_4550_ = lean_nat_dec_lt(v_size_4543_, v___x_4549_);
lean_dec(v___x_4549_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4589_; 
lean_inc(v_r_4547_);
lean_inc(v_l_4546_);
lean_inc(v_v_4545_);
lean_inc(v_k_4544_);
lean_del_object(v___x_4540_);
v_isSharedCheck_4589_ = !lean_is_exclusive(v_r_4358_);
if (v_isSharedCheck_4589_ == 0)
{
lean_object* v_unused_4590_; lean_object* v_unused_4591_; lean_object* v_unused_4592_; lean_object* v_unused_4593_; lean_object* v_unused_4594_; 
v_unused_4590_ = lean_ctor_get(v_r_4358_, 4);
lean_dec(v_unused_4590_);
v_unused_4591_ = lean_ctor_get(v_r_4358_, 3);
lean_dec(v_unused_4591_);
v_unused_4592_ = lean_ctor_get(v_r_4358_, 2);
lean_dec(v_unused_4592_);
v_unused_4593_ = lean_ctor_get(v_r_4358_, 1);
lean_dec(v_unused_4593_);
v_unused_4594_ = lean_ctor_get(v_r_4358_, 0);
lean_dec(v_unused_4594_);
v___x_4552_ = v_r_4358_;
v_isShared_4553_ = v_isSharedCheck_4589_;
goto v_resetjp_4551_;
}
else
{
lean_dec(v_r_4358_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4589_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___x_4577_; lean_object* v___y_4579_; 
v___x_4554_ = lean_unsigned_to_nat(1u);
v___x_4555_ = lean_nat_add(v___x_4554_, v_size_4354_);
lean_dec(v_size_4354_);
v___x_4556_ = lean_nat_add(v___x_4555_, v_size_4529_);
lean_dec(v___x_4555_);
v___x_4577_ = lean_nat_add(v___x_4554_, v_size_4542_);
if (lean_obj_tag(v_l_4546_) == 0)
{
lean_object* v_size_4587_; 
v_size_4587_ = lean_ctor_get(v_l_4546_, 0);
lean_inc(v_size_4587_);
v___y_4579_ = v_size_4587_;
goto v___jp_4578_;
}
else
{
lean_object* v___x_4588_; 
v___x_4588_ = lean_unsigned_to_nat(0u);
v___y_4579_ = v___x_4588_;
goto v___jp_4578_;
}
v___jp_4557_:
{
lean_object* v___x_4561_; lean_object* v___x_4563_; 
v___x_4561_ = lean_nat_add(v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec(v___y_4559_);
lean_inc_ref(v_tree_4526_);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 4, v_tree_4526_);
lean_ctor_set(v___x_4552_, 3, v_r_4547_);
lean_ctor_set(v___x_4552_, 2, v_v_4528_);
lean_ctor_set(v___x_4552_, 1, v_k_4527_);
lean_ctor_set(v___x_4552_, 0, v___x_4561_);
v___x_4563_ = v___x_4552_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v___x_4561_);
lean_ctor_set(v_reuseFailAlloc_4576_, 1, v_k_4527_);
lean_ctor_set(v_reuseFailAlloc_4576_, 2, v_v_4528_);
lean_ctor_set(v_reuseFailAlloc_4576_, 3, v_r_4547_);
lean_ctor_set(v_reuseFailAlloc_4576_, 4, v_tree_4526_);
v___x_4563_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
v_isSharedCheck_4570_ = !lean_is_exclusive(v_tree_4526_);
if (v_isSharedCheck_4570_ == 0)
{
lean_object* v_unused_4571_; lean_object* v_unused_4572_; lean_object* v_unused_4573_; lean_object* v_unused_4574_; lean_object* v_unused_4575_; 
v_unused_4571_ = lean_ctor_get(v_tree_4526_, 4);
lean_dec(v_unused_4571_);
v_unused_4572_ = lean_ctor_get(v_tree_4526_, 3);
lean_dec(v_unused_4572_);
v_unused_4573_ = lean_ctor_get(v_tree_4526_, 2);
lean_dec(v_unused_4573_);
v_unused_4574_ = lean_ctor_get(v_tree_4526_, 1);
lean_dec(v_unused_4574_);
v_unused_4575_ = lean_ctor_get(v_tree_4526_, 0);
lean_dec(v_unused_4575_);
v___x_4565_ = v_tree_4526_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_dec(v_tree_4526_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
lean_ctor_set(v___x_4565_, 4, v___x_4563_);
lean_ctor_set(v___x_4565_, 3, v___y_4558_);
lean_ctor_set(v___x_4565_, 2, v_v_4545_);
lean_ctor_set(v___x_4565_, 1, v_k_4544_);
lean_ctor_set(v___x_4565_, 0, v___x_4556_);
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v___x_4556_);
lean_ctor_set(v_reuseFailAlloc_4569_, 1, v_k_4544_);
lean_ctor_set(v_reuseFailAlloc_4569_, 2, v_v_4545_);
lean_ctor_set(v_reuseFailAlloc_4569_, 3, v___y_4558_);
lean_ctor_set(v_reuseFailAlloc_4569_, 4, v___x_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
v___jp_4578_:
{
lean_object* v___x_4580_; lean_object* v___x_4582_; 
v___x_4580_ = lean_nat_add(v___x_4577_, v___y_4579_);
lean_dec(v___y_4579_);
lean_dec(v___x_4577_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 4, v_l_4546_);
lean_ctor_set(v___x_4523_, 3, v_l_4357_);
lean_ctor_set(v___x_4523_, 2, v_v_4356_);
lean_ctor_set(v___x_4523_, 1, v_k_4355_);
lean_ctor_set(v___x_4523_, 0, v___x_4580_);
v___x_4582_ = v___x_4523_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4580_);
lean_ctor_set(v_reuseFailAlloc_4586_, 1, v_k_4355_);
lean_ctor_set(v_reuseFailAlloc_4586_, 2, v_v_4356_);
lean_ctor_set(v_reuseFailAlloc_4586_, 3, v_l_4357_);
lean_ctor_set(v_reuseFailAlloc_4586_, 4, v_l_4546_);
v___x_4582_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4583_; 
v___x_4583_ = lean_nat_add(v___x_4554_, v_size_4529_);
if (lean_obj_tag(v_r_4547_) == 0)
{
lean_object* v_size_4584_; 
v_size_4584_ = lean_ctor_get(v_r_4547_, 0);
lean_inc(v_size_4584_);
v___y_4558_ = v___x_4582_;
v___y_4559_ = v___x_4583_;
v___y_4560_ = v_size_4584_;
goto v___jp_4557_;
}
else
{
lean_object* v___x_4585_; 
v___x_4585_ = lean_unsigned_to_nat(0u);
v___y_4558_ = v___x_4582_;
v___y_4559_ = v___x_4583_;
v___y_4560_ = v___x_4585_;
goto v___jp_4557_;
}
}
}
}
}
else
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4601_; 
v___x_4595_ = lean_unsigned_to_nat(1u);
v___x_4596_ = lean_nat_add(v___x_4595_, v_size_4354_);
lean_dec(v_size_4354_);
v___x_4597_ = lean_nat_add(v___x_4596_, v_size_4529_);
lean_dec(v___x_4596_);
v___x_4598_ = lean_nat_add(v___x_4595_, v_size_4529_);
v___x_4599_ = lean_nat_add(v___x_4598_, v_size_4543_);
lean_dec(v___x_4598_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 4, v_tree_4526_);
lean_ctor_set(v___x_4523_, 3, v_r_4358_);
lean_ctor_set(v___x_4523_, 2, v_v_4528_);
lean_ctor_set(v___x_4523_, 1, v_k_4527_);
lean_ctor_set(v___x_4523_, 0, v___x_4599_);
v___x_4601_ = v___x_4523_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4599_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_k_4527_);
lean_ctor_set(v_reuseFailAlloc_4605_, 2, v_v_4528_);
lean_ctor_set(v_reuseFailAlloc_4605_, 3, v_r_4358_);
lean_ctor_set(v_reuseFailAlloc_4605_, 4, v_tree_4526_);
v___x_4601_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
lean_object* v___x_4603_; 
if (v_isShared_4541_ == 0)
{
lean_ctor_set(v___x_4540_, 4, v___x_4601_);
lean_ctor_set(v___x_4540_, 0, v___x_4597_);
v___x_4603_ = v___x_4540_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v___x_4597_);
lean_ctor_set(v_reuseFailAlloc_4604_, 1, v_k_4355_);
lean_ctor_set(v_reuseFailAlloc_4604_, 2, v_v_4356_);
lean_ctor_set(v_reuseFailAlloc_4604_, 3, v_l_4357_);
lean_ctor_set(v_reuseFailAlloc_4604_, 4, v___x_4601_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
}
}
else
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
lean_dec_ref_known(v_l_4357_, 5);
lean_del_object(v___x_4540_);
lean_dec(v_v_4528_);
lean_dec_ref_known(v_tree_4526_, 5);
lean_dec(v_k_4527_);
lean_del_object(v___x_4523_);
lean_dec(v_v_4356_);
lean_dec(v_k_4355_);
lean_dec(v_size_4354_);
v___x_4606_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3);
v___x_4607_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4606_);
return v___x_4607_;
}
}
else
{
lean_object* v___x_4608_; lean_object* v___x_4609_; 
lean_del_object(v___x_4540_);
lean_dec(v_v_4528_);
lean_dec_ref_known(v_tree_4526_, 5);
lean_dec(v_k_4527_);
lean_del_object(v___x_4523_);
lean_dec(v_r_4358_);
lean_dec(v_v_4356_);
lean_dec(v_k_4355_);
lean_dec(v_size_4354_);
v___x_4608_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4);
v___x_4609_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4608_);
return v___x_4609_;
}
}
}
}
else
{
if (lean_obj_tag(v_l_4357_) == 0)
{
lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4641_; 
lean_inc_ref(v_l_4357_);
lean_inc(v_v_4356_);
lean_inc(v_k_4355_);
lean_inc(v_size_4354_);
v_isSharedCheck_4641_ = !lean_is_exclusive(v_l_4174_);
if (v_isSharedCheck_4641_ == 0)
{
lean_object* v_unused_4642_; lean_object* v_unused_4643_; lean_object* v_unused_4644_; lean_object* v_unused_4645_; lean_object* v_unused_4646_; 
v_unused_4642_ = lean_ctor_get(v_l_4174_, 4);
lean_dec(v_unused_4642_);
v_unused_4643_ = lean_ctor_get(v_l_4174_, 3);
lean_dec(v_unused_4643_);
v_unused_4644_ = lean_ctor_get(v_l_4174_, 2);
lean_dec(v_unused_4644_);
v_unused_4645_ = lean_ctor_get(v_l_4174_, 1);
lean_dec(v_unused_4645_);
v_unused_4646_ = lean_ctor_get(v_l_4174_, 0);
lean_dec(v_unused_4646_);
v___x_4617_ = v_l_4174_;
v_isShared_4618_ = v_isSharedCheck_4641_;
goto v_resetjp_4616_;
}
else
{
lean_dec(v_l_4174_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4641_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
if (lean_obj_tag(v_r_4358_) == 0)
{
lean_object* v_k_4619_; lean_object* v_v_4620_; lean_object* v_size_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4626_; 
v_k_4619_ = lean_ctor_get(v_d_4525_, 0);
lean_inc(v_k_4619_);
v_v_4620_ = lean_ctor_get(v_d_4525_, 1);
lean_inc(v_v_4620_);
lean_dec_ref(v_d_4525_);
v_size_4621_ = lean_ctor_get(v_r_4358_, 0);
v___x_4622_ = lean_unsigned_to_nat(1u);
v___x_4623_ = lean_nat_add(v___x_4622_, v_size_4354_);
lean_dec(v_size_4354_);
v___x_4624_ = lean_nat_add(v___x_4622_, v_size_4621_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 4, v_tree_4526_);
lean_ctor_set(v___x_4523_, 3, v_r_4358_);
lean_ctor_set(v___x_4523_, 2, v_v_4620_);
lean_ctor_set(v___x_4523_, 1, v_k_4619_);
lean_ctor_set(v___x_4523_, 0, v___x_4624_);
v___x_4626_ = v___x_4523_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4624_);
lean_ctor_set(v_reuseFailAlloc_4630_, 1, v_k_4619_);
lean_ctor_set(v_reuseFailAlloc_4630_, 2, v_v_4620_);
lean_ctor_set(v_reuseFailAlloc_4630_, 3, v_r_4358_);
lean_ctor_set(v_reuseFailAlloc_4630_, 4, v_tree_4526_);
v___x_4626_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
lean_object* v___x_4628_; 
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 4, v___x_4626_);
lean_ctor_set(v___x_4617_, 0, v___x_4623_);
v___x_4628_ = v___x_4617_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4623_);
lean_ctor_set(v_reuseFailAlloc_4629_, 1, v_k_4355_);
lean_ctor_set(v_reuseFailAlloc_4629_, 2, v_v_4356_);
lean_ctor_set(v_reuseFailAlloc_4629_, 3, v_l_4357_);
lean_ctor_set(v_reuseFailAlloc_4629_, 4, v___x_4626_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
else
{
lean_object* v_k_4631_; lean_object* v_v_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4636_; 
lean_dec(v_size_4354_);
v_k_4631_ = lean_ctor_get(v_d_4525_, 0);
lean_inc(v_k_4631_);
v_v_4632_ = lean_ctor_get(v_d_4525_, 1);
lean_inc(v_v_4632_);
lean_dec_ref(v_d_4525_);
v___x_4633_ = lean_unsigned_to_nat(3u);
v___x_4634_ = lean_unsigned_to_nat(1u);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 4, v_r_4358_);
lean_ctor_set(v___x_4523_, 3, v_r_4358_);
lean_ctor_set(v___x_4523_, 2, v_v_4632_);
lean_ctor_set(v___x_4523_, 1, v_k_4631_);
lean_ctor_set(v___x_4523_, 0, v___x_4634_);
v___x_4636_ = v___x_4523_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4634_);
lean_ctor_set(v_reuseFailAlloc_4640_, 1, v_k_4631_);
lean_ctor_set(v_reuseFailAlloc_4640_, 2, v_v_4632_);
lean_ctor_set(v_reuseFailAlloc_4640_, 3, v_r_4358_);
lean_ctor_set(v_reuseFailAlloc_4640_, 4, v_r_4358_);
v___x_4636_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
lean_object* v___x_4638_; 
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 4, v___x_4636_);
lean_ctor_set(v___x_4617_, 0, v___x_4633_);
v___x_4638_ = v___x_4617_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4633_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_k_4355_);
lean_ctor_set(v_reuseFailAlloc_4639_, 2, v_v_4356_);
lean_ctor_set(v_reuseFailAlloc_4639_, 3, v_l_4357_);
lean_ctor_set(v_reuseFailAlloc_4639_, 4, v___x_4636_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4358_) == 0)
{
lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4672_; 
lean_inc(v_l_4357_);
lean_inc(v_v_4356_);
lean_inc(v_k_4355_);
v_isSharedCheck_4672_ = !lean_is_exclusive(v_l_4174_);
if (v_isSharedCheck_4672_ == 0)
{
lean_object* v_unused_4673_; lean_object* v_unused_4674_; lean_object* v_unused_4675_; lean_object* v_unused_4676_; lean_object* v_unused_4677_; 
v_unused_4673_ = lean_ctor_get(v_l_4174_, 4);
lean_dec(v_unused_4673_);
v_unused_4674_ = lean_ctor_get(v_l_4174_, 3);
lean_dec(v_unused_4674_);
v_unused_4675_ = lean_ctor_get(v_l_4174_, 2);
lean_dec(v_unused_4675_);
v_unused_4676_ = lean_ctor_get(v_l_4174_, 1);
lean_dec(v_unused_4676_);
v_unused_4677_ = lean_ctor_get(v_l_4174_, 0);
lean_dec(v_unused_4677_);
v___x_4648_ = v_l_4174_;
v_isShared_4649_ = v_isSharedCheck_4672_;
goto v_resetjp_4647_;
}
else
{
lean_dec(v_l_4174_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4672_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v_k_4650_; lean_object* v_v_4651_; lean_object* v_k_4652_; lean_object* v_v_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4668_; 
v_k_4650_ = lean_ctor_get(v_d_4525_, 0);
lean_inc(v_k_4650_);
v_v_4651_ = lean_ctor_get(v_d_4525_, 1);
lean_inc(v_v_4651_);
lean_dec_ref(v_d_4525_);
v_k_4652_ = lean_ctor_get(v_r_4358_, 1);
v_v_4653_ = lean_ctor_get(v_r_4358_, 2);
v_isSharedCheck_4668_ = !lean_is_exclusive(v_r_4358_);
if (v_isSharedCheck_4668_ == 0)
{
lean_object* v_unused_4669_; lean_object* v_unused_4670_; lean_object* v_unused_4671_; 
v_unused_4669_ = lean_ctor_get(v_r_4358_, 4);
lean_dec(v_unused_4669_);
v_unused_4670_ = lean_ctor_get(v_r_4358_, 3);
lean_dec(v_unused_4670_);
v_unused_4671_ = lean_ctor_get(v_r_4358_, 0);
lean_dec(v_unused_4671_);
v___x_4655_ = v_r_4358_;
v_isShared_4656_ = v_isSharedCheck_4668_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_v_4653_);
lean_inc(v_k_4652_);
lean_dec(v_r_4358_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4668_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4660_; 
v___x_4657_ = lean_unsigned_to_nat(3u);
v___x_4658_ = lean_unsigned_to_nat(1u);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 4, v_l_4357_);
lean_ctor_set(v___x_4655_, 3, v_l_4357_);
lean_ctor_set(v___x_4655_, 2, v_v_4356_);
lean_ctor_set(v___x_4655_, 1, v_k_4355_);
lean_ctor_set(v___x_4655_, 0, v___x_4658_);
v___x_4660_ = v___x_4655_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v___x_4658_);
lean_ctor_set(v_reuseFailAlloc_4667_, 1, v_k_4355_);
lean_ctor_set(v_reuseFailAlloc_4667_, 2, v_v_4356_);
lean_ctor_set(v_reuseFailAlloc_4667_, 3, v_l_4357_);
lean_ctor_set(v_reuseFailAlloc_4667_, 4, v_l_4357_);
v___x_4660_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
lean_object* v___x_4662_; 
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 4, v_l_4357_);
lean_ctor_set(v___x_4523_, 3, v_l_4357_);
lean_ctor_set(v___x_4523_, 2, v_v_4651_);
lean_ctor_set(v___x_4523_, 1, v_k_4650_);
lean_ctor_set(v___x_4523_, 0, v___x_4658_);
v___x_4662_ = v___x_4523_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4658_);
lean_ctor_set(v_reuseFailAlloc_4666_, 1, v_k_4650_);
lean_ctor_set(v_reuseFailAlloc_4666_, 2, v_v_4651_);
lean_ctor_set(v_reuseFailAlloc_4666_, 3, v_l_4357_);
lean_ctor_set(v_reuseFailAlloc_4666_, 4, v_l_4357_);
v___x_4662_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
lean_object* v___x_4664_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v___x_4662_);
lean_ctor_set(v___x_4648_, 3, v___x_4660_);
lean_ctor_set(v___x_4648_, 2, v_v_4653_);
lean_ctor_set(v___x_4648_, 1, v_k_4652_);
lean_ctor_set(v___x_4648_, 0, v___x_4657_);
v___x_4664_ = v___x_4648_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4657_);
lean_ctor_set(v_reuseFailAlloc_4665_, 1, v_k_4652_);
lean_ctor_set(v_reuseFailAlloc_4665_, 2, v_v_4653_);
lean_ctor_set(v_reuseFailAlloc_4665_, 3, v___x_4660_);
lean_ctor_set(v_reuseFailAlloc_4665_, 4, v___x_4662_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
}
}
else
{
lean_object* v_k_4678_; lean_object* v_v_4679_; lean_object* v___x_4680_; lean_object* v___x_4682_; 
v_k_4678_ = lean_ctor_get(v_d_4525_, 0);
lean_inc(v_k_4678_);
v_v_4679_ = lean_ctor_get(v_d_4525_, 1);
lean_inc(v_v_4679_);
lean_dec_ref(v_d_4525_);
v___x_4680_ = lean_unsigned_to_nat(2u);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 4, v_r_4358_);
lean_ctor_set(v___x_4523_, 3, v_l_4174_);
lean_ctor_set(v___x_4523_, 2, v_v_4679_);
lean_ctor_set(v___x_4523_, 1, v_k_4678_);
lean_ctor_set(v___x_4523_, 0, v___x_4680_);
v___x_4682_ = v___x_4523_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v___x_4680_);
lean_ctor_set(v_reuseFailAlloc_4683_, 1, v_k_4678_);
lean_ctor_set(v_reuseFailAlloc_4683_, 2, v_v_4679_);
lean_ctor_set(v_reuseFailAlloc_4683_, 3, v_l_4174_);
lean_ctor_set(v_reuseFailAlloc_4683_, 4, v_r_4358_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
}
}
}
else
{
return v_l_4174_;
}
}
else
{
return v_r_4175_;
}
}
default: 
{
lean_object* v___x_4690_; 
v___x_4690_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4169_, v_k_4170_, v_r_4175_);
if (lean_obj_tag(v___x_4690_) == 0)
{
if (lean_obj_tag(v_l_4174_) == 0)
{
lean_object* v_size_4691_; lean_object* v_size_4692_; lean_object* v_k_4693_; lean_object* v_v_4694_; lean_object* v_l_4695_; lean_object* v_r_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; uint8_t v___x_4699_; 
v_size_4691_ = lean_ctor_get(v___x_4690_, 0);
lean_inc(v_size_4691_);
v_size_4692_ = lean_ctor_get(v_l_4174_, 0);
v_k_4693_ = lean_ctor_get(v_l_4174_, 1);
v_v_4694_ = lean_ctor_get(v_l_4174_, 2);
v_l_4695_ = lean_ctor_get(v_l_4174_, 3);
v_r_4696_ = lean_ctor_get(v_l_4174_, 4);
lean_inc(v_r_4696_);
v___x_4697_ = lean_unsigned_to_nat(3u);
v___x_4698_ = lean_nat_mul(v___x_4697_, v_size_4691_);
v___x_4699_ = lean_nat_dec_lt(v___x_4698_, v_size_4692_);
lean_dec(v___x_4698_);
if (v___x_4699_ == 0)
{
lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4704_; 
lean_dec(v_r_4696_);
v___x_4700_ = lean_unsigned_to_nat(1u);
v___x_4701_ = lean_nat_add(v___x_4700_, v_size_4692_);
v___x_4702_ = lean_nat_add(v___x_4701_, v_size_4691_);
lean_dec(v_size_4691_);
lean_dec(v___x_4701_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 4, v___x_4690_);
lean_ctor_set(v___x_4177_, 0, v___x_4702_);
v___x_4704_ = v___x_4177_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v___x_4702_);
lean_ctor_set(v_reuseFailAlloc_4705_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4705_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4705_, 3, v_l_4174_);
lean_ctor_set(v_reuseFailAlloc_4705_, 4, v___x_4690_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
else
{
lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4777_; 
lean_inc(v_l_4695_);
lean_inc(v_v_4694_);
lean_inc(v_k_4693_);
lean_inc(v_size_4692_);
v_isSharedCheck_4777_ = !lean_is_exclusive(v_l_4174_);
if (v_isSharedCheck_4777_ == 0)
{
lean_object* v_unused_4778_; lean_object* v_unused_4779_; lean_object* v_unused_4780_; lean_object* v_unused_4781_; lean_object* v_unused_4782_; 
v_unused_4778_ = lean_ctor_get(v_l_4174_, 4);
lean_dec(v_unused_4778_);
v_unused_4779_ = lean_ctor_get(v_l_4174_, 3);
lean_dec(v_unused_4779_);
v_unused_4780_ = lean_ctor_get(v_l_4174_, 2);
lean_dec(v_unused_4780_);
v_unused_4781_ = lean_ctor_get(v_l_4174_, 1);
lean_dec(v_unused_4781_);
v_unused_4782_ = lean_ctor_get(v_l_4174_, 0);
lean_dec(v_unused_4782_);
v___x_4707_ = v_l_4174_;
v_isShared_4708_ = v_isSharedCheck_4777_;
goto v_resetjp_4706_;
}
else
{
lean_dec(v_l_4174_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4777_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
if (lean_obj_tag(v_l_4695_) == 0)
{
if (lean_obj_tag(v_r_4696_) == 0)
{
lean_object* v_size_4709_; lean_object* v_size_4710_; lean_object* v_k_4711_; lean_object* v_v_4712_; lean_object* v_l_4713_; lean_object* v_r_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; uint8_t v___x_4717_; 
v_size_4709_ = lean_ctor_get(v_l_4695_, 0);
v_size_4710_ = lean_ctor_get(v_r_4696_, 0);
v_k_4711_ = lean_ctor_get(v_r_4696_, 1);
v_v_4712_ = lean_ctor_get(v_r_4696_, 2);
v_l_4713_ = lean_ctor_get(v_r_4696_, 3);
v_r_4714_ = lean_ctor_get(v_r_4696_, 4);
v___x_4715_ = lean_unsigned_to_nat(2u);
v___x_4716_ = lean_nat_mul(v___x_4715_, v_size_4709_);
v___x_4717_ = lean_nat_dec_lt(v_size_4710_, v___x_4716_);
lean_dec(v___x_4716_);
if (v___x_4717_ == 0)
{
lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4747_; 
lean_inc(v_r_4714_);
lean_inc(v_l_4713_);
lean_inc(v_v_4712_);
lean_inc(v_k_4711_);
v_isSharedCheck_4747_ = !lean_is_exclusive(v_r_4696_);
if (v_isSharedCheck_4747_ == 0)
{
lean_object* v_unused_4748_; lean_object* v_unused_4749_; lean_object* v_unused_4750_; lean_object* v_unused_4751_; lean_object* v_unused_4752_; 
v_unused_4748_ = lean_ctor_get(v_r_4696_, 4);
lean_dec(v_unused_4748_);
v_unused_4749_ = lean_ctor_get(v_r_4696_, 3);
lean_dec(v_unused_4749_);
v_unused_4750_ = lean_ctor_get(v_r_4696_, 2);
lean_dec(v_unused_4750_);
v_unused_4751_ = lean_ctor_get(v_r_4696_, 1);
lean_dec(v_unused_4751_);
v_unused_4752_ = lean_ctor_get(v_r_4696_, 0);
lean_dec(v_unused_4752_);
v___x_4719_ = v_r_4696_;
v_isShared_4720_ = v_isSharedCheck_4747_;
goto v_resetjp_4718_;
}
else
{
lean_dec(v_r_4696_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4747_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___y_4725_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___x_4735_; lean_object* v___y_4737_; 
v___x_4721_ = lean_unsigned_to_nat(1u);
v___x_4722_ = lean_nat_add(v___x_4721_, v_size_4692_);
lean_dec(v_size_4692_);
v___x_4723_ = lean_nat_add(v___x_4722_, v_size_4691_);
lean_dec(v___x_4722_);
v___x_4735_ = lean_nat_add(v___x_4721_, v_size_4709_);
if (lean_obj_tag(v_l_4713_) == 0)
{
lean_object* v_size_4745_; 
v_size_4745_ = lean_ctor_get(v_l_4713_, 0);
lean_inc(v_size_4745_);
v___y_4737_ = v_size_4745_;
goto v___jp_4736_;
}
else
{
lean_object* v___x_4746_; 
v___x_4746_ = lean_unsigned_to_nat(0u);
v___y_4737_ = v___x_4746_;
goto v___jp_4736_;
}
v___jp_4724_:
{
lean_object* v___x_4728_; lean_object* v___x_4730_; 
v___x_4728_ = lean_nat_add(v___y_4726_, v___y_4727_);
lean_dec(v___y_4727_);
lean_dec(v___y_4726_);
if (v_isShared_4720_ == 0)
{
lean_ctor_set(v___x_4719_, 4, v___x_4690_);
lean_ctor_set(v___x_4719_, 3, v_r_4714_);
lean_ctor_set(v___x_4719_, 2, v_v_4173_);
lean_ctor_set(v___x_4719_, 1, v_k_4172_);
lean_ctor_set(v___x_4719_, 0, v___x_4728_);
v___x_4730_ = v___x_4719_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4728_);
lean_ctor_set(v_reuseFailAlloc_4734_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4734_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4734_, 3, v_r_4714_);
lean_ctor_set(v_reuseFailAlloc_4734_, 4, v___x_4690_);
v___x_4730_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
lean_object* v___x_4732_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 4, v___x_4730_);
lean_ctor_set(v___x_4707_, 3, v___y_4725_);
lean_ctor_set(v___x_4707_, 2, v_v_4712_);
lean_ctor_set(v___x_4707_, 1, v_k_4711_);
lean_ctor_set(v___x_4707_, 0, v___x_4723_);
v___x_4732_ = v___x_4707_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4723_);
lean_ctor_set(v_reuseFailAlloc_4733_, 1, v_k_4711_);
lean_ctor_set(v_reuseFailAlloc_4733_, 2, v_v_4712_);
lean_ctor_set(v_reuseFailAlloc_4733_, 3, v___y_4725_);
lean_ctor_set(v_reuseFailAlloc_4733_, 4, v___x_4730_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
v___jp_4736_:
{
lean_object* v___x_4738_; lean_object* v___x_4740_; 
v___x_4738_ = lean_nat_add(v___x_4735_, v___y_4737_);
lean_dec(v___y_4737_);
lean_dec(v___x_4735_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 4, v_l_4713_);
lean_ctor_set(v___x_4177_, 3, v_l_4695_);
lean_ctor_set(v___x_4177_, 2, v_v_4694_);
lean_ctor_set(v___x_4177_, 1, v_k_4693_);
lean_ctor_set(v___x_4177_, 0, v___x_4738_);
v___x_4740_ = v___x_4177_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4738_);
lean_ctor_set(v_reuseFailAlloc_4744_, 1, v_k_4693_);
lean_ctor_set(v_reuseFailAlloc_4744_, 2, v_v_4694_);
lean_ctor_set(v_reuseFailAlloc_4744_, 3, v_l_4695_);
lean_ctor_set(v_reuseFailAlloc_4744_, 4, v_l_4713_);
v___x_4740_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
lean_object* v___x_4741_; 
v___x_4741_ = lean_nat_add(v___x_4721_, v_size_4691_);
lean_dec(v_size_4691_);
if (lean_obj_tag(v_r_4714_) == 0)
{
lean_object* v_size_4742_; 
v_size_4742_ = lean_ctor_get(v_r_4714_, 0);
lean_inc(v_size_4742_);
v___y_4725_ = v___x_4740_;
v___y_4726_ = v___x_4741_;
v___y_4727_ = v_size_4742_;
goto v___jp_4724_;
}
else
{
lean_object* v___x_4743_; 
v___x_4743_ = lean_unsigned_to_nat(0u);
v___y_4725_ = v___x_4740_;
v___y_4726_ = v___x_4741_;
v___y_4727_ = v___x_4743_;
goto v___jp_4724_;
}
}
}
}
}
else
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4759_; 
lean_del_object(v___x_4177_);
v___x_4753_ = lean_unsigned_to_nat(1u);
v___x_4754_ = lean_nat_add(v___x_4753_, v_size_4692_);
lean_dec(v_size_4692_);
v___x_4755_ = lean_nat_add(v___x_4754_, v_size_4691_);
lean_dec(v___x_4754_);
v___x_4756_ = lean_nat_add(v___x_4753_, v_size_4691_);
lean_dec(v_size_4691_);
v___x_4757_ = lean_nat_add(v___x_4756_, v_size_4710_);
lean_dec(v___x_4756_);
lean_inc_ref(v___x_4690_);
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 4, v___x_4690_);
lean_ctor_set(v___x_4707_, 3, v_r_4696_);
lean_ctor_set(v___x_4707_, 2, v_v_4173_);
lean_ctor_set(v___x_4707_, 1, v_k_4172_);
lean_ctor_set(v___x_4707_, 0, v___x_4757_);
v___x_4759_ = v___x_4707_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v___x_4757_);
lean_ctor_set(v_reuseFailAlloc_4772_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4772_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4772_, 3, v_r_4696_);
lean_ctor_set(v_reuseFailAlloc_4772_, 4, v___x_4690_);
v___x_4759_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4766_; 
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4766_ == 0)
{
lean_object* v_unused_4767_; lean_object* v_unused_4768_; lean_object* v_unused_4769_; lean_object* v_unused_4770_; lean_object* v_unused_4771_; 
v_unused_4767_ = lean_ctor_get(v___x_4690_, 4);
lean_dec(v_unused_4767_);
v_unused_4768_ = lean_ctor_get(v___x_4690_, 3);
lean_dec(v_unused_4768_);
v_unused_4769_ = lean_ctor_get(v___x_4690_, 2);
lean_dec(v_unused_4769_);
v_unused_4770_ = lean_ctor_get(v___x_4690_, 1);
lean_dec(v_unused_4770_);
v_unused_4771_ = lean_ctor_get(v___x_4690_, 0);
lean_dec(v_unused_4771_);
v___x_4761_ = v___x_4690_;
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
else
{
lean_dec(v___x_4690_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
lean_ctor_set(v___x_4761_, 4, v___x_4759_);
lean_ctor_set(v___x_4761_, 3, v_l_4695_);
lean_ctor_set(v___x_4761_, 2, v_v_4694_);
lean_ctor_set(v___x_4761_, 1, v_k_4693_);
lean_ctor_set(v___x_4761_, 0, v___x_4755_);
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4755_);
lean_ctor_set(v_reuseFailAlloc_4765_, 1, v_k_4693_);
lean_ctor_set(v_reuseFailAlloc_4765_, 2, v_v_4694_);
lean_ctor_set(v_reuseFailAlloc_4765_, 3, v_l_4695_);
lean_ctor_set(v_reuseFailAlloc_4765_, 4, v___x_4759_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
}
else
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
lean_dec_ref_known(v_l_4695_, 5);
lean_del_object(v___x_4707_);
lean_dec(v_v_4694_);
lean_dec(v_k_4693_);
lean_dec(v_size_4692_);
lean_dec(v_size_4691_);
lean_dec_ref_known(v___x_4690_, 5);
lean_del_object(v___x_4177_);
lean_dec(v_v_4173_);
lean_dec(v_k_4172_);
v___x_4773_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3);
v___x_4774_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4773_);
return v___x_4774_;
}
}
else
{
lean_object* v___x_4775_; lean_object* v___x_4776_; 
lean_del_object(v___x_4707_);
lean_dec(v_r_4696_);
lean_dec(v_v_4694_);
lean_dec(v_k_4693_);
lean_dec(v_size_4692_);
lean_dec(v_size_4691_);
lean_dec_ref_known(v___x_4690_, 5);
lean_del_object(v___x_4177_);
lean_dec(v_v_4173_);
lean_dec(v_k_4172_);
v___x_4775_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4);
v___x_4776_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4775_);
return v___x_4776_;
}
}
}
}
else
{
lean_object* v_size_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4787_; 
v_size_4783_ = lean_ctor_get(v___x_4690_, 0);
lean_inc(v_size_4783_);
v___x_4784_ = lean_unsigned_to_nat(1u);
v___x_4785_ = lean_nat_add(v___x_4784_, v_size_4783_);
lean_dec(v_size_4783_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 4, v___x_4690_);
lean_ctor_set(v___x_4177_, 0, v___x_4785_);
v___x_4787_ = v___x_4177_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4785_);
lean_ctor_set(v_reuseFailAlloc_4788_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4788_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4788_, 3, v_l_4174_);
lean_ctor_set(v_reuseFailAlloc_4788_, 4, v___x_4690_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
else
{
if (lean_obj_tag(v_l_4174_) == 0)
{
lean_object* v_l_4789_; 
v_l_4789_ = lean_ctor_get(v_l_4174_, 3);
if (lean_obj_tag(v_l_4789_) == 0)
{
lean_object* v_r_4790_; 
lean_inc_ref(v_l_4789_);
v_r_4790_ = lean_ctor_get(v_l_4174_, 4);
lean_inc(v_r_4790_);
if (lean_obj_tag(v_r_4790_) == 0)
{
lean_object* v_size_4791_; lean_object* v_k_4792_; lean_object* v_v_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4807_; 
v_size_4791_ = lean_ctor_get(v_l_4174_, 0);
v_k_4792_ = lean_ctor_get(v_l_4174_, 1);
v_v_4793_ = lean_ctor_get(v_l_4174_, 2);
v_isSharedCheck_4807_ = !lean_is_exclusive(v_l_4174_);
if (v_isSharedCheck_4807_ == 0)
{
lean_object* v_unused_4808_; lean_object* v_unused_4809_; 
v_unused_4808_ = lean_ctor_get(v_l_4174_, 4);
lean_dec(v_unused_4808_);
v_unused_4809_ = lean_ctor_get(v_l_4174_, 3);
lean_dec(v_unused_4809_);
v___x_4795_ = v_l_4174_;
v_isShared_4796_ = v_isSharedCheck_4807_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_v_4793_);
lean_inc(v_k_4792_);
lean_inc(v_size_4791_);
lean_dec(v_l_4174_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4807_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v_size_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4802_; 
v_size_4797_ = lean_ctor_get(v_r_4790_, 0);
v___x_4798_ = lean_unsigned_to_nat(1u);
v___x_4799_ = lean_nat_add(v___x_4798_, v_size_4791_);
lean_dec(v_size_4791_);
v___x_4800_ = lean_nat_add(v___x_4798_, v_size_4797_);
if (v_isShared_4796_ == 0)
{
lean_ctor_set(v___x_4795_, 4, v___x_4690_);
lean_ctor_set(v___x_4795_, 3, v_r_4790_);
lean_ctor_set(v___x_4795_, 2, v_v_4173_);
lean_ctor_set(v___x_4795_, 1, v_k_4172_);
lean_ctor_set(v___x_4795_, 0, v___x_4800_);
v___x_4802_ = v___x_4795_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4800_);
lean_ctor_set(v_reuseFailAlloc_4806_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4806_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4806_, 3, v_r_4790_);
lean_ctor_set(v_reuseFailAlloc_4806_, 4, v___x_4690_);
v___x_4802_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
lean_object* v___x_4804_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 4, v___x_4802_);
lean_ctor_set(v___x_4177_, 3, v_l_4789_);
lean_ctor_set(v___x_4177_, 2, v_v_4793_);
lean_ctor_set(v___x_4177_, 1, v_k_4792_);
lean_ctor_set(v___x_4177_, 0, v___x_4799_);
v___x_4804_ = v___x_4177_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v___x_4799_);
lean_ctor_set(v_reuseFailAlloc_4805_, 1, v_k_4792_);
lean_ctor_set(v_reuseFailAlloc_4805_, 2, v_v_4793_);
lean_ctor_set(v_reuseFailAlloc_4805_, 3, v_l_4789_);
lean_ctor_set(v_reuseFailAlloc_4805_, 4, v___x_4802_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
}
else
{
lean_object* v_k_4810_; lean_object* v_v_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4823_; 
v_k_4810_ = lean_ctor_get(v_l_4174_, 1);
v_v_4811_ = lean_ctor_get(v_l_4174_, 2);
v_isSharedCheck_4823_ = !lean_is_exclusive(v_l_4174_);
if (v_isSharedCheck_4823_ == 0)
{
lean_object* v_unused_4824_; lean_object* v_unused_4825_; lean_object* v_unused_4826_; 
v_unused_4824_ = lean_ctor_get(v_l_4174_, 4);
lean_dec(v_unused_4824_);
v_unused_4825_ = lean_ctor_get(v_l_4174_, 3);
lean_dec(v_unused_4825_);
v_unused_4826_ = lean_ctor_get(v_l_4174_, 0);
lean_dec(v_unused_4826_);
v___x_4813_ = v_l_4174_;
v_isShared_4814_ = v_isSharedCheck_4823_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_v_4811_);
lean_inc(v_k_4810_);
lean_dec(v_l_4174_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4823_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4818_; 
v___x_4815_ = lean_unsigned_to_nat(3u);
v___x_4816_ = lean_unsigned_to_nat(1u);
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 3, v_r_4790_);
lean_ctor_set(v___x_4813_, 2, v_v_4173_);
lean_ctor_set(v___x_4813_, 1, v_k_4172_);
lean_ctor_set(v___x_4813_, 0, v___x_4816_);
v___x_4818_ = v___x_4813_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4816_);
lean_ctor_set(v_reuseFailAlloc_4822_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4822_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4822_, 3, v_r_4790_);
lean_ctor_set(v_reuseFailAlloc_4822_, 4, v_r_4790_);
v___x_4818_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
lean_object* v___x_4820_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 4, v___x_4818_);
lean_ctor_set(v___x_4177_, 3, v_l_4789_);
lean_ctor_set(v___x_4177_, 2, v_v_4811_);
lean_ctor_set(v___x_4177_, 1, v_k_4810_);
lean_ctor_set(v___x_4177_, 0, v___x_4815_);
v___x_4820_ = v___x_4177_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v___x_4815_);
lean_ctor_set(v_reuseFailAlloc_4821_, 1, v_k_4810_);
lean_ctor_set(v_reuseFailAlloc_4821_, 2, v_v_4811_);
lean_ctor_set(v_reuseFailAlloc_4821_, 3, v_l_4789_);
lean_ctor_set(v_reuseFailAlloc_4821_, 4, v___x_4818_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
}
}
}
else
{
lean_object* v_r_4827_; 
v_r_4827_ = lean_ctor_get(v_l_4174_, 4);
lean_inc(v_r_4827_);
if (lean_obj_tag(v_r_4827_) == 0)
{
lean_object* v_k_4828_; lean_object* v_v_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4853_; 
lean_inc(v_l_4789_);
v_k_4828_ = lean_ctor_get(v_l_4174_, 1);
v_v_4829_ = lean_ctor_get(v_l_4174_, 2);
v_isSharedCheck_4853_ = !lean_is_exclusive(v_l_4174_);
if (v_isSharedCheck_4853_ == 0)
{
lean_object* v_unused_4854_; lean_object* v_unused_4855_; lean_object* v_unused_4856_; 
v_unused_4854_ = lean_ctor_get(v_l_4174_, 4);
lean_dec(v_unused_4854_);
v_unused_4855_ = lean_ctor_get(v_l_4174_, 3);
lean_dec(v_unused_4855_);
v_unused_4856_ = lean_ctor_get(v_l_4174_, 0);
lean_dec(v_unused_4856_);
v___x_4831_ = v_l_4174_;
v_isShared_4832_ = v_isSharedCheck_4853_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_v_4829_);
lean_inc(v_k_4828_);
lean_dec(v_l_4174_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4853_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v_k_4833_; lean_object* v_v_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4849_; 
v_k_4833_ = lean_ctor_get(v_r_4827_, 1);
v_v_4834_ = lean_ctor_get(v_r_4827_, 2);
v_isSharedCheck_4849_ = !lean_is_exclusive(v_r_4827_);
if (v_isSharedCheck_4849_ == 0)
{
lean_object* v_unused_4850_; lean_object* v_unused_4851_; lean_object* v_unused_4852_; 
v_unused_4850_ = lean_ctor_get(v_r_4827_, 4);
lean_dec(v_unused_4850_);
v_unused_4851_ = lean_ctor_get(v_r_4827_, 3);
lean_dec(v_unused_4851_);
v_unused_4852_ = lean_ctor_get(v_r_4827_, 0);
lean_dec(v_unused_4852_);
v___x_4836_ = v_r_4827_;
v_isShared_4837_ = v_isSharedCheck_4849_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_v_4834_);
lean_inc(v_k_4833_);
lean_dec(v_r_4827_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4849_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4841_; 
v___x_4838_ = lean_unsigned_to_nat(3u);
v___x_4839_ = lean_unsigned_to_nat(1u);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 4, v_l_4789_);
lean_ctor_set(v___x_4836_, 3, v_l_4789_);
lean_ctor_set(v___x_4836_, 2, v_v_4829_);
lean_ctor_set(v___x_4836_, 1, v_k_4828_);
lean_ctor_set(v___x_4836_, 0, v___x_4839_);
v___x_4841_ = v___x_4836_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4839_);
lean_ctor_set(v_reuseFailAlloc_4848_, 1, v_k_4828_);
lean_ctor_set(v_reuseFailAlloc_4848_, 2, v_v_4829_);
lean_ctor_set(v_reuseFailAlloc_4848_, 3, v_l_4789_);
lean_ctor_set(v_reuseFailAlloc_4848_, 4, v_l_4789_);
v___x_4841_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
lean_object* v___x_4843_; 
if (v_isShared_4832_ == 0)
{
lean_ctor_set(v___x_4831_, 4, v_l_4789_);
lean_ctor_set(v___x_4831_, 2, v_v_4173_);
lean_ctor_set(v___x_4831_, 1, v_k_4172_);
lean_ctor_set(v___x_4831_, 0, v___x_4839_);
v___x_4843_ = v___x_4831_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4839_);
lean_ctor_set(v_reuseFailAlloc_4847_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4847_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4847_, 3, v_l_4789_);
lean_ctor_set(v_reuseFailAlloc_4847_, 4, v_l_4789_);
v___x_4843_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
lean_object* v___x_4845_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 4, v___x_4843_);
lean_ctor_set(v___x_4177_, 3, v___x_4841_);
lean_ctor_set(v___x_4177_, 2, v_v_4834_);
lean_ctor_set(v___x_4177_, 1, v_k_4833_);
lean_ctor_set(v___x_4177_, 0, v___x_4838_);
v___x_4845_ = v___x_4177_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4838_);
lean_ctor_set(v_reuseFailAlloc_4846_, 1, v_k_4833_);
lean_ctor_set(v_reuseFailAlloc_4846_, 2, v_v_4834_);
lean_ctor_set(v_reuseFailAlloc_4846_, 3, v___x_4841_);
lean_ctor_set(v_reuseFailAlloc_4846_, 4, v___x_4843_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
}
}
else
{
lean_object* v___x_4857_; lean_object* v___x_4859_; 
v___x_4857_ = lean_unsigned_to_nat(2u);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 4, v_r_4827_);
lean_ctor_set(v___x_4177_, 0, v___x_4857_);
v___x_4859_ = v___x_4177_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4857_);
lean_ctor_set(v_reuseFailAlloc_4860_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4860_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4860_, 3, v_l_4174_);
lean_ctor_set(v_reuseFailAlloc_4860_, 4, v_r_4827_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
}
}
else
{
lean_object* v___x_4861_; lean_object* v___x_4863_; 
v___x_4861_ = lean_unsigned_to_nat(1u);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 4, v_l_4174_);
lean_ctor_set(v___x_4177_, 0, v___x_4861_);
v___x_4863_ = v___x_4177_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v___x_4861_);
lean_ctor_set(v_reuseFailAlloc_4864_, 1, v_k_4172_);
lean_ctor_set(v_reuseFailAlloc_4864_, 2, v_v_4173_);
lean_ctor_set(v_reuseFailAlloc_4864_, 3, v_l_4174_);
lean_ctor_set(v_reuseFailAlloc_4864_, 4, v_l_4174_);
v___x_4863_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
return v___x_4863_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_4170_);
lean_dec_ref(v_cmp_4169_);
return v_t_4171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(lean_object* v_cmp_4867_, lean_object* v_init_4868_, lean_object* v_x_4869_){
_start:
{
if (lean_obj_tag(v_x_4869_) == 0)
{
lean_object* v_k_4870_; lean_object* v_l_4871_; lean_object* v_r_4872_; lean_object* v___x_4873_; lean_object* v_a_4874_; lean_object* v_r_4875_; 
v_k_4870_ = lean_ctor_get(v_x_4869_, 1);
lean_inc(v_k_4870_);
v_l_4871_ = lean_ctor_get(v_x_4869_, 3);
lean_inc(v_l_4871_);
v_r_4872_ = lean_ctor_get(v_x_4869_, 4);
lean_inc(v_r_4872_);
lean_dec_ref_known(v_x_4869_, 5);
lean_inc_ref_n(v_cmp_4867_, 2);
v___x_4873_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4867_, v_init_4868_, v_l_4871_);
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
lean_inc(v_a_4874_);
lean_dec_ref(v___x_4873_);
v_r_4875_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4867_, v_k_4870_, v_a_4874_);
v_init_4868_ = v_r_4875_;
v_x_4869_ = v_r_4872_;
goto _start;
}
else
{
lean_object* v___x_4877_; 
lean_dec_ref(v_cmp_4867_);
v___x_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4877_, 0, v_init_4868_);
return v___x_4877_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(lean_object* v_cmp_4878_, lean_object* v_t_u2081_4879_, lean_object* v_t_u2082_4880_){
_start:
{
lean_object* v___y_4882_; lean_object* v___y_4883_; lean_object* v___y_4889_; 
if (lean_obj_tag(v_t_u2081_4879_) == 0)
{
lean_object* v_size_4892_; 
v_size_4892_ = lean_ctor_get(v_t_u2081_4879_, 0);
lean_inc(v_size_4892_);
v___y_4889_ = v_size_4892_;
goto v___jp_4888_;
}
else
{
lean_object* v___x_4893_; 
v___x_4893_ = lean_unsigned_to_nat(0u);
v___y_4889_ = v___x_4893_;
goto v___jp_4888_;
}
v___jp_4881_:
{
uint8_t v___x_4884_; 
v___x_4884_ = lean_nat_dec_le(v___y_4882_, v___y_4883_);
if (v___x_4884_ == 0)
{
lean_object* v___x_4885_; lean_object* v_a_4886_; 
lean_dec(v___y_4883_);
lean_dec(v___y_4882_);
v___x_4885_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4878_, v_t_u2081_4879_, v_t_u2082_4880_);
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc(v_a_4886_);
lean_dec_ref(v___x_4885_);
return v_a_4886_;
}
else
{
lean_object* v___x_4887_; 
v___x_4887_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4878_, v_t_u2082_4880_, v___y_4882_, v___y_4883_, v_t_u2081_4879_);
lean_dec(v___y_4883_);
lean_dec(v___y_4882_);
return v___x_4887_;
}
}
v___jp_4888_:
{
if (lean_obj_tag(v_t_u2082_4880_) == 0)
{
lean_object* v_size_4890_; 
v_size_4890_ = lean_ctor_get(v_t_u2082_4880_, 0);
lean_inc(v_size_4890_);
v___y_4882_ = v___y_4889_;
v___y_4883_ = v_size_4890_;
goto v___jp_4881_;
}
else
{
lean_object* v___x_4891_; 
v___x_4891_ = lean_unsigned_to_nat(0u);
v___y_4882_ = v___y_4889_;
v___y_4883_ = v___x_4891_;
goto v___jp_4881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff___redArg(lean_object* v_cmp_4894_, lean_object* v_t_u2081_4895_, lean_object* v_t_u2082_4896_){
_start:
{
lean_object* v___x_4897_; 
v___x_4897_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4894_, v_t_u2081_4895_, v_t_u2082_4896_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff(lean_object* v_00_u03b1_4898_, lean_object* v_00_u03b2_4899_, lean_object* v_cmp_4900_, lean_object* v_t_u2081_4901_, lean_object* v_t_u2082_4902_){
_start:
{
lean_object* v___x_4903_; 
v___x_4903_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4900_, v_t_u2081_4901_, v_t_u2082_4902_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0(lean_object* v_00_u03b1_4904_, lean_object* v_cmp_4905_, lean_object* v_00_u03b2_4906_, lean_object* v_t_u2081_4907_, lean_object* v_t_u2082_4908_){
_start:
{
lean_object* v___x_4909_; 
v___x_4909_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4905_, v_t_u2081_4907_, v_t_u2082_4908_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0(lean_object* v_00_u03b1_4910_, lean_object* v_cmp_4911_, lean_object* v_00_u03b2_4912_, lean_object* v_k_4913_, lean_object* v_t_4914_){
_start:
{
lean_object* v___x_4915_; 
v___x_4915_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4911_, v_k_4913_, v_t_4914_);
return v___x_4915_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1(lean_object* v_00_u03b1_4916_, lean_object* v_00_u03b2_4917_, lean_object* v_cmp_4918_, lean_object* v_init_4919_, lean_object* v_x_4920_){
_start:
{
lean_object* v___x_4921_; 
v___x_4921_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4918_, v_init_4919_, v_x_4920_);
return v___x_4921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2(lean_object* v_00_u03b1_4922_, lean_object* v_00_u03b2_4923_, lean_object* v_cmp_4924_, lean_object* v_t_u2082_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v_t_4928_){
_start:
{
lean_object* v___x_4929_; 
v___x_4929_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4924_, v_t_u2082_4925_, v___y_4926_, v___y_4927_, v_t_4928_);
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4930_, lean_object* v_00_u03b2_4931_, lean_object* v_cmp_4932_, lean_object* v_t_u2082_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v_t_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2(v_00_u03b1_4930_, v_00_u03b2_4931_, v_cmp_4932_, v_t_u2082_4933_, v___y_4934_, v___y_4935_, v_t_4936_);
lean_dec(v___y_4935_);
lean_dec(v___y_4934_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff___redArg(lean_object* v_cmp_4938_){
_start:
{
lean_object* v___x_4939_; 
v___x_4939_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_4939_, 0, lean_box(0));
lean_closure_set(v___x_4939_, 1, lean_box(0));
lean_closure_set(v___x_4939_, 2, v_cmp_4938_);
return v___x_4939_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff(lean_object* v_00_u03b1_4940_, lean_object* v_00_u03b2_4941_, lean_object* v_cmp_4942_){
_start:
{
lean_object* v___x_4943_; 
v___x_4943_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_4943_, 0, lean_box(0));
lean_closure_set(v___x_4943_, 1, lean_box(0));
lean_closure_set(v___x_4943_, 2, v_cmp_4942_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_4944_, lean_object* v_a_4945_, lean_object* v_____s_4946_){
_start:
{
lean_object* v_r_4947_; lean_object* v___x_4948_; 
v_r_4947_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_4944_, v_a_4945_, v_____s_4946_);
v___x_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4948_, 0, v_r_4947_);
return v___x_4948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg(lean_object* v_cmp_4949_, lean_object* v_inst_4950_, lean_object* v_t_4951_, lean_object* v_l_4952_){
_start:
{
lean_object* v___f_4953_; lean_object* v___x_4954_; 
v___f_4953_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4953_, 0, v_cmp_4949_);
v___x_4954_ = lean_apply_4(v_inst_4950_, lean_box(0), v_l_4952_, v_t_4951_, v___f_4953_);
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany(lean_object* v_00_u03b1_4955_, lean_object* v_00_u03b2_4956_, lean_object* v_cmp_4957_, lean_object* v_00_u03c1_4958_, lean_object* v_inst_4959_, lean_object* v_t_4960_, lean_object* v_l_4961_){
_start:
{
lean_object* v___f_4962_; lean_object* v___x_4963_; 
v___f_4962_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4962_, 0, v_cmp_4957_);
v___x_4963_ = lean_apply_4(v_inst_4959_, lean_box(0), v_l_4961_, v_t_4960_, v___f_4962_);
return v___x_4963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0(lean_object* v_cmp_4964_, lean_object* v_x_4965_, lean_object* v_____s_4966_){
_start:
{
lean_object* v_fst_4967_; lean_object* v_snd_4968_; lean_object* v_r_4969_; lean_object* v___x_4970_; 
v_fst_4967_ = lean_ctor_get(v_x_4965_, 0);
lean_inc(v_fst_4967_);
v_snd_4968_ = lean_ctor_get(v_x_4965_, 1);
lean_inc(v_snd_4968_);
lean_dec_ref(v_x_4965_);
v_r_4969_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_4964_, v_fst_4967_, v_snd_4968_, v_____s_4966_);
v___x_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4970_, 0, v_r_4969_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg(lean_object* v_cmp_4971_, lean_object* v_inst_4972_, lean_object* v_t_4973_, lean_object* v_l_4974_){
_start:
{
lean_object* v___f_4975_; lean_object* v___x_4976_; 
v___f_4975_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4975_, 0, v_cmp_4971_);
v___x_4976_ = lean_apply_4(v_inst_4972_, lean_box(0), v_l_4974_, v_t_4973_, v___f_4975_);
return v___x_4976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany(lean_object* v_00_u03b1_4977_, lean_object* v_cmp_4978_, lean_object* v_00_u03b2_4979_, lean_object* v_00_u03c1_4980_, lean_object* v_inst_4981_, lean_object* v_t_4982_, lean_object* v_l_4983_){
_start:
{
lean_object* v___f_4984_; lean_object* v___x_4985_; 
v___f_4984_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4984_, 0, v_cmp_4978_);
v___x_4985_ = lean_apply_4(v_inst_4981_, lean_box(0), v_l_4983_, v_t_4982_, v___f_4984_);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_4986_, lean_object* v_a_4987_, lean_object* v_____s_4988_){
_start:
{
uint8_t v___x_4989_; 
lean_inc(v_____s_4988_);
lean_inc(v_a_4987_);
lean_inc_ref(v_cmp_4986_);
v___x_4989_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4986_, v_a_4987_, v_____s_4988_);
if (v___x_4989_ == 0)
{
lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4990_ = lean_box(0);
v___x_4991_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_4986_, v_a_4987_, v___x_4990_, v_____s_4988_);
v___x_4992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4991_);
return v___x_4992_;
}
else
{
lean_object* v___x_4993_; 
lean_dec(v_a_4987_);
lean_dec_ref(v_cmp_4986_);
v___x_4993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4993_, 0, v_____s_4988_);
return v___x_4993_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_4994_, lean_object* v_inst_4995_, lean_object* v_t_4996_, lean_object* v_l_4997_){
_start:
{
lean_object* v___f_4998_; lean_object* v___x_4999_; 
v___f_4998_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4998_, 0, v_cmp_4994_);
v___x_4999_ = lean_apply_4(v_inst_4995_, lean_box(0), v_l_4997_, v_t_4996_, v___f_4998_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_5000_, lean_object* v_cmp_5001_, lean_object* v_00_u03c1_5002_, lean_object* v_inst_5003_, lean_object* v_t_5004_, lean_object* v_l_5005_){
_start:
{
lean_object* v___f_5006_; lean_object* v___x_5007_; 
v___f_5006_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5006_, 0, v_cmp_5001_);
v___x_5007_ = lean_apply_4(v_inst_5003_, lean_box(0), v_l_5005_, v_t_5004_, v___f_5006_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(lean_object* v___f_5011_, lean_object* v___x_5012_, lean_object* v_m_5013_, lean_object* v_prec_5014_){
_start:
{
lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5015_ = ((lean_object*)(l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__1));
v___x_5016_ = lean_box(0);
v___x_5017_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_5018_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_5017_, v___f_5011_, v___x_5016_, v_m_5013_);
v___x_5019_ = l_List_repr___redArg(v___x_5012_, v___x_5018_);
v___x_5020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5020_, 0, v___x_5015_);
lean_ctor_set(v___x_5020_, 1, v___x_5019_);
v___x_5021_ = l_Repr_addAppParen(v___x_5020_, v_prec_5014_);
return v___x_5021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_5022_, lean_object* v___x_5023_, lean_object* v_m_5024_, lean_object* v_prec_5025_){
_start:
{
lean_object* v_res_5026_; 
v_res_5026_ = l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(v___f_5022_, v___x_5023_, v_m_5024_, v_prec_5025_);
lean_dec(v_prec_5025_);
return v_res_5026_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg(lean_object* v_inst_5027_, lean_object* v_inst_5028_){
_start:
{
lean_object* v___f_5029_; lean_object* v___x_5030_; lean_object* v___f_5031_; 
v___f_5029_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_5030_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_5030_, 0, lean_box(0));
lean_closure_set(v___x_5030_, 1, lean_box(0));
lean_closure_set(v___x_5030_, 2, v_inst_5027_);
lean_closure_set(v___x_5030_, 3, v_inst_5028_);
v___f_5031_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5031_, 0, v___f_5029_);
lean_closure_set(v___f_5031_, 1, v___x_5030_);
return v___f_5031_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr(lean_object* v_00_u03b1_5032_, lean_object* v_00_u03b2_5033_, lean_object* v_cmp_5034_, lean_object* v_inst_5035_, lean_object* v_inst_5036_){
_start:
{
lean_object* v___x_5037_; 
v___x_5037_ = l_Std_DTreeMap_Raw_instRepr___redArg(v_inst_5035_, v_inst_5036_);
return v___x_5037_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___boxed(lean_object* v_00_u03b1_5038_, lean_object* v_00_u03b2_5039_, lean_object* v_cmp_5040_, lean_object* v_inst_5041_, lean_object* v_inst_5042_){
_start:
{
lean_object* v_res_5043_; 
v_res_5043_ = l_Std_DTreeMap_Raw_instRepr(v_00_u03b1_5038_, v_00_u03b2_5039_, v_cmp_5040_, v_inst_5041_, v_inst_5042_);
lean_dec_ref(v_cmp_5040_);
return v_res_5043_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
