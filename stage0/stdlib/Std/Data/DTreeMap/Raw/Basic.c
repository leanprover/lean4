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
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__15 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__15_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_DTreeMap_Raw___auto__1___closed__16 = (const lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__16_value;
static const lean_ctor_object l_Std_DTreeMap_Raw___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__15_value),((lean_object*)&l_Std_DTreeMap_Raw___auto__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__18(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__17));
v___x_51_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__13, &l_Std_DTreeMap_Raw___auto__1___closed__13_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__13);
v___x_52_ = lean_array_push(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__19(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__18, &l_Std_DTreeMap_Raw___auto__1___closed__18_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__18);
v___x_54_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__11));
v___x_55_ = lean_box(2);
v___x_56_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
lean_ctor_set(v___x_56_, 2, v___x_53_);
return v___x_56_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__20(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__19, &l_Std_DTreeMap_Raw___auto__1___closed__19_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__19);
v___x_58_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_59_ = lean_array_push(v___x_58_, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__21(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__20, &l_Std_DTreeMap_Raw___auto__1___closed__20_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__20);
v___x_61_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__9));
v___x_62_ = lean_box(2);
v___x_63_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
lean_ctor_set(v___x_63_, 2, v___x_60_);
return v___x_63_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__22(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__21, &l_Std_DTreeMap_Raw___auto__1___closed__21_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__21);
v___x_65_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_66_ = lean_array_push(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__23(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_67_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__22, &l_Std_DTreeMap_Raw___auto__1___closed__22_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__22);
v___x_68_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__7));
v___x_69_ = lean_box(2);
v___x_70_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_68_);
lean_ctor_set(v___x_70_, 2, v___x_67_);
return v___x_70_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__24(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__23, &l_Std_DTreeMap_Raw___auto__1___closed__23_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__23);
v___x_72_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_73_ = lean_array_push(v___x_72_, v___x_71_);
return v___x_73_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__25(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_74_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__24, &l_Std_DTreeMap_Raw___auto__1___closed__24_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__24);
v___x_75_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__4));
v___x_76_ = lean_box(2);
v___x_77_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_75_);
lean_ctor_set(v___x_77_, 2, v___x_74_);
return v___x_77_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner___redArg(){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(0);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner___redArg___boxed(lean_object* v___dummy_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_DTreeMap_Raw_instCoeWFWFInner___redArg();
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_cmp_85_, lean_object* v_t_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_box(0);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner___boxed(lean_object* v_00_u03b1_88_, lean_object* v_00_u03b2_89_, lean_object* v_cmp_90_, lean_object* v_t_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_DTreeMap_Raw_instCoeWFWFInner(v_00_u03b1_88_, v_00_u03b2_89_, v_cmp_90_, v_t_91_);
lean_dec(v_t_91_);
lean_dec_ref(v_cmp_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___redArg(){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(1);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___redArg___boxed(lean_object* v___dummy_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_DTreeMap_Raw_empty___redArg();
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_cmp_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_box(1);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___boxed(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_cmp_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_DTreeMap_Raw_empty(v_00_u03b1_101_, v_00_u03b2_102_, v_cmp_103_);
lean_dec_ref(v_cmp_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(1);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_DTreeMap_Raw_instEmptyCollection___redArg();
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_109_, lean_object* v_00_u03b2_110_, lean_object* v_cmp_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(1);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___boxed(lean_object* v_00_u03b1_113_, lean_object* v_00_u03b2_114_, lean_object* v_cmp_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_DTreeMap_Raw_instEmptyCollection(v_00_u03b1_113_, v_00_u03b2_114_, v_cmp_115_);
lean_dec_ref(v_cmp_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_box(1);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_DTreeMap_Raw_instInhabited___redArg();
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited(lean_object* v_00_u03b1_121_, lean_object* v_00_u03b2_122_, lean_object* v_cmp_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_box(1);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited___boxed(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_cmp_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_DTreeMap_Raw_instInhabited(v_00_u03b1_125_, v_00_u03b2_126_, v_cmp_127_);
lean_dec_ref(v_cmp_127_);
return v_res_128_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__3));
v___x_169_ = l_String_toRawSubstring_x27(v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1(lean_object* v_x_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_188_);
v___x_192_ = l_Lean_Syntax_isOfKind(v_x_188_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_x_188_);
v___x_193_ = lean_box(1);
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v_a_190_);
return v___x_194_;
}
else
{
lean_object* v_quotContext_195_; lean_object* v_currMacroScope_196_; lean_object* v_ref_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_quotContext_195_ = lean_ctor_get(v_a_189_, 1);
v_currMacroScope_196_ = lean_ctor_get(v_a_189_, 2);
v_ref_197_ = lean_ctor_get(v_a_189_, 5);
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = l_Lean_Syntax_getArg(v_x_188_, v___x_198_);
v___x_200_ = lean_unsigned_to_nat(2u);
v___x_201_ = l_Lean_Syntax_getArg(v_x_188_, v___x_200_);
lean_dec(v_x_188_);
v___x_202_ = 0;
v___x_203_ = l_Lean_SourceInfo_fromRef(v_ref_197_, v___x_202_);
v___x_204_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2));
v___x_205_ = lean_obj_once(&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4, &l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4_once, _init_l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4);
v___x_206_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_196_);
lean_inc(v_quotContext_195_);
v___x_207_ = l_Lean_addMacroScope(v_quotContext_195_, v___x_206_, v_currMacroScope_196_);
v___x_208_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__10));
lean_inc_n(v___x_203_, 2);
v___x_209_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_209_, 0, v___x_203_);
lean_ctor_set(v___x_209_, 1, v___x_205_);
lean_ctor_set(v___x_209_, 2, v___x_207_);
lean_ctor_set(v___x_209_, 3, v___x_208_);
v___x_210_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__9));
v___x_211_ = l_Lean_Syntax_node2(v___x_203_, v___x_210_, v___x_199_, v___x_201_);
v___x_212_ = l_Lean_Syntax_node2(v___x_203_, v___x_204_, v___x_209_, v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_a_190_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___boxed(lean_object* v_x_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1(v_x_214_, v_a_215_, v_a_216_);
lean_dec_ref(v_a_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1(lean_object* v_x_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2));
lean_inc(v_x_221_);
v___x_225_ = l_Lean_Syntax_isOfKind(v_x_221_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec(v_x_221_);
v___x_226_ = lean_box(0);
v___x_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_a_223_);
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = l_Lean_Syntax_getArg(v_x_221_, v___x_228_);
v___x_230_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_229_);
v___x_231_ = l_Lean_Syntax_isOfKind(v___x_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v___x_229_);
lean_dec(v_x_221_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v_a_223_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = l_Lean_Syntax_getArg(v_x_221_, v___x_234_);
lean_dec(v_x_221_);
v___x_236_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_235_);
v___x_237_ = l_Lean_Syntax_matchesNull(v___x_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v___x_235_);
lean_dec(v___x_229_);
v___x_238_ = lean_box(0);
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v_a_223_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v_ref_242_; uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_240_ = l_Lean_Syntax_getArg(v___x_235_, v___x_228_);
v___x_241_ = l_Lean_Syntax_getArg(v___x_235_, v___x_234_);
lean_dec(v___x_235_);
v_ref_242_ = l_Lean_replaceRef(v___x_229_, v_a_222_);
lean_dec(v___x_229_);
v___x_243_ = 0;
v___x_244_ = l_Lean_SourceInfo_fromRef(v_ref_242_, v___x_243_);
lean_dec(v_ref_242_);
v___x_245_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__4));
v___x_246_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_244_);
v___x_247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_244_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = l_Lean_Syntax_node3(v___x_244_, v___x_245_, v___x_240_, v___x_247_, v___x_241_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v_a_223_);
return v___x_249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___boxed(lean_object* v_x_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1(v_x_250_, v_a_251_, v_a_252_);
lean_dec(v_a_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insert___redArg(lean_object* v_cmp_254_, lean_object* v_t_255_, lean_object* v_a_256_, lean_object* v_b_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_254_, v_a_256_, v_b_257_, v_t_255_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insert(lean_object* v_00_u03b1_259_, lean_object* v_00_u03b2_260_, lean_object* v_cmp_261_, lean_object* v_t_262_, lean_object* v_a_263_, lean_object* v_b_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_261_, v_a_263_, v_b_264_, v_t_262_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0(lean_object* v_cmp_266_, lean_object* v_e_267_){
_start:
{
lean_object* v_fst_268_; lean_object* v_snd_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_fst_268_ = lean_ctor_get(v_e_267_, 0);
lean_inc(v_fst_268_);
v_snd_269_ = lean_ctor_get(v_e_267_, 1);
lean_inc(v_snd_269_);
lean_dec_ref(v_e_267_);
v___x_270_ = lean_box(1);
v___x_271_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_266_, v_fst_268_, v_snd_269_, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma___redArg(lean_object* v_cmp_272_){
_start:
{
lean_object* v___f_273_; 
v___f_273_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_273_, 0, v_cmp_272_);
return v___f_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma(lean_object* v_00_u03b1_274_, lean_object* v_00_u03b2_275_, lean_object* v_cmp_276_){
_start:
{
lean_object* v___f_277_; 
v___f_277_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_277_, 0, v_cmp_276_);
return v___f_277_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0(lean_object* v_cmp_278_, lean_object* v_e_279_, lean_object* v_s_280_){
_start:
{
lean_object* v_fst_281_; lean_object* v_snd_282_; lean_object* v___x_283_; 
v_fst_281_ = lean_ctor_get(v_e_279_, 0);
lean_inc(v_fst_281_);
v_snd_282_ = lean_ctor_get(v_e_279_, 1);
lean_inc(v_snd_282_);
lean_dec_ref(v_e_279_);
v___x_283_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_278_, v_fst_281_, v_snd_282_, v_s_280_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma___redArg(lean_object* v_cmp_284_){
_start:
{
lean_object* v___f_285_; 
v___f_285_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_285_, 0, v_cmp_284_);
return v___f_285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma(lean_object* v_00_u03b1_286_, lean_object* v_00_u03b2_287_, lean_object* v_cmp_288_){
_start:
{
lean_object* v___f_289_; 
v___f_289_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_289_, 0, v_cmp_288_);
return v___f_289_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertIfNew___redArg(lean_object* v_cmp_290_, lean_object* v_t_291_, lean_object* v_a_292_, lean_object* v_b_293_){
_start:
{
uint8_t v___x_294_; 
lean_inc(v_t_291_);
lean_inc(v_a_292_);
lean_inc_ref(v_cmp_290_);
v___x_294_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_290_, v_a_292_, v_t_291_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
v___x_295_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_290_, v_a_292_, v_b_293_, v_t_291_);
return v___x_295_;
}
else
{
lean_dec(v_b_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_cmp_290_);
return v_t_291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertIfNew(lean_object* v_00_u03b1_296_, lean_object* v_00_u03b2_297_, lean_object* v_cmp_298_, lean_object* v_t_299_, lean_object* v_a_300_, lean_object* v_b_301_){
_start:
{
uint8_t v___x_302_; 
lean_inc(v_t_299_);
lean_inc(v_a_300_);
lean_inc_ref(v_cmp_298_);
v___x_302_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_298_, v_a_300_, v_t_299_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
v___x_303_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_298_, v_a_300_, v_b_301_, v_t_299_);
return v___x_303_;
}
else
{
lean_dec(v_b_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_cmp_298_);
return v_t_299_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsert___redArg(lean_object* v_cmp_304_, lean_object* v_t_305_, lean_object* v_a_306_, lean_object* v_b_307_){
_start:
{
lean_object* v_sz_308_; lean_object* v_m_309_; lean_object* v___y_311_; 
v_sz_308_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_305_);
v_m_309_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_304_, v_a_306_, v_b_307_, v_t_305_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsert(lean_object* v_00_u03b1_317_, lean_object* v_00_u03b2_318_, lean_object* v_cmp_319_, lean_object* v_t_320_, lean_object* v_a_321_, lean_object* v_b_322_){
_start:
{
lean_object* v_sz_323_; lean_object* v_m_324_; lean_object* v___y_326_; 
v_sz_323_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_320_);
v_m_324_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_319_, v_a_321_, v_b_322_, v_t_320_);
if (lean_obj_tag(v_m_324_) == 0)
{
lean_object* v_size_330_; 
v_size_330_ = lean_ctor_get(v_m_324_, 0);
lean_inc(v_size_330_);
v___y_326_ = v_size_330_;
goto v___jp_325_;
}
else
{
lean_object* v___x_331_; 
v___x_331_ = lean_unsigned_to_nat(0u);
v___y_326_ = v___x_331_;
goto v___jp_325_;
}
v___jp_325_:
{
uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_nat_dec_eq(v_sz_323_, v___y_326_);
lean_dec(v___y_326_);
lean_dec(v_sz_323_);
v___x_328_ = lean_box(v___x_327_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_m_324_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_cmp_332_, lean_object* v_t_333_, lean_object* v_a_334_, lean_object* v_b_335_){
_start:
{
uint8_t v___x_336_; 
lean_inc(v_t_333_);
lean_inc(v_a_334_);
lean_inc_ref(v_cmp_332_);
v___x_336_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_332_, v_a_334_, v_t_333_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_332_, v_a_334_, v_b_335_, v_t_333_);
v___x_338_ = lean_box(v___x_336_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
return v___x_339_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec(v_b_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_cmp_332_);
v___x_340_ = lean_box(v___x_336_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v_t_333_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_342_, lean_object* v_00_u03b2_343_, lean_object* v_cmp_344_, lean_object* v_t_345_, lean_object* v_a_346_, lean_object* v_b_347_){
_start:
{
uint8_t v___x_348_; 
lean_inc(v_t_345_);
lean_inc(v_a_346_);
lean_inc_ref(v_cmp_344_);
v___x_348_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_344_, v_a_346_, v_t_345_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_344_, v_a_346_, v_b_347_, v_t_345_);
v___x_350_ = lean_box(v___x_348_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_349_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec(v_b_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_cmp_344_);
v___x_352_ = lean_box(v___x_348_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v_t_345_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_354_, lean_object* v_t_355_, lean_object* v_a_356_, lean_object* v_b_357_){
_start:
{
lean_object* v___x_358_; 
lean_inc(v_a_356_);
lean_inc(v_t_355_);
lean_inc_ref(v_cmp_354_);
v___x_358_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_354_, v_t_355_, v_a_356_);
if (lean_obj_tag(v___x_358_) == 0)
{
uint8_t v___x_359_; 
lean_inc(v_t_355_);
lean_inc(v_a_356_);
lean_inc_ref(v_cmp_354_);
v___x_359_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_354_, v_a_356_, v_t_355_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_354_, v_a_356_, v_b_357_, v_t_355_);
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
lean_dec_ref(v_cmp_354_);
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
lean_dec_ref(v_cmp_354_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_358_);
lean_ctor_set(v___x_363_, 1, v_t_355_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_cmp_366_, lean_object* v_inst_367_, lean_object* v_t_368_, lean_object* v_a_369_, lean_object* v_b_370_){
_start:
{
lean_object* v___x_371_; 
lean_inc(v_a_369_);
lean_inc(v_t_368_);
lean_inc_ref(v_cmp_366_);
v___x_371_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_366_, v_t_368_, v_a_369_);
if (lean_obj_tag(v___x_371_) == 0)
{
uint8_t v___x_372_; 
lean_inc(v_t_368_);
lean_inc(v_a_369_);
lean_inc_ref(v_cmp_366_);
v___x_372_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_366_, v_a_369_, v_t_368_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_366_, v_a_369_, v_b_370_, v_t_368_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_371_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; 
lean_dec(v_b_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_cmp_366_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_371_);
lean_ctor_set(v___x_375_, 1, v_t_368_);
return v___x_375_;
}
}
else
{
lean_object* v___x_376_; 
lean_dec(v_b_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_cmp_366_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_371_);
lean_ctor_set(v___x_376_, 1, v_t_368_);
return v___x_376_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_contains___redArg(lean_object* v_cmp_377_, lean_object* v_t_378_, lean_object* v_a_379_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_377_, v_a_379_, v_t_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_contains___redArg___boxed(lean_object* v_cmp_381_, lean_object* v_t_382_, lean_object* v_a_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_Std_DTreeMap_Raw_contains___redArg(v_cmp_381_, v_t_382_, v_a_383_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_contains(lean_object* v_00_u03b1_386_, lean_object* v_00_u03b2_387_, lean_object* v_cmp_388_, lean_object* v_t_389_, lean_object* v_a_390_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_388_, v_a_390_, v_t_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_contains___boxed(lean_object* v_00_u03b1_392_, lean_object* v_00_u03b2_393_, lean_object* v_cmp_394_, lean_object* v_t_395_, lean_object* v_a_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_Std_DTreeMap_Raw_contains(v_00_u03b1_392_, v_00_u03b2_393_, v_cmp_394_, v_t_395_, v_a_396_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___redArg(){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_box(0);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___redArg___boxed(lean_object* v___dummy_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Std_DTreeMap_Raw_instMembership___redArg();
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_cmp_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lean_box(0);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___boxed(lean_object* v_00_u03b1_407_, lean_object* v_00_u03b2_408_, lean_object* v_cmp_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_DTreeMap_Raw_instMembership(v_00_u03b1_407_, v_00_u03b2_408_, v_cmp_409_);
lean_dec_ref(v_cmp_409_);
return v_res_410_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableMem___redArg(lean_object* v_cmp_411_, lean_object* v_t_412_, lean_object* v_a_413_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_411_, v_a_413_, v_t_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_415_, lean_object* v_t_416_, lean_object* v_a_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Std_DTreeMap_Raw_instDecidableMem___redArg(v_cmp_415_, v_t_416_, v_a_417_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableMem(lean_object* v_00_u03b1_420_, lean_object* v_00_u03b2_421_, lean_object* v_cmp_422_, lean_object* v_t_423_, lean_object* v_a_424_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_422_, v_a_424_, v_t_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_426_, lean_object* v_00_u03b2_427_, lean_object* v_cmp_428_, lean_object* v_t_429_, lean_object* v_a_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_Std_DTreeMap_Raw_instDecidableMem(v_00_u03b1_426_, v_00_u03b2_427_, v_cmp_428_, v_t_429_, v_a_430_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___redArg(lean_object* v_t_433_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___redArg___boxed(lean_object* v_t_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_DTreeMap_Raw_size___redArg(v_t_436_);
lean_dec(v_t_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size(lean_object* v_00_u03b1_438_, lean_object* v_00_u03b2_439_, lean_object* v_cmp_440_, lean_object* v_t_441_){
_start:
{
if (lean_obj_tag(v_t_441_) == 0)
{
lean_object* v_size_442_; 
v_size_442_ = lean_ctor_get(v_t_441_, 0);
lean_inc(v_size_442_);
return v_size_442_;
}
else
{
lean_object* v___x_443_; 
v___x_443_ = lean_unsigned_to_nat(0u);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___boxed(lean_object* v_00_u03b1_444_, lean_object* v_00_u03b2_445_, lean_object* v_cmp_446_, lean_object* v_t_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_DTreeMap_Raw_size(v_00_u03b1_444_, v_00_u03b2_445_, v_cmp_446_, v_t_447_);
lean_dec(v_t_447_);
lean_dec_ref(v_cmp_446_);
return v_res_448_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_isEmpty___redArg(lean_object* v_t_449_){
_start:
{
if (lean_obj_tag(v_t_449_) == 0)
{
uint8_t v___x_450_; 
v___x_450_ = 0;
return v___x_450_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = 1;
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_isEmpty___redArg___boxed(lean_object* v_t_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_Std_DTreeMap_Raw_isEmpty___redArg(v_t_452_);
lean_dec(v_t_452_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_isEmpty(lean_object* v_00_u03b1_455_, lean_object* v_00_u03b2_456_, lean_object* v_cmp_457_, lean_object* v_t_458_){
_start:
{
if (lean_obj_tag(v_t_458_) == 0)
{
uint8_t v___x_459_; 
v___x_459_ = 0;
return v___x_459_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = 1;
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_461_, lean_object* v_00_u03b2_462_, lean_object* v_cmp_463_, lean_object* v_t_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Std_DTreeMap_Raw_isEmpty(v_00_u03b1_461_, v_00_u03b2_462_, v_cmp_463_, v_t_464_);
lean_dec(v_t_464_);
lean_dec_ref(v_cmp_463_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_erase___redArg(lean_object* v_cmp_467_, lean_object* v_t_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_467_, v_a_469_, v_t_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_erase(lean_object* v_00_u03b1_471_, lean_object* v_00_u03b2_472_, lean_object* v_cmp_473_, lean_object* v_t_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_473_, v_a_475_, v_t_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x3f___redArg(lean_object* v_cmp_477_, lean_object* v_t_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_477_, v_t_478_, v_a_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x3f(lean_object* v_00_u03b1_481_, lean_object* v_00_u03b2_482_, lean_object* v_cmp_483_, lean_object* v_inst_484_, lean_object* v_t_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_483_, v_t_485_, v_a_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get___redArg(lean_object* v_cmp_488_, lean_object* v_t_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_488_, v_t_489_, v_a_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get(lean_object* v_00_u03b1_492_, lean_object* v_00_u03b2_493_, lean_object* v_cmp_494_, lean_object* v_inst_495_, lean_object* v_t_496_, lean_object* v_a_497_, lean_object* v_h_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_494_, v_t_496_, v_a_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___redArg(lean_object* v_cmp_500_, lean_object* v_t_501_, lean_object* v_a_502_, lean_object* v_inst_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_500_, v_t_501_, v_a_502_, v_inst_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___redArg___boxed(lean_object* v_cmp_505_, lean_object* v_t_506_, lean_object* v_a_507_, lean_object* v_inst_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_DTreeMap_Raw_get_x21___redArg(v_cmp_505_, v_t_506_, v_a_507_, v_inst_508_);
lean_dec(v_inst_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21(lean_object* v_00_u03b1_510_, lean_object* v_00_u03b2_511_, lean_object* v_cmp_512_, lean_object* v_inst_513_, lean_object* v_t_514_, lean_object* v_a_515_, lean_object* v_inst_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_512_, v_t_514_, v_a_515_, v_inst_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_518_, lean_object* v_00_u03b2_519_, lean_object* v_cmp_520_, lean_object* v_inst_521_, lean_object* v_t_522_, lean_object* v_a_523_, lean_object* v_inst_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_DTreeMap_Raw_get_x21(v_00_u03b1_518_, v_00_u03b2_519_, v_cmp_520_, v_inst_521_, v_t_522_, v_a_523_, v_inst_524_);
lean_dec(v_inst_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg(lean_object* v_cmp_526_, lean_object* v_t_527_, lean_object* v_a_528_, lean_object* v_fallback_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_526_, v_t_527_, v_a_528_, v_fallback_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg___boxed(lean_object* v_cmp_531_, lean_object* v_t_532_, lean_object* v_a_533_, lean_object* v_fallback_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_DTreeMap_Raw_getD___redArg(v_cmp_531_, v_t_532_, v_a_533_, v_fallback_534_);
lean_dec(v_fallback_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_cmp_538_, lean_object* v_inst_539_, lean_object* v_t_540_, lean_object* v_a_541_, lean_object* v_fallback_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_538_, v_t_540_, v_a_541_, v_fallback_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___boxed(lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_, lean_object* v_cmp_546_, lean_object* v_inst_547_, lean_object* v_t_548_, lean_object* v_a_549_, lean_object* v_fallback_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_DTreeMap_Raw_getD(v_00_u03b1_544_, v_00_u03b2_545_, v_cmp_546_, v_inst_547_, v_t_548_, v_a_549_, v_fallback_550_);
lean_dec(v_fallback_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f___redArg(lean_object* v_cmp_552_, lean_object* v_t_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_552_, v_t_553_, v_a_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f(lean_object* v_00_u03b1_556_, lean_object* v_00_u03b2_557_, lean_object* v_cmp_558_, lean_object* v_t_559_, lean_object* v_a_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_558_, v_t_559_, v_a_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry___redArg(lean_object* v_cmp_562_, lean_object* v_t_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_562_, v_t_563_, v_a_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry(lean_object* v_00_u03b1_566_, lean_object* v_00_u03b2_567_, lean_object* v_cmp_568_, lean_object* v_inst_569_, lean_object* v_t_570_, lean_object* v_a_571_, lean_object* v_h_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_568_, v_t_570_, v_a_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___redArg(lean_object* v_cmp_574_, lean_object* v_inst_575_, lean_object* v_t_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_574_, v_inst_575_, v_t_576_, v_a_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___redArg___boxed(lean_object* v_cmp_579_, lean_object* v_inst_580_, lean_object* v_t_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DTreeMap_Raw_getEntry_x21___redArg(v_cmp_579_, v_inst_580_, v_t_581_, v_a_582_);
lean_dec_ref(v_inst_580_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_cmp_586_, lean_object* v_inst_587_, lean_object* v_t_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_586_, v_inst_587_, v_t_588_, v_a_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___boxed(lean_object* v_00_u03b1_591_, lean_object* v_00_u03b2_592_, lean_object* v_cmp_593_, lean_object* v_inst_594_, lean_object* v_t_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_DTreeMap_Raw_getEntry_x21(v_00_u03b1_591_, v_00_u03b2_592_, v_cmp_593_, v_inst_594_, v_t_595_, v_a_596_);
lean_dec_ref(v_inst_594_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg(lean_object* v_cmp_598_, lean_object* v_t_599_, lean_object* v_a_600_, lean_object* v_fallback_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_598_, v_t_599_, v_a_600_, v_fallback_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg___boxed(lean_object* v_cmp_603_, lean_object* v_t_604_, lean_object* v_a_605_, lean_object* v_fallback_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_DTreeMap_Raw_getEntryD___redArg(v_cmp_603_, v_t_604_, v_a_605_, v_fallback_606_);
lean_dec_ref(v_fallback_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_cmp_610_, lean_object* v_t_611_, lean_object* v_a_612_, lean_object* v_fallback_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_610_, v_t_611_, v_a_612_, v_fallback_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___boxed(lean_object* v_00_u03b1_615_, lean_object* v_00_u03b2_616_, lean_object* v_cmp_617_, lean_object* v_t_618_, lean_object* v_a_619_, lean_object* v_fallback_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_DTreeMap_Raw_getEntryD(v_00_u03b1_615_, v_00_u03b2_616_, v_cmp_617_, v_t_618_, v_a_619_, v_fallback_620_);
lean_dec_ref(v_fallback_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f___redArg(lean_object* v_cmp_622_, lean_object* v_t_623_, lean_object* v_a_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_622_, v_t_623_, v_a_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f(lean_object* v_00_u03b1_626_, lean_object* v_00_u03b2_627_, lean_object* v_cmp_628_, lean_object* v_t_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_628_, v_t_629_, v_a_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey___redArg(lean_object* v_cmp_632_, lean_object* v_t_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_632_, v_t_633_, v_a_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey(lean_object* v_00_u03b1_636_, lean_object* v_00_u03b2_637_, lean_object* v_cmp_638_, lean_object* v_t_639_, lean_object* v_a_640_, lean_object* v_h_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_638_, v_t_639_, v_a_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___redArg(lean_object* v_cmp_643_, lean_object* v_inst_644_, lean_object* v_t_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_643_, v_t_645_, v_a_646_, v_inst_644_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___redArg___boxed(lean_object* v_cmp_648_, lean_object* v_inst_649_, lean_object* v_t_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Std_DTreeMap_Raw_getKey_x21___redArg(v_cmp_648_, v_inst_649_, v_t_650_, v_a_651_);
lean_dec(v_inst_649_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21(lean_object* v_00_u03b1_653_, lean_object* v_00_u03b2_654_, lean_object* v_cmp_655_, lean_object* v_inst_656_, lean_object* v_t_657_, lean_object* v_a_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_655_, v_t_657_, v_a_658_, v_inst_656_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_660_, lean_object* v_00_u03b2_661_, lean_object* v_cmp_662_, lean_object* v_inst_663_, lean_object* v_t_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_DTreeMap_Raw_getKey_x21(v_00_u03b1_660_, v_00_u03b2_661_, v_cmp_662_, v_inst_663_, v_t_664_, v_a_665_);
lean_dec(v_inst_663_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___redArg(lean_object* v_cmp_667_, lean_object* v_t_668_, lean_object* v_a_669_, lean_object* v_fallback_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_667_, v_t_668_, v_a_669_, v_fallback_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___redArg___boxed(lean_object* v_cmp_672_, lean_object* v_t_673_, lean_object* v_a_674_, lean_object* v_fallback_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_DTreeMap_Raw_getKeyD___redArg(v_cmp_672_, v_t_673_, v_a_674_, v_fallback_675_);
lean_dec(v_fallback_675_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD(lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_cmp_679_, lean_object* v_t_680_, lean_object* v_a_681_, lean_object* v_fallback_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_679_, v_t_680_, v_a_681_, v_fallback_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_684_, lean_object* v_00_u03b2_685_, lean_object* v_cmp_686_, lean_object* v_t_687_, lean_object* v_a_688_, lean_object* v_fallback_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_DTreeMap_Raw_getKeyD(v_00_u03b1_684_, v_00_u03b2_685_, v_cmp_686_, v_t_687_, v_a_688_, v_fallback_689_);
lean_dec(v_fallback_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___redArg(lean_object* v_t_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___redArg___boxed(lean_object* v_t_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Std_DTreeMap_Raw_minEntry_x3f___redArg(v_t_693_);
lean_dec(v_t_693_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f(lean_object* v_00_u03b1_695_, lean_object* v_00_u03b2_696_, lean_object* v_cmp_697_, lean_object* v_t_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___boxed(lean_object* v_00_u03b1_700_, lean_object* v_00_u03b2_701_, lean_object* v_cmp_702_, lean_object* v_t_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_DTreeMap_Raw_minEntry_x3f(v_00_u03b1_700_, v_00_u03b2_701_, v_cmp_702_, v_t_703_);
lean_dec(v_t_703_);
lean_dec_ref(v_cmp_702_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___redArg(lean_object* v_inst_705_, lean_object* v_t_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_705_, v_t_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___redArg___boxed(lean_object* v_inst_708_, lean_object* v_t_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_DTreeMap_Raw_minEntry_x21___redArg(v_inst_708_, v_t_709_);
lean_dec(v_t_709_);
lean_dec_ref(v_inst_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21(lean_object* v_00_u03b1_711_, lean_object* v_00_u03b2_712_, lean_object* v_cmp_713_, lean_object* v_inst_714_, lean_object* v_t_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_714_, v_t_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___boxed(lean_object* v_00_u03b1_717_, lean_object* v_00_u03b2_718_, lean_object* v_cmp_719_, lean_object* v_inst_720_, lean_object* v_t_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_DTreeMap_Raw_minEntry_x21(v_00_u03b1_717_, v_00_u03b2_718_, v_cmp_719_, v_inst_720_, v_t_721_);
lean_dec(v_t_721_);
lean_dec_ref(v_inst_720_);
lean_dec_ref(v_cmp_719_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___redArg(lean_object* v_t_723_, lean_object* v_fallback_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_723_, v_fallback_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___redArg___boxed(lean_object* v_t_726_, lean_object* v_fallback_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_DTreeMap_Raw_minEntryD___redArg(v_t_726_, v_fallback_727_);
lean_dec_ref(v_fallback_727_);
lean_dec(v_t_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD(lean_object* v_00_u03b1_729_, lean_object* v_00_u03b2_730_, lean_object* v_cmp_731_, lean_object* v_t_732_, lean_object* v_fallback_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_732_, v_fallback_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___boxed(lean_object* v_00_u03b1_735_, lean_object* v_00_u03b2_736_, lean_object* v_cmp_737_, lean_object* v_t_738_, lean_object* v_fallback_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_DTreeMap_Raw_minEntryD(v_00_u03b1_735_, v_00_u03b2_736_, v_cmp_737_, v_t_738_, v_fallback_739_);
lean_dec_ref(v_fallback_739_);
lean_dec(v_t_738_);
lean_dec_ref(v_cmp_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___redArg(lean_object* v_t_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___redArg___boxed(lean_object* v_t_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_DTreeMap_Raw_maxEntry_x3f___redArg(v_t_743_);
lean_dec(v_t_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f(lean_object* v_00_u03b1_745_, lean_object* v_00_u03b2_746_, lean_object* v_cmp_747_, lean_object* v_t_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___boxed(lean_object* v_00_u03b1_750_, lean_object* v_00_u03b2_751_, lean_object* v_cmp_752_, lean_object* v_t_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_DTreeMap_Raw_maxEntry_x3f(v_00_u03b1_750_, v_00_u03b2_751_, v_cmp_752_, v_t_753_);
lean_dec(v_t_753_);
lean_dec_ref(v_cmp_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___redArg(lean_object* v_inst_755_, lean_object* v_t_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_755_, v_t_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___redArg___boxed(lean_object* v_inst_758_, lean_object* v_t_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_DTreeMap_Raw_maxEntry_x21___redArg(v_inst_758_, v_t_759_);
lean_dec(v_t_759_);
lean_dec_ref(v_inst_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21(lean_object* v_00_u03b1_761_, lean_object* v_00_u03b2_762_, lean_object* v_cmp_763_, lean_object* v_inst_764_, lean_object* v_t_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_764_, v_t_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___boxed(lean_object* v_00_u03b1_767_, lean_object* v_00_u03b2_768_, lean_object* v_cmp_769_, lean_object* v_inst_770_, lean_object* v_t_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_DTreeMap_Raw_maxEntry_x21(v_00_u03b1_767_, v_00_u03b2_768_, v_cmp_769_, v_inst_770_, v_t_771_);
lean_dec(v_t_771_);
lean_dec_ref(v_inst_770_);
lean_dec_ref(v_cmp_769_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___redArg(lean_object* v_t_773_, lean_object* v_fallback_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_773_, v_fallback_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___redArg___boxed(lean_object* v_t_776_, lean_object* v_fallback_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_DTreeMap_Raw_maxEntryD___redArg(v_t_776_, v_fallback_777_);
lean_dec_ref(v_fallback_777_);
lean_dec(v_t_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD(lean_object* v_00_u03b1_779_, lean_object* v_00_u03b2_780_, lean_object* v_cmp_781_, lean_object* v_t_782_, lean_object* v_fallback_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_782_, v_fallback_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___boxed(lean_object* v_00_u03b1_785_, lean_object* v_00_u03b2_786_, lean_object* v_cmp_787_, lean_object* v_t_788_, lean_object* v_fallback_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_DTreeMap_Raw_maxEntryD(v_00_u03b1_785_, v_00_u03b2_786_, v_cmp_787_, v_t_788_, v_fallback_789_);
lean_dec_ref(v_fallback_789_);
lean_dec(v_t_788_);
lean_dec_ref(v_cmp_787_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___redArg(lean_object* v_t_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___redArg___boxed(lean_object* v_t_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_DTreeMap_Raw_minKey_x3f___redArg(v_t_793_);
lean_dec(v_t_793_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f(lean_object* v_00_u03b1_795_, lean_object* v_00_u03b2_796_, lean_object* v_cmp_797_, lean_object* v_t_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___boxed(lean_object* v_00_u03b1_800_, lean_object* v_00_u03b2_801_, lean_object* v_cmp_802_, lean_object* v_t_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_DTreeMap_Raw_minKey_x3f(v_00_u03b1_800_, v_00_u03b2_801_, v_cmp_802_, v_t_803_);
lean_dec(v_t_803_);
lean_dec_ref(v_cmp_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___redArg(lean_object* v_t_805_, lean_object* v_fallback_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_805_, v_fallback_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___redArg___boxed(lean_object* v_t_808_, lean_object* v_fallback_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_DTreeMap_Raw_minKeyD___redArg(v_t_808_, v_fallback_809_);
lean_dec(v_fallback_809_);
lean_dec(v_t_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD(lean_object* v_00_u03b1_811_, lean_object* v_00_u03b2_812_, lean_object* v_cmp_813_, lean_object* v_t_814_, lean_object* v_fallback_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_814_, v_fallback_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___boxed(lean_object* v_00_u03b1_817_, lean_object* v_00_u03b2_818_, lean_object* v_cmp_819_, lean_object* v_t_820_, lean_object* v_fallback_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DTreeMap_Raw_minKeyD(v_00_u03b1_817_, v_00_u03b2_818_, v_cmp_819_, v_t_820_, v_fallback_821_);
lean_dec(v_fallback_821_);
lean_dec(v_t_820_);
lean_dec_ref(v_cmp_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___redArg(lean_object* v_inst_823_, lean_object* v_t_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_823_, v_t_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___redArg___boxed(lean_object* v_inst_826_, lean_object* v_t_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Std_DTreeMap_Raw_minKey_x21___redArg(v_inst_826_, v_t_827_);
lean_dec(v_t_827_);
lean_dec(v_inst_826_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21(lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_cmp_831_, lean_object* v_inst_832_, lean_object* v_t_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_832_, v_t_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___boxed(lean_object* v_00_u03b1_835_, lean_object* v_00_u03b2_836_, lean_object* v_cmp_837_, lean_object* v_inst_838_, lean_object* v_t_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_DTreeMap_Raw_minKey_x21(v_00_u03b1_835_, v_00_u03b2_836_, v_cmp_837_, v_inst_838_, v_t_839_);
lean_dec(v_t_839_);
lean_dec(v_inst_838_);
lean_dec_ref(v_cmp_837_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___redArg(lean_object* v_t_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___redArg___boxed(lean_object* v_t_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_DTreeMap_Raw_maxKey_x3f___redArg(v_t_843_);
lean_dec(v_t_843_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f(lean_object* v_00_u03b1_845_, lean_object* v_00_u03b2_846_, lean_object* v_cmp_847_, lean_object* v_t_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___boxed(lean_object* v_00_u03b1_850_, lean_object* v_00_u03b2_851_, lean_object* v_cmp_852_, lean_object* v_t_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Std_DTreeMap_Raw_maxKey_x3f(v_00_u03b1_850_, v_00_u03b2_851_, v_cmp_852_, v_t_853_);
lean_dec(v_t_853_);
lean_dec_ref(v_cmp_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___redArg(lean_object* v_inst_855_, lean_object* v_t_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_855_, v_t_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___redArg___boxed(lean_object* v_inst_858_, lean_object* v_t_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Std_DTreeMap_Raw_maxKey_x21___redArg(v_inst_858_, v_t_859_);
lean_dec(v_t_859_);
lean_dec(v_inst_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21(lean_object* v_00_u03b1_861_, lean_object* v_00_u03b2_862_, lean_object* v_cmp_863_, lean_object* v_inst_864_, lean_object* v_t_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_864_, v_t_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___boxed(lean_object* v_00_u03b1_867_, lean_object* v_00_u03b2_868_, lean_object* v_cmp_869_, lean_object* v_inst_870_, lean_object* v_t_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_DTreeMap_Raw_maxKey_x21(v_00_u03b1_867_, v_00_u03b2_868_, v_cmp_869_, v_inst_870_, v_t_871_);
lean_dec(v_t_871_);
lean_dec(v_inst_870_);
lean_dec_ref(v_cmp_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___redArg(lean_object* v_t_873_, lean_object* v_fallback_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_873_, v_fallback_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___redArg___boxed(lean_object* v_t_876_, lean_object* v_fallback_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Std_DTreeMap_Raw_maxKeyD___redArg(v_t_876_, v_fallback_877_);
lean_dec(v_fallback_877_);
lean_dec(v_t_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD(lean_object* v_00_u03b1_879_, lean_object* v_00_u03b2_880_, lean_object* v_cmp_881_, lean_object* v_t_882_, lean_object* v_fallback_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_882_, v_fallback_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___boxed(lean_object* v_00_u03b1_885_, lean_object* v_00_u03b2_886_, lean_object* v_cmp_887_, lean_object* v_t_888_, lean_object* v_fallback_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_DTreeMap_Raw_maxKeyD(v_00_u03b1_885_, v_00_u03b2_886_, v_cmp_887_, v_t_888_, v_fallback_889_);
lean_dec(v_fallback_889_);
lean_dec(v_t_888_);
lean_dec_ref(v_cmp_887_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg(lean_object* v_t_891_, lean_object* v_n_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_891_, v_n_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_894_, lean_object* v_n_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg(v_t_894_, v_n_895_);
lean_dec(v_t_894_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f(lean_object* v_00_u03b1_897_, lean_object* v_00_u03b2_898_, lean_object* v_cmp_899_, lean_object* v_t_900_, lean_object* v_n_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_900_, v_n_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_903_, lean_object* v_00_u03b2_904_, lean_object* v_cmp_905_, lean_object* v_t_906_, lean_object* v_n_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_DTreeMap_Raw_entryAtIdx_x3f(v_00_u03b1_903_, v_00_u03b2_904_, v_cmp_905_, v_t_906_, v_n_907_);
lean_dec(v_t_906_);
lean_dec_ref(v_cmp_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg(lean_object* v_inst_909_, lean_object* v_t_910_, lean_object* v_n_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_909_, v_t_910_, v_n_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_913_, lean_object* v_t_914_, lean_object* v_n_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg(v_inst_913_, v_t_914_, v_n_915_);
lean_dec(v_t_914_);
lean_dec_ref(v_inst_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21(lean_object* v_00_u03b1_917_, lean_object* v_00_u03b2_918_, lean_object* v_cmp_919_, lean_object* v_inst_920_, lean_object* v_t_921_, lean_object* v_n_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_920_, v_t_921_, v_n_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_cmp_926_, lean_object* v_inst_927_, lean_object* v_t_928_, lean_object* v_n_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Std_DTreeMap_Raw_entryAtIdx_x21(v_00_u03b1_924_, v_00_u03b2_925_, v_cmp_926_, v_inst_927_, v_t_928_, v_n_929_);
lean_dec(v_t_928_);
lean_dec_ref(v_inst_927_);
lean_dec_ref(v_cmp_926_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___redArg(lean_object* v_t_931_, lean_object* v_n_932_, lean_object* v_fallback_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_931_, v_n_932_, v_fallback_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___redArg___boxed(lean_object* v_t_935_, lean_object* v_n_936_, lean_object* v_fallback_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_DTreeMap_Raw_entryAtIdxD___redArg(v_t_935_, v_n_936_, v_fallback_937_);
lean_dec_ref(v_fallback_937_);
lean_dec(v_t_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD(lean_object* v_00_u03b1_939_, lean_object* v_00_u03b2_940_, lean_object* v_cmp_941_, lean_object* v_t_942_, lean_object* v_n_943_, lean_object* v_fallback_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_942_, v_n_943_, v_fallback_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___boxed(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_cmp_948_, lean_object* v_t_949_, lean_object* v_n_950_, lean_object* v_fallback_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_DTreeMap_Raw_entryAtIdxD(v_00_u03b1_946_, v_00_u03b2_947_, v_cmp_948_, v_t_949_, v_n_950_, v_fallback_951_);
lean_dec_ref(v_fallback_951_);
lean_dec(v_t_949_);
lean_dec_ref(v_cmp_948_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg(lean_object* v_t_953_, lean_object* v_n_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_953_, v_n_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_956_, lean_object* v_n_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg(v_t_956_, v_n_957_);
lean_dec(v_t_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f(lean_object* v_00_u03b1_959_, lean_object* v_00_u03b2_960_, lean_object* v_cmp_961_, lean_object* v_t_962_, lean_object* v_n_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_962_, v_n_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_965_, lean_object* v_00_u03b2_966_, lean_object* v_cmp_967_, lean_object* v_t_968_, lean_object* v_n_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_DTreeMap_Raw_keyAtIdx_x3f(v_00_u03b1_965_, v_00_u03b2_966_, v_cmp_967_, v_t_968_, v_n_969_);
lean_dec(v_t_968_);
lean_dec_ref(v_cmp_967_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg(lean_object* v_inst_971_, lean_object* v_t_972_, lean_object* v_n_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_971_, v_t_972_, v_n_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_975_, lean_object* v_t_976_, lean_object* v_n_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg(v_inst_975_, v_t_976_, v_n_977_);
lean_dec(v_t_976_);
lean_dec(v_inst_975_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21(lean_object* v_00_u03b1_979_, lean_object* v_00_u03b2_980_, lean_object* v_cmp_981_, lean_object* v_inst_982_, lean_object* v_t_983_, lean_object* v_n_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_982_, v_t_983_, v_n_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_986_, lean_object* v_00_u03b2_987_, lean_object* v_cmp_988_, lean_object* v_inst_989_, lean_object* v_t_990_, lean_object* v_n_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_DTreeMap_Raw_keyAtIdx_x21(v_00_u03b1_986_, v_00_u03b2_987_, v_cmp_988_, v_inst_989_, v_t_990_, v_n_991_);
lean_dec(v_t_990_);
lean_dec(v_inst_989_);
lean_dec_ref(v_cmp_988_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___redArg(lean_object* v_t_993_, lean_object* v_n_994_, lean_object* v_fallback_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_993_, v_n_994_, v_fallback_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___redArg___boxed(lean_object* v_t_997_, lean_object* v_n_998_, lean_object* v_fallback_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_DTreeMap_Raw_keyAtIdxD___redArg(v_t_997_, v_n_998_, v_fallback_999_);
lean_dec(v_fallback_999_);
lean_dec(v_t_997_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD(lean_object* v_00_u03b1_1001_, lean_object* v_00_u03b2_1002_, lean_object* v_cmp_1003_, lean_object* v_t_1004_, lean_object* v_n_1005_, lean_object* v_fallback_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1004_, v_n_1005_, v_fallback_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___boxed(lean_object* v_00_u03b1_1008_, lean_object* v_00_u03b2_1009_, lean_object* v_cmp_1010_, lean_object* v_t_1011_, lean_object* v_n_1012_, lean_object* v_fallback_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Std_DTreeMap_Raw_keyAtIdxD(v_00_u03b1_1008_, v_00_u03b2_1009_, v_cmp_1010_, v_t_1011_, v_n_1012_, v_fallback_1013_);
lean_dec(v_fallback_1013_);
lean_dec(v_t_1011_);
lean_dec_ref(v_cmp_1010_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x3f___redArg(lean_object* v_cmp_1015_, lean_object* v_t_1016_, lean_object* v_k_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_box(0);
v___x_1019_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1015_, v_k_1017_, v___x_1018_, v_t_1016_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x3f(lean_object* v_00_u03b1_1020_, lean_object* v_00_u03b2_1021_, lean_object* v_cmp_1022_, lean_object* v_t_1023_, lean_object* v_k_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1022_, v_k_1024_, v___x_1025_, v_t_1023_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x3f___redArg(lean_object* v_cmp_1027_, lean_object* v_t_1028_, lean_object* v_k_1029_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1027_, v_k_1029_, v___x_1030_, v_t_1028_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x3f(lean_object* v_00_u03b1_1032_, lean_object* v_00_u03b2_1033_, lean_object* v_cmp_1034_, lean_object* v_t_1035_, lean_object* v_k_1036_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1034_, v_k_1036_, v___x_1037_, v_t_1035_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x3f___redArg(lean_object* v_cmp_1039_, lean_object* v_t_1040_, lean_object* v_k_1041_){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1039_, v_k_1041_, v___x_1042_, v_t_1040_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x3f(lean_object* v_00_u03b1_1044_, lean_object* v_00_u03b2_1045_, lean_object* v_cmp_1046_, lean_object* v_t_1047_, lean_object* v_k_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1046_, v_k_1048_, v___x_1049_, v_t_1047_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x3f___redArg(lean_object* v_cmp_1051_, lean_object* v_t_1052_, lean_object* v_k_1053_){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1051_, v_k_1053_, v___x_1054_, v_t_1052_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x3f(lean_object* v_00_u03b1_1056_, lean_object* v_00_u03b2_1057_, lean_object* v_cmp_1058_, lean_object* v_t_1059_, lean_object* v_k_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1058_, v_k_1060_, v___x_1061_, v_t_1059_);
return v___x_1062_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1066_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__2));
v___x_1067_ = lean_unsigned_to_nat(14u);
v___x_1068_ = lean_unsigned_to_nat(22u);
v___x_1069_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__1));
v___x_1070_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__0));
v___x_1071_ = l_mkPanicMessageWithDecl(v___x_1070_, v___x_1069_, v___x_1068_, v___x_1067_, v___x_1066_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg(lean_object* v_cmp_1072_, lean_object* v_inst_1073_, lean_object* v_t_1074_, lean_object* v_k_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1072_, v_k_1075_, v___x_1076_, v_t_1074_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1079_ = l_panic___redArg(v_inst_1073_, v___x_1078_);
return v___x_1079_;
}
else
{
lean_object* v_val_1080_; 
v_val_1080_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_val_1080_);
lean_dec_ref_known(v___x_1077_, 1);
return v_val_1080_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1081_, lean_object* v_inst_1082_, lean_object* v_t_1083_, lean_object* v_k_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Std_DTreeMap_Raw_getEntryGE_x21___redArg(v_cmp_1081_, v_inst_1082_, v_t_1083_, v_k_1084_);
lean_dec_ref(v_inst_1082_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21(lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_cmp_1088_, lean_object* v_inst_1089_, lean_object* v_t_1090_, lean_object* v_k_1091_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1088_, v_k_1091_, v___x_1092_, v_t_1090_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1095_ = l_panic___redArg(v_inst_1089_, v___x_1094_);
return v___x_1095_;
}
else
{
lean_object* v_val_1096_; 
v_val_1096_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_val_1096_);
lean_dec_ref_known(v___x_1093_, 1);
return v_val_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1097_, lean_object* v_00_u03b2_1098_, lean_object* v_cmp_1099_, lean_object* v_inst_1100_, lean_object* v_t_1101_, lean_object* v_k_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_DTreeMap_Raw_getEntryGE_x21(v_00_u03b1_1097_, v_00_u03b2_1098_, v_cmp_1099_, v_inst_1100_, v_t_1101_, v_k_1102_);
lean_dec_ref(v_inst_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___redArg(lean_object* v_cmp_1104_, lean_object* v_inst_1105_, lean_object* v_t_1106_, lean_object* v_k_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_box(0);
v___x_1109_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1104_, v_k_1107_, v___x_1108_, v_t_1106_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1111_ = l_panic___redArg(v_inst_1105_, v___x_1110_);
return v___x_1111_;
}
else
{
lean_object* v_val_1112_; 
v_val_1112_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_val_1112_);
lean_dec_ref_known(v___x_1109_, 1);
return v_val_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1113_, lean_object* v_inst_1114_, lean_object* v_t_1115_, lean_object* v_k_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_DTreeMap_Raw_getEntryGT_x21___redArg(v_cmp_1113_, v_inst_1114_, v_t_1115_, v_k_1116_);
lean_dec_ref(v_inst_1114_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21(lean_object* v_00_u03b1_1118_, lean_object* v_00_u03b2_1119_, lean_object* v_cmp_1120_, lean_object* v_inst_1121_, lean_object* v_t_1122_, lean_object* v_k_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_box(0);
v___x_1125_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1120_, v_k_1123_, v___x_1124_, v_t_1122_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1127_ = l_panic___redArg(v_inst_1121_, v___x_1126_);
return v___x_1127_;
}
else
{
lean_object* v_val_1128_; 
v_val_1128_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_val_1128_);
lean_dec_ref_known(v___x_1125_, 1);
return v_val_1128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_cmp_1131_, lean_object* v_inst_1132_, lean_object* v_t_1133_, lean_object* v_k_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Std_DTreeMap_Raw_getEntryGT_x21(v_00_u03b1_1129_, v_00_u03b2_1130_, v_cmp_1131_, v_inst_1132_, v_t_1133_, v_k_1134_);
lean_dec_ref(v_inst_1132_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___redArg(lean_object* v_cmp_1136_, lean_object* v_inst_1137_, lean_object* v_t_1138_, lean_object* v_k_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_box(0);
v___x_1141_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1136_, v_k_1139_, v___x_1140_, v_t_1138_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1143_ = l_panic___redArg(v_inst_1137_, v___x_1142_);
return v___x_1143_;
}
else
{
lean_object* v_val_1144_; 
v_val_1144_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_val_1144_);
lean_dec_ref_known(v___x_1141_, 1);
return v_val_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1145_, lean_object* v_inst_1146_, lean_object* v_t_1147_, lean_object* v_k_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Std_DTreeMap_Raw_getEntryLE_x21___redArg(v_cmp_1145_, v_inst_1146_, v_t_1147_, v_k_1148_);
lean_dec_ref(v_inst_1146_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21(lean_object* v_00_u03b1_1150_, lean_object* v_00_u03b2_1151_, lean_object* v_cmp_1152_, lean_object* v_inst_1153_, lean_object* v_t_1154_, lean_object* v_k_1155_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_box(0);
v___x_1157_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1152_, v_k_1155_, v___x_1156_, v_t_1154_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1159_ = l_panic___redArg(v_inst_1153_, v___x_1158_);
return v___x_1159_;
}
else
{
lean_object* v_val_1160_; 
v_val_1160_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_val_1160_);
lean_dec_ref_known(v___x_1157_, 1);
return v_val_1160_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1161_, lean_object* v_00_u03b2_1162_, lean_object* v_cmp_1163_, lean_object* v_inst_1164_, lean_object* v_t_1165_, lean_object* v_k_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Std_DTreeMap_Raw_getEntryLE_x21(v_00_u03b1_1161_, v_00_u03b2_1162_, v_cmp_1163_, v_inst_1164_, v_t_1165_, v_k_1166_);
lean_dec_ref(v_inst_1164_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___redArg(lean_object* v_cmp_1168_, lean_object* v_inst_1169_, lean_object* v_t_1170_, lean_object* v_k_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_box(0);
v___x_1173_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1168_, v_k_1171_, v___x_1172_, v_t_1170_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1175_ = l_panic___redArg(v_inst_1169_, v___x_1174_);
return v___x_1175_;
}
else
{
lean_object* v_val_1176_; 
v_val_1176_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_val_1176_);
lean_dec_ref_known(v___x_1173_, 1);
return v_val_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1177_, lean_object* v_inst_1178_, lean_object* v_t_1179_, lean_object* v_k_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Std_DTreeMap_Raw_getEntryLT_x21___redArg(v_cmp_1177_, v_inst_1178_, v_t_1179_, v_k_1180_);
lean_dec_ref(v_inst_1178_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21(lean_object* v_00_u03b1_1182_, lean_object* v_00_u03b2_1183_, lean_object* v_cmp_1184_, lean_object* v_inst_1185_, lean_object* v_t_1186_, lean_object* v_k_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_box(0);
v___x_1189_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1184_, v_k_1187_, v___x_1188_, v_t_1186_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1191_ = l_panic___redArg(v_inst_1185_, v___x_1190_);
return v___x_1191_;
}
else
{
lean_object* v_val_1192_; 
v_val_1192_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_val_1192_);
lean_dec_ref_known(v___x_1189_, 1);
return v_val_1192_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1193_, lean_object* v_00_u03b2_1194_, lean_object* v_cmp_1195_, lean_object* v_inst_1196_, lean_object* v_t_1197_, lean_object* v_k_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Std_DTreeMap_Raw_getEntryLT_x21(v_00_u03b1_1193_, v_00_u03b2_1194_, v_cmp_1195_, v_inst_1196_, v_t_1197_, v_k_1198_);
lean_dec_ref(v_inst_1196_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___redArg(lean_object* v_cmp_1200_, lean_object* v_t_1201_, lean_object* v_k_1202_, lean_object* v_fallback_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1200_, v_k_1202_, v___x_1204_, v_t_1201_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_inc_ref(v_fallback_1203_);
return v_fallback_1203_;
}
else
{
lean_object* v_val_1206_; 
v_val_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_val_1206_);
lean_dec_ref_known(v___x_1205_, 1);
return v_val_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___redArg___boxed(lean_object* v_cmp_1207_, lean_object* v_t_1208_, lean_object* v_k_1209_, lean_object* v_fallback_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_DTreeMap_Raw_getEntryGED___redArg(v_cmp_1207_, v_t_1208_, v_k_1209_, v_fallback_1210_);
lean_dec_ref(v_fallback_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED(lean_object* v_00_u03b1_1212_, lean_object* v_00_u03b2_1213_, lean_object* v_cmp_1214_, lean_object* v_t_1215_, lean_object* v_k_1216_, lean_object* v_fallback_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1214_, v_k_1216_, v___x_1218_, v_t_1215_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_inc_ref(v_fallback_1217_);
return v_fallback_1217_;
}
else
{
lean_object* v_val_1220_; 
v_val_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_val_1220_);
lean_dec_ref_known(v___x_1219_, 1);
return v_val_1220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___boxed(lean_object* v_00_u03b1_1221_, lean_object* v_00_u03b2_1222_, lean_object* v_cmp_1223_, lean_object* v_t_1224_, lean_object* v_k_1225_, lean_object* v_fallback_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Std_DTreeMap_Raw_getEntryGED(v_00_u03b1_1221_, v_00_u03b2_1222_, v_cmp_1223_, v_t_1224_, v_k_1225_, v_fallback_1226_);
lean_dec_ref(v_fallback_1226_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___redArg(lean_object* v_cmp_1228_, lean_object* v_t_1229_, lean_object* v_k_1230_, lean_object* v_fallback_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_box(0);
v___x_1233_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1228_, v_k_1230_, v___x_1232_, v_t_1229_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_inc_ref(v_fallback_1231_);
return v_fallback_1231_;
}
else
{
lean_object* v_val_1234_; 
v_val_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_val_1234_);
lean_dec_ref_known(v___x_1233_, 1);
return v_val_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___redArg___boxed(lean_object* v_cmp_1235_, lean_object* v_t_1236_, lean_object* v_k_1237_, lean_object* v_fallback_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Std_DTreeMap_Raw_getEntryGTD___redArg(v_cmp_1235_, v_t_1236_, v_k_1237_, v_fallback_1238_);
lean_dec_ref(v_fallback_1238_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD(lean_object* v_00_u03b1_1240_, lean_object* v_00_u03b2_1241_, lean_object* v_cmp_1242_, lean_object* v_t_1243_, lean_object* v_k_1244_, lean_object* v_fallback_1245_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_box(0);
v___x_1247_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1242_, v_k_1244_, v___x_1246_, v_t_1243_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_inc_ref(v_fallback_1245_);
return v_fallback_1245_;
}
else
{
lean_object* v_val_1248_; 
v_val_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_val_1248_);
lean_dec_ref_known(v___x_1247_, 1);
return v_val_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_00_u03b2_1250_, lean_object* v_cmp_1251_, lean_object* v_t_1252_, lean_object* v_k_1253_, lean_object* v_fallback_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Std_DTreeMap_Raw_getEntryGTD(v_00_u03b1_1249_, v_00_u03b2_1250_, v_cmp_1251_, v_t_1252_, v_k_1253_, v_fallback_1254_);
lean_dec_ref(v_fallback_1254_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___redArg(lean_object* v_cmp_1256_, lean_object* v_t_1257_, lean_object* v_k_1258_, lean_object* v_fallback_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_box(0);
v___x_1261_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1256_, v_k_1258_, v___x_1260_, v_t_1257_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_inc_ref(v_fallback_1259_);
return v_fallback_1259_;
}
else
{
lean_object* v_val_1262_; 
v_val_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v___x_1261_, 1);
return v_val_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___redArg___boxed(lean_object* v_cmp_1263_, lean_object* v_t_1264_, lean_object* v_k_1265_, lean_object* v_fallback_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_DTreeMap_Raw_getEntryLED___redArg(v_cmp_1263_, v_t_1264_, v_k_1265_, v_fallback_1266_);
lean_dec_ref(v_fallback_1266_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED(lean_object* v_00_u03b1_1268_, lean_object* v_00_u03b2_1269_, lean_object* v_cmp_1270_, lean_object* v_t_1271_, lean_object* v_k_1272_, lean_object* v_fallback_1273_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_box(0);
v___x_1275_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1270_, v_k_1272_, v___x_1274_, v_t_1271_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_inc_ref(v_fallback_1273_);
return v_fallback_1273_;
}
else
{
lean_object* v_val_1276_; 
v_val_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_val_1276_);
lean_dec_ref_known(v___x_1275_, 1);
return v_val_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___boxed(lean_object* v_00_u03b1_1277_, lean_object* v_00_u03b2_1278_, lean_object* v_cmp_1279_, lean_object* v_t_1280_, lean_object* v_k_1281_, lean_object* v_fallback_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Std_DTreeMap_Raw_getEntryLED(v_00_u03b1_1277_, v_00_u03b2_1278_, v_cmp_1279_, v_t_1280_, v_k_1281_, v_fallback_1282_);
lean_dec_ref(v_fallback_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___redArg(lean_object* v_cmp_1284_, lean_object* v_t_1285_, lean_object* v_k_1286_, lean_object* v_fallback_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_box(0);
v___x_1289_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1284_, v_k_1286_, v___x_1288_, v_t_1285_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_inc_ref(v_fallback_1287_);
return v_fallback_1287_;
}
else
{
lean_object* v_val_1290_; 
v_val_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_val_1290_);
lean_dec_ref_known(v___x_1289_, 1);
return v_val_1290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___redArg___boxed(lean_object* v_cmp_1291_, lean_object* v_t_1292_, lean_object* v_k_1293_, lean_object* v_fallback_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Std_DTreeMap_Raw_getEntryLTD___redArg(v_cmp_1291_, v_t_1292_, v_k_1293_, v_fallback_1294_);
lean_dec_ref(v_fallback_1294_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD(lean_object* v_00_u03b1_1296_, lean_object* v_00_u03b2_1297_, lean_object* v_cmp_1298_, lean_object* v_t_1299_, lean_object* v_k_1300_, lean_object* v_fallback_1301_){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_box(0);
v___x_1303_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1298_, v_k_1300_, v___x_1302_, v_t_1299_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_inc_ref(v_fallback_1301_);
return v_fallback_1301_;
}
else
{
lean_object* v_val_1304_; 
v_val_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v___x_1303_, 1);
return v_val_1304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___boxed(lean_object* v_00_u03b1_1305_, lean_object* v_00_u03b2_1306_, lean_object* v_cmp_1307_, lean_object* v_t_1308_, lean_object* v_k_1309_, lean_object* v_fallback_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Std_DTreeMap_Raw_getEntryLTD(v_00_u03b1_1305_, v_00_u03b2_1306_, v_cmp_1307_, v_t_1308_, v_k_1309_, v_fallback_1310_);
lean_dec_ref(v_fallback_1310_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x3f___redArg(lean_object* v_cmp_1312_, lean_object* v_t_1313_, lean_object* v_k_1314_){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_box(0);
v___x_1316_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1312_, v_k_1314_, v___x_1315_, v_t_1313_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x3f(lean_object* v_00_u03b1_1317_, lean_object* v_00_u03b2_1318_, lean_object* v_cmp_1319_, lean_object* v_t_1320_, lean_object* v_k_1321_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_box(0);
v___x_1323_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1319_, v_k_1321_, v___x_1322_, v_t_1320_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x3f___redArg(lean_object* v_cmp_1324_, lean_object* v_t_1325_, lean_object* v_k_1326_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_box(0);
v___x_1328_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1324_, v_k_1326_, v___x_1327_, v_t_1325_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x3f(lean_object* v_00_u03b1_1329_, lean_object* v_00_u03b2_1330_, lean_object* v_cmp_1331_, lean_object* v_t_1332_, lean_object* v_k_1333_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_box(0);
v___x_1335_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1331_, v_k_1333_, v___x_1334_, v_t_1332_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x3f___redArg(lean_object* v_cmp_1336_, lean_object* v_t_1337_, lean_object* v_k_1338_){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1336_, v_k_1338_, v___x_1339_, v_t_1337_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x3f(lean_object* v_00_u03b1_1341_, lean_object* v_00_u03b2_1342_, lean_object* v_cmp_1343_, lean_object* v_t_1344_, lean_object* v_k_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_box(0);
v___x_1347_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1343_, v_k_1345_, v___x_1346_, v_t_1344_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x3f___redArg(lean_object* v_cmp_1348_, lean_object* v_t_1349_, lean_object* v_k_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_box(0);
v___x_1352_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1348_, v_k_1350_, v___x_1351_, v_t_1349_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x3f(lean_object* v_00_u03b1_1353_, lean_object* v_00_u03b2_1354_, lean_object* v_cmp_1355_, lean_object* v_t_1356_, lean_object* v_k_1357_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_box(0);
v___x_1359_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1355_, v_k_1357_, v___x_1358_, v_t_1356_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___redArg(lean_object* v_cmp_1360_, lean_object* v_inst_1361_, lean_object* v_t_1362_, lean_object* v_k_1363_){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_box(0);
v___x_1365_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1360_, v_k_1363_, v___x_1364_, v_t_1362_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1367_ = l_panic___redArg(v_inst_1361_, v___x_1366_);
return v___x_1367_;
}
else
{
lean_object* v_val_1368_; 
v_val_1368_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_val_1368_);
lean_dec_ref_known(v___x_1365_, 1);
return v_val_1368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1369_, lean_object* v_inst_1370_, lean_object* v_t_1371_, lean_object* v_k_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Std_DTreeMap_Raw_getKeyGE_x21___redArg(v_cmp_1369_, v_inst_1370_, v_t_1371_, v_k_1372_);
lean_dec(v_inst_1370_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21(lean_object* v_00_u03b1_1374_, lean_object* v_00_u03b2_1375_, lean_object* v_cmp_1376_, lean_object* v_inst_1377_, lean_object* v_t_1378_, lean_object* v_k_1379_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1376_, v_k_1379_, v___x_1380_, v_t_1378_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1383_ = l_panic___redArg(v_inst_1377_, v___x_1382_);
return v___x_1383_;
}
else
{
lean_object* v_val_1384_; 
v_val_1384_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_val_1384_);
lean_dec_ref_known(v___x_1381_, 1);
return v_val_1384_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1385_, lean_object* v_00_u03b2_1386_, lean_object* v_cmp_1387_, lean_object* v_inst_1388_, lean_object* v_t_1389_, lean_object* v_k_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Std_DTreeMap_Raw_getKeyGE_x21(v_00_u03b1_1385_, v_00_u03b2_1386_, v_cmp_1387_, v_inst_1388_, v_t_1389_, v_k_1390_);
lean_dec(v_inst_1388_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___redArg(lean_object* v_cmp_1392_, lean_object* v_inst_1393_, lean_object* v_t_1394_, lean_object* v_k_1395_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_box(0);
v___x_1397_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1392_, v_k_1395_, v___x_1396_, v_t_1394_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1399_ = l_panic___redArg(v_inst_1393_, v___x_1398_);
return v___x_1399_;
}
else
{
lean_object* v_val_1400_; 
v_val_1400_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v___x_1397_, 1);
return v_val_1400_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1401_, lean_object* v_inst_1402_, lean_object* v_t_1403_, lean_object* v_k_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Std_DTreeMap_Raw_getKeyGT_x21___redArg(v_cmp_1401_, v_inst_1402_, v_t_1403_, v_k_1404_);
lean_dec(v_inst_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21(lean_object* v_00_u03b1_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_cmp_1408_, lean_object* v_inst_1409_, lean_object* v_t_1410_, lean_object* v_k_1411_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_box(0);
v___x_1413_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1408_, v_k_1411_, v___x_1412_, v_t_1410_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1415_ = l_panic___redArg(v_inst_1409_, v___x_1414_);
return v___x_1415_;
}
else
{
lean_object* v_val_1416_; 
v_val_1416_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_val_1416_);
lean_dec_ref_known(v___x_1413_, 1);
return v_val_1416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1417_, lean_object* v_00_u03b2_1418_, lean_object* v_cmp_1419_, lean_object* v_inst_1420_, lean_object* v_t_1421_, lean_object* v_k_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Std_DTreeMap_Raw_getKeyGT_x21(v_00_u03b1_1417_, v_00_u03b2_1418_, v_cmp_1419_, v_inst_1420_, v_t_1421_, v_k_1422_);
lean_dec(v_inst_1420_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___redArg(lean_object* v_cmp_1424_, lean_object* v_inst_1425_, lean_object* v_t_1426_, lean_object* v_k_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_box(0);
v___x_1429_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1424_, v_k_1427_, v___x_1428_, v_t_1426_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1431_ = l_panic___redArg(v_inst_1425_, v___x_1430_);
return v___x_1431_;
}
else
{
lean_object* v_val_1432_; 
v_val_1432_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_val_1432_);
lean_dec_ref_known(v___x_1429_, 1);
return v_val_1432_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1433_, lean_object* v_inst_1434_, lean_object* v_t_1435_, lean_object* v_k_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Std_DTreeMap_Raw_getKeyLE_x21___redArg(v_cmp_1433_, v_inst_1434_, v_t_1435_, v_k_1436_);
lean_dec(v_inst_1434_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21(lean_object* v_00_u03b1_1438_, lean_object* v_00_u03b2_1439_, lean_object* v_cmp_1440_, lean_object* v_inst_1441_, lean_object* v_t_1442_, lean_object* v_k_1443_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_box(0);
v___x_1445_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1440_, v_k_1443_, v___x_1444_, v_t_1442_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1447_ = l_panic___redArg(v_inst_1441_, v___x_1446_);
return v___x_1447_;
}
else
{
lean_object* v_val_1448_; 
v_val_1448_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_val_1448_);
lean_dec_ref_known(v___x_1445_, 1);
return v_val_1448_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1449_, lean_object* v_00_u03b2_1450_, lean_object* v_cmp_1451_, lean_object* v_inst_1452_, lean_object* v_t_1453_, lean_object* v_k_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Std_DTreeMap_Raw_getKeyLE_x21(v_00_u03b1_1449_, v_00_u03b2_1450_, v_cmp_1451_, v_inst_1452_, v_t_1453_, v_k_1454_);
lean_dec(v_inst_1452_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___redArg(lean_object* v_cmp_1456_, lean_object* v_inst_1457_, lean_object* v_t_1458_, lean_object* v_k_1459_){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_box(0);
v___x_1461_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1456_, v_k_1459_, v___x_1460_, v_t_1458_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1463_ = l_panic___redArg(v_inst_1457_, v___x_1462_);
return v___x_1463_;
}
else
{
lean_object* v_val_1464_; 
v_val_1464_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_val_1464_);
lean_dec_ref_known(v___x_1461_, 1);
return v_val_1464_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1465_, lean_object* v_inst_1466_, lean_object* v_t_1467_, lean_object* v_k_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Std_DTreeMap_Raw_getKeyLT_x21___redArg(v_cmp_1465_, v_inst_1466_, v_t_1467_, v_k_1468_);
lean_dec(v_inst_1466_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21(lean_object* v_00_u03b1_1470_, lean_object* v_00_u03b2_1471_, lean_object* v_cmp_1472_, lean_object* v_inst_1473_, lean_object* v_t_1474_, lean_object* v_k_1475_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = lean_box(0);
v___x_1477_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1472_, v_k_1475_, v___x_1476_, v_t_1474_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1479_ = l_panic___redArg(v_inst_1473_, v___x_1478_);
return v___x_1479_;
}
else
{
lean_object* v_val_1480_; 
v_val_1480_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_val_1480_);
lean_dec_ref_known(v___x_1477_, 1);
return v_val_1480_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1481_, lean_object* v_00_u03b2_1482_, lean_object* v_cmp_1483_, lean_object* v_inst_1484_, lean_object* v_t_1485_, lean_object* v_k_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Std_DTreeMap_Raw_getKeyLT_x21(v_00_u03b1_1481_, v_00_u03b2_1482_, v_cmp_1483_, v_inst_1484_, v_t_1485_, v_k_1486_);
lean_dec(v_inst_1484_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___redArg(lean_object* v_cmp_1488_, lean_object* v_t_1489_, lean_object* v_k_1490_, lean_object* v_fallback_1491_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = lean_box(0);
v___x_1493_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1488_, v_k_1490_, v___x_1492_, v_t_1489_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_inc(v_fallback_1491_);
return v_fallback_1491_;
}
else
{
lean_object* v_val_1494_; 
v_val_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_val_1494_);
lean_dec_ref_known(v___x_1493_, 1);
return v_val_1494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___redArg___boxed(lean_object* v_cmp_1495_, lean_object* v_t_1496_, lean_object* v_k_1497_, lean_object* v_fallback_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Std_DTreeMap_Raw_getKeyGED___redArg(v_cmp_1495_, v_t_1496_, v_k_1497_, v_fallback_1498_);
lean_dec(v_fallback_1498_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED(lean_object* v_00_u03b1_1500_, lean_object* v_00_u03b2_1501_, lean_object* v_cmp_1502_, lean_object* v_t_1503_, lean_object* v_k_1504_, lean_object* v_fallback_1505_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_box(0);
v___x_1507_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1502_, v_k_1504_, v___x_1506_, v_t_1503_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_inc(v_fallback_1505_);
return v_fallback_1505_;
}
else
{
lean_object* v_val_1508_; 
v_val_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_val_1508_);
lean_dec_ref_known(v___x_1507_, 1);
return v_val_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___boxed(lean_object* v_00_u03b1_1509_, lean_object* v_00_u03b2_1510_, lean_object* v_cmp_1511_, lean_object* v_t_1512_, lean_object* v_k_1513_, lean_object* v_fallback_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Std_DTreeMap_Raw_getKeyGED(v_00_u03b1_1509_, v_00_u03b2_1510_, v_cmp_1511_, v_t_1512_, v_k_1513_, v_fallback_1514_);
lean_dec(v_fallback_1514_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___redArg(lean_object* v_cmp_1516_, lean_object* v_t_1517_, lean_object* v_k_1518_, lean_object* v_fallback_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_box(0);
v___x_1521_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1516_, v_k_1518_, v___x_1520_, v_t_1517_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_inc(v_fallback_1519_);
return v_fallback_1519_;
}
else
{
lean_object* v_val_1522_; 
v_val_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_val_1522_);
lean_dec_ref_known(v___x_1521_, 1);
return v_val_1522_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___redArg___boxed(lean_object* v_cmp_1523_, lean_object* v_t_1524_, lean_object* v_k_1525_, lean_object* v_fallback_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Std_DTreeMap_Raw_getKeyGTD___redArg(v_cmp_1523_, v_t_1524_, v_k_1525_, v_fallback_1526_);
lean_dec(v_fallback_1526_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD(lean_object* v_00_u03b1_1528_, lean_object* v_00_u03b2_1529_, lean_object* v_cmp_1530_, lean_object* v_t_1531_, lean_object* v_k_1532_, lean_object* v_fallback_1533_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_box(0);
v___x_1535_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1530_, v_k_1532_, v___x_1534_, v_t_1531_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_inc(v_fallback_1533_);
return v_fallback_1533_;
}
else
{
lean_object* v_val_1536_; 
v_val_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___x_1535_, 1);
return v_val_1536_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_00_u03b2_1538_, lean_object* v_cmp_1539_, lean_object* v_t_1540_, lean_object* v_k_1541_, lean_object* v_fallback_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Std_DTreeMap_Raw_getKeyGTD(v_00_u03b1_1537_, v_00_u03b2_1538_, v_cmp_1539_, v_t_1540_, v_k_1541_, v_fallback_1542_);
lean_dec(v_fallback_1542_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___redArg(lean_object* v_cmp_1544_, lean_object* v_t_1545_, lean_object* v_k_1546_, lean_object* v_fallback_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1544_, v_k_1546_, v___x_1548_, v_t_1545_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_inc(v_fallback_1547_);
return v_fallback_1547_;
}
else
{
lean_object* v_val_1550_; 
v_val_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_val_1550_);
lean_dec_ref_known(v___x_1549_, 1);
return v_val_1550_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___redArg___boxed(lean_object* v_cmp_1551_, lean_object* v_t_1552_, lean_object* v_k_1553_, lean_object* v_fallback_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Std_DTreeMap_Raw_getKeyLED___redArg(v_cmp_1551_, v_t_1552_, v_k_1553_, v_fallback_1554_);
lean_dec(v_fallback_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED(lean_object* v_00_u03b1_1556_, lean_object* v_00_u03b2_1557_, lean_object* v_cmp_1558_, lean_object* v_t_1559_, lean_object* v_k_1560_, lean_object* v_fallback_1561_){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1558_, v_k_1560_, v___x_1562_, v_t_1559_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_inc(v_fallback_1561_);
return v_fallback_1561_;
}
else
{
lean_object* v_val_1564_; 
v_val_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v___x_1563_, 1);
return v_val_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___boxed(lean_object* v_00_u03b1_1565_, lean_object* v_00_u03b2_1566_, lean_object* v_cmp_1567_, lean_object* v_t_1568_, lean_object* v_k_1569_, lean_object* v_fallback_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Std_DTreeMap_Raw_getKeyLED(v_00_u03b1_1565_, v_00_u03b2_1566_, v_cmp_1567_, v_t_1568_, v_k_1569_, v_fallback_1570_);
lean_dec(v_fallback_1570_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___redArg(lean_object* v_cmp_1572_, lean_object* v_t_1573_, lean_object* v_k_1574_, lean_object* v_fallback_1575_){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_box(0);
v___x_1577_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1572_, v_k_1574_, v___x_1576_, v_t_1573_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_inc(v_fallback_1575_);
return v_fallback_1575_;
}
else
{
lean_object* v_val_1578_; 
v_val_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_val_1578_);
lean_dec_ref_known(v___x_1577_, 1);
return v_val_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___redArg___boxed(lean_object* v_cmp_1579_, lean_object* v_t_1580_, lean_object* v_k_1581_, lean_object* v_fallback_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Std_DTreeMap_Raw_getKeyLTD___redArg(v_cmp_1579_, v_t_1580_, v_k_1581_, v_fallback_1582_);
lean_dec(v_fallback_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD(lean_object* v_00_u03b1_1584_, lean_object* v_00_u03b2_1585_, lean_object* v_cmp_1586_, lean_object* v_t_1587_, lean_object* v_k_1588_, lean_object* v_fallback_1589_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_box(0);
v___x_1591_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1586_, v_k_1588_, v___x_1590_, v_t_1587_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_inc(v_fallback_1589_);
return v_fallback_1589_;
}
else
{
lean_object* v_val_1592_; 
v_val_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v___x_1591_, 1);
return v_val_1592_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___boxed(lean_object* v_00_u03b1_1593_, lean_object* v_00_u03b2_1594_, lean_object* v_cmp_1595_, lean_object* v_t_1596_, lean_object* v_k_1597_, lean_object* v_fallback_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Std_DTreeMap_Raw_getKeyLTD(v_00_u03b1_1593_, v_00_u03b2_1594_, v_cmp_1595_, v_t_1596_, v_k_1597_, v_fallback_1598_);
lean_dec(v_fallback_1598_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1600_, lean_object* v_t_1601_, lean_object* v_a_1602_, lean_object* v_b_1603_){
_start:
{
lean_object* v___x_1604_; 
lean_inc(v_a_1602_);
lean_inc(v_t_1601_);
lean_inc_ref(v_cmp_1600_);
v___x_1604_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1600_, v_t_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1604_) == 0)
{
uint8_t v___x_1605_; 
lean_inc(v_t_1601_);
lean_inc(v_a_1602_);
lean_inc_ref(v_cmp_1600_);
v___x_1605_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1600_, v_a_1602_, v_t_1601_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1600_, v_a_1602_, v_b_1603_, v_t_1601_);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1604_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
return v___x_1607_;
}
else
{
lean_object* v___x_1608_; 
lean_dec(v_b_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_cmp_1600_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1604_);
lean_ctor_set(v___x_1608_, 1, v_t_1601_);
return v___x_1608_;
}
}
else
{
lean_object* v___x_1609_; 
lean_dec(v_b_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_cmp_1600_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1604_);
lean_ctor_set(v___x_1609_, 1, v_t_1601_);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1610_, lean_object* v_cmp_1611_, lean_object* v_00_u03b2_1612_, lean_object* v_t_1613_, lean_object* v_a_1614_, lean_object* v_b_1615_){
_start:
{
lean_object* v___x_1616_; 
lean_inc(v_a_1614_);
lean_inc(v_t_1613_);
lean_inc_ref(v_cmp_1611_);
v___x_1616_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1611_, v_t_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1616_) == 0)
{
uint8_t v___x_1617_; 
lean_inc(v_t_1613_);
lean_inc(v_a_1614_);
lean_inc_ref(v_cmp_1611_);
v___x_1617_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1611_, v_a_1614_, v_t_1613_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1611_, v_a_1614_, v_b_1615_, v_t_1613_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1616_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
return v___x_1619_;
}
else
{
lean_object* v___x_1620_; 
lean_dec(v_b_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_cmp_1611_);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1616_);
lean_ctor_set(v___x_1620_, 1, v_t_1613_);
return v___x_1620_;
}
}
else
{
lean_object* v___x_1621_; 
lean_dec(v_b_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_cmp_1611_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1616_);
lean_ctor_set(v___x_1621_, 1, v_t_1613_);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x3f___redArg(lean_object* v_cmp_1622_, lean_object* v_t_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1622_, v_t_1623_, v_a_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x3f(lean_object* v_00_u03b1_1626_, lean_object* v_cmp_1627_, lean_object* v_00_u03b2_1628_, lean_object* v_t_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1627_, v_t_1629_, v_a_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get___redArg(lean_object* v_cmp_1632_, lean_object* v_t_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1632_, v_t_1633_, v_a_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get(lean_object* v_00_u03b1_1636_, lean_object* v_cmp_1637_, lean_object* v_00_u03b2_1638_, lean_object* v_t_1639_, lean_object* v_a_1640_, lean_object* v_h_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1637_, v_t_1639_, v_a_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___redArg(lean_object* v_cmp_1643_, lean_object* v_inst_1644_, lean_object* v_t_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1643_, v_inst_1644_, v_t_1645_, v_a_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___redArg___boxed(lean_object* v_cmp_1648_, lean_object* v_inst_1649_, lean_object* v_t_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Std_DTreeMap_Raw_Const_get_x21___redArg(v_cmp_1648_, v_inst_1649_, v_t_1650_, v_a_1651_);
lean_dec(v_inst_1649_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21(lean_object* v_00_u03b1_1653_, lean_object* v_cmp_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_inst_1656_, lean_object* v_t_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1654_, v_inst_1656_, v_t_1657_, v_a_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___boxed(lean_object* v_00_u03b1_1660_, lean_object* v_cmp_1661_, lean_object* v_00_u03b2_1662_, lean_object* v_inst_1663_, lean_object* v_t_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Std_DTreeMap_Raw_Const_get_x21(v_00_u03b1_1660_, v_cmp_1661_, v_00_u03b2_1662_, v_inst_1663_, v_t_1664_, v_a_1665_);
lean_dec(v_inst_1663_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___redArg(lean_object* v_cmp_1667_, lean_object* v_t_1668_, lean_object* v_a_1669_, lean_object* v_fallback_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1667_, v_t_1668_, v_a_1669_, v_fallback_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___redArg___boxed(lean_object* v_cmp_1672_, lean_object* v_t_1673_, lean_object* v_a_1674_, lean_object* v_fallback_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Std_DTreeMap_Raw_Const_getD___redArg(v_cmp_1672_, v_t_1673_, v_a_1674_, v_fallback_1675_);
lean_dec(v_fallback_1675_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD(lean_object* v_00_u03b1_1677_, lean_object* v_cmp_1678_, lean_object* v_00_u03b2_1679_, lean_object* v_t_1680_, lean_object* v_a_1681_, lean_object* v_fallback_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1678_, v_t_1680_, v_a_1681_, v_fallback_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___boxed(lean_object* v_00_u03b1_1684_, lean_object* v_cmp_1685_, lean_object* v_00_u03b2_1686_, lean_object* v_t_1687_, lean_object* v_a_1688_, lean_object* v_fallback_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_DTreeMap_Raw_Const_getD(v_00_u03b1_1684_, v_cmp_1685_, v_00_u03b2_1686_, v_t_1687_, v_a_1688_, v_fallback_1689_);
lean_dec(v_fallback_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg(lean_object* v_t_1691_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg(v_t_1693_);
lean_dec(v_t_1693_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f(lean_object* v_00_u03b1_1695_, lean_object* v_cmp_1696_, lean_object* v_00_u03b2_1697_, lean_object* v_t_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_cmp_1701_, lean_object* v_00_u03b2_1702_, lean_object* v_t_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Std_DTreeMap_Raw_Const_minEntry_x3f(v_00_u03b1_1700_, v_cmp_1701_, v_00_u03b2_1702_, v_t_1703_);
lean_dec(v_t_1703_);
lean_dec_ref(v_cmp_1701_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg(lean_object* v_inst_1705_, lean_object* v_t_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1705_, v_t_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1708_, lean_object* v_t_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg(v_inst_1708_, v_t_1709_);
lean_dec(v_t_1709_);
lean_dec_ref(v_inst_1708_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21(lean_object* v_00_u03b1_1711_, lean_object* v_cmp_1712_, lean_object* v_00_u03b2_1713_, lean_object* v_inst_1714_, lean_object* v_t_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1714_, v_t_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1717_, lean_object* v_cmp_1718_, lean_object* v_00_u03b2_1719_, lean_object* v_inst_1720_, lean_object* v_t_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Std_DTreeMap_Raw_Const_minEntry_x21(v_00_u03b1_1717_, v_cmp_1718_, v_00_u03b2_1719_, v_inst_1720_, v_t_1721_);
lean_dec(v_t_1721_);
lean_dec_ref(v_inst_1720_);
lean_dec_ref(v_cmp_1718_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___redArg(lean_object* v_t_1723_, lean_object* v_fallback_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1723_, v_fallback_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___redArg___boxed(lean_object* v_t_1726_, lean_object* v_fallback_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Std_DTreeMap_Raw_Const_minEntryD___redArg(v_t_1726_, v_fallback_1727_);
lean_dec_ref(v_fallback_1727_);
lean_dec(v_t_1726_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD(lean_object* v_00_u03b1_1729_, lean_object* v_cmp_1730_, lean_object* v_00_u03b2_1731_, lean_object* v_t_1732_, lean_object* v_fallback_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1732_, v_fallback_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___boxed(lean_object* v_00_u03b1_1735_, lean_object* v_cmp_1736_, lean_object* v_00_u03b2_1737_, lean_object* v_t_1738_, lean_object* v_fallback_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Std_DTreeMap_Raw_Const_minEntryD(v_00_u03b1_1735_, v_cmp_1736_, v_00_u03b2_1737_, v_t_1738_, v_fallback_1739_);
lean_dec_ref(v_fallback_1739_);
lean_dec(v_t_1738_);
lean_dec_ref(v_cmp_1736_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg(lean_object* v_t_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg(v_t_1743_);
lean_dec(v_t_1743_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f(lean_object* v_00_u03b1_1745_, lean_object* v_cmp_1746_, lean_object* v_00_u03b2_1747_, lean_object* v_t_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1750_, lean_object* v_cmp_1751_, lean_object* v_00_u03b2_1752_, lean_object* v_t_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Std_DTreeMap_Raw_Const_maxEntry_x3f(v_00_u03b1_1750_, v_cmp_1751_, v_00_u03b2_1752_, v_t_1753_);
lean_dec(v_t_1753_);
lean_dec_ref(v_cmp_1751_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg(lean_object* v_inst_1755_, lean_object* v_t_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1755_, v_t_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_1758_, lean_object* v_t_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg(v_inst_1758_, v_t_1759_);
lean_dec(v_t_1759_);
lean_dec_ref(v_inst_1758_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21(lean_object* v_00_u03b1_1761_, lean_object* v_cmp_1762_, lean_object* v_00_u03b2_1763_, lean_object* v_inst_1764_, lean_object* v_t_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1764_, v_t_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_1767_, lean_object* v_cmp_1768_, lean_object* v_00_u03b2_1769_, lean_object* v_inst_1770_, lean_object* v_t_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Std_DTreeMap_Raw_Const_maxEntry_x21(v_00_u03b1_1767_, v_cmp_1768_, v_00_u03b2_1769_, v_inst_1770_, v_t_1771_);
lean_dec(v_t_1771_);
lean_dec_ref(v_inst_1770_);
lean_dec_ref(v_cmp_1768_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___redArg(lean_object* v_t_1773_, lean_object* v_fallback_1774_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1773_, v_fallback_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___redArg___boxed(lean_object* v_t_1776_, lean_object* v_fallback_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Std_DTreeMap_Raw_Const_maxEntryD___redArg(v_t_1776_, v_fallback_1777_);
lean_dec_ref(v_fallback_1777_);
lean_dec(v_t_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD(lean_object* v_00_u03b1_1779_, lean_object* v_cmp_1780_, lean_object* v_00_u03b2_1781_, lean_object* v_t_1782_, lean_object* v_fallback_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1782_, v_fallback_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___boxed(lean_object* v_00_u03b1_1785_, lean_object* v_cmp_1786_, lean_object* v_00_u03b2_1787_, lean_object* v_t_1788_, lean_object* v_fallback_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Std_DTreeMap_Raw_Const_maxEntryD(v_00_u03b1_1785_, v_cmp_1786_, v_00_u03b2_1787_, v_t_1788_, v_fallback_1789_);
lean_dec_ref(v_fallback_1789_);
lean_dec(v_t_1788_);
lean_dec_ref(v_cmp_1786_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg(lean_object* v_t_1791_, lean_object* v_n_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1791_, v_n_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_1794_, lean_object* v_n_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg(v_t_1794_, v_n_1795_);
lean_dec(v_t_1794_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_1797_, lean_object* v_cmp_1798_, lean_object* v_00_u03b2_1799_, lean_object* v_t_1800_, lean_object* v_n_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1800_, v_n_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1803_, lean_object* v_cmp_1804_, lean_object* v_00_u03b2_1805_, lean_object* v_t_1806_, lean_object* v_n_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f(v_00_u03b1_1803_, v_cmp_1804_, v_00_u03b2_1805_, v_t_1806_, v_n_1807_);
lean_dec(v_t_1806_);
lean_dec_ref(v_cmp_1804_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg(lean_object* v_inst_1809_, lean_object* v_t_1810_, lean_object* v_n_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1809_, v_t_1810_, v_n_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_1813_, lean_object* v_t_1814_, lean_object* v_n_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg(v_inst_1813_, v_t_1814_, v_n_1815_);
lean_dec(v_t_1814_);
lean_dec_ref(v_inst_1813_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21(lean_object* v_00_u03b1_1817_, lean_object* v_cmp_1818_, lean_object* v_00_u03b2_1819_, lean_object* v_inst_1820_, lean_object* v_t_1821_, lean_object* v_n_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1820_, v_t_1821_, v_n_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_cmp_1825_, lean_object* v_00_u03b2_1826_, lean_object* v_inst_1827_, lean_object* v_t_1828_, lean_object* v_n_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x21(v_00_u03b1_1824_, v_cmp_1825_, v_00_u03b2_1826_, v_inst_1827_, v_t_1828_, v_n_1829_);
lean_dec(v_t_1828_);
lean_dec_ref(v_inst_1827_);
lean_dec_ref(v_cmp_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg(lean_object* v_t_1831_, lean_object* v_n_1832_, lean_object* v_fallback_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1831_, v_n_1832_, v_fallback_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_1835_, lean_object* v_n_1836_, lean_object* v_fallback_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg(v_t_1835_, v_n_1836_, v_fallback_1837_);
lean_dec_ref(v_fallback_1837_);
lean_dec(v_t_1835_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD(lean_object* v_00_u03b1_1839_, lean_object* v_cmp_1840_, lean_object* v_00_u03b2_1841_, lean_object* v_t_1842_, lean_object* v_n_1843_, lean_object* v_fallback_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1842_, v_n_1843_, v_fallback_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_1846_, lean_object* v_cmp_1847_, lean_object* v_00_u03b2_1848_, lean_object* v_t_1849_, lean_object* v_n_1850_, lean_object* v_fallback_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Std_DTreeMap_Raw_Const_entryAtIdxD(v_00_u03b1_1846_, v_cmp_1847_, v_00_u03b2_1848_, v_t_1849_, v_n_1850_, v_fallback_1851_);
lean_dec_ref(v_fallback_1851_);
lean_dec(v_t_1849_);
lean_dec_ref(v_cmp_1847_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_1853_, lean_object* v_t_1854_, lean_object* v_k_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_box(0);
v___x_1857_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1853_, v_k_1855_, v___x_1856_, v_t_1854_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x3f(lean_object* v_00_u03b1_1858_, lean_object* v_cmp_1859_, lean_object* v_00_u03b2_1860_, lean_object* v_t_1861_, lean_object* v_k_1862_){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_box(0);
v___x_1864_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1859_, v_k_1862_, v___x_1863_, v_t_1861_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_1865_, lean_object* v_t_1866_, lean_object* v_k_1867_){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_box(0);
v___x_1869_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1865_, v_k_1867_, v___x_1868_, v_t_1866_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x3f(lean_object* v_00_u03b1_1870_, lean_object* v_cmp_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_t_1873_, lean_object* v_k_1874_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1871_, v_k_1874_, v___x_1875_, v_t_1873_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_1877_, lean_object* v_t_1878_, lean_object* v_k_1879_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_box(0);
v___x_1881_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1877_, v_k_1879_, v___x_1880_, v_t_1878_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x3f(lean_object* v_00_u03b1_1882_, lean_object* v_cmp_1883_, lean_object* v_00_u03b2_1884_, lean_object* v_t_1885_, lean_object* v_k_1886_){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_box(0);
v___x_1888_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1883_, v_k_1886_, v___x_1887_, v_t_1885_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_1889_, lean_object* v_t_1890_, lean_object* v_k_1891_){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_box(0);
v___x_1893_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1889_, v_k_1891_, v___x_1892_, v_t_1890_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x3f(lean_object* v_00_u03b1_1894_, lean_object* v_cmp_1895_, lean_object* v_00_u03b2_1896_, lean_object* v_t_1897_, lean_object* v_k_1898_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_box(0);
v___x_1900_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1895_, v_k_1898_, v___x_1899_, v_t_1897_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg(lean_object* v_cmp_1901_, lean_object* v_inst_1902_, lean_object* v_t_1903_, lean_object* v_k_1904_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1901_, v_k_1904_, v___x_1905_, v_t_1903_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1908_ = l_panic___redArg(v_inst_1902_, v___x_1907_);
return v___x_1908_;
}
else
{
lean_object* v_val_1909_; 
v_val_1909_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_val_1909_);
lean_dec_ref_known(v___x_1906_, 1);
return v_val_1909_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1910_, lean_object* v_inst_1911_, lean_object* v_t_1912_, lean_object* v_k_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg(v_cmp_1910_, v_inst_1911_, v_t_1912_, v_k_1913_);
lean_dec_ref(v_inst_1911_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21(lean_object* v_00_u03b1_1915_, lean_object* v_cmp_1916_, lean_object* v_00_u03b2_1917_, lean_object* v_inst_1918_, lean_object* v_t_1919_, lean_object* v_k_1920_){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_box(0);
v___x_1922_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1916_, v_k_1920_, v___x_1921_, v_t_1919_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1924_ = l_panic___redArg(v_inst_1918_, v___x_1923_);
return v___x_1924_;
}
else
{
lean_object* v_val_1925_; 
v_val_1925_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_val_1925_);
lean_dec_ref_known(v___x_1922_, 1);
return v_val_1925_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1926_, lean_object* v_cmp_1927_, lean_object* v_00_u03b2_1928_, lean_object* v_inst_1929_, lean_object* v_t_1930_, lean_object* v_k_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Std_DTreeMap_Raw_Const_getEntryGE_x21(v_00_u03b1_1926_, v_cmp_1927_, v_00_u03b2_1928_, v_inst_1929_, v_t_1930_, v_k_1931_);
lean_dec_ref(v_inst_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg(lean_object* v_cmp_1933_, lean_object* v_inst_1934_, lean_object* v_t_1935_, lean_object* v_k_1936_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_box(0);
v___x_1938_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1933_, v_k_1936_, v___x_1937_, v_t_1935_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1940_ = l_panic___redArg(v_inst_1934_, v___x_1939_);
return v___x_1940_;
}
else
{
lean_object* v_val_1941_; 
v_val_1941_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v___x_1938_, 1);
return v_val_1941_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1942_, lean_object* v_inst_1943_, lean_object* v_t_1944_, lean_object* v_k_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg(v_cmp_1942_, v_inst_1943_, v_t_1944_, v_k_1945_);
lean_dec_ref(v_inst_1943_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21(lean_object* v_00_u03b1_1947_, lean_object* v_cmp_1948_, lean_object* v_00_u03b2_1949_, lean_object* v_inst_1950_, lean_object* v_t_1951_, lean_object* v_k_1952_){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_box(0);
v___x_1954_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1948_, v_k_1952_, v___x_1953_, v_t_1951_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1956_ = l_panic___redArg(v_inst_1950_, v___x_1955_);
return v___x_1956_;
}
else
{
lean_object* v_val_1957_; 
v_val_1957_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_val_1957_);
lean_dec_ref_known(v___x_1954_, 1);
return v_val_1957_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1958_, lean_object* v_cmp_1959_, lean_object* v_00_u03b2_1960_, lean_object* v_inst_1961_, lean_object* v_t_1962_, lean_object* v_k_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Std_DTreeMap_Raw_Const_getEntryGT_x21(v_00_u03b1_1958_, v_cmp_1959_, v_00_u03b2_1960_, v_inst_1961_, v_t_1962_, v_k_1963_);
lean_dec_ref(v_inst_1961_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg(lean_object* v_cmp_1965_, lean_object* v_inst_1966_, lean_object* v_t_1967_, lean_object* v_k_1968_){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_box(0);
v___x_1970_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1965_, v_k_1968_, v___x_1969_, v_t_1967_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1972_ = l_panic___redArg(v_inst_1966_, v___x_1971_);
return v___x_1972_;
}
else
{
lean_object* v_val_1973_; 
v_val_1973_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_val_1973_);
lean_dec_ref_known(v___x_1970_, 1);
return v_val_1973_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1974_, lean_object* v_inst_1975_, lean_object* v_t_1976_, lean_object* v_k_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg(v_cmp_1974_, v_inst_1975_, v_t_1976_, v_k_1977_);
lean_dec_ref(v_inst_1975_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21(lean_object* v_00_u03b1_1979_, lean_object* v_cmp_1980_, lean_object* v_00_u03b2_1981_, lean_object* v_inst_1982_, lean_object* v_t_1983_, lean_object* v_k_1984_){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = lean_box(0);
v___x_1986_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1980_, v_k_1984_, v___x_1985_, v_t_1983_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1988_ = l_panic___redArg(v_inst_1982_, v___x_1987_);
return v___x_1988_;
}
else
{
lean_object* v_val_1989_; 
v_val_1989_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_val_1989_);
lean_dec_ref_known(v___x_1986_, 1);
return v_val_1989_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1990_, lean_object* v_cmp_1991_, lean_object* v_00_u03b2_1992_, lean_object* v_inst_1993_, lean_object* v_t_1994_, lean_object* v_k_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Std_DTreeMap_Raw_Const_getEntryLE_x21(v_00_u03b1_1990_, v_cmp_1991_, v_00_u03b2_1992_, v_inst_1993_, v_t_1994_, v_k_1995_);
lean_dec_ref(v_inst_1993_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg(lean_object* v_cmp_1997_, lean_object* v_inst_1998_, lean_object* v_t_1999_, lean_object* v_k_2000_){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_box(0);
v___x_2002_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1997_, v_k_2000_, v___x_2001_, v_t_1999_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_2004_ = l_panic___redArg(v_inst_1998_, v___x_2003_);
return v___x_2004_;
}
else
{
lean_object* v_val_2005_; 
v_val_2005_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_val_2005_);
lean_dec_ref_known(v___x_2002_, 1);
return v_val_2005_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_2006_, lean_object* v_inst_2007_, lean_object* v_t_2008_, lean_object* v_k_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg(v_cmp_2006_, v_inst_2007_, v_t_2008_, v_k_2009_);
lean_dec_ref(v_inst_2007_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21(lean_object* v_00_u03b1_2011_, lean_object* v_cmp_2012_, lean_object* v_00_u03b2_2013_, lean_object* v_inst_2014_, lean_object* v_t_2015_, lean_object* v_k_2016_){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = lean_box(0);
v___x_2018_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2012_, v_k_2016_, v___x_2017_, v_t_2015_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_2020_ = l_panic___redArg(v_inst_2014_, v___x_2019_);
return v___x_2020_;
}
else
{
lean_object* v_val_2021_; 
v_val_2021_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_val_2021_);
lean_dec_ref_known(v___x_2018_, 1);
return v_val_2021_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_cmp_2023_, lean_object* v_00_u03b2_2024_, lean_object* v_inst_2025_, lean_object* v_t_2026_, lean_object* v_k_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Std_DTreeMap_Raw_Const_getEntryLT_x21(v_00_u03b1_2022_, v_cmp_2023_, v_00_u03b2_2024_, v_inst_2025_, v_t_2026_, v_k_2027_);
lean_dec_ref(v_inst_2025_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___redArg(lean_object* v_cmp_2029_, lean_object* v_t_2030_, lean_object* v_k_2031_, lean_object* v_fallback_2032_){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_box(0);
v___x_2034_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2029_, v_k_2031_, v___x_2033_, v_t_2030_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_inc_ref(v_fallback_2032_);
return v_fallback_2032_;
}
else
{
lean_object* v_val_2035_; 
v_val_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_val_2035_);
lean_dec_ref_known(v___x_2034_, 1);
return v_val_2035_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2036_, lean_object* v_t_2037_, lean_object* v_k_2038_, lean_object* v_fallback_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Std_DTreeMap_Raw_Const_getEntryGED___redArg(v_cmp_2036_, v_t_2037_, v_k_2038_, v_fallback_2039_);
lean_dec_ref(v_fallback_2039_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED(lean_object* v_00_u03b1_2041_, lean_object* v_cmp_2042_, lean_object* v_00_u03b2_2043_, lean_object* v_t_2044_, lean_object* v_k_2045_, lean_object* v_fallback_2046_){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_box(0);
v___x_2048_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2042_, v_k_2045_, v___x_2047_, v_t_2044_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_inc_ref(v_fallback_2046_);
return v_fallback_2046_;
}
else
{
lean_object* v_val_2049_; 
v_val_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_val_2049_);
lean_dec_ref_known(v___x_2048_, 1);
return v_val_2049_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2050_, lean_object* v_cmp_2051_, lean_object* v_00_u03b2_2052_, lean_object* v_t_2053_, lean_object* v_k_2054_, lean_object* v_fallback_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Std_DTreeMap_Raw_Const_getEntryGED(v_00_u03b1_2050_, v_cmp_2051_, v_00_u03b2_2052_, v_t_2053_, v_k_2054_, v_fallback_2055_);
lean_dec_ref(v_fallback_2055_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg(lean_object* v_cmp_2057_, lean_object* v_t_2058_, lean_object* v_k_2059_, lean_object* v_fallback_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_box(0);
v___x_2062_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2057_, v_k_2059_, v___x_2061_, v_t_2058_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_inc_ref(v_fallback_2060_);
return v_fallback_2060_;
}
else
{
lean_object* v_val_2063_; 
v_val_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_val_2063_);
lean_dec_ref_known(v___x_2062_, 1);
return v_val_2063_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2064_, lean_object* v_t_2065_, lean_object* v_k_2066_, lean_object* v_fallback_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg(v_cmp_2064_, v_t_2065_, v_k_2066_, v_fallback_2067_);
lean_dec_ref(v_fallback_2067_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD(lean_object* v_00_u03b1_2069_, lean_object* v_cmp_2070_, lean_object* v_00_u03b2_2071_, lean_object* v_t_2072_, lean_object* v_k_2073_, lean_object* v_fallback_2074_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_box(0);
v___x_2076_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2070_, v_k_2073_, v___x_2075_, v_t_2072_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_inc_ref(v_fallback_2074_);
return v_fallback_2074_;
}
else
{
lean_object* v_val_2077_; 
v_val_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_val_2077_);
lean_dec_ref_known(v___x_2076_, 1);
return v_val_2077_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2078_, lean_object* v_cmp_2079_, lean_object* v_00_u03b2_2080_, lean_object* v_t_2081_, lean_object* v_k_2082_, lean_object* v_fallback_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Std_DTreeMap_Raw_Const_getEntryGTD(v_00_u03b1_2078_, v_cmp_2079_, v_00_u03b2_2080_, v_t_2081_, v_k_2082_, v_fallback_2083_);
lean_dec_ref(v_fallback_2083_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___redArg(lean_object* v_cmp_2085_, lean_object* v_t_2086_, lean_object* v_k_2087_, lean_object* v_fallback_2088_){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_box(0);
v___x_2090_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2085_, v_k_2087_, v___x_2089_, v_t_2086_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_inc_ref(v_fallback_2088_);
return v_fallback_2088_;
}
else
{
lean_object* v_val_2091_; 
v_val_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_val_2091_);
lean_dec_ref_known(v___x_2090_, 1);
return v_val_2091_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2092_, lean_object* v_t_2093_, lean_object* v_k_2094_, lean_object* v_fallback_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Std_DTreeMap_Raw_Const_getEntryLED___redArg(v_cmp_2092_, v_t_2093_, v_k_2094_, v_fallback_2095_);
lean_dec_ref(v_fallback_2095_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED(lean_object* v_00_u03b1_2097_, lean_object* v_cmp_2098_, lean_object* v_00_u03b2_2099_, lean_object* v_t_2100_, lean_object* v_k_2101_, lean_object* v_fallback_2102_){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = lean_box(0);
v___x_2104_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2098_, v_k_2101_, v___x_2103_, v_t_2100_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_inc_ref(v_fallback_2102_);
return v_fallback_2102_;
}
else
{
lean_object* v_val_2105_; 
v_val_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_val_2105_);
lean_dec_ref_known(v___x_2104_, 1);
return v_val_2105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2106_, lean_object* v_cmp_2107_, lean_object* v_00_u03b2_2108_, lean_object* v_t_2109_, lean_object* v_k_2110_, lean_object* v_fallback_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Std_DTreeMap_Raw_Const_getEntryLED(v_00_u03b1_2106_, v_cmp_2107_, v_00_u03b2_2108_, v_t_2109_, v_k_2110_, v_fallback_2111_);
lean_dec_ref(v_fallback_2111_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg(lean_object* v_cmp_2113_, lean_object* v_t_2114_, lean_object* v_k_2115_, lean_object* v_fallback_2116_){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_box(0);
v___x_2118_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2113_, v_k_2115_, v___x_2117_, v_t_2114_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_inc_ref(v_fallback_2116_);
return v_fallback_2116_;
}
else
{
lean_object* v_val_2119_; 
v_val_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_val_2119_);
lean_dec_ref_known(v___x_2118_, 1);
return v_val_2119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2120_, lean_object* v_t_2121_, lean_object* v_k_2122_, lean_object* v_fallback_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg(v_cmp_2120_, v_t_2121_, v_k_2122_, v_fallback_2123_);
lean_dec_ref(v_fallback_2123_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD(lean_object* v_00_u03b1_2125_, lean_object* v_cmp_2126_, lean_object* v_00_u03b2_2127_, lean_object* v_t_2128_, lean_object* v_k_2129_, lean_object* v_fallback_2130_){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_box(0);
v___x_2132_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2126_, v_k_2129_, v___x_2131_, v_t_2128_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_inc_ref(v_fallback_2130_);
return v_fallback_2130_;
}
else
{
lean_object* v_val_2133_; 
v_val_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_val_2133_);
lean_dec_ref_known(v___x_2132_, 1);
return v_val_2133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2134_, lean_object* v_cmp_2135_, lean_object* v_00_u03b2_2136_, lean_object* v_t_2137_, lean_object* v_k_2138_, lean_object* v_fallback_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Std_DTreeMap_Raw_Const_getEntryLTD(v_00_u03b1_2134_, v_cmp_2135_, v_00_u03b2_2136_, v_t_2137_, v_k_2138_, v_fallback_2139_);
lean_dec_ref(v_fallback_2139_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter___redArg(lean_object* v_f_2141_, lean_object* v_t_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_2141_, v_t_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter(lean_object* v_00_u03b1_2144_, lean_object* v_00_u03b2_2145_, lean_object* v_cmp_2146_, lean_object* v_f_2147_, lean_object* v_t_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_2147_, v_t_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter___boxed(lean_object* v_00_u03b1_2150_, lean_object* v_00_u03b2_2151_, lean_object* v_cmp_2152_, lean_object* v_f_2153_, lean_object* v_t_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Std_DTreeMap_Raw_filter(v_00_u03b1_2150_, v_00_u03b2_2151_, v_cmp_2152_, v_f_2153_, v_t_2154_);
lean_dec_ref(v_cmp_2152_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM___redArg(lean_object* v_inst_2156_, lean_object* v_f_2157_, lean_object* v_init_2158_, lean_object* v_t_2159_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2156_, v_f_2157_, v_init_2158_, v_t_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM(lean_object* v_00_u03b1_2161_, lean_object* v_00_u03b2_2162_, lean_object* v_cmp_2163_, lean_object* v_00_u03b4_2164_, lean_object* v_m_2165_, lean_object* v_inst_2166_, lean_object* v_f_2167_, lean_object* v_init_2168_, lean_object* v_t_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2166_, v_f_2167_, v_init_2168_, v_t_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM___boxed(lean_object* v_00_u03b1_2171_, lean_object* v_00_u03b2_2172_, lean_object* v_cmp_2173_, lean_object* v_00_u03b4_2174_, lean_object* v_m_2175_, lean_object* v_inst_2176_, lean_object* v_f_2177_, lean_object* v_init_2178_, lean_object* v_t_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Std_DTreeMap_Raw_foldlM(v_00_u03b1_2171_, v_00_u03b2_2172_, v_cmp_2173_, v_00_u03b4_2174_, v_m_2175_, v_inst_2176_, v_f_2177_, v_init_2178_, v_t_2179_);
lean_dec_ref(v_cmp_2173_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl___redArg(lean_object* v_f_2181_, lean_object* v_init_2182_, lean_object* v_t_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2181_, v_init_2182_, v_t_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl(lean_object* v_00_u03b1_2185_, lean_object* v_00_u03b2_2186_, lean_object* v_cmp_2187_, lean_object* v_00_u03b4_2188_, lean_object* v_f_2189_, lean_object* v_init_2190_, lean_object* v_t_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2189_, v_init_2190_, v_t_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl___boxed(lean_object* v_00_u03b1_2193_, lean_object* v_00_u03b2_2194_, lean_object* v_cmp_2195_, lean_object* v_00_u03b4_2196_, lean_object* v_f_2197_, lean_object* v_init_2198_, lean_object* v_t_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Std_DTreeMap_Raw_foldl(v_00_u03b1_2193_, v_00_u03b2_2194_, v_cmp_2195_, v_00_u03b4_2196_, v_f_2197_, v_init_2198_, v_t_2199_);
lean_dec_ref(v_cmp_2195_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM___redArg(lean_object* v_inst_2201_, lean_object* v_f_2202_, lean_object* v_init_2203_, lean_object* v_t_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2201_, v_f_2202_, v_init_2203_, v_t_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM(lean_object* v_00_u03b1_2206_, lean_object* v_00_u03b2_2207_, lean_object* v_cmp_2208_, lean_object* v_00_u03b4_2209_, lean_object* v_m_2210_, lean_object* v_inst_2211_, lean_object* v_f_2212_, lean_object* v_init_2213_, lean_object* v_t_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2211_, v_f_2212_, v_init_2213_, v_t_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM___boxed(lean_object* v_00_u03b1_2216_, lean_object* v_00_u03b2_2217_, lean_object* v_cmp_2218_, lean_object* v_00_u03b4_2219_, lean_object* v_m_2220_, lean_object* v_inst_2221_, lean_object* v_f_2222_, lean_object* v_init_2223_, lean_object* v_t_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Std_DTreeMap_Raw_foldrM(v_00_u03b1_2216_, v_00_u03b2_2217_, v_cmp_2218_, v_00_u03b4_2219_, v_m_2220_, v_inst_2221_, v_f_2222_, v_init_2223_, v_t_2224_);
lean_dec_ref(v_cmp_2218_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___redArg___lam__0(lean_object* v_f_2226_, lean_object* v_x1_2227_, lean_object* v_x2_2228_, lean_object* v_x3_2229_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_apply_3(v_f_2226_, v_x1_2227_, v_x2_2228_, v_x3_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___redArg(lean_object* v_f_2250_, lean_object* v_init_2251_, lean_object* v_t_2252_){
_start:
{
lean_object* v___f_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___f_2253_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2253_, 0, v_f_2250_);
v___x_2254_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2255_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2254_, v___f_2253_, v_init_2251_, v_t_2252_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr(lean_object* v_00_u03b1_2256_, lean_object* v_00_u03b2_2257_, lean_object* v_cmp_2258_, lean_object* v_00_u03b4_2259_, lean_object* v_f_2260_, lean_object* v_init_2261_, lean_object* v_t_2262_){
_start:
{
lean_object* v___f_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___f_2263_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2263_, 0, v_f_2260_);
v___x_2264_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2265_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2264_, v___f_2263_, v_init_2261_, v_t_2262_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___boxed(lean_object* v_00_u03b1_2266_, lean_object* v_00_u03b2_2267_, lean_object* v_cmp_2268_, lean_object* v_00_u03b4_2269_, lean_object* v_f_2270_, lean_object* v_init_2271_, lean_object* v_t_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Std_DTreeMap_Raw_foldr(v_00_u03b1_2266_, v_00_u03b2_2267_, v_cmp_2268_, v_00_u03b4_2269_, v_f_2270_, v_init_2271_, v_t_2272_);
lean_dec_ref(v_cmp_2268_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition___redArg___lam__0(lean_object* v_f_2274_, lean_object* v_cmp_2275_, lean_object* v_x_2276_, lean_object* v_a_2277_, lean_object* v_b_2278_){
_start:
{
lean_object* v_fst_2279_; lean_object* v_snd_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2294_; 
v_fst_2279_ = lean_ctor_get(v_x_2276_, 0);
v_snd_2280_ = lean_ctor_get(v_x_2276_, 1);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_x_2276_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2282_ = v_x_2276_;
v_isShared_2283_ = v_isSharedCheck_2294_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_snd_2280_);
lean_inc(v_fst_2279_);
lean_dec(v_x_2276_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2294_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
lean_inc(v_b_2278_);
lean_inc(v_a_2277_);
v___x_2284_ = lean_apply_2(v_f_2274_, v_a_2277_, v_b_2278_);
v___x_2285_ = lean_unbox(v___x_2284_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2275_, v_a_2277_, v_b_2278_, v_snd_2280_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 1, v___x_2286_);
v___x_2288_ = v___x_2282_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_fst_2279_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2290_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2275_, v_a_2277_, v_b_2278_, v_fst_2279_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2290_);
v___x_2292_ = v___x_2282_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2290_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_snd_2280_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition___redArg(lean_object* v_cmp_2297_, lean_object* v_f_2298_, lean_object* v_t_2299_){
_start:
{
lean_object* v___f_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___f_2300_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2300_, 0, v_f_2298_);
lean_closure_set(v___f_2300_, 1, v_cmp_2297_);
v___x_2301_ = ((lean_object*)(l_Std_DTreeMap_Raw_partition___redArg___closed__0));
v___x_2302_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2300_, v___x_2301_, v_t_2299_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition(lean_object* v_00_u03b1_2303_, lean_object* v_00_u03b2_2304_, lean_object* v_cmp_2305_, lean_object* v_f_2306_, lean_object* v_t_2307_){
_start:
{
lean_object* v___f_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___f_2308_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2308_, 0, v_f_2306_);
lean_closure_set(v___f_2308_, 1, v_cmp_2305_);
v___x_2309_ = ((lean_object*)(l_Std_DTreeMap_Raw_partition___redArg___closed__0));
v___x_2310_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2308_, v___x_2309_, v_t_2307_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___redArg___lam__0(lean_object* v_f_2311_, lean_object* v_x_2312_, lean_object* v_k_2313_, lean_object* v_v_2314_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_apply_2(v_f_2311_, v_k_2313_, v_v_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___redArg(lean_object* v_inst_2316_, lean_object* v_f_2317_, lean_object* v_t_2318_){
_start:
{
lean_object* v___f_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___f_2319_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2319_, 0, v_f_2317_);
v___x_2320_ = lean_box(0);
v___x_2321_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2316_, v___f_2319_, v___x_2320_, v_t_2318_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM(lean_object* v_00_u03b1_2322_, lean_object* v_00_u03b2_2323_, lean_object* v_cmp_2324_, lean_object* v_m_2325_, lean_object* v_inst_2326_, lean_object* v_f_2327_, lean_object* v_t_2328_){
_start:
{
lean_object* v___f_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___f_2329_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2329_, 0, v_f_2327_);
v___x_2330_ = lean_box(0);
v___x_2331_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2326_, v___f_2329_, v___x_2330_, v_t_2328_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___boxed(lean_object* v_00_u03b1_2332_, lean_object* v_00_u03b2_2333_, lean_object* v_cmp_2334_, lean_object* v_m_2335_, lean_object* v_inst_2336_, lean_object* v_f_2337_, lean_object* v_t_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Std_DTreeMap_Raw_forM(v_00_u03b1_2332_, v_00_u03b2_2333_, v_cmp_2334_, v_m_2335_, v_inst_2336_, v_f_2337_, v_t_2338_);
lean_dec_ref(v_cmp_2334_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___redArg___lam__0(lean_object* v_toPure_2340_, lean_object* v_____do__lift_2341_){
_start:
{
lean_object* v_a_2342_; lean_object* v___x_2343_; 
v_a_2342_ = lean_ctor_get(v_____do__lift_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref(v_____do__lift_2341_);
v___x_2343_ = lean_apply_2(v_toPure_2340_, lean_box(0), v_a_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___redArg(lean_object* v_inst_2344_, lean_object* v_f_2345_, lean_object* v_init_2346_, lean_object* v_t_2347_){
_start:
{
lean_object* v_toApplicative_2348_; lean_object* v_toBind_2349_; lean_object* v_toPure_2350_; lean_object* v___x_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; 
v_toApplicative_2348_ = lean_ctor_get(v_inst_2344_, 0);
v_toBind_2349_ = lean_ctor_get(v_inst_2344_, 1);
lean_inc(v_toBind_2349_);
v_toPure_2350_ = lean_ctor_get(v_toApplicative_2348_, 1);
lean_inc(v_toPure_2350_);
v___x_2351_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2344_, v_f_2345_, v_init_2346_, v_t_2347_);
v___f_2352_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2352_, 0, v_toPure_2350_);
v___x_2353_ = lean_apply_4(v_toBind_2349_, lean_box(0), lean_box(0), v___x_2351_, v___f_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn(lean_object* v_00_u03b1_2354_, lean_object* v_00_u03b2_2355_, lean_object* v_cmp_2356_, lean_object* v_00_u03b4_2357_, lean_object* v_m_2358_, lean_object* v_inst_2359_, lean_object* v_f_2360_, lean_object* v_init_2361_, lean_object* v_t_2362_){
_start:
{
lean_object* v_toApplicative_2363_; lean_object* v_toBind_2364_; lean_object* v_toPure_2365_; lean_object* v___x_2366_; lean_object* v___f_2367_; lean_object* v___x_2368_; 
v_toApplicative_2363_ = lean_ctor_get(v_inst_2359_, 0);
v_toBind_2364_ = lean_ctor_get(v_inst_2359_, 1);
lean_inc(v_toBind_2364_);
v_toPure_2365_ = lean_ctor_get(v_toApplicative_2363_, 1);
lean_inc(v_toPure_2365_);
v___x_2366_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2359_, v_f_2360_, v_init_2361_, v_t_2362_);
v___f_2367_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2367_, 0, v_toPure_2365_);
v___x_2368_ = lean_apply_4(v_toBind_2364_, lean_box(0), lean_box(0), v___x_2366_, v___f_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___boxed(lean_object* v_00_u03b1_2369_, lean_object* v_00_u03b2_2370_, lean_object* v_cmp_2371_, lean_object* v_00_u03b4_2372_, lean_object* v_m_2373_, lean_object* v_inst_2374_, lean_object* v_f_2375_, lean_object* v_init_2376_, lean_object* v_t_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Std_DTreeMap_Raw_forIn(v_00_u03b1_2369_, v_00_u03b2_2370_, v_cmp_2371_, v_00_u03b4_2372_, v_m_2373_, v_inst_2374_, v_f_2375_, v_init_2376_, v_t_2377_);
lean_dec_ref(v_cmp_2371_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_2379_, lean_object* v_x_2380_, lean_object* v_k_2381_, lean_object* v_v_2382_){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v_k_2381_);
lean_ctor_set(v___x_2383_, 1, v_v_2382_);
v___x_2384_ = lean_apply_1(v_f_2379_, v___x_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1(lean_object* v_inst_2385_, lean_object* v_t_2386_, lean_object* v_f_2387_){
_start:
{
lean_object* v___f_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___f_2388_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2388_, 0, v_f_2387_);
v___x_2389_ = lean_box(0);
v___x_2390_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2385_, v___f_2388_, v___x_2389_, v_t_2386_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg(lean_object* v_inst_2391_){
_start:
{
lean_object* v___f_2392_; 
v___f_2392_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2392_, 0, v_inst_2391_);
return v___f_2392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad(lean_object* v_00_u03b1_2393_, lean_object* v_00_u03b2_2394_, lean_object* v_cmp_2395_, lean_object* v_m_2396_, lean_object* v_inst_2397_){
_start:
{
lean_object* v___f_2398_; 
v___f_2398_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2398_, 0, v_inst_2397_);
return v___f_2398_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___boxed(lean_object* v_00_u03b1_2399_, lean_object* v_00_u03b2_2400_, lean_object* v_cmp_2401_, lean_object* v_m_2402_, lean_object* v_inst_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Std_DTreeMap_Raw_instForMSigmaOfMonad(v_00_u03b1_2399_, v_00_u03b2_2400_, v_cmp_2401_, v_m_2402_, v_inst_2403_);
lean_dec_ref(v_cmp_2401_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_2405_, lean_object* v_a_2406_, lean_object* v_b_2407_, lean_object* v_acc_2408_){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_a_2406_);
lean_ctor_set(v___x_2409_, 1, v_b_2407_);
v___x_2410_ = lean_apply_2(v_f_2405_, v___x_2409_, v_acc_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_2411_, lean_object* v_00_u03b2_2412_, lean_object* v_t_2413_, lean_object* v_init_2414_, lean_object* v_f_2415_){
_start:
{
lean_object* v_toApplicative_2416_; lean_object* v_toBind_2417_; lean_object* v_toPure_2418_; lean_object* v___f_2419_; lean_object* v___x_2420_; lean_object* v___f_2421_; lean_object* v___x_2422_; 
v_toApplicative_2416_ = lean_ctor_get(v_inst_2411_, 0);
v_toBind_2417_ = lean_ctor_get(v_inst_2411_, 1);
lean_inc(v_toBind_2417_);
v_toPure_2418_ = lean_ctor_get(v_toApplicative_2416_, 1);
lean_inc(v_toPure_2418_);
v___f_2419_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2419_, 0, v_f_2415_);
v___x_2420_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2411_, v___f_2419_, v_init_2414_, v_t_2413_);
v___f_2421_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2421_, 0, v_toPure_2418_);
v___x_2422_ = lean_apply_4(v_toBind_2417_, lean_box(0), lean_box(0), v___x_2420_, v___f_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg(lean_object* v_inst_2423_){
_start:
{
lean_object* v___f_2424_; 
v___f_2424_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2424_, 0, v_inst_2423_);
return v___f_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad(lean_object* v_00_u03b1_2425_, lean_object* v_00_u03b2_2426_, lean_object* v_cmp_2427_, lean_object* v_m_2428_, lean_object* v_inst_2429_){
_start:
{
lean_object* v___f_2430_; 
v___f_2430_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2430_, 0, v_inst_2429_);
return v___f_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___boxed(lean_object* v_00_u03b1_2431_, lean_object* v_00_u03b2_2432_, lean_object* v_cmp_2433_, lean_object* v_m_2434_, lean_object* v_inst_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Std_DTreeMap_Raw_instForInSigmaOfMonad(v_00_u03b1_2431_, v_00_u03b2_2432_, v_cmp_2433_, v_m_2434_, v_inst_2435_);
lean_dec_ref(v_cmp_2433_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2437_, lean_object* v_x_2438_, lean_object* v_k_2439_, lean_object* v_v_2440_){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v_k_2439_);
lean_ctor_set(v___x_2441_, 1, v_v_2440_);
v___x_2442_ = lean_apply_1(v_f_2437_, v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___redArg(lean_object* v_inst_2443_, lean_object* v_f_2444_, lean_object* v_t_2445_){
_start:
{
lean_object* v___f_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___f_2446_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2446_, 0, v_f_2444_);
v___x_2447_ = lean_box(0);
v___x_2448_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2443_, v___f_2446_, v___x_2447_, v_t_2445_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried(lean_object* v_00_u03b1_2449_, lean_object* v_cmp_2450_, lean_object* v_m_2451_, lean_object* v_inst_2452_, lean_object* v_00_u03b2_2453_, lean_object* v_f_2454_, lean_object* v_t_2455_){
_start:
{
lean_object* v___f_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___f_2456_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2456_, 0, v_f_2454_);
v___x_2457_ = lean_box(0);
v___x_2458_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2452_, v___f_2456_, v___x_2457_, v_t_2455_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2459_, lean_object* v_cmp_2460_, lean_object* v_m_2461_, lean_object* v_inst_2462_, lean_object* v_00_u03b2_2463_, lean_object* v_f_2464_, lean_object* v_t_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Std_DTreeMap_Raw_Const_forMUncurried(v_00_u03b1_2459_, v_cmp_2460_, v_m_2461_, v_inst_2462_, v_00_u03b2_2463_, v_f_2464_, v_t_2465_);
lean_dec_ref(v_cmp_2460_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2467_, lean_object* v_a_2468_, lean_object* v_b_2469_, lean_object* v_d_2470_){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_a_2468_);
lean_ctor_set(v___x_2471_, 1, v_b_2469_);
v___x_2472_ = lean_apply_2(v_f_2467_, v___x_2471_, v_d_2470_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___redArg(lean_object* v_inst_2473_, lean_object* v_f_2474_, lean_object* v_init_2475_, lean_object* v_t_2476_){
_start:
{
lean_object* v_toApplicative_2477_; lean_object* v_toBind_2478_; lean_object* v_toPure_2479_; lean_object* v___f_2480_; lean_object* v___x_2481_; lean_object* v___f_2482_; lean_object* v___x_2483_; 
v_toApplicative_2477_ = lean_ctor_get(v_inst_2473_, 0);
v_toBind_2478_ = lean_ctor_get(v_inst_2473_, 1);
lean_inc(v_toBind_2478_);
v_toPure_2479_ = lean_ctor_get(v_toApplicative_2477_, 1);
lean_inc(v_toPure_2479_);
v___f_2480_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2480_, 0, v_f_2474_);
v___x_2481_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2473_, v___f_2480_, v_init_2475_, v_t_2476_);
v___f_2482_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2482_, 0, v_toPure_2479_);
v___x_2483_ = lean_apply_4(v_toBind_2478_, lean_box(0), lean_box(0), v___x_2481_, v___f_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried(lean_object* v_00_u03b1_2484_, lean_object* v_cmp_2485_, lean_object* v_00_u03b4_2486_, lean_object* v_m_2487_, lean_object* v_inst_2488_, lean_object* v_00_u03b2_2489_, lean_object* v_f_2490_, lean_object* v_init_2491_, lean_object* v_t_2492_){
_start:
{
lean_object* v_toApplicative_2493_; lean_object* v_toBind_2494_; lean_object* v_toPure_2495_; lean_object* v___f_2496_; lean_object* v___x_2497_; lean_object* v___f_2498_; lean_object* v___x_2499_; 
v_toApplicative_2493_ = lean_ctor_get(v_inst_2488_, 0);
v_toBind_2494_ = lean_ctor_get(v_inst_2488_, 1);
lean_inc(v_toBind_2494_);
v_toPure_2495_ = lean_ctor_get(v_toApplicative_2493_, 1);
lean_inc(v_toPure_2495_);
v___f_2496_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2496_, 0, v_f_2490_);
v___x_2497_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2488_, v___f_2496_, v_init_2491_, v_t_2492_);
v___f_2498_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2498_, 0, v_toPure_2495_);
v___x_2499_ = lean_apply_4(v_toBind_2494_, lean_box(0), lean_box(0), v___x_2497_, v___f_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2500_, lean_object* v_cmp_2501_, lean_object* v_00_u03b4_2502_, lean_object* v_m_2503_, lean_object* v_inst_2504_, lean_object* v_00_u03b2_2505_, lean_object* v_f_2506_, lean_object* v_init_2507_, lean_object* v_t_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Std_DTreeMap_Raw_Const_forInUncurried(v_00_u03b1_2500_, v_cmp_2501_, v_00_u03b4_2502_, v_m_2503_, v_inst_2504_, v_00_u03b2_2505_, v_f_2506_, v_init_2507_, v_t_2508_);
lean_dec_ref(v_cmp_2501_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___lam__0(lean_object* v_p_2510_, lean_object* v___x_2511_, lean_object* v___x_2512_, lean_object* v_a_2513_, lean_object* v_b_2514_, lean_object* v_acc_2515_){
_start:
{
lean_object* v___x_2516_; uint8_t v___x_2517_; 
v___x_2516_ = lean_apply_2(v_p_2510_, v_a_2513_, v_b_2514_);
v___x_2517_ = lean_unbox(v___x_2516_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2511_);
return v___x_2518_;
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec_ref(v___x_2511_);
v___x_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2516_);
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
lean_ctor_set(v___x_2520_, 1, v___x_2512_);
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_2522_, lean_object* v___x_2523_, lean_object* v___x_2524_, lean_object* v_a_2525_, lean_object* v_b_2526_, lean_object* v_acc_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Std_DTreeMap_Raw_any___redArg___lam__0(v_p_2522_, v___x_2523_, v___x_2524_, v_a_2525_, v_b_2526_, v_acc_2527_);
lean_dec_ref(v_acc_2527_);
return v_res_2528_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_any___redArg(lean_object* v_t_2532_, lean_object* v_p_2533_){
_start:
{
lean_object* v___y_2535_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; lean_object* v_a_2545_; 
v___x_2540_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2541_ = lean_box(0);
v___x_2542_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2543_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2543_, 0, v_p_2533_);
lean_closure_set(v___f_2543_, 1, v___x_2542_);
lean_closure_set(v___f_2543_, 2, v___x_2541_);
v___x_2544_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2540_, v___f_2543_, v___x_2542_, v_t_2532_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___y_2535_ = v_a_2545_;
goto v___jp_2534_;
v___jp_2534_:
{
lean_object* v_fst_2536_; 
v_fst_2536_ = lean_ctor_get(v___y_2535_, 0);
lean_inc(v_fst_2536_);
lean_dec_ref(v___y_2535_);
if (lean_obj_tag(v_fst_2536_) == 0)
{
uint8_t v___x_2537_; 
v___x_2537_ = 0;
return v___x_2537_;
}
else
{
lean_object* v_val_2538_; uint8_t v___x_2539_; 
v_val_2538_ = lean_ctor_get(v_fst_2536_, 0);
lean_inc(v_val_2538_);
lean_dec_ref_known(v_fst_2536_, 1);
v___x_2539_ = lean_unbox(v_val_2538_);
lean_dec(v_val_2538_);
return v___x_2539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___boxed(lean_object* v_t_2546_, lean_object* v_p_2547_){
_start:
{
uint8_t v_res_2548_; lean_object* v_r_2549_; 
v_res_2548_ = l_Std_DTreeMap_Raw_any___redArg(v_t_2546_, v_p_2547_);
v_r_2549_ = lean_box(v_res_2548_);
return v_r_2549_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_any(lean_object* v_00_u03b1_2550_, lean_object* v_00_u03b2_2551_, lean_object* v_cmp_2552_, lean_object* v_t_2553_, lean_object* v_p_2554_){
_start:
{
lean_object* v___y_2556_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___f_2564_; lean_object* v___x_2565_; lean_object* v_a_2566_; 
v___x_2561_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2562_ = lean_box(0);
v___x_2563_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2564_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2564_, 0, v_p_2554_);
lean_closure_set(v___f_2564_, 1, v___x_2563_);
lean_closure_set(v___f_2564_, 2, v___x_2562_);
v___x_2565_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2561_, v___f_2564_, v___x_2563_, v_t_2553_);
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___y_2556_ = v_a_2566_;
goto v___jp_2555_;
v___jp_2555_:
{
lean_object* v_fst_2557_; 
v_fst_2557_ = lean_ctor_get(v___y_2556_, 0);
lean_inc(v_fst_2557_);
lean_dec_ref(v___y_2556_);
if (lean_obj_tag(v_fst_2557_) == 0)
{
uint8_t v___x_2558_; 
v___x_2558_ = 0;
return v___x_2558_;
}
else
{
lean_object* v_val_2559_; uint8_t v___x_2560_; 
v_val_2559_ = lean_ctor_get(v_fst_2557_, 0);
lean_inc(v_val_2559_);
lean_dec_ref_known(v_fst_2557_, 1);
v___x_2560_ = lean_unbox(v_val_2559_);
lean_dec(v_val_2559_);
return v___x_2560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___boxed(lean_object* v_00_u03b1_2567_, lean_object* v_00_u03b2_2568_, lean_object* v_cmp_2569_, lean_object* v_t_2570_, lean_object* v_p_2571_){
_start:
{
uint8_t v_res_2572_; lean_object* v_r_2573_; 
v_res_2572_ = l_Std_DTreeMap_Raw_any(v_00_u03b1_2567_, v_00_u03b2_2568_, v_cmp_2569_, v_t_2570_, v_p_2571_);
lean_dec_ref(v_cmp_2569_);
v_r_2573_ = lean_box(v_res_2572_);
return v_r_2573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___lam__0(lean_object* v_p_2574_, lean_object* v___x_2575_, lean_object* v___x_2576_, lean_object* v_a_2577_, lean_object* v_b_2578_, lean_object* v_acc_2579_){
_start:
{
lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2580_ = lean_apply_2(v_p_2574_, v_a_2577_, v_b_2578_);
v___x_2581_ = lean_unbox(v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_dec_ref(v___x_2576_);
v___x_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
lean_ctor_set(v___x_2583_, 1, v___x_2575_);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
return v___x_2584_;
}
else
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2576_);
return v___x_2585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_2586_, lean_object* v___x_2587_, lean_object* v___x_2588_, lean_object* v_a_2589_, lean_object* v_b_2590_, lean_object* v_acc_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Std_DTreeMap_Raw_all___redArg___lam__0(v_p_2586_, v___x_2587_, v___x_2588_, v_a_2589_, v_b_2590_, v_acc_2591_);
lean_dec_ref(v_acc_2591_);
return v_res_2592_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_all___redArg(lean_object* v_t_2593_, lean_object* v_p_2594_){
_start:
{
lean_object* v___y_2596_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v_a_2606_; 
v___x_2601_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2602_ = lean_box(0);
v___x_2603_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2604_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2604_, 0, v_p_2594_);
lean_closure_set(v___f_2604_, 1, v___x_2602_);
lean_closure_set(v___f_2604_, 2, v___x_2603_);
v___x_2605_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2601_, v___f_2604_, v___x_2603_, v_t_2593_);
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___y_2596_ = v_a_2606_;
goto v___jp_2595_;
v___jp_2595_:
{
lean_object* v_fst_2597_; 
v_fst_2597_ = lean_ctor_get(v___y_2596_, 0);
lean_inc(v_fst_2597_);
lean_dec_ref(v___y_2596_);
if (lean_obj_tag(v_fst_2597_) == 0)
{
uint8_t v___x_2598_; 
v___x_2598_ = 1;
return v___x_2598_;
}
else
{
lean_object* v_val_2599_; uint8_t v___x_2600_; 
v_val_2599_ = lean_ctor_get(v_fst_2597_, 0);
lean_inc(v_val_2599_);
lean_dec_ref_known(v_fst_2597_, 1);
v___x_2600_ = lean_unbox(v_val_2599_);
lean_dec(v_val_2599_);
return v___x_2600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___boxed(lean_object* v_t_2607_, lean_object* v_p_2608_){
_start:
{
uint8_t v_res_2609_; lean_object* v_r_2610_; 
v_res_2609_ = l_Std_DTreeMap_Raw_all___redArg(v_t_2607_, v_p_2608_);
v_r_2610_ = lean_box(v_res_2609_);
return v_r_2610_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_all(lean_object* v_00_u03b1_2611_, lean_object* v_00_u03b2_2612_, lean_object* v_cmp_2613_, lean_object* v_t_2614_, lean_object* v_p_2615_){
_start:
{
lean_object* v___y_2617_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___f_2625_; lean_object* v___x_2626_; lean_object* v_a_2627_; 
v___x_2622_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2623_ = lean_box(0);
v___x_2624_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2625_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2625_, 0, v_p_2615_);
lean_closure_set(v___f_2625_, 1, v___x_2623_);
lean_closure_set(v___f_2625_, 2, v___x_2624_);
v___x_2626_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2622_, v___f_2625_, v___x_2624_, v_t_2614_);
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___y_2617_ = v_a_2627_;
goto v___jp_2616_;
v___jp_2616_:
{
lean_object* v_fst_2618_; 
v_fst_2618_ = lean_ctor_get(v___y_2617_, 0);
lean_inc(v_fst_2618_);
lean_dec_ref(v___y_2617_);
if (lean_obj_tag(v_fst_2618_) == 0)
{
uint8_t v___x_2619_; 
v___x_2619_ = 1;
return v___x_2619_;
}
else
{
lean_object* v_val_2620_; uint8_t v___x_2621_; 
v_val_2620_ = lean_ctor_get(v_fst_2618_, 0);
lean_inc(v_val_2620_);
lean_dec_ref_known(v_fst_2618_, 1);
v___x_2621_ = lean_unbox(v_val_2620_);
lean_dec(v_val_2620_);
return v___x_2621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___boxed(lean_object* v_00_u03b1_2628_, lean_object* v_00_u03b2_2629_, lean_object* v_cmp_2630_, lean_object* v_t_2631_, lean_object* v_p_2632_){
_start:
{
uint8_t v_res_2633_; lean_object* v_r_2634_; 
v_res_2633_ = l_Std_DTreeMap_Raw_all(v_00_u03b1_2628_, v_00_u03b2_2629_, v_cmp_2630_, v_t_2631_, v_p_2632_);
lean_dec_ref(v_cmp_2630_);
v_r_2634_ = lean_box(v_res_2633_);
return v_r_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg___lam__0(lean_object* v_x1_2635_, lean_object* v_x2_2636_, lean_object* v_x3_2637_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2638_, 0, v_x1_2635_);
lean_ctor_set(v___x_2638_, 1, v_x3_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_x1_2639_, lean_object* v_x2_2640_, lean_object* v_x3_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Std_DTreeMap_Raw_keys___redArg___lam__0(v_x1_2639_, v_x2_2640_, v_x3_2641_);
lean_dec(v_x2_2640_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg(lean_object* v_t_2644_){
_start:
{
lean_object* v___f_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___f_2645_ = ((lean_object*)(l_Std_DTreeMap_Raw_keys___redArg___closed__0));
v___x_2646_ = lean_box(0);
v___x_2647_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2648_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2647_, v___f_2645_, v___x_2646_, v_t_2644_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys(lean_object* v_00_u03b1_2649_, lean_object* v_00_u03b2_2650_, lean_object* v_cmp_2651_, lean_object* v_t_2652_){
_start:
{
lean_object* v___f_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___f_2653_ = ((lean_object*)(l_Std_DTreeMap_Raw_keys___redArg___closed__0));
v___x_2654_ = lean_box(0);
v___x_2655_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2656_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2655_, v___f_2653_, v___x_2654_, v_t_2652_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___boxed(lean_object* v_00_u03b1_2657_, lean_object* v_00_u03b2_2658_, lean_object* v_cmp_2659_, lean_object* v_t_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Std_DTreeMap_Raw_keys(v_00_u03b1_2657_, v_00_u03b2_2658_, v_cmp_2659_, v_t_2660_);
lean_dec_ref(v_cmp_2659_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___lam__0(lean_object* v_l_2662_, lean_object* v_k_2663_, lean_object* v_x_2664_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_array_push(v_l_2662_, v_k_2663_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_l_2666_, lean_object* v_k_2667_, lean_object* v_x_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Std_DTreeMap_Raw_keysArray___redArg___lam__0(v_l_2666_, v_k_2667_, v_x_2668_);
lean_dec(v_x_2668_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg(lean_object* v_t_2671_){
_start:
{
lean_object* v___f_2672_; lean_object* v___y_2674_; 
v___f_2672_ = ((lean_object*)(l_Std_DTreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2671_) == 0)
{
lean_object* v_size_2677_; 
v_size_2677_ = lean_ctor_get(v_t_2671_, 0);
lean_inc(v_size_2677_);
v___y_2674_ = v_size_2677_;
goto v___jp_2673_;
}
else
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_unsigned_to_nat(0u);
v___y_2674_ = v___x_2678_;
goto v___jp_2673_;
}
v___jp_2673_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = lean_mk_empty_array_with_capacity(v___y_2674_);
lean_dec(v___y_2674_);
v___x_2676_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2672_, v___x_2675_, v_t_2671_);
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray(lean_object* v_00_u03b1_2679_, lean_object* v_00_u03b2_2680_, lean_object* v_cmp_2681_, lean_object* v_t_2682_){
_start:
{
lean_object* v___f_2683_; lean_object* v___y_2685_; 
v___f_2683_ = ((lean_object*)(l_Std_DTreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2682_) == 0)
{
lean_object* v_size_2688_; 
v_size_2688_ = lean_ctor_get(v_t_2682_, 0);
lean_inc(v_size_2688_);
v___y_2685_ = v_size_2688_;
goto v___jp_2684_;
}
else
{
lean_object* v___x_2689_; 
v___x_2689_ = lean_unsigned_to_nat(0u);
v___y_2685_ = v___x_2689_;
goto v___jp_2684_;
}
v___jp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = lean_mk_empty_array_with_capacity(v___y_2685_);
lean_dec(v___y_2685_);
v___x_2687_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2683_, v___x_2686_, v_t_2682_);
return v___x_2687_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___boxed(lean_object* v_00_u03b1_2690_, lean_object* v_00_u03b2_2691_, lean_object* v_cmp_2692_, lean_object* v_t_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Std_DTreeMap_Raw_keysArray(v_00_u03b1_2690_, v_00_u03b2_2691_, v_cmp_2692_, v_t_2693_);
lean_dec_ref(v_cmp_2692_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg___lam__0(lean_object* v_x1_2695_, lean_object* v_x2_2696_, lean_object* v_x3_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2698_, 0, v_x2_2696_);
lean_ctor_set(v___x_2698_, 1, v_x3_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg___lam__0___boxed(lean_object* v_x1_2699_, lean_object* v_x2_2700_, lean_object* v_x3_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Std_DTreeMap_Raw_values___redArg___lam__0(v_x1_2699_, v_x2_2700_, v_x3_2701_);
lean_dec(v_x1_2699_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg(lean_object* v_t_2704_){
_start:
{
lean_object* v___f_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___f_2705_ = ((lean_object*)(l_Std_DTreeMap_Raw_values___redArg___closed__0));
v___x_2706_ = lean_box(0);
v___x_2707_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2708_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2707_, v___f_2705_, v___x_2706_, v_t_2704_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values(lean_object* v_00_u03b1_2709_, lean_object* v_cmp_2710_, lean_object* v_00_u03b2_2711_, lean_object* v_t_2712_){
_start:
{
lean_object* v___f_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___f_2713_ = ((lean_object*)(l_Std_DTreeMap_Raw_values___redArg___closed__0));
v___x_2714_ = lean_box(0);
v___x_2715_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2716_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2715_, v___f_2713_, v___x_2714_, v_t_2712_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___boxed(lean_object* v_00_u03b1_2717_, lean_object* v_cmp_2718_, lean_object* v_00_u03b2_2719_, lean_object* v_t_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Std_DTreeMap_Raw_values(v_00_u03b1_2717_, v_cmp_2718_, v_00_u03b2_2719_, v_t_2720_);
lean_dec_ref(v_cmp_2718_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0(lean_object* v_l_2722_, lean_object* v_x_2723_, lean_object* v_v_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = lean_array_push(v_l_2722_, v_v_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2726_, lean_object* v_x_2727_, lean_object* v_v_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0(v_l_2726_, v_x_2727_, v_v_2728_);
lean_dec(v_x_2727_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg(lean_object* v_t_2731_){
_start:
{
lean_object* v___f_2732_; lean_object* v___y_2734_; 
v___f_2732_ = ((lean_object*)(l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0));
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray(lean_object* v_00_u03b1_2739_, lean_object* v_cmp_2740_, lean_object* v_00_u03b2_2741_, lean_object* v_t_2742_){
_start:
{
lean_object* v___f_2743_; lean_object* v___y_2745_; 
v___f_2743_ = ((lean_object*)(l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0));
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___boxed(lean_object* v_00_u03b1_2750_, lean_object* v_cmp_2751_, lean_object* v_00_u03b2_2752_, lean_object* v_t_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Std_DTreeMap_Raw_valuesArray(v_00_u03b1_2750_, v_cmp_2751_, v_00_u03b2_2752_, v_t_2753_);
lean_dec_ref(v_cmp_2751_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___redArg___lam__0(lean_object* v_x1_2755_, lean_object* v_x2_2756_, lean_object* v_x3_2757_){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v_x1_2755_);
lean_ctor_set(v___x_2758_, 1, v_x2_2756_);
v___x_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v_x3_2757_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___redArg(lean_object* v_t_2761_){
_start:
{
lean_object* v___f_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___f_2762_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_2763_ = lean_box(0);
v___x_2764_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2765_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2764_, v___f_2762_, v___x_2763_, v_t_2761_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList(lean_object* v_00_u03b1_2766_, lean_object* v_00_u03b2_2767_, lean_object* v_cmp_2768_, lean_object* v_t_2769_){
_start:
{
lean_object* v___f_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___f_2770_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_2771_ = lean_box(0);
v___x_2772_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2773_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2772_, v___f_2770_, v___x_2771_, v_t_2769_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___boxed(lean_object* v_00_u03b1_2774_, lean_object* v_00_u03b2_2775_, lean_object* v_cmp_2776_, lean_object* v_t_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Std_DTreeMap_Raw_toList(v_00_u03b1_2774_, v_00_u03b2_2775_, v_cmp_2776_, v_t_2777_);
lean_dec_ref(v_cmp_2776_);
return v_res_2778_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg___lam__0(lean_object* v_cmp_2780_, lean_object* v_a_2781_, lean_object* v_x_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_fst_2784_; lean_object* v_snd_2785_; lean_object* v_r_2786_; lean_object* v___x_2787_; 
v_fst_2784_ = lean_ctor_get(v_a_2781_, 0);
lean_inc(v_fst_2784_);
v_snd_2785_ = lean_ctor_get(v_a_2781_, 1);
lean_inc(v_snd_2785_);
lean_dec_ref(v_a_2781_);
v_r_2786_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2780_, v_fst_2784_, v_snd_2785_, v___y_2783_);
v___x_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_r_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg(lean_object* v_l_2788_, lean_object* v_cmp_2789_){
_start:
{
lean_object* v___f_2790_; lean_object* v___x_2791_; lean_object* v_r_2792_; lean_object* v___x_2793_; 
v___f_2790_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2790_, 0, v_cmp_2789_);
v___x_2791_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2792_ = lean_box(1);
v___x_2793_ = l_List_forIn_x27_loop___redArg(v___x_2791_, v___f_2790_, v_l_2788_, v_r_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg___boxed(lean_object* v_l_2794_, lean_object* v_cmp_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Std_DTreeMap_Raw_ofList___redArg(v_l_2794_, v_cmp_2795_);
lean_dec(v_l_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList(lean_object* v_00_u03b1_2797_, lean_object* v_00_u03b2_2798_, lean_object* v_l_2799_, lean_object* v_cmp_2800_){
_start:
{
lean_object* v___f_2801_; lean_object* v___x_2802_; lean_object* v_r_2803_; lean_object* v___x_2804_; 
v___f_2801_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2801_, 0, v_cmp_2800_);
v___x_2802_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2803_ = lean_box(1);
v___x_2804_ = l_List_forIn_x27_loop___redArg(v___x_2802_, v___f_2801_, v_l_2799_, v_r_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___boxed(lean_object* v_00_u03b1_2805_, lean_object* v_00_u03b2_2806_, lean_object* v_l_2807_, lean_object* v_cmp_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Std_DTreeMap_Raw_ofList(v_00_u03b1_2805_, v_00_u03b2_2806_, v_l_2807_, v_cmp_2808_);
lean_dec(v_l_2807_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg___lam__0(lean_object* v_l_2810_, lean_object* v_k_2811_, lean_object* v_v_2812_){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2813_, 0, v_k_2811_);
lean_ctor_set(v___x_2813_, 1, v_v_2812_);
v___x_2814_ = lean_array_push(v_l_2810_, v___x_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg(lean_object* v_t_2816_){
_start:
{
lean_object* v___f_2817_; lean_object* v___y_2819_; 
v___f_2817_ = ((lean_object*)(l_Std_DTreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2816_) == 0)
{
lean_object* v_size_2822_; 
v_size_2822_ = lean_ctor_get(v_t_2816_, 0);
lean_inc(v_size_2822_);
v___y_2819_ = v_size_2822_;
goto v___jp_2818_;
}
else
{
lean_object* v___x_2823_; 
v___x_2823_ = lean_unsigned_to_nat(0u);
v___y_2819_ = v___x_2823_;
goto v___jp_2818_;
}
v___jp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = lean_mk_empty_array_with_capacity(v___y_2819_);
lean_dec(v___y_2819_);
v___x_2821_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2817_, v___x_2820_, v_t_2816_);
return v___x_2821_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray(lean_object* v_00_u03b1_2824_, lean_object* v_00_u03b2_2825_, lean_object* v_cmp_2826_, lean_object* v_t_2827_){
_start:
{
lean_object* v___f_2828_; lean_object* v___y_2830_; 
v___f_2828_ = ((lean_object*)(l_Std_DTreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2827_) == 0)
{
lean_object* v_size_2833_; 
v_size_2833_ = lean_ctor_get(v_t_2827_, 0);
lean_inc(v_size_2833_);
v___y_2830_ = v_size_2833_;
goto v___jp_2829_;
}
else
{
lean_object* v___x_2834_; 
v___x_2834_ = lean_unsigned_to_nat(0u);
v___y_2830_ = v___x_2834_;
goto v___jp_2829_;
}
v___jp_2829_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = lean_mk_empty_array_with_capacity(v___y_2830_);
lean_dec(v___y_2830_);
v___x_2832_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2828_, v___x_2831_, v_t_2827_);
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___boxed(lean_object* v_00_u03b1_2835_, lean_object* v_00_u03b2_2836_, lean_object* v_cmp_2837_, lean_object* v_t_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Std_DTreeMap_Raw_toArray(v_00_u03b1_2835_, v_00_u03b2_2836_, v_cmp_2837_, v_t_2838_);
lean_dec_ref(v_cmp_2837_);
return v_res_2839_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray___redArg(lean_object* v_a_2841_, lean_object* v_cmp_2842_){
_start:
{
lean_object* v___f_2843_; lean_object* v___x_2844_; lean_object* v_r_2845_; size_t v_sz_2846_; size_t v___x_2847_; lean_object* v___x_2848_; 
v___f_2843_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2843_, 0, v_cmp_2842_);
v___x_2844_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2845_ = lean_box(1);
v_sz_2846_ = lean_array_size(v_a_2841_);
v___x_2847_ = ((size_t)0ULL);
v___x_2848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2844_, v_a_2841_, v___f_2843_, v_sz_2846_, v___x_2847_, v_r_2845_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray(lean_object* v_00_u03b1_2849_, lean_object* v_00_u03b2_2850_, lean_object* v_a_2851_, lean_object* v_cmp_2852_){
_start:
{
lean_object* v___f_2853_; lean_object* v___x_2854_; lean_object* v_r_2855_; size_t v_sz_2856_; size_t v___x_2857_; lean_object* v___x_2858_; 
v___f_2853_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2853_, 0, v_cmp_2852_);
v___x_2854_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2855_ = lean_box(1);
v_sz_2856_ = lean_array_size(v_a_2851_);
v___x_2857_ = ((size_t)0ULL);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2854_, v_a_2851_, v___f_2853_, v_sz_2856_, v___x_2857_, v_r_2855_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify___redArg(lean_object* v_cmp_2859_, lean_object* v_t_2860_, lean_object* v_a_2861_, lean_object* v_f_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2859_, v_a_2861_, v_f_2862_, v_t_2860_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify(lean_object* v_00_u03b1_2864_, lean_object* v_00_u03b2_2865_, lean_object* v_cmp_2866_, lean_object* v_inst_2867_, lean_object* v_t_2868_, lean_object* v_a_2869_, lean_object* v_f_2870_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2866_, v_a_2869_, v_f_2870_, v_t_2868_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter___redArg(lean_object* v_cmp_2872_, lean_object* v_t_2873_, lean_object* v_a_2874_, lean_object* v_f_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2872_, v_a_2874_, v_f_2875_, v_t_2873_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter(lean_object* v_00_u03b1_2877_, lean_object* v_00_u03b2_2878_, lean_object* v_cmp_2879_, lean_object* v_inst_2880_, lean_object* v_t_2881_, lean_object* v_a_2882_, lean_object* v_f_2883_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2879_, v_a_2882_, v_f_2883_, v_t_2881_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2885_, lean_object* v_mergeFn_2886_, lean_object* v_a_2887_, lean_object* v_x_2888_){
_start:
{
if (lean_obj_tag(v_x_2888_) == 0)
{
lean_object* v___x_2889_; 
lean_dec(v_a_2887_);
lean_dec(v_mergeFn_2886_);
v___x_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2889_, 0, v_b_u2082_2885_);
return v___x_2889_;
}
else
{
lean_object* v_val_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2898_; 
v_val_2890_ = lean_ctor_get(v_x_2888_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_x_2888_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2892_ = v_x_2888_;
v_isShared_2893_ = v_isSharedCheck_2898_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_val_2890_);
lean_dec(v_x_2888_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2898_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2894_ = lean_apply_3(v_mergeFn_2886_, v_a_2887_, v_val_2890_, v_b_u2082_2885_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2894_);
v___x_2896_ = v___x_2892_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2899_, lean_object* v_cmp_2900_, lean_object* v_t_2901_, lean_object* v_a_2902_, lean_object* v_b_u2082_2903_){
_start:
{
lean_object* v___f_2904_; lean_object* v___x_2905_; 
lean_inc(v_a_2902_);
v___f_2904_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2904_, 0, v_b_u2082_2903_);
lean_closure_set(v___f_2904_, 1, v_mergeFn_2899_);
lean_closure_set(v___f_2904_, 2, v_a_2902_);
v___x_2905_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2900_, v_a_2902_, v___f_2904_, v_t_2901_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg(lean_object* v_cmp_2906_, lean_object* v_mergeFn_2907_, lean_object* v_t_u2081_2908_, lean_object* v_t_u2082_2909_){
_start:
{
lean_object* v___f_2910_; lean_object* v___x_2911_; 
v___f_2910_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2910_, 0, v_mergeFn_2907_);
lean_closure_set(v___f_2910_, 1, v_cmp_2906_);
v___x_2911_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2910_, v_t_u2081_2908_, v_t_u2082_2909_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith(lean_object* v_00_u03b1_2912_, lean_object* v_00_u03b2_2913_, lean_object* v_cmp_2914_, lean_object* v_inst_2915_, lean_object* v_mergeFn_2916_, lean_object* v_t_u2081_2917_, lean_object* v_t_u2082_2918_){
_start:
{
lean_object* v___f_2919_; lean_object* v___x_2920_; 
v___f_2919_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2919_, 0, v_mergeFn_2916_);
lean_closure_set(v___f_2919_, 1, v_cmp_2914_);
v___x_2920_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2919_, v_t_u2081_2917_, v_t_u2082_2918_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg___lam__0(lean_object* v_x1_2921_, lean_object* v_x2_2922_, lean_object* v_x3_2923_){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2924_, 0, v_x1_2921_);
lean_ctor_set(v___x_2924_, 1, v_x2_2922_);
v___x_2925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
lean_ctor_set(v___x_2925_, 1, v_x3_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg(lean_object* v_t_2927_){
_start:
{
lean_object* v___f_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___f_2928_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0));
v___x_2929_ = lean_box(0);
v___x_2930_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2931_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2930_, v___f_2928_, v___x_2929_, v_t_2927_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList(lean_object* v_00_u03b1_2932_, lean_object* v_cmp_2933_, lean_object* v_00_u03b2_2934_, lean_object* v_t_2935_){
_start:
{
lean_object* v___f_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___f_2936_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0));
v___x_2937_ = lean_box(0);
v___x_2938_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2939_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2938_, v___f_2936_, v___x_2937_, v_t_2935_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___boxed(lean_object* v_00_u03b1_2940_, lean_object* v_cmp_2941_, lean_object* v_00_u03b2_2942_, lean_object* v_t_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Std_DTreeMap_Raw_Const_toList(v_00_u03b1_2940_, v_cmp_2941_, v_00_u03b2_2942_, v_t_2943_);
lean_dec_ref(v_cmp_2941_);
return v_res_2944_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0(lean_object* v_cmp_2946_, lean_object* v_a_2947_, lean_object* v_x_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v_fst_2950_; lean_object* v_snd_2951_; lean_object* v_r_2952_; lean_object* v___x_2953_; 
v_fst_2950_ = lean_ctor_get(v_a_2947_, 0);
lean_inc(v_fst_2950_);
v_snd_2951_ = lean_ctor_get(v_a_2947_, 1);
lean_inc(v_snd_2951_);
lean_dec_ref(v_a_2947_);
v_r_2952_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2946_, v_fst_2950_, v_snd_2951_, v___y_2949_);
v___x_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2953_, 0, v_r_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg(lean_object* v_l_2954_, lean_object* v_cmp_2955_){
_start:
{
lean_object* v___f_2956_; lean_object* v___x_2957_; lean_object* v_r_2958_; lean_object* v___x_2959_; 
v___f_2956_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2956_, 0, v_cmp_2955_);
v___x_2957_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2958_ = lean_box(1);
v___x_2959_ = l_List_forIn_x27_loop___redArg(v___x_2957_, v___f_2956_, v_l_2954_, v_r_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg___boxed(lean_object* v_l_2960_, lean_object* v_cmp_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Std_DTreeMap_Raw_Const_ofList___redArg(v_l_2960_, v_cmp_2961_);
lean_dec(v_l_2960_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList(lean_object* v_00_u03b1_2963_, lean_object* v_00_u03b2_2964_, lean_object* v_l_2965_, lean_object* v_cmp_2966_){
_start:
{
lean_object* v___f_2967_; lean_object* v___x_2968_; lean_object* v_r_2969_; lean_object* v___x_2970_; 
v___f_2967_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2967_, 0, v_cmp_2966_);
v___x_2968_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2969_ = lean_box(1);
v___x_2970_ = l_List_forIn_x27_loop___redArg(v___x_2968_, v___f_2967_, v_l_2965_, v_r_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___boxed(lean_object* v_00_u03b1_2971_, lean_object* v_00_u03b2_2972_, lean_object* v_l_2973_, lean_object* v_cmp_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Std_DTreeMap_Raw_Const_ofList(v_00_u03b1_2971_, v_00_u03b2_2972_, v_l_2973_, v_cmp_2974_);
lean_dec(v_l_2973_);
return v_res_2975_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_2977_, lean_object* v_a_2978_, lean_object* v_x_2979_, lean_object* v___y_2980_){
_start:
{
uint8_t v___x_2981_; 
lean_inc(v___y_2980_);
lean_inc(v_a_2978_);
lean_inc_ref(v_cmp_2977_);
v___x_2981_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2977_, v_a_2978_, v___y_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2982_ = lean_box(0);
v___x_2983_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2977_, v_a_2978_, v___x_2982_, v___y_2980_);
v___x_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
return v___x_2984_;
}
else
{
lean_object* v___x_2985_; 
lean_dec(v_a_2978_);
lean_dec_ref(v_cmp_2977_);
v___x_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___y_2980_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg(lean_object* v_l_2986_, lean_object* v_cmp_2987_){
_start:
{
lean_object* v___f_2988_; lean_object* v___x_2989_; lean_object* v_r_2990_; lean_object* v___x_2991_; 
v___f_2988_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2988_, 0, v_cmp_2987_);
v___x_2989_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2990_ = lean_box(1);
v___x_2991_ = l_List_forIn_x27_loop___redArg(v___x_2989_, v___f_2988_, v_l_2986_, v_r_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___boxed(lean_object* v_l_2992_, lean_object* v_cmp_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Std_DTreeMap_Raw_Const_unitOfList___redArg(v_l_2992_, v_cmp_2993_);
lean_dec(v_l_2992_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList(lean_object* v_00_u03b1_2995_, lean_object* v_l_2996_, lean_object* v_cmp_2997_){
_start:
{
lean_object* v___f_2998_; lean_object* v___x_2999_; lean_object* v_r_3000_; lean_object* v___x_3001_; 
v___f_2998_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2998_, 0, v_cmp_2997_);
v___x_2999_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3000_ = lean_box(1);
v___x_3001_ = l_List_forIn_x27_loop___redArg(v___x_2999_, v___f_2998_, v_l_2996_, v_r_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___boxed(lean_object* v_00_u03b1_3002_, lean_object* v_l_3003_, lean_object* v_cmp_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Std_DTreeMap_Raw_Const_unitOfList(v_00_u03b1_3002_, v_l_3003_, v_cmp_3004_);
lean_dec(v_l_3003_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg___lam__0(lean_object* v_l_3006_, lean_object* v_k_3007_, lean_object* v_v_3008_){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3009_, 0, v_k_3007_);
lean_ctor_set(v___x_3009_, 1, v_v_3008_);
v___x_3010_ = lean_array_push(v_l_3006_, v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg(lean_object* v_t_3012_){
_start:
{
lean_object* v___f_3013_; lean_object* v___y_3015_; 
v___f_3013_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3012_) == 0)
{
lean_object* v_size_3018_; 
v_size_3018_ = lean_ctor_get(v_t_3012_, 0);
lean_inc(v_size_3018_);
v___y_3015_ = v_size_3018_;
goto v___jp_3014_;
}
else
{
lean_object* v___x_3019_; 
v___x_3019_ = lean_unsigned_to_nat(0u);
v___y_3015_ = v___x_3019_;
goto v___jp_3014_;
}
v___jp_3014_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_mk_empty_array_with_capacity(v___y_3015_);
lean_dec(v___y_3015_);
v___x_3017_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3013_, v___x_3016_, v_t_3012_);
return v___x_3017_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray(lean_object* v_00_u03b1_3020_, lean_object* v_cmp_3021_, lean_object* v_00_u03b2_3022_, lean_object* v_t_3023_){
_start:
{
lean_object* v___f_3024_; lean_object* v___y_3026_; 
v___f_3024_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3023_) == 0)
{
lean_object* v_size_3029_; 
v_size_3029_ = lean_ctor_get(v_t_3023_, 0);
lean_inc(v_size_3029_);
v___y_3026_ = v_size_3029_;
goto v___jp_3025_;
}
else
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_unsigned_to_nat(0u);
v___y_3026_ = v___x_3030_;
goto v___jp_3025_;
}
v___jp_3025_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_mk_empty_array_with_capacity(v___y_3026_);
lean_dec(v___y_3026_);
v___x_3028_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3024_, v___x_3027_, v_t_3023_);
return v___x_3028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___boxed(lean_object* v_00_u03b1_3031_, lean_object* v_cmp_3032_, lean_object* v_00_u03b2_3033_, lean_object* v_t_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Std_DTreeMap_Raw_Const_toArray(v_00_u03b1_3031_, v_cmp_3032_, v_00_u03b2_3033_, v_t_3034_);
lean_dec_ref(v_cmp_3032_);
return v_res_3035_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray___redArg(lean_object* v_a_3037_, lean_object* v_cmp_3038_){
_start:
{
lean_object* v___f_3039_; lean_object* v___x_3040_; lean_object* v_r_3041_; size_t v_sz_3042_; size_t v___x_3043_; lean_object* v___x_3044_; 
v___f_3039_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3039_, 0, v_cmp_3038_);
v___x_3040_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3041_ = lean_box(1);
v_sz_3042_ = lean_array_size(v_a_3037_);
v___x_3043_ = ((size_t)0ULL);
v___x_3044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3040_, v_a_3037_, v___f_3039_, v_sz_3042_, v___x_3043_, v_r_3041_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray(lean_object* v_00_u03b1_3045_, lean_object* v_00_u03b2_3046_, lean_object* v_a_3047_, lean_object* v_cmp_3048_){
_start:
{
lean_object* v___f_3049_; lean_object* v___x_3050_; lean_object* v_r_3051_; size_t v_sz_3052_; size_t v___x_3053_; lean_object* v___x_3054_; 
v___f_3049_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3049_, 0, v_cmp_3048_);
v___x_3050_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3051_ = lean_box(1);
v_sz_3052_ = lean_array_size(v_a_3047_);
v___x_3053_ = ((size_t)0ULL);
v___x_3054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3050_, v_a_3047_, v___f_3049_, v_sz_3052_, v___x_3053_, v_r_3051_);
return v___x_3054_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray___redArg(lean_object* v_a_3056_, lean_object* v_cmp_3057_){
_start:
{
lean_object* v___f_3058_; lean_object* v___x_3059_; lean_object* v_r_3060_; size_t v_sz_3061_; size_t v___x_3062_; lean_object* v___x_3063_; 
v___f_3058_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3058_, 0, v_cmp_3057_);
v___x_3059_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3060_ = lean_box(1);
v_sz_3061_ = lean_array_size(v_a_3056_);
v___x_3062_ = ((size_t)0ULL);
v___x_3063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3059_, v_a_3056_, v___f_3058_, v_sz_3061_, v___x_3062_, v_r_3060_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray(lean_object* v_00_u03b1_3064_, lean_object* v_a_3065_, lean_object* v_cmp_3066_){
_start:
{
lean_object* v___f_3067_; lean_object* v___x_3068_; lean_object* v_r_3069_; size_t v_sz_3070_; size_t v___x_3071_; lean_object* v___x_3072_; 
v___f_3067_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3067_, 0, v_cmp_3066_);
v___x_3068_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3069_ = lean_box(1);
v_sz_3070_ = lean_array_size(v_a_3065_);
v___x_3071_ = ((size_t)0ULL);
v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3068_, v_a_3065_, v___f_3067_, v_sz_3070_, v___x_3071_, v_r_3069_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify___redArg(lean_object* v_cmp_3073_, lean_object* v_t_3074_, lean_object* v_a_3075_, lean_object* v_f_3076_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3073_, v_a_3075_, v_f_3076_, v_t_3074_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify(lean_object* v_00_u03b1_3078_, lean_object* v_cmp_3079_, lean_object* v_00_u03b2_3080_, lean_object* v_t_3081_, lean_object* v_a_3082_, lean_object* v_f_3083_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3079_, v_a_3082_, v_f_3083_, v_t_3081_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter___redArg(lean_object* v_cmp_3085_, lean_object* v_t_3086_, lean_object* v_a_3087_, lean_object* v_f_3088_){
_start:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3085_, v_a_3087_, v_f_3088_, v_t_3086_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter(lean_object* v_00_u03b1_3090_, lean_object* v_cmp_3091_, lean_object* v_00_u03b2_3092_, lean_object* v_t_3093_, lean_object* v_a_3094_, lean_object* v_f_3095_){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3091_, v_a_3094_, v_f_3095_, v_t_3093_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3097_, lean_object* v_cmp_3098_, lean_object* v_t_3099_, lean_object* v_a_3100_, lean_object* v_b_u2082_3101_){
_start:
{
lean_object* v___f_3102_; lean_object* v___x_3103_; 
lean_inc(v_a_3100_);
v___f_3102_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3102_, 0, v_b_u2082_3101_);
lean_closure_set(v___f_3102_, 1, v_mergeFn_3097_);
lean_closure_set(v___f_3102_, 2, v_a_3100_);
v___x_3103_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3098_, v_a_3100_, v___f_3102_, v_t_3099_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg(lean_object* v_cmp_3104_, lean_object* v_mergeFn_3105_, lean_object* v_t_u2081_3106_, lean_object* v_t_u2082_3107_){
_start:
{
lean_object* v___f_3108_; lean_object* v___x_3109_; 
v___f_3108_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3108_, 0, v_mergeFn_3105_);
lean_closure_set(v___f_3108_, 1, v_cmp_3104_);
v___x_3109_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3108_, v_t_u2081_3106_, v_t_u2082_3107_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith(lean_object* v_00_u03b1_3110_, lean_object* v_cmp_3111_, lean_object* v_00_u03b2_3112_, lean_object* v_mergeFn_3113_, lean_object* v_t_u2081_3114_, lean_object* v_t_u2082_3115_){
_start:
{
lean_object* v___f_3116_; lean_object* v___x_3117_; 
v___f_3116_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3116_, 0, v_mergeFn_3113_);
lean_closure_set(v___f_3116_, 1, v_cmp_3111_);
v___x_3117_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3116_, v_t_u2081_3114_, v_t_u2082_3115_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_3118_, lean_object* v_x_3119_, lean_object* v_____s_3120_){
_start:
{
lean_object* v_fst_3121_; lean_object* v_snd_3122_; lean_object* v_r_3123_; lean_object* v___x_3124_; 
v_fst_3121_ = lean_ctor_get(v_x_3119_, 0);
lean_inc(v_fst_3121_);
v_snd_3122_ = lean_ctor_get(v_x_3119_, 1);
lean_inc(v_snd_3122_);
lean_dec_ref(v_x_3119_);
v_r_3123_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_3118_, v_fst_3121_, v_snd_3122_, v_____s_3120_);
v___x_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3124_, 0, v_r_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg(lean_object* v_cmp_3125_, lean_object* v_inst_3126_, lean_object* v_t_3127_, lean_object* v_l_3128_){
_start:
{
lean_object* v___f_3129_; lean_object* v___x_3130_; 
v___f_3129_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3129_, 0, v_cmp_3125_);
v___x_3130_ = lean_apply_4(v_inst_3126_, lean_box(0), v_l_3128_, v_t_3127_, v___f_3129_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany(lean_object* v_00_u03b1_3131_, lean_object* v_00_u03b2_3132_, lean_object* v_cmp_3133_, lean_object* v_00_u03c1_3134_, lean_object* v_inst_3135_, lean_object* v_t_3136_, lean_object* v_l_3137_){
_start:
{
lean_object* v___f_3138_; lean_object* v___x_3139_; 
v___f_3138_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3138_, 0, v_cmp_3133_);
v___x_3139_ = lean_apply_4(v_inst_3135_, lean_box(0), v_l_3137_, v_t_3136_, v___f_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3140_){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = lean_box(1);
v___x_3142_ = lean_panic_fn_borrowed(v___x_3141_, v_msg_3140_);
return v___x_3142_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3146_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__2));
v___x_3147_ = lean_unsigned_to_nat(35u);
v___x_3148_ = lean_unsigned_to_nat(182u);
v___x_3149_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__1));
v___x_3150_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0));
v___x_3151_ = l_mkPanicMessageWithDecl(v___x_3150_, v___x_3149_, v___x_3148_, v___x_3147_, v___x_3146_);
return v___x_3151_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3152_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__2));
v___x_3153_ = lean_unsigned_to_nat(21u);
v___x_3154_ = lean_unsigned_to_nat(183u);
v___x_3155_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__1));
v___x_3156_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0));
v___x_3157_ = l_mkPanicMessageWithDecl(v___x_3156_, v___x_3155_, v___x_3154_, v___x_3153_, v___x_3152_);
return v___x_3157_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3160_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__6));
v___x_3161_ = lean_unsigned_to_nat(35u);
v___x_3162_ = lean_unsigned_to_nat(276u);
v___x_3163_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__5));
v___x_3164_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0));
v___x_3165_ = l_mkPanicMessageWithDecl(v___x_3164_, v___x_3163_, v___x_3162_, v___x_3161_, v___x_3160_);
return v___x_3165_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3166_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__6));
v___x_3167_ = lean_unsigned_to_nat(21u);
v___x_3168_ = lean_unsigned_to_nat(277u);
v___x_3169_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__5));
v___x_3170_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0));
v___x_3171_ = l_mkPanicMessageWithDecl(v___x_3170_, v___x_3169_, v___x_3168_, v___x_3167_, v___x_3166_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(lean_object* v_cmp_3172_, lean_object* v_k_3173_, lean_object* v_v_3174_, lean_object* v_t_3175_){
_start:
{
if (lean_obj_tag(v_t_3175_) == 0)
{
lean_object* v_size_3176_; lean_object* v_k_3177_; lean_object* v_v_3178_; lean_object* v_l_3179_; lean_object* v_r_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3537_; 
v_size_3176_ = lean_ctor_get(v_t_3175_, 0);
v_k_3177_ = lean_ctor_get(v_t_3175_, 1);
v_v_3178_ = lean_ctor_get(v_t_3175_, 2);
v_l_3179_ = lean_ctor_get(v_t_3175_, 3);
v_r_3180_ = lean_ctor_get(v_t_3175_, 4);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_t_3175_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3182_ = v_t_3175_;
v_isShared_3183_ = v_isSharedCheck_3537_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_r_3180_);
lean_inc(v_l_3179_);
lean_inc(v_v_3178_);
lean_inc(v_k_3177_);
lean_inc(v_size_3176_);
lean_dec(v_t_3175_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3537_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; uint8_t v___x_3185_; 
lean_inc_ref(v_cmp_3172_);
lean_inc(v_k_3177_);
lean_inc(v_k_3173_);
v___x_3184_ = lean_apply_2(v_cmp_3172_, v_k_3173_, v_k_3177_);
v___x_3185_ = lean_unbox(v___x_3184_);
switch(v___x_3185_)
{
case 0:
{
lean_object* v___x_3186_; 
lean_dec(v_size_3176_);
v___x_3186_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3172_, v_k_3173_, v_v_3174_, v_l_3179_);
if (lean_obj_tag(v_r_3180_) == 0)
{
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_size_3187_; lean_object* v_size_3188_; lean_object* v_k_3189_; lean_object* v_v_3190_; lean_object* v_l_3191_; lean_object* v_r_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v_size_3187_ = lean_ctor_get(v_r_3180_, 0);
v_size_3188_ = lean_ctor_get(v___x_3186_, 0);
v_k_3189_ = lean_ctor_get(v___x_3186_, 1);
v_v_3190_ = lean_ctor_get(v___x_3186_, 2);
v_l_3191_ = lean_ctor_get(v___x_3186_, 3);
v_r_3192_ = lean_ctor_get(v___x_3186_, 4);
lean_inc(v_r_3192_);
v___x_3193_ = lean_unsigned_to_nat(3u);
v___x_3194_ = lean_nat_mul(v___x_3193_, v_size_3187_);
v___x_3195_ = lean_nat_dec_lt(v___x_3194_, v_size_3188_);
lean_dec(v___x_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3200_; 
lean_dec(v_r_3192_);
v___x_3196_ = lean_unsigned_to_nat(1u);
v___x_3197_ = lean_nat_add(v___x_3196_, v_size_3188_);
v___x_3198_ = lean_nat_add(v___x_3197_, v_size_3187_);
lean_dec(v___x_3197_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 3, v___x_3186_);
lean_ctor_set(v___x_3182_, 0, v___x_3198_);
v___x_3200_ = v___x_3182_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3201_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3201_, 3, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3201_, 4, v_r_3180_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
else
{
lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3273_; 
lean_inc(v_l_3191_);
lean_inc(v_v_3190_);
lean_inc(v_k_3189_);
lean_inc(v_size_3188_);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3273_ == 0)
{
lean_object* v_unused_3274_; lean_object* v_unused_3275_; lean_object* v_unused_3276_; lean_object* v_unused_3277_; lean_object* v_unused_3278_; 
v_unused_3274_ = lean_ctor_get(v___x_3186_, 4);
lean_dec(v_unused_3274_);
v_unused_3275_ = lean_ctor_get(v___x_3186_, 3);
lean_dec(v_unused_3275_);
v_unused_3276_ = lean_ctor_get(v___x_3186_, 2);
lean_dec(v_unused_3276_);
v_unused_3277_ = lean_ctor_get(v___x_3186_, 1);
lean_dec(v_unused_3277_);
v_unused_3278_ = lean_ctor_get(v___x_3186_, 0);
lean_dec(v_unused_3278_);
v___x_3203_ = v___x_3186_;
v_isShared_3204_ = v_isSharedCheck_3273_;
goto v_resetjp_3202_;
}
else
{
lean_dec(v___x_3186_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3273_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
if (lean_obj_tag(v_l_3191_) == 0)
{
if (lean_obj_tag(v_r_3192_) == 0)
{
lean_object* v_size_3205_; lean_object* v_size_3206_; lean_object* v_k_3207_; lean_object* v_v_3208_; lean_object* v_l_3209_; lean_object* v_r_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v_size_3205_ = lean_ctor_get(v_l_3191_, 0);
v_size_3206_ = lean_ctor_get(v_r_3192_, 0);
v_k_3207_ = lean_ctor_get(v_r_3192_, 1);
v_v_3208_ = lean_ctor_get(v_r_3192_, 2);
v_l_3209_ = lean_ctor_get(v_r_3192_, 3);
v_r_3210_ = lean_ctor_get(v_r_3192_, 4);
v___x_3211_ = lean_unsigned_to_nat(2u);
v___x_3212_ = lean_nat_mul(v___x_3211_, v_size_3205_);
v___x_3213_ = lean_nat_dec_lt(v_size_3206_, v___x_3212_);
lean_dec(v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3243_; 
lean_inc(v_r_3210_);
lean_inc(v_l_3209_);
lean_inc(v_v_3208_);
lean_inc(v_k_3207_);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_r_3192_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; lean_object* v_unused_3245_; lean_object* v_unused_3246_; lean_object* v_unused_3247_; lean_object* v_unused_3248_; 
v_unused_3244_ = lean_ctor_get(v_r_3192_, 4);
lean_dec(v_unused_3244_);
v_unused_3245_ = lean_ctor_get(v_r_3192_, 3);
lean_dec(v_unused_3245_);
v_unused_3246_ = lean_ctor_get(v_r_3192_, 2);
lean_dec(v_unused_3246_);
v_unused_3247_ = lean_ctor_get(v_r_3192_, 1);
lean_dec(v_unused_3247_);
v_unused_3248_ = lean_ctor_get(v_r_3192_, 0);
lean_dec(v_unused_3248_);
v___x_3215_ = v_r_3192_;
v_isShared_3216_ = v_isSharedCheck_3243_;
goto v_resetjp_3214_;
}
else
{
lean_dec(v_r_3192_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3243_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___x_3231_; lean_object* v___y_3233_; 
v___x_3217_ = lean_unsigned_to_nat(1u);
v___x_3218_ = lean_nat_add(v___x_3217_, v_size_3188_);
lean_dec(v_size_3188_);
v___x_3219_ = lean_nat_add(v___x_3218_, v_size_3187_);
lean_dec(v___x_3218_);
v___x_3231_ = lean_nat_add(v___x_3217_, v_size_3205_);
if (lean_obj_tag(v_l_3209_) == 0)
{
lean_object* v_size_3241_; 
v_size_3241_ = lean_ctor_get(v_l_3209_, 0);
lean_inc(v_size_3241_);
v___y_3233_ = v_size_3241_;
goto v___jp_3232_;
}
else
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_unsigned_to_nat(0u);
v___y_3233_ = v___x_3242_;
goto v___jp_3232_;
}
v___jp_3220_:
{
lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3224_ = lean_nat_add(v___y_3222_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec(v___y_3222_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 4, v_r_3180_);
lean_ctor_set(v___x_3215_, 3, v_r_3210_);
lean_ctor_set(v___x_3215_, 2, v_v_3178_);
lean_ctor_set(v___x_3215_, 1, v_k_3177_);
lean_ctor_set(v___x_3215_, 0, v___x_3224_);
v___x_3226_ = v___x_3215_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3230_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3230_, 3, v_r_3210_);
lean_ctor_set(v_reuseFailAlloc_3230_, 4, v_r_3180_);
v___x_3226_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3228_; 
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 4, v___x_3226_);
lean_ctor_set(v___x_3203_, 3, v___y_3221_);
lean_ctor_set(v___x_3203_, 2, v_v_3208_);
lean_ctor_set(v___x_3203_, 1, v_k_3207_);
lean_ctor_set(v___x_3203_, 0, v___x_3219_);
v___x_3228_ = v___x_3203_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_k_3207_);
lean_ctor_set(v_reuseFailAlloc_3229_, 2, v_v_3208_);
lean_ctor_set(v_reuseFailAlloc_3229_, 3, v___y_3221_);
lean_ctor_set(v_reuseFailAlloc_3229_, 4, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
v___jp_3232_:
{
lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3234_ = lean_nat_add(v___x_3231_, v___y_3233_);
lean_dec(v___y_3233_);
lean_dec(v___x_3231_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v_l_3209_);
lean_ctor_set(v___x_3182_, 3, v_l_3191_);
lean_ctor_set(v___x_3182_, 2, v_v_3190_);
lean_ctor_set(v___x_3182_, 1, v_k_3189_);
lean_ctor_set(v___x_3182_, 0, v___x_3234_);
v___x_3236_ = v___x_3182_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v_k_3189_);
lean_ctor_set(v_reuseFailAlloc_3240_, 2, v_v_3190_);
lean_ctor_set(v_reuseFailAlloc_3240_, 3, v_l_3191_);
lean_ctor_set(v_reuseFailAlloc_3240_, 4, v_l_3209_);
v___x_3236_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_nat_add(v___x_3217_, v_size_3187_);
if (lean_obj_tag(v_r_3210_) == 0)
{
lean_object* v_size_3238_; 
v_size_3238_ = lean_ctor_get(v_r_3210_, 0);
lean_inc(v_size_3238_);
v___y_3221_ = v___x_3236_;
v___y_3222_ = v___x_3237_;
v___y_3223_ = v_size_3238_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_unsigned_to_nat(0u);
v___y_3221_ = v___x_3236_;
v___y_3222_ = v___x_3237_;
v___y_3223_ = v___x_3239_;
goto v___jp_3220_;
}
}
}
}
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3255_; 
lean_del_object(v___x_3182_);
v___x_3249_ = lean_unsigned_to_nat(1u);
v___x_3250_ = lean_nat_add(v___x_3249_, v_size_3188_);
lean_dec(v_size_3188_);
v___x_3251_ = lean_nat_add(v___x_3250_, v_size_3187_);
lean_dec(v___x_3250_);
v___x_3252_ = lean_nat_add(v___x_3249_, v_size_3187_);
v___x_3253_ = lean_nat_add(v___x_3252_, v_size_3206_);
lean_dec(v___x_3252_);
lean_inc_ref(v_r_3180_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 4, v_r_3180_);
lean_ctor_set(v___x_3203_, 3, v_r_3192_);
lean_ctor_set(v___x_3203_, 2, v_v_3178_);
lean_ctor_set(v___x_3203_, 1, v_k_3177_);
lean_ctor_set(v___x_3203_, 0, v___x_3253_);
v___x_3255_ = v___x_3203_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3253_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3268_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3268_, 3, v_r_3192_);
lean_ctor_set(v_reuseFailAlloc_3268_, 4, v_r_3180_);
v___x_3255_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
v_isSharedCheck_3262_ = !lean_is_exclusive(v_r_3180_);
if (v_isSharedCheck_3262_ == 0)
{
lean_object* v_unused_3263_; lean_object* v_unused_3264_; lean_object* v_unused_3265_; lean_object* v_unused_3266_; lean_object* v_unused_3267_; 
v_unused_3263_ = lean_ctor_get(v_r_3180_, 4);
lean_dec(v_unused_3263_);
v_unused_3264_ = lean_ctor_get(v_r_3180_, 3);
lean_dec(v_unused_3264_);
v_unused_3265_ = lean_ctor_get(v_r_3180_, 2);
lean_dec(v_unused_3265_);
v_unused_3266_ = lean_ctor_get(v_r_3180_, 1);
lean_dec(v_unused_3266_);
v_unused_3267_ = lean_ctor_get(v_r_3180_, 0);
lean_dec(v_unused_3267_);
v___x_3257_ = v_r_3180_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_dec(v_r_3180_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 4, v___x_3255_);
lean_ctor_set(v___x_3257_, 3, v_l_3191_);
lean_ctor_set(v___x_3257_, 2, v_v_3190_);
lean_ctor_set(v___x_3257_, 1, v_k_3189_);
lean_ctor_set(v___x_3257_, 0, v___x_3251_);
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v_k_3189_);
lean_ctor_set(v_reuseFailAlloc_3261_, 2, v_v_3190_);
lean_ctor_set(v_reuseFailAlloc_3261_, 3, v_l_3191_);
lean_ctor_set(v_reuseFailAlloc_3261_, 4, v___x_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
lean_dec_ref_known(v_l_3191_, 5);
lean_del_object(v___x_3203_);
lean_dec(v_v_3190_);
lean_dec(v_k_3189_);
lean_dec(v_size_3188_);
lean_dec_ref_known(v_r_3180_, 5);
lean_del_object(v___x_3182_);
lean_dec(v_v_3178_);
lean_dec(v_k_3177_);
v___x_3269_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3);
v___x_3270_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_3269_);
return v___x_3270_;
}
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_del_object(v___x_3203_);
lean_dec(v_r_3192_);
lean_dec(v_v_3190_);
lean_dec(v_k_3189_);
lean_dec(v_size_3188_);
lean_dec_ref_known(v_r_3180_, 5);
lean_del_object(v___x_3182_);
lean_dec(v_v_3178_);
lean_dec(v_k_3177_);
v___x_3271_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4);
v___x_3272_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_3271_);
return v___x_3272_;
}
}
}
}
else
{
lean_object* v_size_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
v_size_3279_ = lean_ctor_get(v_r_3180_, 0);
v___x_3280_ = lean_unsigned_to_nat(1u);
v___x_3281_ = lean_nat_add(v___x_3280_, v_size_3279_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 3, v___x_3186_);
lean_ctor_set(v___x_3182_, 0, v___x_3281_);
v___x_3283_ = v___x_3182_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3284_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3284_, 3, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3284_, 4, v_r_3180_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
else
{
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_l_3285_; 
v_l_3285_ = lean_ctor_get(v___x_3186_, 3);
if (lean_obj_tag(v_l_3285_) == 0)
{
lean_object* v_r_3286_; 
lean_inc_ref(v_l_3285_);
v_r_3286_ = lean_ctor_get(v___x_3186_, 4);
lean_inc(v_r_3286_);
if (lean_obj_tag(v_r_3286_) == 0)
{
lean_object* v_size_3287_; lean_object* v_k_3288_; lean_object* v_v_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3303_; 
v_size_3287_ = lean_ctor_get(v___x_3186_, 0);
v_k_3288_ = lean_ctor_get(v___x_3186_, 1);
v_v_3289_ = lean_ctor_get(v___x_3186_, 2);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3303_ == 0)
{
lean_object* v_unused_3304_; lean_object* v_unused_3305_; 
v_unused_3304_ = lean_ctor_get(v___x_3186_, 4);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v___x_3186_, 3);
lean_dec(v_unused_3305_);
v___x_3291_ = v___x_3186_;
v_isShared_3292_ = v_isSharedCheck_3303_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_v_3289_);
lean_inc(v_k_3288_);
lean_inc(v_size_3287_);
lean_dec(v___x_3186_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3303_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v_size_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
v_size_3293_ = lean_ctor_get(v_r_3286_, 0);
v___x_3294_ = lean_unsigned_to_nat(1u);
v___x_3295_ = lean_nat_add(v___x_3294_, v_size_3287_);
lean_dec(v_size_3287_);
v___x_3296_ = lean_nat_add(v___x_3294_, v_size_3293_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 4, v_r_3180_);
lean_ctor_set(v___x_3291_, 3, v_r_3286_);
lean_ctor_set(v___x_3291_, 2, v_v_3178_);
lean_ctor_set(v___x_3291_, 1, v_k_3177_);
lean_ctor_set(v___x_3291_, 0, v___x_3296_);
v___x_3298_ = v___x_3291_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3302_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3302_, 3, v_r_3286_);
lean_ctor_set(v_reuseFailAlloc_3302_, 4, v_r_3180_);
v___x_3298_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3300_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v___x_3298_);
lean_ctor_set(v___x_3182_, 3, v_l_3285_);
lean_ctor_set(v___x_3182_, 2, v_v_3289_);
lean_ctor_set(v___x_3182_, 1, v_k_3288_);
lean_ctor_set(v___x_3182_, 0, v___x_3295_);
v___x_3300_ = v___x_3182_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3295_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3301_, 3, v_l_3285_);
lean_ctor_set(v_reuseFailAlloc_3301_, 4, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_object* v_k_3306_; lean_object* v_v_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3319_; 
v_k_3306_ = lean_ctor_get(v___x_3186_, 1);
v_v_3307_ = lean_ctor_get(v___x_3186_, 2);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3319_ == 0)
{
lean_object* v_unused_3320_; lean_object* v_unused_3321_; lean_object* v_unused_3322_; 
v_unused_3320_ = lean_ctor_get(v___x_3186_, 4);
lean_dec(v_unused_3320_);
v_unused_3321_ = lean_ctor_get(v___x_3186_, 3);
lean_dec(v_unused_3321_);
v_unused_3322_ = lean_ctor_get(v___x_3186_, 0);
lean_dec(v_unused_3322_);
v___x_3309_ = v___x_3186_;
v_isShared_3310_ = v_isSharedCheck_3319_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_v_3307_);
lean_inc(v_k_3306_);
lean_dec(v___x_3186_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3319_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3314_; 
v___x_3311_ = lean_unsigned_to_nat(3u);
v___x_3312_ = lean_unsigned_to_nat(1u);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 3, v_r_3286_);
lean_ctor_set(v___x_3309_, 2, v_v_3178_);
lean_ctor_set(v___x_3309_, 1, v_k_3177_);
lean_ctor_set(v___x_3309_, 0, v___x_3312_);
v___x_3314_ = v___x_3309_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3312_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3318_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3318_, 3, v_r_3286_);
lean_ctor_set(v_reuseFailAlloc_3318_, 4, v_r_3286_);
v___x_3314_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
lean_object* v___x_3316_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v___x_3314_);
lean_ctor_set(v___x_3182_, 3, v_l_3285_);
lean_ctor_set(v___x_3182_, 2, v_v_3307_);
lean_ctor_set(v___x_3182_, 1, v_k_3306_);
lean_ctor_set(v___x_3182_, 0, v___x_3311_);
v___x_3316_ = v___x_3182_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_k_3306_);
lean_ctor_set(v_reuseFailAlloc_3317_, 2, v_v_3307_);
lean_ctor_set(v_reuseFailAlloc_3317_, 3, v_l_3285_);
lean_ctor_set(v_reuseFailAlloc_3317_, 4, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
}
else
{
lean_object* v_r_3323_; 
v_r_3323_ = lean_ctor_get(v___x_3186_, 4);
lean_inc(v_r_3323_);
if (lean_obj_tag(v_r_3323_) == 0)
{
lean_object* v_k_3324_; lean_object* v_v_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3349_; 
lean_inc(v_l_3285_);
v_k_3324_ = lean_ctor_get(v___x_3186_, 1);
v_v_3325_ = lean_ctor_get(v___x_3186_, 2);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3349_ == 0)
{
lean_object* v_unused_3350_; lean_object* v_unused_3351_; lean_object* v_unused_3352_; 
v_unused_3350_ = lean_ctor_get(v___x_3186_, 4);
lean_dec(v_unused_3350_);
v_unused_3351_ = lean_ctor_get(v___x_3186_, 3);
lean_dec(v_unused_3351_);
v_unused_3352_ = lean_ctor_get(v___x_3186_, 0);
lean_dec(v_unused_3352_);
v___x_3327_ = v___x_3186_;
v_isShared_3328_ = v_isSharedCheck_3349_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_v_3325_);
lean_inc(v_k_3324_);
lean_dec(v___x_3186_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3349_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v_k_3329_; lean_object* v_v_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3345_; 
v_k_3329_ = lean_ctor_get(v_r_3323_, 1);
v_v_3330_ = lean_ctor_get(v_r_3323_, 2);
v_isSharedCheck_3345_ = !lean_is_exclusive(v_r_3323_);
if (v_isSharedCheck_3345_ == 0)
{
lean_object* v_unused_3346_; lean_object* v_unused_3347_; lean_object* v_unused_3348_; 
v_unused_3346_ = lean_ctor_get(v_r_3323_, 4);
lean_dec(v_unused_3346_);
v_unused_3347_ = lean_ctor_get(v_r_3323_, 3);
lean_dec(v_unused_3347_);
v_unused_3348_ = lean_ctor_get(v_r_3323_, 0);
lean_dec(v_unused_3348_);
v___x_3332_ = v_r_3323_;
v_isShared_3333_ = v_isSharedCheck_3345_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_v_3330_);
lean_inc(v_k_3329_);
lean_dec(v_r_3323_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3345_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3334_ = lean_unsigned_to_nat(3u);
v___x_3335_ = lean_unsigned_to_nat(1u);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_l_3285_);
lean_ctor_set(v___x_3332_, 3, v_l_3285_);
lean_ctor_set(v___x_3332_, 2, v_v_3325_);
lean_ctor_set(v___x_3332_, 1, v_k_3324_);
lean_ctor_set(v___x_3332_, 0, v___x_3335_);
v___x_3337_ = v___x_3332_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3344_, 1, v_k_3324_);
lean_ctor_set(v_reuseFailAlloc_3344_, 2, v_v_3325_);
lean_ctor_set(v_reuseFailAlloc_3344_, 3, v_l_3285_);
lean_ctor_set(v_reuseFailAlloc_3344_, 4, v_l_3285_);
v___x_3337_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3339_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 4, v_l_3285_);
lean_ctor_set(v___x_3327_, 2, v_v_3178_);
lean_ctor_set(v___x_3327_, 1, v_k_3177_);
lean_ctor_set(v___x_3327_, 0, v___x_3335_);
v___x_3339_ = v___x_3327_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3343_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3343_, 3, v_l_3285_);
lean_ctor_set(v_reuseFailAlloc_3343_, 4, v_l_3285_);
v___x_3339_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
lean_object* v___x_3341_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v___x_3339_);
lean_ctor_set(v___x_3182_, 3, v___x_3337_);
lean_ctor_set(v___x_3182_, 2, v_v_3330_);
lean_ctor_set(v___x_3182_, 1, v_k_3329_);
lean_ctor_set(v___x_3182_, 0, v___x_3334_);
v___x_3341_ = v___x_3182_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_k_3329_);
lean_ctor_set(v_reuseFailAlloc_3342_, 2, v_v_3330_);
lean_ctor_set(v_reuseFailAlloc_3342_, 3, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3342_, 4, v___x_3339_);
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
else
{
lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3353_ = lean_unsigned_to_nat(2u);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v_r_3323_);
lean_ctor_set(v___x_3182_, 3, v___x_3186_);
lean_ctor_set(v___x_3182_, 0, v___x_3353_);
v___x_3355_ = v___x_3182_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3356_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3356_, 3, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3356_, 4, v_r_3323_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3357_ = lean_unsigned_to_nat(1u);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v___x_3186_);
lean_ctor_set(v___x_3182_, 3, v___x_3186_);
lean_ctor_set(v___x_3182_, 0, v___x_3357_);
v___x_3359_ = v___x_3182_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3360_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3360_, 3, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3360_, 4, v___x_3186_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
case 1:
{
lean_object* v___x_3362_; 
lean_dec(v_v_3178_);
lean_dec(v_k_3177_);
lean_dec_ref(v_cmp_3172_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 2, v_v_3174_);
lean_ctor_set(v___x_3182_, 1, v_k_3173_);
v___x_3362_ = v___x_3182_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_size_3176_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_3173_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_3174_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_l_3179_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_r_3180_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
default: 
{
lean_object* v___x_3364_; 
lean_dec(v_size_3176_);
v___x_3364_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3172_, v_k_3173_, v_v_3174_, v_r_3180_);
if (lean_obj_tag(v_l_3179_) == 0)
{
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_size_3365_; lean_object* v_size_3366_; lean_object* v_k_3367_; lean_object* v_v_3368_; lean_object* v_l_3369_; lean_object* v_r_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v_size_3365_ = lean_ctor_get(v_l_3179_, 0);
v_size_3366_ = lean_ctor_get(v___x_3364_, 0);
v_k_3367_ = lean_ctor_get(v___x_3364_, 1);
v_v_3368_ = lean_ctor_get(v___x_3364_, 2);
v_l_3369_ = lean_ctor_get(v___x_3364_, 3);
lean_inc(v_l_3369_);
v_r_3370_ = lean_ctor_get(v___x_3364_, 4);
v___x_3371_ = lean_unsigned_to_nat(3u);
v___x_3372_ = lean_nat_mul(v___x_3371_, v_size_3365_);
v___x_3373_ = lean_nat_dec_lt(v___x_3372_, v_size_3366_);
lean_dec(v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3378_; 
lean_dec(v_l_3369_);
v___x_3374_ = lean_unsigned_to_nat(1u);
v___x_3375_ = lean_nat_add(v___x_3374_, v_size_3365_);
v___x_3376_ = lean_nat_add(v___x_3375_, v_size_3366_);
lean_dec(v___x_3375_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v___x_3364_);
lean_ctor_set(v___x_3182_, 0, v___x_3376_);
v___x_3378_ = v___x_3182_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3379_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3379_, 3, v_l_3179_);
lean_ctor_set(v_reuseFailAlloc_3379_, 4, v___x_3364_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
else
{
lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3449_; 
lean_inc(v_r_3370_);
lean_inc(v_v_3368_);
lean_inc(v_k_3367_);
lean_inc(v_size_3366_);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3449_ == 0)
{
lean_object* v_unused_3450_; lean_object* v_unused_3451_; lean_object* v_unused_3452_; lean_object* v_unused_3453_; lean_object* v_unused_3454_; 
v_unused_3450_ = lean_ctor_get(v___x_3364_, 4);
lean_dec(v_unused_3450_);
v_unused_3451_ = lean_ctor_get(v___x_3364_, 3);
lean_dec(v_unused_3451_);
v_unused_3452_ = lean_ctor_get(v___x_3364_, 2);
lean_dec(v_unused_3452_);
v_unused_3453_ = lean_ctor_get(v___x_3364_, 1);
lean_dec(v_unused_3453_);
v_unused_3454_ = lean_ctor_get(v___x_3364_, 0);
lean_dec(v_unused_3454_);
v___x_3381_ = v___x_3364_;
v_isShared_3382_ = v_isSharedCheck_3449_;
goto v_resetjp_3380_;
}
else
{
lean_dec(v___x_3364_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3449_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
if (lean_obj_tag(v_l_3369_) == 0)
{
if (lean_obj_tag(v_r_3370_) == 0)
{
lean_object* v_size_3383_; lean_object* v_k_3384_; lean_object* v_v_3385_; lean_object* v_l_3386_; lean_object* v_r_3387_; lean_object* v_size_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; 
v_size_3383_ = lean_ctor_get(v_l_3369_, 0);
v_k_3384_ = lean_ctor_get(v_l_3369_, 1);
v_v_3385_ = lean_ctor_get(v_l_3369_, 2);
v_l_3386_ = lean_ctor_get(v_l_3369_, 3);
v_r_3387_ = lean_ctor_get(v_l_3369_, 4);
v_size_3388_ = lean_ctor_get(v_r_3370_, 0);
v___x_3389_ = lean_unsigned_to_nat(2u);
v___x_3390_ = lean_nat_mul(v___x_3389_, v_size_3388_);
v___x_3391_ = lean_nat_dec_lt(v_size_3383_, v___x_3390_);
lean_dec(v___x_3390_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3420_; 
lean_inc(v_r_3387_);
lean_inc(v_l_3386_);
lean_inc(v_v_3385_);
lean_inc(v_k_3384_);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_l_3369_);
if (v_isSharedCheck_3420_ == 0)
{
lean_object* v_unused_3421_; lean_object* v_unused_3422_; lean_object* v_unused_3423_; lean_object* v_unused_3424_; lean_object* v_unused_3425_; 
v_unused_3421_ = lean_ctor_get(v_l_3369_, 4);
lean_dec(v_unused_3421_);
v_unused_3422_ = lean_ctor_get(v_l_3369_, 3);
lean_dec(v_unused_3422_);
v_unused_3423_ = lean_ctor_get(v_l_3369_, 2);
lean_dec(v_unused_3423_);
v_unused_3424_ = lean_ctor_get(v_l_3369_, 1);
lean_dec(v_unused_3424_);
v_unused_3425_ = lean_ctor_get(v_l_3369_, 0);
lean_dec(v_unused_3425_);
v___x_3393_ = v_l_3369_;
v_isShared_3394_ = v_isSharedCheck_3420_;
goto v_resetjp_3392_;
}
else
{
lean_dec(v_l_3369_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3420_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3410_; 
v___x_3395_ = lean_unsigned_to_nat(1u);
v___x_3396_ = lean_nat_add(v___x_3395_, v_size_3365_);
v___x_3397_ = lean_nat_add(v___x_3396_, v_size_3366_);
lean_dec(v_size_3366_);
if (lean_obj_tag(v_l_3386_) == 0)
{
lean_object* v_size_3418_; 
v_size_3418_ = lean_ctor_get(v_l_3386_, 0);
lean_inc(v_size_3418_);
v___y_3410_ = v_size_3418_;
goto v___jp_3409_;
}
else
{
lean_object* v___x_3419_; 
v___x_3419_ = lean_unsigned_to_nat(0u);
v___y_3410_ = v___x_3419_;
goto v___jp_3409_;
}
v___jp_3398_:
{
lean_object* v___x_3402_; lean_object* v___x_3404_; 
v___x_3402_ = lean_nat_add(v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec(v___y_3400_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 4, v_r_3370_);
lean_ctor_set(v___x_3393_, 3, v_r_3387_);
lean_ctor_set(v___x_3393_, 2, v_v_3368_);
lean_ctor_set(v___x_3393_, 1, v_k_3367_);
lean_ctor_set(v___x_3393_, 0, v___x_3402_);
v___x_3404_ = v___x_3393_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_k_3367_);
lean_ctor_set(v_reuseFailAlloc_3408_, 2, v_v_3368_);
lean_ctor_set(v_reuseFailAlloc_3408_, 3, v_r_3387_);
lean_ctor_set(v_reuseFailAlloc_3408_, 4, v_r_3370_);
v___x_3404_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3406_; 
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 4, v___x_3404_);
lean_ctor_set(v___x_3381_, 3, v___y_3399_);
lean_ctor_set(v___x_3381_, 2, v_v_3385_);
lean_ctor_set(v___x_3381_, 1, v_k_3384_);
lean_ctor_set(v___x_3381_, 0, v___x_3397_);
v___x_3406_ = v___x_3381_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_k_3384_);
lean_ctor_set(v_reuseFailAlloc_3407_, 2, v_v_3385_);
lean_ctor_set(v_reuseFailAlloc_3407_, 3, v___y_3399_);
lean_ctor_set(v_reuseFailAlloc_3407_, 4, v___x_3404_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
v___jp_3409_:
{
lean_object* v___x_3411_; lean_object* v___x_3413_; 
v___x_3411_ = lean_nat_add(v___x_3396_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec(v___x_3396_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v_l_3386_);
lean_ctor_set(v___x_3182_, 0, v___x_3411_);
v___x_3413_ = v___x_3182_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3417_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3417_, 3, v_l_3179_);
lean_ctor_set(v_reuseFailAlloc_3417_, 4, v_l_3386_);
v___x_3413_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3414_; 
v___x_3414_ = lean_nat_add(v___x_3395_, v_size_3388_);
if (lean_obj_tag(v_r_3387_) == 0)
{
lean_object* v_size_3415_; 
v_size_3415_ = lean_ctor_get(v_r_3387_, 0);
lean_inc(v_size_3415_);
v___y_3399_ = v___x_3413_;
v___y_3400_ = v___x_3414_;
v___y_3401_ = v_size_3415_;
goto v___jp_3398_;
}
else
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_unsigned_to_nat(0u);
v___y_3399_ = v___x_3413_;
v___y_3400_ = v___x_3414_;
v___y_3401_ = v___x_3416_;
goto v___jp_3398_;
}
}
}
}
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3431_; 
lean_del_object(v___x_3182_);
v___x_3426_ = lean_unsigned_to_nat(1u);
v___x_3427_ = lean_nat_add(v___x_3426_, v_size_3365_);
v___x_3428_ = lean_nat_add(v___x_3427_, v_size_3366_);
lean_dec(v_size_3366_);
v___x_3429_ = lean_nat_add(v___x_3427_, v_size_3383_);
lean_dec(v___x_3427_);
lean_inc_ref(v_l_3179_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 4, v_l_3369_);
lean_ctor_set(v___x_3381_, 3, v_l_3179_);
lean_ctor_set(v___x_3381_, 2, v_v_3178_);
lean_ctor_set(v___x_3381_, 1, v_k_3177_);
lean_ctor_set(v___x_3381_, 0, v___x_3429_);
v___x_3431_ = v___x_3381_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3429_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3444_, 3, v_l_3179_);
lean_ctor_set(v_reuseFailAlloc_3444_, 4, v_l_3369_);
v___x_3431_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
v_isSharedCheck_3438_ = !lean_is_exclusive(v_l_3179_);
if (v_isSharedCheck_3438_ == 0)
{
lean_object* v_unused_3439_; lean_object* v_unused_3440_; lean_object* v_unused_3441_; lean_object* v_unused_3442_; lean_object* v_unused_3443_; 
v_unused_3439_ = lean_ctor_get(v_l_3179_, 4);
lean_dec(v_unused_3439_);
v_unused_3440_ = lean_ctor_get(v_l_3179_, 3);
lean_dec(v_unused_3440_);
v_unused_3441_ = lean_ctor_get(v_l_3179_, 2);
lean_dec(v_unused_3441_);
v_unused_3442_ = lean_ctor_get(v_l_3179_, 1);
lean_dec(v_unused_3442_);
v_unused_3443_ = lean_ctor_get(v_l_3179_, 0);
lean_dec(v_unused_3443_);
v___x_3433_ = v_l_3179_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_dec(v_l_3179_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 4, v_r_3370_);
lean_ctor_set(v___x_3433_, 3, v___x_3431_);
lean_ctor_set(v___x_3433_, 2, v_v_3368_);
lean_ctor_set(v___x_3433_, 1, v_k_3367_);
lean_ctor_set(v___x_3433_, 0, v___x_3428_);
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3428_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_k_3367_);
lean_ctor_set(v_reuseFailAlloc_3437_, 2, v_v_3368_);
lean_ctor_set(v_reuseFailAlloc_3437_, 3, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3437_, 4, v_r_3370_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
else
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
lean_dec_ref_known(v_l_3369_, 5);
lean_del_object(v___x_3381_);
lean_dec(v_v_3368_);
lean_dec(v_k_3367_);
lean_dec(v_size_3366_);
lean_dec_ref_known(v_l_3179_, 5);
lean_del_object(v___x_3182_);
lean_dec(v_v_3178_);
lean_dec(v_k_3177_);
v___x_3445_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7);
v___x_3446_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_3445_);
return v___x_3446_;
}
}
else
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_del_object(v___x_3381_);
lean_dec(v_r_3370_);
lean_dec(v_v_3368_);
lean_dec(v_k_3367_);
lean_dec(v_size_3366_);
lean_dec_ref_known(v_l_3179_, 5);
lean_del_object(v___x_3182_);
lean_dec(v_v_3178_);
lean_dec(v_k_3177_);
v___x_3447_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8);
v___x_3448_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_3447_);
return v___x_3448_;
}
}
}
}
else
{
lean_object* v_size_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
v_size_3455_ = lean_ctor_get(v_l_3179_, 0);
v___x_3456_ = lean_unsigned_to_nat(1u);
v___x_3457_ = lean_nat_add(v___x_3456_, v_size_3455_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v___x_3364_);
lean_ctor_set(v___x_3182_, 0, v___x_3457_);
v___x_3459_ = v___x_3182_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3460_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3460_, 3, v_l_3179_);
lean_ctor_set(v_reuseFailAlloc_3460_, 4, v___x_3364_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
else
{
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_l_3461_; 
v_l_3461_ = lean_ctor_get(v___x_3364_, 3);
lean_inc(v_l_3461_);
if (lean_obj_tag(v_l_3461_) == 0)
{
lean_object* v_r_3462_; 
v_r_3462_ = lean_ctor_get(v___x_3364_, 4);
lean_inc(v_r_3462_);
if (lean_obj_tag(v_r_3462_) == 0)
{
lean_object* v_size_3463_; lean_object* v_k_3464_; lean_object* v_v_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3479_; 
v_size_3463_ = lean_ctor_get(v___x_3364_, 0);
v_k_3464_ = lean_ctor_get(v___x_3364_, 1);
v_v_3465_ = lean_ctor_get(v___x_3364_, 2);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; lean_object* v_unused_3481_; 
v_unused_3480_ = lean_ctor_get(v___x_3364_, 4);
lean_dec(v_unused_3480_);
v_unused_3481_ = lean_ctor_get(v___x_3364_, 3);
lean_dec(v_unused_3481_);
v___x_3467_ = v___x_3364_;
v_isShared_3468_ = v_isSharedCheck_3479_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_v_3465_);
lean_inc(v_k_3464_);
lean_inc(v_size_3463_);
lean_dec(v___x_3364_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3479_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v_size_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3474_; 
v_size_3469_ = lean_ctor_get(v_l_3461_, 0);
v___x_3470_ = lean_unsigned_to_nat(1u);
v___x_3471_ = lean_nat_add(v___x_3470_, v_size_3463_);
lean_dec(v_size_3463_);
v___x_3472_ = lean_nat_add(v___x_3470_, v_size_3469_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 4, v_l_3461_);
lean_ctor_set(v___x_3467_, 3, v_l_3179_);
lean_ctor_set(v___x_3467_, 2, v_v_3178_);
lean_ctor_set(v___x_3467_, 1, v_k_3177_);
lean_ctor_set(v___x_3467_, 0, v___x_3472_);
v___x_3474_ = v___x_3467_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3472_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3478_, 3, v_l_3179_);
lean_ctor_set(v_reuseFailAlloc_3478_, 4, v_l_3461_);
v___x_3474_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3476_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v_r_3462_);
lean_ctor_set(v___x_3182_, 3, v___x_3474_);
lean_ctor_set(v___x_3182_, 2, v_v_3465_);
lean_ctor_set(v___x_3182_, 1, v_k_3464_);
lean_ctor_set(v___x_3182_, 0, v___x_3471_);
v___x_3476_ = v___x_3182_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_k_3464_);
lean_ctor_set(v_reuseFailAlloc_3477_, 2, v_v_3465_);
lean_ctor_set(v_reuseFailAlloc_3477_, 3, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3477_, 4, v_r_3462_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
lean_object* v_k_3482_; lean_object* v_v_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3507_; 
v_k_3482_ = lean_ctor_get(v___x_3364_, 1);
v_v_3483_ = lean_ctor_get(v___x_3364_, 2);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3507_ == 0)
{
lean_object* v_unused_3508_; lean_object* v_unused_3509_; lean_object* v_unused_3510_; 
v_unused_3508_ = lean_ctor_get(v___x_3364_, 4);
lean_dec(v_unused_3508_);
v_unused_3509_ = lean_ctor_get(v___x_3364_, 3);
lean_dec(v_unused_3509_);
v_unused_3510_ = lean_ctor_get(v___x_3364_, 0);
lean_dec(v_unused_3510_);
v___x_3485_ = v___x_3364_;
v_isShared_3486_ = v_isSharedCheck_3507_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_v_3483_);
lean_inc(v_k_3482_);
lean_dec(v___x_3364_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3507_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v_k_3487_; lean_object* v_v_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3503_; 
v_k_3487_ = lean_ctor_get(v_l_3461_, 1);
v_v_3488_ = lean_ctor_get(v_l_3461_, 2);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_l_3461_);
if (v_isSharedCheck_3503_ == 0)
{
lean_object* v_unused_3504_; lean_object* v_unused_3505_; lean_object* v_unused_3506_; 
v_unused_3504_ = lean_ctor_get(v_l_3461_, 4);
lean_dec(v_unused_3504_);
v_unused_3505_ = lean_ctor_get(v_l_3461_, 3);
lean_dec(v_unused_3505_);
v_unused_3506_ = lean_ctor_get(v_l_3461_, 0);
lean_dec(v_unused_3506_);
v___x_3490_ = v_l_3461_;
v_isShared_3491_ = v_isSharedCheck_3503_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_v_3488_);
lean_inc(v_k_3487_);
lean_dec(v_l_3461_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3503_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3495_; 
v___x_3492_ = lean_unsigned_to_nat(3u);
v___x_3493_ = lean_unsigned_to_nat(1u);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 4, v_r_3462_);
lean_ctor_set(v___x_3490_, 3, v_r_3462_);
lean_ctor_set(v___x_3490_, 2, v_v_3178_);
lean_ctor_set(v___x_3490_, 1, v_k_3177_);
lean_ctor_set(v___x_3490_, 0, v___x_3493_);
v___x_3495_ = v___x_3490_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3502_, 3, v_r_3462_);
lean_ctor_set(v_reuseFailAlloc_3502_, 4, v_r_3462_);
v___x_3495_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
lean_object* v___x_3497_; 
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 3, v_r_3462_);
lean_ctor_set(v___x_3485_, 0, v___x_3493_);
v___x_3497_ = v___x_3485_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_k_3482_);
lean_ctor_set(v_reuseFailAlloc_3501_, 2, v_v_3483_);
lean_ctor_set(v_reuseFailAlloc_3501_, 3, v_r_3462_);
lean_ctor_set(v_reuseFailAlloc_3501_, 4, v_r_3462_);
v___x_3497_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3499_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v___x_3497_);
lean_ctor_set(v___x_3182_, 3, v___x_3495_);
lean_ctor_set(v___x_3182_, 2, v_v_3488_);
lean_ctor_set(v___x_3182_, 1, v_k_3487_);
lean_ctor_set(v___x_3182_, 0, v___x_3492_);
v___x_3499_ = v___x_3182_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3492_);
lean_ctor_set(v_reuseFailAlloc_3500_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3500_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3500_, 3, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3500_, 4, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3511_; 
v_r_3511_ = lean_ctor_get(v___x_3364_, 4);
lean_inc(v_r_3511_);
if (lean_obj_tag(v_r_3511_) == 0)
{
lean_object* v_k_3512_; lean_object* v_v_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3525_; 
v_k_3512_ = lean_ctor_get(v___x_3364_, 1);
v_v_3513_ = lean_ctor_get(v___x_3364_, 2);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3525_ == 0)
{
lean_object* v_unused_3526_; lean_object* v_unused_3527_; lean_object* v_unused_3528_; 
v_unused_3526_ = lean_ctor_get(v___x_3364_, 4);
lean_dec(v_unused_3526_);
v_unused_3527_ = lean_ctor_get(v___x_3364_, 3);
lean_dec(v_unused_3527_);
v_unused_3528_ = lean_ctor_get(v___x_3364_, 0);
lean_dec(v_unused_3528_);
v___x_3515_ = v___x_3364_;
v_isShared_3516_ = v_isSharedCheck_3525_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_v_3513_);
lean_inc(v_k_3512_);
lean_dec(v___x_3364_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3525_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3517_ = lean_unsigned_to_nat(3u);
v___x_3518_ = lean_unsigned_to_nat(1u);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 4, v_l_3461_);
lean_ctor_set(v___x_3515_, 2, v_v_3178_);
lean_ctor_set(v___x_3515_, 1, v_k_3177_);
lean_ctor_set(v___x_3515_, 0, v___x_3518_);
v___x_3520_ = v___x_3515_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3524_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3524_, 3, v_l_3461_);
lean_ctor_set(v_reuseFailAlloc_3524_, 4, v_l_3461_);
v___x_3520_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3522_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v_r_3511_);
lean_ctor_set(v___x_3182_, 3, v___x_3520_);
lean_ctor_set(v___x_3182_, 2, v_v_3513_);
lean_ctor_set(v___x_3182_, 1, v_k_3512_);
lean_ctor_set(v___x_3182_, 0, v___x_3517_);
v___x_3522_ = v___x_3182_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_k_3512_);
lean_ctor_set(v_reuseFailAlloc_3523_, 2, v_v_3513_);
lean_ctor_set(v_reuseFailAlloc_3523_, 3, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3523_, 4, v_r_3511_);
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
else
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3529_ = lean_unsigned_to_nat(2u);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v___x_3364_);
lean_ctor_set(v___x_3182_, 3, v_r_3511_);
lean_ctor_set(v___x_3182_, 0, v___x_3529_);
v___x_3531_ = v___x_3182_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3532_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3532_, 3, v_r_3511_);
lean_ctor_set(v_reuseFailAlloc_3532_, 4, v___x_3364_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
else
{
lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3533_ = lean_unsigned_to_nat(1u);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v___x_3364_);
lean_ctor_set(v___x_3182_, 3, v___x_3364_);
lean_ctor_set(v___x_3182_, 0, v___x_3533_);
v___x_3535_ = v___x_3182_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3536_, 2, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3536_, 3, v___x_3364_);
lean_ctor_set(v_reuseFailAlloc_3536_, 4, v___x_3364_);
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
lean_object* v___x_3538_; lean_object* v___x_3539_; 
lean_dec_ref(v_cmp_3172_);
v___x_3538_ = lean_unsigned_to_nat(1u);
v___x_3539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
lean_ctor_set(v___x_3539_, 1, v_k_3173_);
lean_ctor_set(v___x_3539_, 2, v_v_3174_);
lean_ctor_set(v___x_3539_, 3, v_t_3175_);
lean_ctor_set(v___x_3539_, 4, v_t_3175_);
return v___x_3539_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(lean_object* v_cmp_3540_, lean_object* v_init_3541_, lean_object* v_x_3542_){
_start:
{
if (lean_obj_tag(v_x_3542_) == 0)
{
lean_object* v_k_3543_; lean_object* v_v_3544_; lean_object* v_l_3545_; lean_object* v_r_3546_; lean_object* v___x_3547_; lean_object* v_a_3548_; lean_object* v_r_3549_; 
v_k_3543_ = lean_ctor_get(v_x_3542_, 1);
lean_inc(v_k_3543_);
v_v_3544_ = lean_ctor_get(v_x_3542_, 2);
lean_inc(v_v_3544_);
v_l_3545_ = lean_ctor_get(v_x_3542_, 3);
lean_inc(v_l_3545_);
v_r_3546_ = lean_ctor_get(v_x_3542_, 4);
lean_inc(v_r_3546_);
lean_dec_ref_known(v_x_3542_, 5);
lean_inc_ref_n(v_cmp_3540_, 2);
v___x_3547_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3540_, v_init_3541_, v_l_3545_);
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref(v___x_3547_);
v_r_3549_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3540_, v_k_3543_, v_v_3544_, v_a_3548_);
v_init_3541_ = v_r_3549_;
v_x_3542_ = v_r_3546_;
goto _start;
}
else
{
lean_object* v___x_3551_; 
lean_dec_ref(v_cmp_3540_);
v___x_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3551_, 0, v_init_3541_);
return v___x_3551_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(lean_object* v_cmp_3552_, lean_object* v_k_3553_, lean_object* v_t_3554_){
_start:
{
if (lean_obj_tag(v_t_3554_) == 0)
{
lean_object* v_k_3555_; lean_object* v_l_3556_; lean_object* v_r_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v_k_3555_ = lean_ctor_get(v_t_3554_, 1);
lean_inc(v_k_3555_);
v_l_3556_ = lean_ctor_get(v_t_3554_, 3);
lean_inc(v_l_3556_);
v_r_3557_ = lean_ctor_get(v_t_3554_, 4);
lean_inc(v_r_3557_);
lean_dec_ref_known(v_t_3554_, 5);
lean_inc_ref(v_cmp_3552_);
lean_inc(v_k_3553_);
v___x_3558_ = lean_apply_2(v_cmp_3552_, v_k_3553_, v_k_3555_);
v___x_3559_ = lean_unbox(v___x_3558_);
switch(v___x_3559_)
{
case 0:
{
lean_dec(v_r_3557_);
v_t_3554_ = v_l_3556_;
goto _start;
}
case 1:
{
uint8_t v___x_3561_; 
lean_dec(v_r_3557_);
lean_dec(v_l_3556_);
lean_dec(v_k_3553_);
lean_dec_ref(v_cmp_3552_);
v___x_3561_ = 1;
return v___x_3561_;
}
default: 
{
lean_dec(v_l_3556_);
v_t_3554_ = v_r_3557_;
goto _start;
}
}
}
else
{
uint8_t v___x_3563_; 
lean_dec(v_k_3553_);
lean_dec_ref(v_cmp_3552_);
v___x_3563_ = 0;
return v___x_3563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_3564_, lean_object* v_k_3565_, lean_object* v_t_3566_){
_start:
{
uint8_t v_res_3567_; lean_object* v_r_3568_; 
v_res_3567_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3564_, v_k_3565_, v_t_3566_);
v_r_3568_ = lean_box(v_res_3567_);
return v_r_3568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(lean_object* v_cmp_3569_, lean_object* v_init_3570_, lean_object* v_x_3571_){
_start:
{
if (lean_obj_tag(v_x_3571_) == 0)
{
lean_object* v_k_3572_; lean_object* v_v_3573_; lean_object* v_l_3574_; lean_object* v_r_3575_; lean_object* v___x_3576_; lean_object* v_a_3577_; uint8_t v___x_3578_; 
v_k_3572_ = lean_ctor_get(v_x_3571_, 1);
lean_inc_n(v_k_3572_, 2);
v_v_3573_ = lean_ctor_get(v_x_3571_, 2);
lean_inc(v_v_3573_);
v_l_3574_ = lean_ctor_get(v_x_3571_, 3);
lean_inc(v_l_3574_);
v_r_3575_ = lean_ctor_get(v_x_3571_, 4);
lean_inc(v_r_3575_);
lean_dec_ref_known(v_x_3571_, 5);
lean_inc_ref_n(v_cmp_3569_, 2);
v___x_3576_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3569_, v_init_3570_, v_l_3574_);
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc_n(v_a_3577_, 2);
lean_dec_ref(v___x_3576_);
v___x_3578_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3569_, v_k_3572_, v_a_3577_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; 
lean_inc_ref(v_cmp_3569_);
v___x_3579_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3569_, v_k_3572_, v_v_3573_, v_a_3577_);
v_init_3570_ = v___x_3579_;
v_x_3571_ = v_r_3575_;
goto _start;
}
else
{
lean_dec(v_v_3573_);
lean_dec(v_k_3572_);
v_init_3570_ = v_a_3577_;
v_x_3571_ = v_r_3575_;
goto _start;
}
}
else
{
lean_object* v___x_3582_; 
lean_dec_ref(v_cmp_3569_);
v___x_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3582_, 0, v_init_3570_);
return v___x_3582_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(lean_object* v_cmp_3583_, lean_object* v_t_u2081_3584_, lean_object* v_t_u2082_3585_){
_start:
{
lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3595_; 
if (lean_obj_tag(v_t_u2081_3584_) == 0)
{
lean_object* v_size_3598_; 
v_size_3598_ = lean_ctor_get(v_t_u2081_3584_, 0);
lean_inc(v_size_3598_);
v___y_3595_ = v_size_3598_;
goto v___jp_3594_;
}
else
{
lean_object* v___x_3599_; 
v___x_3599_ = lean_unsigned_to_nat(0u);
v___y_3595_ = v___x_3599_;
goto v___jp_3594_;
}
v___jp_3586_:
{
uint8_t v___x_3589_; 
v___x_3589_ = lean_nat_dec_le(v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; lean_object* v_a_3591_; 
v___x_3590_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3583_, v_t_u2081_3584_, v_t_u2082_3585_);
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref(v___x_3590_);
return v_a_3591_;
}
else
{
lean_object* v___x_3592_; lean_object* v_a_3593_; 
v___x_3592_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3583_, v_t_u2082_3585_, v_t_u2081_3584_);
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref(v___x_3592_);
return v_a_3593_;
}
}
v___jp_3594_:
{
if (lean_obj_tag(v_t_u2082_3585_) == 0)
{
lean_object* v_size_3596_; 
v_size_3596_ = lean_ctor_get(v_t_u2082_3585_, 0);
lean_inc(v_size_3596_);
v___y_3587_ = v___y_3595_;
v___y_3588_ = v_size_3596_;
goto v___jp_3586_;
}
else
{
lean_object* v___x_3597_; 
v___x_3597_ = lean_unsigned_to_nat(0u);
v___y_3587_ = v___y_3595_;
v___y_3588_ = v___x_3597_;
goto v___jp_3586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union___redArg(lean_object* v_cmp_3600_, lean_object* v_t_u2081_3601_, lean_object* v_t_u2082_3602_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3600_, v_t_u2081_3601_, v_t_u2082_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union(lean_object* v_00_u03b1_3604_, lean_object* v_00_u03b2_3605_, lean_object* v_cmp_3606_, lean_object* v_t_u2081_3607_, lean_object* v_t_u2082_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3606_, v_t_u2081_3607_, v_t_u2082_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0(lean_object* v_00_u03b1_3610_, lean_object* v_cmp_3611_, lean_object* v_00_u03b2_3612_, lean_object* v_t_u2081_3613_, lean_object* v_t_u2082_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3611_, v_t_u2081_3613_, v_t_u2082_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3616_, lean_object* v_00_u03b2_3617_, lean_object* v_msg_3618_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v_msg_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0(lean_object* v_00_u03b1_3620_, lean_object* v_cmp_3621_, lean_object* v_00_u03b2_3622_, lean_object* v_k_3623_, lean_object* v_v_3624_, lean_object* v_t_3625_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3621_, v_k_3623_, v_v_3624_, v_t_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1(lean_object* v_00_u03b1_3627_, lean_object* v_cmp_3628_, lean_object* v_00_u03b2_3629_, lean_object* v_k_3630_, lean_object* v_t_3631_){
_start:
{
uint8_t v___x_3632_; 
v___x_3632_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3628_, v_k_3630_, v_t_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3633_, lean_object* v_cmp_3634_, lean_object* v_00_u03b2_3635_, lean_object* v_k_3636_, lean_object* v_t_3637_){
_start:
{
uint8_t v_res_3638_; lean_object* v_r_3639_; 
v_res_3638_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1(v_00_u03b1_3633_, v_cmp_3634_, v_00_u03b2_3635_, v_k_3636_, v_t_3637_);
v_r_3639_ = lean_box(v_res_3638_);
return v_r_3639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2(lean_object* v_00_u03b1_3640_, lean_object* v_00_u03b2_3641_, lean_object* v_cmp_3642_, lean_object* v_init_3643_, lean_object* v_x_3644_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3642_, v_init_3643_, v_x_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3(lean_object* v_00_u03b1_3646_, lean_object* v_00_u03b2_3647_, lean_object* v_cmp_3648_, lean_object* v_init_3649_, lean_object* v_x_3650_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3648_, v_init_3649_, v_x_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion___redArg(lean_object* v_cmp_3652_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_3653_, 0, lean_box(0));
lean_closure_set(v___x_3653_, 1, lean_box(0));
lean_closure_set(v___x_3653_, 2, v_cmp_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion(lean_object* v_00_u03b1_3654_, lean_object* v_00_u03b2_3655_, lean_object* v_cmp_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_3657_, 0, lean_box(0));
lean_closure_set(v___x_3657_, 1, lean_box(0));
lean_closure_set(v___x_3657_, 2, v_cmp_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(lean_object* v_cmp_3658_, lean_object* v_k_3659_, lean_object* v_v_3660_, lean_object* v_t_3661_){
_start:
{
if (lean_obj_tag(v_t_3661_) == 0)
{
lean_object* v_size_3662_; lean_object* v_k_3663_; lean_object* v_v_3664_; lean_object* v_l_3665_; lean_object* v_r_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3947_; 
v_size_3662_ = lean_ctor_get(v_t_3661_, 0);
v_k_3663_ = lean_ctor_get(v_t_3661_, 1);
v_v_3664_ = lean_ctor_get(v_t_3661_, 2);
v_l_3665_ = lean_ctor_get(v_t_3661_, 3);
v_r_3666_ = lean_ctor_get(v_t_3661_, 4);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_t_3661_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3668_ = v_t_3661_;
v_isShared_3669_ = v_isSharedCheck_3947_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_r_3666_);
lean_inc(v_l_3665_);
lean_inc(v_v_3664_);
lean_inc(v_k_3663_);
lean_inc(v_size_3662_);
lean_dec(v_t_3661_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3947_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3670_; uint8_t v___x_3671_; 
lean_inc_ref(v_cmp_3658_);
lean_inc(v_k_3663_);
lean_inc(v_k_3659_);
v___x_3670_ = lean_apply_2(v_cmp_3658_, v_k_3659_, v_k_3663_);
v___x_3671_ = lean_unbox(v___x_3670_);
switch(v___x_3671_)
{
case 0:
{
lean_object* v_impl_3672_; lean_object* v___x_3673_; 
lean_dec(v_size_3662_);
v_impl_3672_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3658_, v_k_3659_, v_v_3660_, v_l_3665_);
v___x_3673_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3666_) == 0)
{
lean_object* v_size_3674_; lean_object* v_size_3675_; lean_object* v_k_3676_; lean_object* v_v_3677_; lean_object* v_l_3678_; lean_object* v_r_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v_size_3674_ = lean_ctor_get(v_r_3666_, 0);
v_size_3675_ = lean_ctor_get(v_impl_3672_, 0);
v_k_3676_ = lean_ctor_get(v_impl_3672_, 1);
v_v_3677_ = lean_ctor_get(v_impl_3672_, 2);
v_l_3678_ = lean_ctor_get(v_impl_3672_, 3);
v_r_3679_ = lean_ctor_get(v_impl_3672_, 4);
lean_inc(v_r_3679_);
v___x_3680_ = lean_unsigned_to_nat(3u);
v___x_3681_ = lean_nat_mul(v___x_3680_, v_size_3674_);
v___x_3682_ = lean_nat_dec_lt(v___x_3681_, v_size_3675_);
lean_dec(v___x_3681_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3686_; 
lean_dec(v_r_3679_);
v___x_3683_ = lean_nat_add(v___x_3673_, v_size_3675_);
v___x_3684_ = lean_nat_add(v___x_3683_, v_size_3674_);
lean_dec(v___x_3683_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 3, v_impl_3672_);
lean_ctor_set(v___x_3668_, 0, v___x_3684_);
v___x_3686_ = v___x_3668_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3687_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3687_, 3, v_impl_3672_);
lean_ctor_set(v_reuseFailAlloc_3687_, 4, v_r_3666_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
else
{
lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3753_; 
lean_inc(v_l_3678_);
lean_inc(v_v_3677_);
lean_inc(v_k_3676_);
lean_inc(v_size_3675_);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_impl_3672_);
if (v_isSharedCheck_3753_ == 0)
{
lean_object* v_unused_3754_; lean_object* v_unused_3755_; lean_object* v_unused_3756_; lean_object* v_unused_3757_; lean_object* v_unused_3758_; 
v_unused_3754_ = lean_ctor_get(v_impl_3672_, 4);
lean_dec(v_unused_3754_);
v_unused_3755_ = lean_ctor_get(v_impl_3672_, 3);
lean_dec(v_unused_3755_);
v_unused_3756_ = lean_ctor_get(v_impl_3672_, 2);
lean_dec(v_unused_3756_);
v_unused_3757_ = lean_ctor_get(v_impl_3672_, 1);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_impl_3672_, 0);
lean_dec(v_unused_3758_);
v___x_3689_ = v_impl_3672_;
v_isShared_3690_ = v_isSharedCheck_3753_;
goto v_resetjp_3688_;
}
else
{
lean_dec(v_impl_3672_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3753_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v_size_3691_; lean_object* v_size_3692_; lean_object* v_k_3693_; lean_object* v_v_3694_; lean_object* v_l_3695_; lean_object* v_r_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; 
v_size_3691_ = lean_ctor_get(v_l_3678_, 0);
v_size_3692_ = lean_ctor_get(v_r_3679_, 0);
v_k_3693_ = lean_ctor_get(v_r_3679_, 1);
v_v_3694_ = lean_ctor_get(v_r_3679_, 2);
v_l_3695_ = lean_ctor_get(v_r_3679_, 3);
v_r_3696_ = lean_ctor_get(v_r_3679_, 4);
v___x_3697_ = lean_unsigned_to_nat(2u);
v___x_3698_ = lean_nat_mul(v___x_3697_, v_size_3691_);
v___x_3699_ = lean_nat_dec_lt(v_size_3692_, v___x_3698_);
lean_dec(v___x_3698_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3728_; 
lean_inc(v_r_3696_);
lean_inc(v_l_3695_);
lean_inc(v_v_3694_);
lean_inc(v_k_3693_);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_r_3679_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; lean_object* v_unused_3730_; lean_object* v_unused_3731_; lean_object* v_unused_3732_; lean_object* v_unused_3733_; 
v_unused_3729_ = lean_ctor_get(v_r_3679_, 4);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v_r_3679_, 3);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_r_3679_, 2);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_r_3679_, 1);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_r_3679_, 0);
lean_dec(v_unused_3733_);
v___x_3701_ = v_r_3679_;
v_isShared_3702_ = v_isSharedCheck_3728_;
goto v_resetjp_3700_;
}
else
{
lean_dec(v_r_3679_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3728_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___x_3716_; lean_object* v___y_3718_; 
v___x_3703_ = lean_nat_add(v___x_3673_, v_size_3675_);
lean_dec(v_size_3675_);
v___x_3704_ = lean_nat_add(v___x_3703_, v_size_3674_);
lean_dec(v___x_3703_);
v___x_3716_ = lean_nat_add(v___x_3673_, v_size_3691_);
if (lean_obj_tag(v_l_3695_) == 0)
{
lean_object* v_size_3726_; 
v_size_3726_ = lean_ctor_get(v_l_3695_, 0);
lean_inc(v_size_3726_);
v___y_3718_ = v_size_3726_;
goto v___jp_3717_;
}
else
{
lean_object* v___x_3727_; 
v___x_3727_ = lean_unsigned_to_nat(0u);
v___y_3718_ = v___x_3727_;
goto v___jp_3717_;
}
v___jp_3705_:
{
lean_object* v___x_3709_; lean_object* v___x_3711_; 
v___x_3709_ = lean_nat_add(v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec(v___y_3707_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 4, v_r_3666_);
lean_ctor_set(v___x_3701_, 3, v_r_3696_);
lean_ctor_set(v___x_3701_, 2, v_v_3664_);
lean_ctor_set(v___x_3701_, 1, v_k_3663_);
lean_ctor_set(v___x_3701_, 0, v___x_3709_);
v___x_3711_ = v___x_3701_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3709_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3715_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3715_, 3, v_r_3696_);
lean_ctor_set(v_reuseFailAlloc_3715_, 4, v_r_3666_);
v___x_3711_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3713_; 
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 4, v___x_3711_);
lean_ctor_set(v___x_3689_, 3, v___y_3706_);
lean_ctor_set(v___x_3689_, 2, v_v_3694_);
lean_ctor_set(v___x_3689_, 1, v_k_3693_);
lean_ctor_set(v___x_3689_, 0, v___x_3704_);
v___x_3713_ = v___x_3689_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_k_3693_);
lean_ctor_set(v_reuseFailAlloc_3714_, 2, v_v_3694_);
lean_ctor_set(v_reuseFailAlloc_3714_, 3, v___y_3706_);
lean_ctor_set(v_reuseFailAlloc_3714_, 4, v___x_3711_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
v___jp_3717_:
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
v___x_3719_ = lean_nat_add(v___x_3716_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec(v___x_3716_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 4, v_l_3695_);
lean_ctor_set(v___x_3668_, 3, v_l_3678_);
lean_ctor_set(v___x_3668_, 2, v_v_3677_);
lean_ctor_set(v___x_3668_, 1, v_k_3676_);
lean_ctor_set(v___x_3668_, 0, v___x_3719_);
v___x_3721_ = v___x_3668_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v_k_3676_);
lean_ctor_set(v_reuseFailAlloc_3725_, 2, v_v_3677_);
lean_ctor_set(v_reuseFailAlloc_3725_, 3, v_l_3678_);
lean_ctor_set(v_reuseFailAlloc_3725_, 4, v_l_3695_);
v___x_3721_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_nat_add(v___x_3673_, v_size_3674_);
if (lean_obj_tag(v_r_3696_) == 0)
{
lean_object* v_size_3723_; 
v_size_3723_ = lean_ctor_get(v_r_3696_, 0);
lean_inc(v_size_3723_);
v___y_3706_ = v___x_3721_;
v___y_3707_ = v___x_3722_;
v___y_3708_ = v_size_3723_;
goto v___jp_3705_;
}
else
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_unsigned_to_nat(0u);
v___y_3706_ = v___x_3721_;
v___y_3707_ = v___x_3722_;
v___y_3708_ = v___x_3724_;
goto v___jp_3705_;
}
}
}
}
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3739_; 
lean_del_object(v___x_3668_);
v___x_3734_ = lean_nat_add(v___x_3673_, v_size_3675_);
lean_dec(v_size_3675_);
v___x_3735_ = lean_nat_add(v___x_3734_, v_size_3674_);
lean_dec(v___x_3734_);
v___x_3736_ = lean_nat_add(v___x_3673_, v_size_3674_);
v___x_3737_ = lean_nat_add(v___x_3736_, v_size_3692_);
lean_dec(v___x_3736_);
lean_inc_ref(v_r_3666_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 4, v_r_3666_);
lean_ctor_set(v___x_3689_, 3, v_r_3679_);
lean_ctor_set(v___x_3689_, 2, v_v_3664_);
lean_ctor_set(v___x_3689_, 1, v_k_3663_);
lean_ctor_set(v___x_3689_, 0, v___x_3737_);
v___x_3739_ = v___x_3689_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3752_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3752_, 3, v_r_3679_);
lean_ctor_set(v_reuseFailAlloc_3752_, 4, v_r_3666_);
v___x_3739_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
v_isSharedCheck_3746_ = !lean_is_exclusive(v_r_3666_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; lean_object* v_unused_3748_; lean_object* v_unused_3749_; lean_object* v_unused_3750_; lean_object* v_unused_3751_; 
v_unused_3747_ = lean_ctor_get(v_r_3666_, 4);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_r_3666_, 3);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_r_3666_, 2);
lean_dec(v_unused_3749_);
v_unused_3750_ = lean_ctor_get(v_r_3666_, 1);
lean_dec(v_unused_3750_);
v_unused_3751_ = lean_ctor_get(v_r_3666_, 0);
lean_dec(v_unused_3751_);
v___x_3741_ = v_r_3666_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_dec(v_r_3666_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 4, v___x_3739_);
lean_ctor_set(v___x_3741_, 3, v_l_3678_);
lean_ctor_set(v___x_3741_, 2, v_v_3677_);
lean_ctor_set(v___x_3741_, 1, v_k_3676_);
lean_ctor_set(v___x_3741_, 0, v___x_3735_);
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_k_3676_);
lean_ctor_set(v_reuseFailAlloc_3745_, 2, v_v_3677_);
lean_ctor_set(v_reuseFailAlloc_3745_, 3, v_l_3678_);
lean_ctor_set(v_reuseFailAlloc_3745_, 4, v___x_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3759_; 
v_l_3759_ = lean_ctor_get(v_impl_3672_, 3);
if (lean_obj_tag(v_l_3759_) == 0)
{
lean_object* v_r_3760_; lean_object* v_k_3761_; lean_object* v_v_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3773_; 
lean_inc_ref(v_l_3759_);
v_r_3760_ = lean_ctor_get(v_impl_3672_, 4);
v_k_3761_ = lean_ctor_get(v_impl_3672_, 1);
v_v_3762_ = lean_ctor_get(v_impl_3672_, 2);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_impl_3672_);
if (v_isSharedCheck_3773_ == 0)
{
lean_object* v_unused_3774_; lean_object* v_unused_3775_; 
v_unused_3774_ = lean_ctor_get(v_impl_3672_, 3);
lean_dec(v_unused_3774_);
v_unused_3775_ = lean_ctor_get(v_impl_3672_, 0);
lean_dec(v_unused_3775_);
v___x_3764_ = v_impl_3672_;
v_isShared_3765_ = v_isSharedCheck_3773_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_r_3760_);
lean_inc(v_v_3762_);
lean_inc(v_k_3761_);
lean_dec(v_impl_3672_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3773_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3766_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3760_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 3, v_r_3760_);
lean_ctor_set(v___x_3764_, 2, v_v_3664_);
lean_ctor_set(v___x_3764_, 1, v_k_3663_);
lean_ctor_set(v___x_3764_, 0, v___x_3673_);
v___x_3768_ = v___x_3764_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3772_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3772_, 3, v_r_3760_);
lean_ctor_set(v_reuseFailAlloc_3772_, 4, v_r_3760_);
v___x_3768_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3770_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 4, v___x_3768_);
lean_ctor_set(v___x_3668_, 3, v_l_3759_);
lean_ctor_set(v___x_3668_, 2, v_v_3762_);
lean_ctor_set(v___x_3668_, 1, v_k_3761_);
lean_ctor_set(v___x_3668_, 0, v___x_3766_);
v___x_3770_ = v___x_3668_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v_k_3761_);
lean_ctor_set(v_reuseFailAlloc_3771_, 2, v_v_3762_);
lean_ctor_set(v_reuseFailAlloc_3771_, 3, v_l_3759_);
lean_ctor_set(v_reuseFailAlloc_3771_, 4, v___x_3768_);
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
lean_object* v_r_3776_; 
v_r_3776_ = lean_ctor_get(v_impl_3672_, 4);
lean_inc(v_r_3776_);
if (lean_obj_tag(v_r_3776_) == 0)
{
lean_object* v_k_3777_; lean_object* v_v_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3801_; 
lean_inc(v_l_3759_);
v_k_3777_ = lean_ctor_get(v_impl_3672_, 1);
v_v_3778_ = lean_ctor_get(v_impl_3672_, 2);
v_isSharedCheck_3801_ = !lean_is_exclusive(v_impl_3672_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; lean_object* v_unused_3803_; lean_object* v_unused_3804_; 
v_unused_3802_ = lean_ctor_get(v_impl_3672_, 4);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_impl_3672_, 3);
lean_dec(v_unused_3803_);
v_unused_3804_ = lean_ctor_get(v_impl_3672_, 0);
lean_dec(v_unused_3804_);
v___x_3780_ = v_impl_3672_;
v_isShared_3781_ = v_isSharedCheck_3801_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_v_3778_);
lean_inc(v_k_3777_);
lean_dec(v_impl_3672_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3801_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v_k_3782_; lean_object* v_v_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3797_; 
v_k_3782_ = lean_ctor_get(v_r_3776_, 1);
v_v_3783_ = lean_ctor_get(v_r_3776_, 2);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_r_3776_);
if (v_isSharedCheck_3797_ == 0)
{
lean_object* v_unused_3798_; lean_object* v_unused_3799_; lean_object* v_unused_3800_; 
v_unused_3798_ = lean_ctor_get(v_r_3776_, 4);
lean_dec(v_unused_3798_);
v_unused_3799_ = lean_ctor_get(v_r_3776_, 3);
lean_dec(v_unused_3799_);
v_unused_3800_ = lean_ctor_get(v_r_3776_, 0);
lean_dec(v_unused_3800_);
v___x_3785_ = v_r_3776_;
v_isShared_3786_ = v_isSharedCheck_3797_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_v_3783_);
lean_inc(v_k_3782_);
lean_dec(v_r_3776_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3797_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3787_ = lean_unsigned_to_nat(3u);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 4, v_l_3759_);
lean_ctor_set(v___x_3785_, 3, v_l_3759_);
lean_ctor_set(v___x_3785_, 2, v_v_3778_);
lean_ctor_set(v___x_3785_, 1, v_k_3777_);
lean_ctor_set(v___x_3785_, 0, v___x_3673_);
v___x_3789_ = v___x_3785_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_k_3777_);
lean_ctor_set(v_reuseFailAlloc_3796_, 2, v_v_3778_);
lean_ctor_set(v_reuseFailAlloc_3796_, 3, v_l_3759_);
lean_ctor_set(v_reuseFailAlloc_3796_, 4, v_l_3759_);
v___x_3789_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3791_; 
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 4, v_l_3759_);
lean_ctor_set(v___x_3780_, 2, v_v_3664_);
lean_ctor_set(v___x_3780_, 1, v_k_3663_);
lean_ctor_set(v___x_3780_, 0, v___x_3673_);
v___x_3791_ = v___x_3780_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3795_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3795_, 3, v_l_3759_);
lean_ctor_set(v_reuseFailAlloc_3795_, 4, v_l_3759_);
v___x_3791_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
lean_object* v___x_3793_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 4, v___x_3791_);
lean_ctor_set(v___x_3668_, 3, v___x_3789_);
lean_ctor_set(v___x_3668_, 2, v_v_3783_);
lean_ctor_set(v___x_3668_, 1, v_k_3782_);
lean_ctor_set(v___x_3668_, 0, v___x_3787_);
v___x_3793_ = v___x_3668_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3787_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_k_3782_);
lean_ctor_set(v_reuseFailAlloc_3794_, 2, v_v_3783_);
lean_ctor_set(v_reuseFailAlloc_3794_, 3, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3794_, 4, v___x_3791_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3805_ = lean_unsigned_to_nat(2u);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 4, v_r_3776_);
lean_ctor_set(v___x_3668_, 3, v_impl_3672_);
lean_ctor_set(v___x_3668_, 0, v___x_3805_);
v___x_3807_ = v___x_3668_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3808_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3808_, 3, v_impl_3672_);
lean_ctor_set(v_reuseFailAlloc_3808_, 4, v_r_3776_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3810_; 
lean_dec(v_v_3664_);
lean_dec(v_k_3663_);
lean_dec_ref(v_cmp_3658_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 2, v_v_3660_);
lean_ctor_set(v___x_3668_, 1, v_k_3659_);
v___x_3810_ = v___x_3668_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_size_3662_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v_k_3659_);
lean_ctor_set(v_reuseFailAlloc_3811_, 2, v_v_3660_);
lean_ctor_set(v_reuseFailAlloc_3811_, 3, v_l_3665_);
lean_ctor_set(v_reuseFailAlloc_3811_, 4, v_r_3666_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
default: 
{
lean_object* v_impl_3812_; lean_object* v___x_3813_; 
lean_dec(v_size_3662_);
v_impl_3812_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3658_, v_k_3659_, v_v_3660_, v_r_3666_);
v___x_3813_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3665_) == 0)
{
lean_object* v_size_3814_; lean_object* v_size_3815_; lean_object* v_k_3816_; lean_object* v_v_3817_; lean_object* v_l_3818_; lean_object* v_r_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v_size_3814_ = lean_ctor_get(v_l_3665_, 0);
v_size_3815_ = lean_ctor_get(v_impl_3812_, 0);
v_k_3816_ = lean_ctor_get(v_impl_3812_, 1);
v_v_3817_ = lean_ctor_get(v_impl_3812_, 2);
v_l_3818_ = lean_ctor_get(v_impl_3812_, 3);
lean_inc(v_l_3818_);
v_r_3819_ = lean_ctor_get(v_impl_3812_, 4);
v___x_3820_ = lean_unsigned_to_nat(3u);
v___x_3821_ = lean_nat_mul(v___x_3820_, v_size_3814_);
v___x_3822_ = lean_nat_dec_lt(v___x_3821_, v_size_3815_);
lean_dec(v___x_3821_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
lean_dec(v_l_3818_);
v___x_3823_ = lean_nat_add(v___x_3813_, v_size_3814_);
v___x_3824_ = lean_nat_add(v___x_3823_, v_size_3815_);
lean_dec(v___x_3823_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 4, v_impl_3812_);
lean_ctor_set(v___x_3668_, 0, v___x_3824_);
v___x_3826_ = v___x_3668_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3827_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3827_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3827_, 3, v_l_3665_);
lean_ctor_set(v_reuseFailAlloc_3827_, 4, v_impl_3812_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
else
{
lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3891_; 
lean_inc(v_r_3819_);
lean_inc(v_v_3817_);
lean_inc(v_k_3816_);
lean_inc(v_size_3815_);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_impl_3812_);
if (v_isSharedCheck_3891_ == 0)
{
lean_object* v_unused_3892_; lean_object* v_unused_3893_; lean_object* v_unused_3894_; lean_object* v_unused_3895_; lean_object* v_unused_3896_; 
v_unused_3892_ = lean_ctor_get(v_impl_3812_, 4);
lean_dec(v_unused_3892_);
v_unused_3893_ = lean_ctor_get(v_impl_3812_, 3);
lean_dec(v_unused_3893_);
v_unused_3894_ = lean_ctor_get(v_impl_3812_, 2);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_impl_3812_, 1);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_impl_3812_, 0);
lean_dec(v_unused_3896_);
v___x_3829_ = v_impl_3812_;
v_isShared_3830_ = v_isSharedCheck_3891_;
goto v_resetjp_3828_;
}
else
{
lean_dec(v_impl_3812_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3891_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v_size_3831_; lean_object* v_k_3832_; lean_object* v_v_3833_; lean_object* v_l_3834_; lean_object* v_r_3835_; lean_object* v_size_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; 
v_size_3831_ = lean_ctor_get(v_l_3818_, 0);
v_k_3832_ = lean_ctor_get(v_l_3818_, 1);
v_v_3833_ = lean_ctor_get(v_l_3818_, 2);
v_l_3834_ = lean_ctor_get(v_l_3818_, 3);
v_r_3835_ = lean_ctor_get(v_l_3818_, 4);
v_size_3836_ = lean_ctor_get(v_r_3819_, 0);
v___x_3837_ = lean_unsigned_to_nat(2u);
v___x_3838_ = lean_nat_mul(v___x_3837_, v_size_3836_);
v___x_3839_ = lean_nat_dec_lt(v_size_3831_, v___x_3838_);
lean_dec(v___x_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3867_; 
lean_inc(v_r_3835_);
lean_inc(v_l_3834_);
lean_inc(v_v_3833_);
lean_inc(v_k_3832_);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_l_3818_);
if (v_isSharedCheck_3867_ == 0)
{
lean_object* v_unused_3868_; lean_object* v_unused_3869_; lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; 
v_unused_3868_ = lean_ctor_get(v_l_3818_, 4);
lean_dec(v_unused_3868_);
v_unused_3869_ = lean_ctor_get(v_l_3818_, 3);
lean_dec(v_unused_3869_);
v_unused_3870_ = lean_ctor_get(v_l_3818_, 2);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_l_3818_, 1);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_l_3818_, 0);
lean_dec(v_unused_3872_);
v___x_3841_ = v_l_3818_;
v_isShared_3842_ = v_isSharedCheck_3867_;
goto v_resetjp_3840_;
}
else
{
lean_dec(v_l_3818_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3867_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3857_; 
v___x_3843_ = lean_nat_add(v___x_3813_, v_size_3814_);
v___x_3844_ = lean_nat_add(v___x_3843_, v_size_3815_);
lean_dec(v_size_3815_);
if (lean_obj_tag(v_l_3834_) == 0)
{
lean_object* v_size_3865_; 
v_size_3865_ = lean_ctor_get(v_l_3834_, 0);
lean_inc(v_size_3865_);
v___y_3857_ = v_size_3865_;
goto v___jp_3856_;
}
else
{
lean_object* v___x_3866_; 
v___x_3866_ = lean_unsigned_to_nat(0u);
v___y_3857_ = v___x_3866_;
goto v___jp_3856_;
}
v___jp_3845_:
{
lean_object* v___x_3849_; lean_object* v___x_3851_; 
v___x_3849_ = lean_nat_add(v___y_3846_, v___y_3848_);
lean_dec(v___y_3848_);
lean_dec(v___y_3846_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 4, v_r_3819_);
lean_ctor_set(v___x_3841_, 3, v_r_3835_);
lean_ctor_set(v___x_3841_, 2, v_v_3817_);
lean_ctor_set(v___x_3841_, 1, v_k_3816_);
lean_ctor_set(v___x_3841_, 0, v___x_3849_);
v___x_3851_ = v___x_3841_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3849_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_k_3816_);
lean_ctor_set(v_reuseFailAlloc_3855_, 2, v_v_3817_);
lean_ctor_set(v_reuseFailAlloc_3855_, 3, v_r_3835_);
lean_ctor_set(v_reuseFailAlloc_3855_, 4, v_r_3819_);
v___x_3851_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3853_; 
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 4, v___x_3851_);
lean_ctor_set(v___x_3829_, 3, v___y_3847_);
lean_ctor_set(v___x_3829_, 2, v_v_3833_);
lean_ctor_set(v___x_3829_, 1, v_k_3832_);
lean_ctor_set(v___x_3829_, 0, v___x_3844_);
v___x_3853_ = v___x_3829_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3844_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_k_3832_);
lean_ctor_set(v_reuseFailAlloc_3854_, 2, v_v_3833_);
lean_ctor_set(v_reuseFailAlloc_3854_, 3, v___y_3847_);
lean_ctor_set(v_reuseFailAlloc_3854_, 4, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
v___jp_3856_:
{
lean_object* v___x_3858_; lean_object* v___x_3860_; 
v___x_3858_ = lean_nat_add(v___x_3843_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec(v___x_3843_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 4, v_l_3834_);
lean_ctor_set(v___x_3668_, 0, v___x_3858_);
v___x_3860_ = v___x_3668_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3864_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3864_, 3, v_l_3665_);
lean_ctor_set(v_reuseFailAlloc_3864_, 4, v_l_3834_);
v___x_3860_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_nat_add(v___x_3813_, v_size_3836_);
if (lean_obj_tag(v_r_3835_) == 0)
{
lean_object* v_size_3862_; 
v_size_3862_ = lean_ctor_get(v_r_3835_, 0);
lean_inc(v_size_3862_);
v___y_3846_ = v___x_3861_;
v___y_3847_ = v___x_3860_;
v___y_3848_ = v_size_3862_;
goto v___jp_3845_;
}
else
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_unsigned_to_nat(0u);
v___y_3846_ = v___x_3861_;
v___y_3847_ = v___x_3860_;
v___y_3848_ = v___x_3863_;
goto v___jp_3845_;
}
}
}
}
}
else
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
lean_del_object(v___x_3668_);
v___x_3873_ = lean_nat_add(v___x_3813_, v_size_3814_);
v___x_3874_ = lean_nat_add(v___x_3873_, v_size_3815_);
lean_dec(v_size_3815_);
v___x_3875_ = lean_nat_add(v___x_3873_, v_size_3831_);
lean_dec(v___x_3873_);
lean_inc_ref(v_l_3665_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 4, v_l_3818_);
lean_ctor_set(v___x_3829_, 3, v_l_3665_);
lean_ctor_set(v___x_3829_, 2, v_v_3664_);
lean_ctor_set(v___x_3829_, 1, v_k_3663_);
lean_ctor_set(v___x_3829_, 0, v___x_3875_);
v___x_3877_ = v___x_3829_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3875_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3890_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3890_, 3, v_l_3665_);
lean_ctor_set(v_reuseFailAlloc_3890_, 4, v_l_3818_);
v___x_3877_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
v_isSharedCheck_3884_ = !lean_is_exclusive(v_l_3665_);
if (v_isSharedCheck_3884_ == 0)
{
lean_object* v_unused_3885_; lean_object* v_unused_3886_; lean_object* v_unused_3887_; lean_object* v_unused_3888_; lean_object* v_unused_3889_; 
v_unused_3885_ = lean_ctor_get(v_l_3665_, 4);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_l_3665_, 3);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_l_3665_, 2);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_l_3665_, 1);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_l_3665_, 0);
lean_dec(v_unused_3889_);
v___x_3879_ = v_l_3665_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_dec(v_l_3665_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 4, v_r_3819_);
lean_ctor_set(v___x_3879_, 3, v___x_3877_);
lean_ctor_set(v___x_3879_, 2, v_v_3817_);
lean_ctor_set(v___x_3879_, 1, v_k_3816_);
lean_ctor_set(v___x_3879_, 0, v___x_3874_);
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3874_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v_k_3816_);
lean_ctor_set(v_reuseFailAlloc_3883_, 2, v_v_3817_);
lean_ctor_set(v_reuseFailAlloc_3883_, 3, v___x_3877_);
lean_ctor_set(v_reuseFailAlloc_3883_, 4, v_r_3819_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3897_; 
v_l_3897_ = lean_ctor_get(v_impl_3812_, 3);
lean_inc(v_l_3897_);
if (lean_obj_tag(v_l_3897_) == 0)
{
lean_object* v_r_3898_; lean_object* v_k_3899_; lean_object* v_v_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3923_; 
v_r_3898_ = lean_ctor_get(v_impl_3812_, 4);
v_k_3899_ = lean_ctor_get(v_impl_3812_, 1);
v_v_3900_ = lean_ctor_get(v_impl_3812_, 2);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_impl_3812_);
if (v_isSharedCheck_3923_ == 0)
{
lean_object* v_unused_3924_; lean_object* v_unused_3925_; 
v_unused_3924_ = lean_ctor_get(v_impl_3812_, 3);
lean_dec(v_unused_3924_);
v_unused_3925_ = lean_ctor_get(v_impl_3812_, 0);
lean_dec(v_unused_3925_);
v___x_3902_ = v_impl_3812_;
v_isShared_3903_ = v_isSharedCheck_3923_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_r_3898_);
lean_inc(v_v_3900_);
lean_inc(v_k_3899_);
lean_dec(v_impl_3812_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3923_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v_k_3904_; lean_object* v_v_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3919_; 
v_k_3904_ = lean_ctor_get(v_l_3897_, 1);
v_v_3905_ = lean_ctor_get(v_l_3897_, 2);
v_isSharedCheck_3919_ = !lean_is_exclusive(v_l_3897_);
if (v_isSharedCheck_3919_ == 0)
{
lean_object* v_unused_3920_; lean_object* v_unused_3921_; lean_object* v_unused_3922_; 
v_unused_3920_ = lean_ctor_get(v_l_3897_, 4);
lean_dec(v_unused_3920_);
v_unused_3921_ = lean_ctor_get(v_l_3897_, 3);
lean_dec(v_unused_3921_);
v_unused_3922_ = lean_ctor_get(v_l_3897_, 0);
lean_dec(v_unused_3922_);
v___x_3907_ = v_l_3897_;
v_isShared_3908_ = v_isSharedCheck_3919_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_v_3905_);
lean_inc(v_k_3904_);
lean_dec(v_l_3897_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3919_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3909_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3898_, 2);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 4, v_r_3898_);
lean_ctor_set(v___x_3907_, 3, v_r_3898_);
lean_ctor_set(v___x_3907_, 2, v_v_3664_);
lean_ctor_set(v___x_3907_, 1, v_k_3663_);
lean_ctor_set(v___x_3907_, 0, v___x_3813_);
v___x_3911_ = v___x_3907_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3918_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3918_, 3, v_r_3898_);
lean_ctor_set(v_reuseFailAlloc_3918_, 4, v_r_3898_);
v___x_3911_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3913_; 
lean_inc(v_r_3898_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 3, v_r_3898_);
lean_ctor_set(v___x_3902_, 0, v___x_3813_);
v___x_3913_ = v___x_3902_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v_k_3899_);
lean_ctor_set(v_reuseFailAlloc_3917_, 2, v_v_3900_);
lean_ctor_set(v_reuseFailAlloc_3917_, 3, v_r_3898_);
lean_ctor_set(v_reuseFailAlloc_3917_, 4, v_r_3898_);
v___x_3913_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3915_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 4, v___x_3913_);
lean_ctor_set(v___x_3668_, 3, v___x_3911_);
lean_ctor_set(v___x_3668_, 2, v_v_3905_);
lean_ctor_set(v___x_3668_, 1, v_k_3904_);
lean_ctor_set(v___x_3668_, 0, v___x_3909_);
v___x_3915_ = v___x_3668_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3916_, 1, v_k_3904_);
lean_ctor_set(v_reuseFailAlloc_3916_, 2, v_v_3905_);
lean_ctor_set(v_reuseFailAlloc_3916_, 3, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3916_, 4, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
}
}
else
{
lean_object* v_r_3926_; 
v_r_3926_ = lean_ctor_get(v_impl_3812_, 4);
lean_inc(v_r_3926_);
if (lean_obj_tag(v_r_3926_) == 0)
{
lean_object* v_k_3927_; lean_object* v_v_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3939_; 
v_k_3927_ = lean_ctor_get(v_impl_3812_, 1);
v_v_3928_ = lean_ctor_get(v_impl_3812_, 2);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_impl_3812_);
if (v_isSharedCheck_3939_ == 0)
{
lean_object* v_unused_3940_; lean_object* v_unused_3941_; lean_object* v_unused_3942_; 
v_unused_3940_ = lean_ctor_get(v_impl_3812_, 4);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v_impl_3812_, 3);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v_impl_3812_, 0);
lean_dec(v_unused_3942_);
v___x_3930_ = v_impl_3812_;
v_isShared_3931_ = v_isSharedCheck_3939_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_v_3928_);
lean_inc(v_k_3927_);
lean_dec(v_impl_3812_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3939_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3932_ = lean_unsigned_to_nat(3u);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 4, v_l_3897_);
lean_ctor_set(v___x_3930_, 2, v_v_3664_);
lean_ctor_set(v___x_3930_, 1, v_k_3663_);
lean_ctor_set(v___x_3930_, 0, v___x_3813_);
v___x_3934_ = v___x_3930_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3938_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3938_, 3, v_l_3897_);
lean_ctor_set(v_reuseFailAlloc_3938_, 4, v_l_3897_);
v___x_3934_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3936_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 4, v_r_3926_);
lean_ctor_set(v___x_3668_, 3, v___x_3934_);
lean_ctor_set(v___x_3668_, 2, v_v_3928_);
lean_ctor_set(v___x_3668_, 1, v_k_3927_);
lean_ctor_set(v___x_3668_, 0, v___x_3932_);
v___x_3936_ = v___x_3668_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_k_3927_);
lean_ctor_set(v_reuseFailAlloc_3937_, 2, v_v_3928_);
lean_ctor_set(v_reuseFailAlloc_3937_, 3, v___x_3934_);
lean_ctor_set(v_reuseFailAlloc_3937_, 4, v_r_3926_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
else
{
lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3943_ = lean_unsigned_to_nat(2u);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 4, v_impl_3812_);
lean_ctor_set(v___x_3668_, 3, v_r_3926_);
lean_ctor_set(v___x_3668_, 0, v___x_3943_);
v___x_3945_ = v___x_3668_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3943_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3946_, 3, v_r_3926_);
lean_ctor_set(v_reuseFailAlloc_3946_, 4, v_impl_3812_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
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
lean_object* v___x_3948_; lean_object* v___x_3949_; 
lean_dec_ref(v_cmp_3658_);
v___x_3948_ = lean_unsigned_to_nat(1u);
v___x_3949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
lean_ctor_set(v___x_3949_, 1, v_k_3659_);
lean_ctor_set(v___x_3949_, 2, v_v_3660_);
lean_ctor_set(v___x_3949_, 3, v_t_3661_);
lean_ctor_set(v___x_3949_, 4, v_t_3661_);
return v___x_3949_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_3950_, lean_object* v_t_3951_, lean_object* v_k_3952_){
_start:
{
if (lean_obj_tag(v_t_3951_) == 0)
{
lean_object* v_k_3953_; lean_object* v_v_3954_; lean_object* v_l_3955_; lean_object* v_r_3956_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
v_k_3953_ = lean_ctor_get(v_t_3951_, 1);
lean_inc_n(v_k_3953_, 2);
v_v_3954_ = lean_ctor_get(v_t_3951_, 2);
lean_inc(v_v_3954_);
v_l_3955_ = lean_ctor_get(v_t_3951_, 3);
lean_inc(v_l_3955_);
v_r_3956_ = lean_ctor_get(v_t_3951_, 4);
lean_inc(v_r_3956_);
lean_dec_ref_known(v_t_3951_, 5);
lean_inc_ref(v_cmp_3950_);
lean_inc(v_k_3952_);
v___x_3957_ = lean_apply_2(v_cmp_3950_, v_k_3952_, v_k_3953_);
v___x_3958_ = lean_unbox(v___x_3957_);
switch(v___x_3958_)
{
case 0:
{
lean_dec(v_r_3956_);
lean_dec(v_v_3954_);
lean_dec(v_k_3953_);
v_t_3951_ = v_l_3955_;
goto _start;
}
case 1:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
lean_dec(v_r_3956_);
lean_dec(v_l_3955_);
lean_dec(v_k_3952_);
lean_dec_ref(v_cmp_3950_);
v___x_3960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3960_, 0, v_k_3953_);
lean_ctor_set(v___x_3960_, 1, v_v_3954_);
v___x_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
return v___x_3961_;
}
default: 
{
lean_dec(v_l_3955_);
lean_dec(v_v_3954_);
lean_dec(v_k_3953_);
v_t_3951_ = v_r_3956_;
goto _start;
}
}
}
else
{
lean_object* v___x_3963_; 
lean_dec(v_k_3952_);
lean_dec_ref(v_cmp_3950_);
v___x_3963_ = lean_box(0);
return v___x_3963_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_cmp_3964_, lean_object* v_m_u2081_3965_, lean_object* v_init_3966_, lean_object* v_x_3967_){
_start:
{
if (lean_obj_tag(v_x_3967_) == 0)
{
lean_object* v_k_3968_; lean_object* v_l_3969_; lean_object* v_r_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v_k_3968_ = lean_ctor_get(v_x_3967_, 1);
lean_inc(v_k_3968_);
v_l_3969_ = lean_ctor_get(v_x_3967_, 3);
lean_inc(v_l_3969_);
v_r_3970_ = lean_ctor_get(v_x_3967_, 4);
lean_inc(v_r_3970_);
lean_dec_ref_known(v_x_3967_, 5);
lean_inc_n(v_m_u2081_3965_, 2);
lean_inc_ref_n(v_cmp_3964_, 2);
v___x_3971_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3964_, v_m_u2081_3965_, v_init_3966_, v_l_3969_);
v___x_3972_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3964_, v_m_u2081_3965_, v_k_3968_);
if (lean_obj_tag(v___x_3972_) == 0)
{
v_init_3966_ = v___x_3971_;
v_x_3967_ = v_r_3970_;
goto _start;
}
else
{
lean_object* v_val_3974_; lean_object* v_fst_3975_; lean_object* v_snd_3976_; lean_object* v_impl_3977_; 
v_val_3974_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_val_3974_);
lean_dec_ref_known(v___x_3972_, 1);
v_fst_3975_ = lean_ctor_get(v_val_3974_, 0);
lean_inc(v_fst_3975_);
v_snd_3976_ = lean_ctor_get(v_val_3974_, 1);
lean_inc(v_snd_3976_);
lean_dec(v_val_3974_);
lean_inc_ref(v_cmp_3964_);
v_impl_3977_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3964_, v_fst_3975_, v_snd_3976_, v___x_3971_);
v_init_3966_ = v_impl_3977_;
v_x_3967_ = v_r_3970_;
goto _start;
}
}
else
{
lean_dec(v_m_u2081_3965_);
lean_dec_ref(v_cmp_3964_);
return v_init_3966_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(lean_object* v_cmp_3979_, lean_object* v_m_u2081_3980_, lean_object* v_m_u2082_3981_){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3982_ = lean_box(1);
v___x_3983_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3979_, v_m_u2081_3980_, v___x_3982_, v_m_u2082_3981_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(lean_object* v_cmp_3984_, lean_object* v_m_u2082_3985_, lean_object* v_t_3986_){
_start:
{
if (lean_obj_tag(v_t_3986_) == 0)
{
lean_object* v_k_3987_; lean_object* v_v_3988_; lean_object* v_l_3989_; lean_object* v_r_3990_; uint8_t v___x_3991_; 
v_k_3987_ = lean_ctor_get(v_t_3986_, 1);
lean_inc_n(v_k_3987_, 2);
v_v_3988_ = lean_ctor_get(v_t_3986_, 2);
lean_inc(v_v_3988_);
v_l_3989_ = lean_ctor_get(v_t_3986_, 3);
lean_inc(v_l_3989_);
v_r_3990_ = lean_ctor_get(v_t_3986_, 4);
lean_inc(v_r_3990_);
lean_dec_ref_known(v_t_3986_, 5);
lean_inc(v_m_u2082_3985_);
lean_inc_ref(v_cmp_3984_);
v___x_3991_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3984_, v_k_3987_, v_m_u2082_3985_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec(v_v_3988_);
lean_dec(v_k_3987_);
lean_inc(v_m_u2082_3985_);
lean_inc_ref(v_cmp_3984_);
v___x_3992_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3984_, v_m_u2082_3985_, v_l_3989_);
v___x_3993_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3984_, v_m_u2082_3985_, v_r_3990_);
v___x_3994_ = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(v___x_3992_, v___x_3993_);
return v___x_3994_;
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
lean_inc(v_m_u2082_3985_);
lean_inc_ref(v_cmp_3984_);
v___x_3995_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3984_, v_m_u2082_3985_, v_l_3989_);
v___x_3996_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3984_, v_m_u2082_3985_, v_r_3990_);
v___x_3997_ = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(v_k_3987_, v_v_3988_, v___x_3995_, v___x_3996_);
return v___x_3997_;
}
}
else
{
lean_dec(v_m_u2082_3985_);
lean_dec_ref(v_cmp_3984_);
return v_t_3986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(lean_object* v_cmp_3998_, lean_object* v_m_u2081_3999_, lean_object* v_m_u2082_4000_){
_start:
{
lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4008_; 
if (lean_obj_tag(v_m_u2081_3999_) == 0)
{
lean_object* v_size_4011_; 
v_size_4011_ = lean_ctor_get(v_m_u2081_3999_, 0);
lean_inc(v_size_4011_);
v___y_4008_ = v_size_4011_;
goto v___jp_4007_;
}
else
{
lean_object* v___x_4012_; 
v___x_4012_ = lean_unsigned_to_nat(0u);
v___y_4008_ = v___x_4012_;
goto v___jp_4007_;
}
v___jp_4001_:
{
uint8_t v___x_4004_; 
v___x_4004_ = lean_nat_dec_le(v___y_4002_, v___y_4003_);
lean_dec(v___y_4003_);
lean_dec(v___y_4002_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4005_; 
v___x_4005_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(v_cmp_3998_, v_m_u2081_3999_, v_m_u2082_4000_);
return v___x_4005_;
}
else
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_3998_, v_m_u2082_4000_, v_m_u2081_3999_);
return v___x_4006_;
}
}
v___jp_4007_:
{
if (lean_obj_tag(v_m_u2082_4000_) == 0)
{
lean_object* v_size_4009_; 
v_size_4009_ = lean_ctor_get(v_m_u2082_4000_, 0);
lean_inc(v_size_4009_);
v___y_4002_ = v___y_4008_;
v___y_4003_ = v_size_4009_;
goto v___jp_4001_;
}
else
{
lean_object* v___x_4010_; 
v___x_4010_ = lean_unsigned_to_nat(0u);
v___y_4002_ = v___y_4008_;
v___y_4003_ = v___x_4010_;
goto v___jp_4001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter___redArg(lean_object* v_cmp_4013_, lean_object* v_t_u2081_4014_, lean_object* v_t_u2082_4015_){
_start:
{
lean_object* v___x_4016_; 
v___x_4016_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_4013_, v_t_u2081_4014_, v_t_u2082_4015_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter(lean_object* v_00_u03b1_4017_, lean_object* v_00_u03b2_4018_, lean_object* v_cmp_4019_, lean_object* v_t_u2081_4020_, lean_object* v_t_u2082_4021_){
_start:
{
lean_object* v___x_4022_; 
v___x_4022_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_4019_, v_t_u2081_4020_, v_t_u2082_4021_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0(lean_object* v_00_u03b1_4023_, lean_object* v_cmp_4024_, lean_object* v_00_u03b2_4025_, lean_object* v_m_u2081_4026_, lean_object* v_m_u2082_4027_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_4024_, v_m_u2081_4026_, v_m_u2082_4027_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0(lean_object* v_00_u03b1_4029_, lean_object* v_cmp_4030_, lean_object* v_00_u03b2_4031_, lean_object* v_m_u2081_4032_, lean_object* v_m_u2082_4033_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(v_cmp_4030_, v_m_u2081_4032_, v_m_u2082_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1(lean_object* v_00_u03b1_4035_, lean_object* v_00_u03b2_4036_, lean_object* v_cmp_4037_, lean_object* v_m_u2082_4038_, lean_object* v_t_4039_){
_start:
{
lean_object* v___x_4040_; 
v___x_4040_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_4037_, v_m_u2082_4038_, v_t_4039_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4041_, lean_object* v_cmp_4042_, lean_object* v_00_u03b2_4043_, lean_object* v_t_4044_, lean_object* v_k_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(v_cmp_4042_, v_t_4044_, v_k_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_4047_, lean_object* v_cmp_4048_, lean_object* v_00_u03b2_4049_, lean_object* v_k_4050_, lean_object* v_v_4051_, lean_object* v_t_4052_, lean_object* v_hl_4053_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_4048_, v_k_4050_, v_v_4051_, v_t_4052_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3___redArg(lean_object* v_cmp_4055_, lean_object* v_m_u2081_4056_, lean_object* v_init_4057_, lean_object* v_t_4058_){
_start:
{
lean_object* v___x_4059_; 
v___x_4059_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4055_, v_m_u2081_4056_, v_init_4057_, v_t_4058_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4060_, lean_object* v_00_u03b2_4061_, lean_object* v_cmp_4062_, lean_object* v_m_u2081_4063_, lean_object* v_init_4064_, lean_object* v_t_4065_){
_start:
{
lean_object* v___x_4066_; 
v___x_4066_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4062_, v_m_u2081_4063_, v_init_4064_, v_t_4065_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b1_4067_, lean_object* v_00_u03b2_4068_, lean_object* v_cmp_4069_, lean_object* v_m_u2081_4070_, lean_object* v_init_4071_, lean_object* v_x_4072_){
_start:
{
lean_object* v___x_4073_; 
v___x_4073_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4069_, v_m_u2081_4070_, v_init_4071_, v_x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter___redArg(lean_object* v_cmp_4074_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_4075_, 0, lean_box(0));
lean_closure_set(v___x_4075_, 1, lean_box(0));
lean_closure_set(v___x_4075_, 2, v_cmp_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter(lean_object* v_00_u03b1_4076_, lean_object* v_00_u03b2_4077_, lean_object* v_cmp_4078_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_4079_, 0, lean_box(0));
lean_closure_set(v___x_4079_, 1, lean_box(0));
lean_closure_set(v___x_4079_, 2, v_cmp_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_beq___redArg(lean_object* v_cmp_4080_, lean_object* v_inst_4081_, lean_object* v_t_u2081_4082_, lean_object* v_t_u2082_4083_){
_start:
{
uint8_t v___x_4084_; 
v___x_4084_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_4080_, v_inst_4081_, v_t_u2081_4082_, v_t_u2082_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___redArg___boxed(lean_object* v_cmp_4085_, lean_object* v_inst_4086_, lean_object* v_t_u2081_4087_, lean_object* v_t_u2082_4088_){
_start:
{
uint8_t v_res_4089_; lean_object* v_r_4090_; 
v_res_4089_ = l_Std_DTreeMap_Raw_beq___redArg(v_cmp_4085_, v_inst_4086_, v_t_u2081_4087_, v_t_u2082_4088_);
v_r_4090_ = lean_box(v_res_4089_);
return v_r_4090_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_beq(lean_object* v_00_u03b1_4091_, lean_object* v_00_u03b2_4092_, lean_object* v_cmp_4093_, lean_object* v_inst_4094_, lean_object* v_inst_4095_, lean_object* v_t_u2081_4096_, lean_object* v_t_u2082_4097_){
_start:
{
uint8_t v___x_4098_; 
v___x_4098_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_4093_, v_inst_4095_, v_t_u2081_4096_, v_t_u2082_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___boxed(lean_object* v_00_u03b1_4099_, lean_object* v_00_u03b2_4100_, lean_object* v_cmp_4101_, lean_object* v_inst_4102_, lean_object* v_inst_4103_, lean_object* v_t_u2081_4104_, lean_object* v_t_u2082_4105_){
_start:
{
uint8_t v_res_4106_; lean_object* v_r_4107_; 
v_res_4106_ = l_Std_DTreeMap_Raw_beq(v_00_u03b1_4099_, v_00_u03b2_4100_, v_cmp_4101_, v_inst_4102_, v_inst_4103_, v_t_u2081_4104_, v_t_u2082_4105_);
v_r_4107_ = lean_box(v_res_4106_);
return v_r_4107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp___redArg(lean_object* v_cmp_4108_, lean_object* v_inst_4109_){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_4110_, 0, lean_box(0));
lean_closure_set(v___x_4110_, 1, lean_box(0));
lean_closure_set(v___x_4110_, 2, v_cmp_4108_);
lean_closure_set(v___x_4110_, 3, lean_box(0));
lean_closure_set(v___x_4110_, 4, v_inst_4109_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp(lean_object* v_00_u03b1_4111_, lean_object* v_00_u03b2_4112_, lean_object* v_cmp_4113_, lean_object* v_inst_4114_, lean_object* v_inst_4115_){
_start:
{
lean_object* v___x_4116_; 
v___x_4116_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_4116_, 0, lean_box(0));
lean_closure_set(v___x_4116_, 1, lean_box(0));
lean_closure_set(v___x_4116_, 2, v_cmp_4113_);
lean_closure_set(v___x_4116_, 3, lean_box(0));
lean_closure_set(v___x_4116_, 4, v_inst_4115_);
return v___x_4116_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___redArg(lean_object* v_cmp_4117_, lean_object* v_inst_4118_, lean_object* v_t_u2081_4119_, lean_object* v_t_u2082_4120_){
_start:
{
uint8_t v___x_4121_; 
v___x_4121_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_4117_, v_inst_4118_, v_t_u2081_4119_, v_t_u2082_4120_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___redArg___boxed(lean_object* v_cmp_4122_, lean_object* v_inst_4123_, lean_object* v_t_u2081_4124_, lean_object* v_t_u2082_4125_){
_start:
{
uint8_t v_res_4126_; lean_object* v_r_4127_; 
v_res_4126_ = l_Std_DTreeMap_Raw_Const_beq___redArg(v_cmp_4122_, v_inst_4123_, v_t_u2081_4124_, v_t_u2082_4125_);
v_r_4127_ = lean_box(v_res_4126_);
return v_r_4127_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq(lean_object* v_00_u03b1_4128_, lean_object* v_cmp_4129_, lean_object* v_00_u03b2_4130_, lean_object* v_inst_4131_, lean_object* v_t_u2081_4132_, lean_object* v_t_u2082_4133_){
_start:
{
uint8_t v___x_4134_; 
v___x_4134_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_4129_, v_inst_4131_, v_t_u2081_4132_, v_t_u2082_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___boxed(lean_object* v_00_u03b1_4135_, lean_object* v_cmp_4136_, lean_object* v_00_u03b2_4137_, lean_object* v_inst_4138_, lean_object* v_t_u2081_4139_, lean_object* v_t_u2082_4140_){
_start:
{
uint8_t v_res_4141_; lean_object* v_r_4142_; 
v_res_4141_ = l_Std_DTreeMap_Raw_Const_beq(v_00_u03b1_4135_, v_cmp_4136_, v_00_u03b2_4137_, v_inst_4138_, v_t_u2081_4139_, v_t_u2082_4140_);
v_r_4142_ = lean_box(v_res_4141_);
return v_r_4142_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(lean_object* v_cmp_4143_, lean_object* v_t_u2082_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v_t_4147_){
_start:
{
if (lean_obj_tag(v_t_4147_) == 0)
{
lean_object* v_k_4148_; lean_object* v_v_4149_; lean_object* v_l_4150_; lean_object* v_r_4151_; uint8_t v___x_4156_; 
v_k_4148_ = lean_ctor_get(v_t_4147_, 1);
lean_inc_n(v_k_4148_, 2);
v_v_4149_ = lean_ctor_get(v_t_4147_, 2);
lean_inc(v_v_4149_);
v_l_4150_ = lean_ctor_get(v_t_4147_, 3);
lean_inc(v_l_4150_);
v_r_4151_ = lean_ctor_get(v_t_4147_, 4);
lean_inc(v_r_4151_);
lean_dec_ref_known(v_t_4147_, 5);
lean_inc(v_t_u2082_4144_);
lean_inc_ref(v_cmp_4143_);
v___x_4156_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_4143_, v_k_4148_, v_t_u2082_4144_);
if (v___x_4156_ == 0)
{
uint8_t v___x_4157_; 
v___x_4157_ = lean_nat_dec_le(v___y_4145_, v___y_4146_);
if (v___x_4157_ == 0)
{
lean_dec(v_v_4149_);
lean_dec(v_k_4148_);
goto v___jp_4152_;
}
else
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_inc(v_t_u2082_4144_);
lean_inc_ref(v_cmp_4143_);
v___x_4158_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4143_, v_t_u2082_4144_, v___y_4145_, v___y_4146_, v_l_4150_);
v___x_4159_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4143_, v_t_u2082_4144_, v___y_4145_, v___y_4146_, v_r_4151_);
v___x_4160_ = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(v_k_4148_, v_v_4149_, v___x_4158_, v___x_4159_);
return v___x_4160_;
}
}
else
{
lean_dec(v_v_4149_);
lean_dec(v_k_4148_);
goto v___jp_4152_;
}
v___jp_4152_:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_inc(v_t_u2082_4144_);
lean_inc_ref(v_cmp_4143_);
v___x_4153_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4143_, v_t_u2082_4144_, v___y_4145_, v___y_4146_, v_l_4150_);
v___x_4154_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4143_, v_t_u2082_4144_, v___y_4145_, v___y_4146_, v_r_4151_);
v___x_4155_ = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(v___x_4153_, v___x_4154_);
return v___x_4155_;
}
}
else
{
lean_dec(v_t_u2082_4144_);
lean_dec_ref(v_cmp_4143_);
return v_t_4147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg___boxed(lean_object* v_cmp_4161_, lean_object* v_t_u2082_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v_t_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4161_, v_t_u2082_4162_, v___y_4163_, v___y_4164_, v_t_4165_);
lean_dec(v___y_4164_);
lean_dec(v___y_4163_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(lean_object* v_cmp_4167_, lean_object* v_k_4168_, lean_object* v_t_4169_){
_start:
{
if (lean_obj_tag(v_t_4169_) == 0)
{
lean_object* v_k_4170_; lean_object* v_v_4171_; lean_object* v_l_4172_; lean_object* v_r_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4863_; 
v_k_4170_ = lean_ctor_get(v_t_4169_, 1);
v_v_4171_ = lean_ctor_get(v_t_4169_, 2);
v_l_4172_ = lean_ctor_get(v_t_4169_, 3);
v_r_4173_ = lean_ctor_get(v_t_4169_, 4);
v_isSharedCheck_4863_ = !lean_is_exclusive(v_t_4169_);
if (v_isSharedCheck_4863_ == 0)
{
lean_object* v_unused_4864_; 
v_unused_4864_ = lean_ctor_get(v_t_4169_, 0);
lean_dec(v_unused_4864_);
v___x_4175_ = v_t_4169_;
v_isShared_4176_ = v_isSharedCheck_4863_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_r_4173_);
lean_inc(v_l_4172_);
lean_inc(v_v_4171_);
lean_inc(v_k_4170_);
lean_dec(v_t_4169_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4863_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4177_; uint8_t v___x_4178_; 
lean_inc_ref(v_cmp_4167_);
lean_inc(v_k_4170_);
lean_inc(v_k_4168_);
v___x_4177_ = lean_apply_2(v_cmp_4167_, v_k_4168_, v_k_4170_);
v___x_4178_ = lean_unbox(v___x_4177_);
switch(v___x_4178_)
{
case 0:
{
lean_object* v___x_4179_; 
v___x_4179_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4167_, v_k_4168_, v_l_4172_);
if (lean_obj_tag(v___x_4179_) == 0)
{
if (lean_obj_tag(v_r_4173_) == 0)
{
lean_object* v_size_4180_; lean_object* v_size_4181_; lean_object* v_k_4182_; lean_object* v_v_4183_; lean_object* v_l_4184_; lean_object* v_r_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; uint8_t v___x_4188_; 
v_size_4180_ = lean_ctor_get(v___x_4179_, 0);
v_size_4181_ = lean_ctor_get(v_r_4173_, 0);
v_k_4182_ = lean_ctor_get(v_r_4173_, 1);
v_v_4183_ = lean_ctor_get(v_r_4173_, 2);
v_l_4184_ = lean_ctor_get(v_r_4173_, 3);
lean_inc(v_l_4184_);
v_r_4185_ = lean_ctor_get(v_r_4173_, 4);
v___x_4186_ = lean_unsigned_to_nat(3u);
v___x_4187_ = lean_nat_mul(v___x_4186_, v_size_4180_);
v___x_4188_ = lean_nat_dec_lt(v___x_4187_, v_size_4181_);
lean_dec(v___x_4187_);
if (v___x_4188_ == 0)
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4193_; 
lean_dec(v_l_4184_);
v___x_4189_ = lean_unsigned_to_nat(1u);
v___x_4190_ = lean_nat_add(v___x_4189_, v_size_4180_);
v___x_4191_ = lean_nat_add(v___x_4190_, v_size_4181_);
lean_dec(v___x_4190_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 3, v___x_4179_);
lean_ctor_set(v___x_4175_, 0, v___x_4191_);
v___x_4193_ = v___x_4175_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4191_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4194_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4194_, 3, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4194_, 4, v_r_4173_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
else
{
lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4264_; 
lean_inc(v_r_4185_);
lean_inc(v_v_4183_);
lean_inc(v_k_4182_);
lean_inc(v_size_4181_);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_r_4173_);
if (v_isSharedCheck_4264_ == 0)
{
lean_object* v_unused_4265_; lean_object* v_unused_4266_; lean_object* v_unused_4267_; lean_object* v_unused_4268_; lean_object* v_unused_4269_; 
v_unused_4265_ = lean_ctor_get(v_r_4173_, 4);
lean_dec(v_unused_4265_);
v_unused_4266_ = lean_ctor_get(v_r_4173_, 3);
lean_dec(v_unused_4266_);
v_unused_4267_ = lean_ctor_get(v_r_4173_, 2);
lean_dec(v_unused_4267_);
v_unused_4268_ = lean_ctor_get(v_r_4173_, 1);
lean_dec(v_unused_4268_);
v_unused_4269_ = lean_ctor_get(v_r_4173_, 0);
lean_dec(v_unused_4269_);
v___x_4196_ = v_r_4173_;
v_isShared_4197_ = v_isSharedCheck_4264_;
goto v_resetjp_4195_;
}
else
{
lean_dec(v_r_4173_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4264_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
if (lean_obj_tag(v_l_4184_) == 0)
{
if (lean_obj_tag(v_r_4185_) == 0)
{
lean_object* v_size_4198_; lean_object* v_k_4199_; lean_object* v_v_4200_; lean_object* v_l_4201_; lean_object* v_r_4202_; lean_object* v_size_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; uint8_t v___x_4206_; 
v_size_4198_ = lean_ctor_get(v_l_4184_, 0);
v_k_4199_ = lean_ctor_get(v_l_4184_, 1);
v_v_4200_ = lean_ctor_get(v_l_4184_, 2);
v_l_4201_ = lean_ctor_get(v_l_4184_, 3);
v_r_4202_ = lean_ctor_get(v_l_4184_, 4);
v_size_4203_ = lean_ctor_get(v_r_4185_, 0);
v___x_4204_ = lean_unsigned_to_nat(2u);
v___x_4205_ = lean_nat_mul(v___x_4204_, v_size_4203_);
v___x_4206_ = lean_nat_dec_lt(v_size_4198_, v___x_4205_);
lean_dec(v___x_4205_);
if (v___x_4206_ == 0)
{
lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4235_; 
lean_inc(v_r_4202_);
lean_inc(v_l_4201_);
lean_inc(v_v_4200_);
lean_inc(v_k_4199_);
v_isSharedCheck_4235_ = !lean_is_exclusive(v_l_4184_);
if (v_isSharedCheck_4235_ == 0)
{
lean_object* v_unused_4236_; lean_object* v_unused_4237_; lean_object* v_unused_4238_; lean_object* v_unused_4239_; lean_object* v_unused_4240_; 
v_unused_4236_ = lean_ctor_get(v_l_4184_, 4);
lean_dec(v_unused_4236_);
v_unused_4237_ = lean_ctor_get(v_l_4184_, 3);
lean_dec(v_unused_4237_);
v_unused_4238_ = lean_ctor_get(v_l_4184_, 2);
lean_dec(v_unused_4238_);
v_unused_4239_ = lean_ctor_get(v_l_4184_, 1);
lean_dec(v_unused_4239_);
v_unused_4240_ = lean_ctor_get(v_l_4184_, 0);
lean_dec(v_unused_4240_);
v___x_4208_ = v_l_4184_;
v_isShared_4209_ = v_isSharedCheck_4235_;
goto v_resetjp_4207_;
}
else
{
lean_dec(v_l_4184_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4235_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4225_; 
v___x_4210_ = lean_unsigned_to_nat(1u);
v___x_4211_ = lean_nat_add(v___x_4210_, v_size_4180_);
v___x_4212_ = lean_nat_add(v___x_4211_, v_size_4181_);
lean_dec(v_size_4181_);
if (lean_obj_tag(v_l_4201_) == 0)
{
lean_object* v_size_4233_; 
v_size_4233_ = lean_ctor_get(v_l_4201_, 0);
lean_inc(v_size_4233_);
v___y_4225_ = v_size_4233_;
goto v___jp_4224_;
}
else
{
lean_object* v___x_4234_; 
v___x_4234_ = lean_unsigned_to_nat(0u);
v___y_4225_ = v___x_4234_;
goto v___jp_4224_;
}
v___jp_4213_:
{
lean_object* v___x_4217_; lean_object* v___x_4219_; 
v___x_4217_ = lean_nat_add(v___y_4214_, v___y_4216_);
lean_dec(v___y_4216_);
lean_dec(v___y_4214_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 4, v_r_4185_);
lean_ctor_set(v___x_4208_, 3, v_r_4202_);
lean_ctor_set(v___x_4208_, 2, v_v_4183_);
lean_ctor_set(v___x_4208_, 1, v_k_4182_);
lean_ctor_set(v___x_4208_, 0, v___x_4217_);
v___x_4219_ = v___x_4208_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4217_);
lean_ctor_set(v_reuseFailAlloc_4223_, 1, v_k_4182_);
lean_ctor_set(v_reuseFailAlloc_4223_, 2, v_v_4183_);
lean_ctor_set(v_reuseFailAlloc_4223_, 3, v_r_4202_);
lean_ctor_set(v_reuseFailAlloc_4223_, 4, v_r_4185_);
v___x_4219_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
lean_object* v___x_4221_; 
if (v_isShared_4197_ == 0)
{
lean_ctor_set(v___x_4196_, 4, v___x_4219_);
lean_ctor_set(v___x_4196_, 3, v___y_4215_);
lean_ctor_set(v___x_4196_, 2, v_v_4200_);
lean_ctor_set(v___x_4196_, 1, v_k_4199_);
lean_ctor_set(v___x_4196_, 0, v___x_4212_);
v___x_4221_ = v___x_4196_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4212_);
lean_ctor_set(v_reuseFailAlloc_4222_, 1, v_k_4199_);
lean_ctor_set(v_reuseFailAlloc_4222_, 2, v_v_4200_);
lean_ctor_set(v_reuseFailAlloc_4222_, 3, v___y_4215_);
lean_ctor_set(v_reuseFailAlloc_4222_, 4, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
v___jp_4224_:
{
lean_object* v___x_4226_; lean_object* v___x_4228_; 
v___x_4226_ = lean_nat_add(v___x_4211_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec(v___x_4211_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v_l_4201_);
lean_ctor_set(v___x_4175_, 3, v___x_4179_);
lean_ctor_set(v___x_4175_, 0, v___x_4226_);
v___x_4228_ = v___x_4175_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4226_);
lean_ctor_set(v_reuseFailAlloc_4232_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4232_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4232_, 3, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4232_, 4, v_l_4201_);
v___x_4228_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
lean_object* v___x_4229_; 
v___x_4229_ = lean_nat_add(v___x_4210_, v_size_4203_);
if (lean_obj_tag(v_r_4202_) == 0)
{
lean_object* v_size_4230_; 
v_size_4230_ = lean_ctor_get(v_r_4202_, 0);
lean_inc(v_size_4230_);
v___y_4214_ = v___x_4229_;
v___y_4215_ = v___x_4228_;
v___y_4216_ = v_size_4230_;
goto v___jp_4213_;
}
else
{
lean_object* v___x_4231_; 
v___x_4231_ = lean_unsigned_to_nat(0u);
v___y_4214_ = v___x_4229_;
v___y_4215_ = v___x_4228_;
v___y_4216_ = v___x_4231_;
goto v___jp_4213_;
}
}
}
}
}
else
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4246_; 
lean_del_object(v___x_4175_);
v___x_4241_ = lean_unsigned_to_nat(1u);
v___x_4242_ = lean_nat_add(v___x_4241_, v_size_4180_);
v___x_4243_ = lean_nat_add(v___x_4242_, v_size_4181_);
lean_dec(v_size_4181_);
v___x_4244_ = lean_nat_add(v___x_4242_, v_size_4198_);
lean_dec(v___x_4242_);
lean_inc_ref(v___x_4179_);
if (v_isShared_4197_ == 0)
{
lean_ctor_set(v___x_4196_, 4, v_l_4184_);
lean_ctor_set(v___x_4196_, 3, v___x_4179_);
lean_ctor_set(v___x_4196_, 2, v_v_4171_);
lean_ctor_set(v___x_4196_, 1, v_k_4170_);
lean_ctor_set(v___x_4196_, 0, v___x_4244_);
v___x_4246_ = v___x_4196_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4244_);
lean_ctor_set(v_reuseFailAlloc_4259_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4259_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4259_, 3, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4259_, 4, v_l_4184_);
v___x_4246_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4253_ == 0)
{
lean_object* v_unused_4254_; lean_object* v_unused_4255_; lean_object* v_unused_4256_; lean_object* v_unused_4257_; lean_object* v_unused_4258_; 
v_unused_4254_ = lean_ctor_get(v___x_4179_, 4);
lean_dec(v_unused_4254_);
v_unused_4255_ = lean_ctor_get(v___x_4179_, 3);
lean_dec(v_unused_4255_);
v_unused_4256_ = lean_ctor_get(v___x_4179_, 2);
lean_dec(v_unused_4256_);
v_unused_4257_ = lean_ctor_get(v___x_4179_, 1);
lean_dec(v_unused_4257_);
v_unused_4258_ = lean_ctor_get(v___x_4179_, 0);
lean_dec(v_unused_4258_);
v___x_4248_ = v___x_4179_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_dec(v___x_4179_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
lean_ctor_set(v___x_4248_, 4, v_r_4185_);
lean_ctor_set(v___x_4248_, 3, v___x_4246_);
lean_ctor_set(v___x_4248_, 2, v_v_4183_);
lean_ctor_set(v___x_4248_, 1, v_k_4182_);
lean_ctor_set(v___x_4248_, 0, v___x_4243_);
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4243_);
lean_ctor_set(v_reuseFailAlloc_4252_, 1, v_k_4182_);
lean_ctor_set(v_reuseFailAlloc_4252_, 2, v_v_4183_);
lean_ctor_set(v_reuseFailAlloc_4252_, 3, v___x_4246_);
lean_ctor_set(v_reuseFailAlloc_4252_, 4, v_r_4185_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
else
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
lean_dec_ref_known(v_l_4184_, 5);
lean_del_object(v___x_4196_);
lean_dec(v_v_4183_);
lean_dec(v_k_4182_);
lean_dec(v_size_4181_);
lean_dec_ref_known(v___x_4179_, 5);
lean_del_object(v___x_4175_);
lean_dec(v_v_4171_);
lean_dec(v_k_4170_);
v___x_4260_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7);
v___x_4261_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4260_);
return v___x_4261_;
}
}
else
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
lean_del_object(v___x_4196_);
lean_dec(v_r_4185_);
lean_dec(v_v_4183_);
lean_dec(v_k_4182_);
lean_dec(v_size_4181_);
lean_dec_ref_known(v___x_4179_, 5);
lean_del_object(v___x_4175_);
lean_dec(v_v_4171_);
lean_dec(v_k_4170_);
v___x_4262_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8);
v___x_4263_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4262_);
return v___x_4263_;
}
}
}
}
else
{
lean_object* v_size_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4274_; 
v_size_4270_ = lean_ctor_get(v___x_4179_, 0);
v___x_4271_ = lean_unsigned_to_nat(1u);
v___x_4272_ = lean_nat_add(v___x_4271_, v_size_4270_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 3, v___x_4179_);
lean_ctor_set(v___x_4175_, 0, v___x_4272_);
v___x_4274_ = v___x_4175_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4272_);
lean_ctor_set(v_reuseFailAlloc_4275_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4275_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4275_, 3, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4275_, 4, v_r_4173_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
else
{
if (lean_obj_tag(v_r_4173_) == 0)
{
lean_object* v_l_4276_; 
v_l_4276_ = lean_ctor_get(v_r_4173_, 3);
lean_inc(v_l_4276_);
if (lean_obj_tag(v_l_4276_) == 0)
{
lean_object* v_r_4277_; 
v_r_4277_ = lean_ctor_get(v_r_4173_, 4);
lean_inc(v_r_4277_);
if (lean_obj_tag(v_r_4277_) == 0)
{
lean_object* v_size_4278_; lean_object* v_k_4279_; lean_object* v_v_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4294_; 
v_size_4278_ = lean_ctor_get(v_r_4173_, 0);
v_k_4279_ = lean_ctor_get(v_r_4173_, 1);
v_v_4280_ = lean_ctor_get(v_r_4173_, 2);
v_isSharedCheck_4294_ = !lean_is_exclusive(v_r_4173_);
if (v_isSharedCheck_4294_ == 0)
{
lean_object* v_unused_4295_; lean_object* v_unused_4296_; 
v_unused_4295_ = lean_ctor_get(v_r_4173_, 4);
lean_dec(v_unused_4295_);
v_unused_4296_ = lean_ctor_get(v_r_4173_, 3);
lean_dec(v_unused_4296_);
v___x_4282_ = v_r_4173_;
v_isShared_4283_ = v_isSharedCheck_4294_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_v_4280_);
lean_inc(v_k_4279_);
lean_inc(v_size_4278_);
lean_dec(v_r_4173_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4294_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v_size_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4289_; 
v_size_4284_ = lean_ctor_get(v_l_4276_, 0);
v___x_4285_ = lean_unsigned_to_nat(1u);
v___x_4286_ = lean_nat_add(v___x_4285_, v_size_4278_);
lean_dec(v_size_4278_);
v___x_4287_ = lean_nat_add(v___x_4285_, v_size_4284_);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 4, v_l_4276_);
lean_ctor_set(v___x_4282_, 3, v___x_4179_);
lean_ctor_set(v___x_4282_, 2, v_v_4171_);
lean_ctor_set(v___x_4282_, 1, v_k_4170_);
lean_ctor_set(v___x_4282_, 0, v___x_4287_);
v___x_4289_ = v___x_4282_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4287_);
lean_ctor_set(v_reuseFailAlloc_4293_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4293_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4293_, 3, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4293_, 4, v_l_4276_);
v___x_4289_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
lean_object* v___x_4291_; 
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v_r_4277_);
lean_ctor_set(v___x_4175_, 3, v___x_4289_);
lean_ctor_set(v___x_4175_, 2, v_v_4280_);
lean_ctor_set(v___x_4175_, 1, v_k_4279_);
lean_ctor_set(v___x_4175_, 0, v___x_4286_);
v___x_4291_ = v___x_4175_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v___x_4286_);
lean_ctor_set(v_reuseFailAlloc_4292_, 1, v_k_4279_);
lean_ctor_set(v_reuseFailAlloc_4292_, 2, v_v_4280_);
lean_ctor_set(v_reuseFailAlloc_4292_, 3, v___x_4289_);
lean_ctor_set(v_reuseFailAlloc_4292_, 4, v_r_4277_);
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
lean_object* v_k_4297_; lean_object* v_v_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4322_; 
v_k_4297_ = lean_ctor_get(v_r_4173_, 1);
v_v_4298_ = lean_ctor_get(v_r_4173_, 2);
v_isSharedCheck_4322_ = !lean_is_exclusive(v_r_4173_);
if (v_isSharedCheck_4322_ == 0)
{
lean_object* v_unused_4323_; lean_object* v_unused_4324_; lean_object* v_unused_4325_; 
v_unused_4323_ = lean_ctor_get(v_r_4173_, 4);
lean_dec(v_unused_4323_);
v_unused_4324_ = lean_ctor_get(v_r_4173_, 3);
lean_dec(v_unused_4324_);
v_unused_4325_ = lean_ctor_get(v_r_4173_, 0);
lean_dec(v_unused_4325_);
v___x_4300_ = v_r_4173_;
v_isShared_4301_ = v_isSharedCheck_4322_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_v_4298_);
lean_inc(v_k_4297_);
lean_dec(v_r_4173_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4322_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v_k_4302_; lean_object* v_v_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4318_; 
v_k_4302_ = lean_ctor_get(v_l_4276_, 1);
v_v_4303_ = lean_ctor_get(v_l_4276_, 2);
v_isSharedCheck_4318_ = !lean_is_exclusive(v_l_4276_);
if (v_isSharedCheck_4318_ == 0)
{
lean_object* v_unused_4319_; lean_object* v_unused_4320_; lean_object* v_unused_4321_; 
v_unused_4319_ = lean_ctor_get(v_l_4276_, 4);
lean_dec(v_unused_4319_);
v_unused_4320_ = lean_ctor_get(v_l_4276_, 3);
lean_dec(v_unused_4320_);
v_unused_4321_ = lean_ctor_get(v_l_4276_, 0);
lean_dec(v_unused_4321_);
v___x_4305_ = v_l_4276_;
v_isShared_4306_ = v_isSharedCheck_4318_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_v_4303_);
lean_inc(v_k_4302_);
lean_dec(v_l_4276_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4318_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4310_; 
v___x_4307_ = lean_unsigned_to_nat(3u);
v___x_4308_ = lean_unsigned_to_nat(1u);
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 4, v_r_4277_);
lean_ctor_set(v___x_4305_, 3, v_r_4277_);
lean_ctor_set(v___x_4305_, 2, v_v_4171_);
lean_ctor_set(v___x_4305_, 1, v_k_4170_);
lean_ctor_set(v___x_4305_, 0, v___x_4308_);
v___x_4310_ = v___x_4305_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4308_);
lean_ctor_set(v_reuseFailAlloc_4317_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4317_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4317_, 3, v_r_4277_);
lean_ctor_set(v_reuseFailAlloc_4317_, 4, v_r_4277_);
v___x_4310_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
lean_object* v___x_4312_; 
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 3, v_r_4277_);
lean_ctor_set(v___x_4300_, 0, v___x_4308_);
v___x_4312_ = v___x_4300_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4308_);
lean_ctor_set(v_reuseFailAlloc_4316_, 1, v_k_4297_);
lean_ctor_set(v_reuseFailAlloc_4316_, 2, v_v_4298_);
lean_ctor_set(v_reuseFailAlloc_4316_, 3, v_r_4277_);
lean_ctor_set(v_reuseFailAlloc_4316_, 4, v_r_4277_);
v___x_4312_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
lean_object* v___x_4314_; 
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v___x_4312_);
lean_ctor_set(v___x_4175_, 3, v___x_4310_);
lean_ctor_set(v___x_4175_, 2, v_v_4303_);
lean_ctor_set(v___x_4175_, 1, v_k_4302_);
lean_ctor_set(v___x_4175_, 0, v___x_4307_);
v___x_4314_ = v___x_4175_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4307_);
lean_ctor_set(v_reuseFailAlloc_4315_, 1, v_k_4302_);
lean_ctor_set(v_reuseFailAlloc_4315_, 2, v_v_4303_);
lean_ctor_set(v_reuseFailAlloc_4315_, 3, v___x_4310_);
lean_ctor_set(v_reuseFailAlloc_4315_, 4, v___x_4312_);
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
}
}
}
else
{
lean_object* v_r_4326_; 
v_r_4326_ = lean_ctor_get(v_r_4173_, 4);
lean_inc(v_r_4326_);
if (lean_obj_tag(v_r_4326_) == 0)
{
lean_object* v_k_4327_; lean_object* v_v_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4340_; 
v_k_4327_ = lean_ctor_get(v_r_4173_, 1);
v_v_4328_ = lean_ctor_get(v_r_4173_, 2);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_r_4173_);
if (v_isSharedCheck_4340_ == 0)
{
lean_object* v_unused_4341_; lean_object* v_unused_4342_; lean_object* v_unused_4343_; 
v_unused_4341_ = lean_ctor_get(v_r_4173_, 4);
lean_dec(v_unused_4341_);
v_unused_4342_ = lean_ctor_get(v_r_4173_, 3);
lean_dec(v_unused_4342_);
v_unused_4343_ = lean_ctor_get(v_r_4173_, 0);
lean_dec(v_unused_4343_);
v___x_4330_ = v_r_4173_;
v_isShared_4331_ = v_isSharedCheck_4340_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_v_4328_);
lean_inc(v_k_4327_);
lean_dec(v_r_4173_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4340_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4335_; 
v___x_4332_ = lean_unsigned_to_nat(3u);
v___x_4333_ = lean_unsigned_to_nat(1u);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 4, v_l_4276_);
lean_ctor_set(v___x_4330_, 2, v_v_4171_);
lean_ctor_set(v___x_4330_, 1, v_k_4170_);
lean_ctor_set(v___x_4330_, 0, v___x_4333_);
v___x_4335_ = v___x_4330_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v___x_4333_);
lean_ctor_set(v_reuseFailAlloc_4339_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4339_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4339_, 3, v_l_4276_);
lean_ctor_set(v_reuseFailAlloc_4339_, 4, v_l_4276_);
v___x_4335_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4337_; 
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v_r_4326_);
lean_ctor_set(v___x_4175_, 3, v___x_4335_);
lean_ctor_set(v___x_4175_, 2, v_v_4328_);
lean_ctor_set(v___x_4175_, 1, v_k_4327_);
lean_ctor_set(v___x_4175_, 0, v___x_4332_);
v___x_4337_ = v___x_4175_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4332_);
lean_ctor_set(v_reuseFailAlloc_4338_, 1, v_k_4327_);
lean_ctor_set(v_reuseFailAlloc_4338_, 2, v_v_4328_);
lean_ctor_set(v_reuseFailAlloc_4338_, 3, v___x_4335_);
lean_ctor_set(v_reuseFailAlloc_4338_, 4, v_r_4326_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
else
{
lean_object* v___x_4344_; lean_object* v___x_4346_; 
v___x_4344_ = lean_unsigned_to_nat(2u);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 3, v_r_4326_);
lean_ctor_set(v___x_4175_, 0, v___x_4344_);
v___x_4346_ = v___x_4175_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v___x_4344_);
lean_ctor_set(v_reuseFailAlloc_4347_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4347_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4347_, 3, v_r_4326_);
lean_ctor_set(v_reuseFailAlloc_4347_, 4, v_r_4173_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
}
else
{
lean_object* v___x_4348_; lean_object* v___x_4350_; 
v___x_4348_ = lean_unsigned_to_nat(1u);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 3, v_r_4173_);
lean_ctor_set(v___x_4175_, 0, v___x_4348_);
v___x_4350_ = v___x_4175_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4348_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4351_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4351_, 3, v_r_4173_);
lean_ctor_set(v_reuseFailAlloc_4351_, 4, v_r_4173_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
}
case 1:
{
lean_del_object(v___x_4175_);
lean_dec(v_v_4171_);
lean_dec(v_k_4170_);
lean_dec(v_k_4168_);
lean_dec_ref(v_cmp_4167_);
if (lean_obj_tag(v_l_4172_) == 0)
{
if (lean_obj_tag(v_r_4173_) == 0)
{
lean_object* v_size_4352_; lean_object* v_k_4353_; lean_object* v_v_4354_; lean_object* v_l_4355_; lean_object* v_r_4356_; lean_object* v_size_4357_; lean_object* v_k_4358_; lean_object* v_v_4359_; lean_object* v_l_4360_; lean_object* v_r_4361_; uint8_t v___x_4362_; 
v_size_4352_ = lean_ctor_get(v_l_4172_, 0);
v_k_4353_ = lean_ctor_get(v_l_4172_, 1);
v_v_4354_ = lean_ctor_get(v_l_4172_, 2);
v_l_4355_ = lean_ctor_get(v_l_4172_, 3);
v_r_4356_ = lean_ctor_get(v_l_4172_, 4);
lean_inc(v_r_4356_);
v_size_4357_ = lean_ctor_get(v_r_4173_, 0);
v_k_4358_ = lean_ctor_get(v_r_4173_, 1);
v_v_4359_ = lean_ctor_get(v_r_4173_, 2);
v_l_4360_ = lean_ctor_get(v_r_4173_, 3);
lean_inc(v_l_4360_);
v_r_4361_ = lean_ctor_get(v_r_4173_, 4);
v___x_4362_ = lean_nat_dec_lt(v_size_4352_, v_size_4357_);
if (v___x_4362_ == 0)
{
lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4514_; 
lean_inc(v_l_4355_);
lean_inc(v_v_4354_);
lean_inc(v_k_4353_);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_l_4172_);
if (v_isSharedCheck_4514_ == 0)
{
lean_object* v_unused_4515_; lean_object* v_unused_4516_; lean_object* v_unused_4517_; lean_object* v_unused_4518_; lean_object* v_unused_4519_; 
v_unused_4515_ = lean_ctor_get(v_l_4172_, 4);
lean_dec(v_unused_4515_);
v_unused_4516_ = lean_ctor_get(v_l_4172_, 3);
lean_dec(v_unused_4516_);
v_unused_4517_ = lean_ctor_get(v_l_4172_, 2);
lean_dec(v_unused_4517_);
v_unused_4518_ = lean_ctor_get(v_l_4172_, 1);
lean_dec(v_unused_4518_);
v_unused_4519_ = lean_ctor_get(v_l_4172_, 0);
lean_dec(v_unused_4519_);
v___x_4364_ = v_l_4172_;
v_isShared_4365_ = v_isSharedCheck_4514_;
goto v_resetjp_4363_;
}
else
{
lean_dec(v_l_4172_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4514_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v_d_4366_; lean_object* v_tree_4367_; 
v_d_4366_ = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(v_k_4353_, v_v_4354_, v_l_4355_, v_r_4356_);
v_tree_4367_ = lean_ctor_get(v_d_4366_, 2);
if (lean_obj_tag(v_tree_4367_) == 0)
{
lean_object* v_k_4368_; lean_object* v_v_4369_; lean_object* v_size_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; uint8_t v___x_4373_; 
lean_inc_ref(v_tree_4367_);
v_k_4368_ = lean_ctor_get(v_d_4366_, 0);
lean_inc(v_k_4368_);
v_v_4369_ = lean_ctor_get(v_d_4366_, 1);
lean_inc(v_v_4369_);
lean_dec_ref(v_d_4366_);
v_size_4370_ = lean_ctor_get(v_tree_4367_, 0);
v___x_4371_ = lean_unsigned_to_nat(3u);
v___x_4372_ = lean_nat_mul(v___x_4371_, v_size_4370_);
v___x_4373_ = lean_nat_dec_lt(v___x_4372_, v_size_4357_);
lean_dec(v___x_4372_);
if (v___x_4373_ == 0)
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4378_; 
lean_dec(v_l_4360_);
v___x_4374_ = lean_unsigned_to_nat(1u);
v___x_4375_ = lean_nat_add(v___x_4374_, v_size_4370_);
v___x_4376_ = lean_nat_add(v___x_4375_, v_size_4357_);
lean_dec(v___x_4375_);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 4, v_r_4173_);
lean_ctor_set(v___x_4364_, 3, v_tree_4367_);
lean_ctor_set(v___x_4364_, 2, v_v_4369_);
lean_ctor_set(v___x_4364_, 1, v_k_4368_);
lean_ctor_set(v___x_4364_, 0, v___x_4376_);
v___x_4378_ = v___x_4364_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v___x_4376_);
lean_ctor_set(v_reuseFailAlloc_4379_, 1, v_k_4368_);
lean_ctor_set(v_reuseFailAlloc_4379_, 2, v_v_4369_);
lean_ctor_set(v_reuseFailAlloc_4379_, 3, v_tree_4367_);
lean_ctor_set(v_reuseFailAlloc_4379_, 4, v_r_4173_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
else
{
lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4440_; 
lean_inc(v_r_4361_);
lean_inc(v_v_4359_);
lean_inc(v_k_4358_);
lean_inc(v_size_4357_);
v_isSharedCheck_4440_ = !lean_is_exclusive(v_r_4173_);
if (v_isSharedCheck_4440_ == 0)
{
lean_object* v_unused_4441_; lean_object* v_unused_4442_; lean_object* v_unused_4443_; lean_object* v_unused_4444_; lean_object* v_unused_4445_; 
v_unused_4441_ = lean_ctor_get(v_r_4173_, 4);
lean_dec(v_unused_4441_);
v_unused_4442_ = lean_ctor_get(v_r_4173_, 3);
lean_dec(v_unused_4442_);
v_unused_4443_ = lean_ctor_get(v_r_4173_, 2);
lean_dec(v_unused_4443_);
v_unused_4444_ = lean_ctor_get(v_r_4173_, 1);
lean_dec(v_unused_4444_);
v_unused_4445_ = lean_ctor_get(v_r_4173_, 0);
lean_dec(v_unused_4445_);
v___x_4381_ = v_r_4173_;
v_isShared_4382_ = v_isSharedCheck_4440_;
goto v_resetjp_4380_;
}
else
{
lean_dec(v_r_4173_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4440_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
if (lean_obj_tag(v_l_4360_) == 0)
{
if (lean_obj_tag(v_r_4361_) == 0)
{
lean_object* v_size_4383_; lean_object* v_k_4384_; lean_object* v_v_4385_; lean_object* v_l_4386_; lean_object* v_r_4387_; lean_object* v_size_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; uint8_t v___x_4391_; 
v_size_4383_ = lean_ctor_get(v_l_4360_, 0);
v_k_4384_ = lean_ctor_get(v_l_4360_, 1);
v_v_4385_ = lean_ctor_get(v_l_4360_, 2);
v_l_4386_ = lean_ctor_get(v_l_4360_, 3);
v_r_4387_ = lean_ctor_get(v_l_4360_, 4);
v_size_4388_ = lean_ctor_get(v_r_4361_, 0);
v___x_4389_ = lean_unsigned_to_nat(2u);
v___x_4390_ = lean_nat_mul(v___x_4389_, v_size_4388_);
v___x_4391_ = lean_nat_dec_lt(v_size_4383_, v___x_4390_);
lean_dec(v___x_4390_);
if (v___x_4391_ == 0)
{
lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4420_; 
lean_inc(v_r_4387_);
lean_inc(v_l_4386_);
lean_inc(v_v_4385_);
lean_inc(v_k_4384_);
v_isSharedCheck_4420_ = !lean_is_exclusive(v_l_4360_);
if (v_isSharedCheck_4420_ == 0)
{
lean_object* v_unused_4421_; lean_object* v_unused_4422_; lean_object* v_unused_4423_; lean_object* v_unused_4424_; lean_object* v_unused_4425_; 
v_unused_4421_ = lean_ctor_get(v_l_4360_, 4);
lean_dec(v_unused_4421_);
v_unused_4422_ = lean_ctor_get(v_l_4360_, 3);
lean_dec(v_unused_4422_);
v_unused_4423_ = lean_ctor_get(v_l_4360_, 2);
lean_dec(v_unused_4423_);
v_unused_4424_ = lean_ctor_get(v_l_4360_, 1);
lean_dec(v_unused_4424_);
v_unused_4425_ = lean_ctor_get(v_l_4360_, 0);
lean_dec(v_unused_4425_);
v___x_4393_ = v_l_4360_;
v_isShared_4394_ = v_isSharedCheck_4420_;
goto v_resetjp_4392_;
}
else
{
lean_dec(v_l_4360_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4420_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4410_; 
v___x_4395_ = lean_unsigned_to_nat(1u);
v___x_4396_ = lean_nat_add(v___x_4395_, v_size_4370_);
v___x_4397_ = lean_nat_add(v___x_4396_, v_size_4357_);
lean_dec(v_size_4357_);
if (lean_obj_tag(v_l_4386_) == 0)
{
lean_object* v_size_4418_; 
v_size_4418_ = lean_ctor_get(v_l_4386_, 0);
lean_inc(v_size_4418_);
v___y_4410_ = v_size_4418_;
goto v___jp_4409_;
}
else
{
lean_object* v___x_4419_; 
v___x_4419_ = lean_unsigned_to_nat(0u);
v___y_4410_ = v___x_4419_;
goto v___jp_4409_;
}
v___jp_4398_:
{
lean_object* v___x_4402_; lean_object* v___x_4404_; 
v___x_4402_ = lean_nat_add(v___y_4400_, v___y_4401_);
lean_dec(v___y_4401_);
lean_dec(v___y_4400_);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 4, v_r_4361_);
lean_ctor_set(v___x_4393_, 3, v_r_4387_);
lean_ctor_set(v___x_4393_, 2, v_v_4359_);
lean_ctor_set(v___x_4393_, 1, v_k_4358_);
lean_ctor_set(v___x_4393_, 0, v___x_4402_);
v___x_4404_ = v___x_4393_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4402_);
lean_ctor_set(v_reuseFailAlloc_4408_, 1, v_k_4358_);
lean_ctor_set(v_reuseFailAlloc_4408_, 2, v_v_4359_);
lean_ctor_set(v_reuseFailAlloc_4408_, 3, v_r_4387_);
lean_ctor_set(v_reuseFailAlloc_4408_, 4, v_r_4361_);
v___x_4404_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
lean_object* v___x_4406_; 
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 4, v___x_4404_);
lean_ctor_set(v___x_4381_, 3, v___y_4399_);
lean_ctor_set(v___x_4381_, 2, v_v_4385_);
lean_ctor_set(v___x_4381_, 1, v_k_4384_);
lean_ctor_set(v___x_4381_, 0, v___x_4397_);
v___x_4406_ = v___x_4381_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4397_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_k_4384_);
lean_ctor_set(v_reuseFailAlloc_4407_, 2, v_v_4385_);
lean_ctor_set(v_reuseFailAlloc_4407_, 3, v___y_4399_);
lean_ctor_set(v_reuseFailAlloc_4407_, 4, v___x_4404_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
v___jp_4409_:
{
lean_object* v___x_4411_; lean_object* v___x_4413_; 
v___x_4411_ = lean_nat_add(v___x_4396_, v___y_4410_);
lean_dec(v___y_4410_);
lean_dec(v___x_4396_);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 4, v_l_4386_);
lean_ctor_set(v___x_4364_, 3, v_tree_4367_);
lean_ctor_set(v___x_4364_, 2, v_v_4369_);
lean_ctor_set(v___x_4364_, 1, v_k_4368_);
lean_ctor_set(v___x_4364_, 0, v___x_4411_);
v___x_4413_ = v___x_4364_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v___x_4411_);
lean_ctor_set(v_reuseFailAlloc_4417_, 1, v_k_4368_);
lean_ctor_set(v_reuseFailAlloc_4417_, 2, v_v_4369_);
lean_ctor_set(v_reuseFailAlloc_4417_, 3, v_tree_4367_);
lean_ctor_set(v_reuseFailAlloc_4417_, 4, v_l_4386_);
v___x_4413_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
lean_object* v___x_4414_; 
v___x_4414_ = lean_nat_add(v___x_4395_, v_size_4388_);
if (lean_obj_tag(v_r_4387_) == 0)
{
lean_object* v_size_4415_; 
v_size_4415_ = lean_ctor_get(v_r_4387_, 0);
lean_inc(v_size_4415_);
v___y_4399_ = v___x_4413_;
v___y_4400_ = v___x_4414_;
v___y_4401_ = v_size_4415_;
goto v___jp_4398_;
}
else
{
lean_object* v___x_4416_; 
v___x_4416_ = lean_unsigned_to_nat(0u);
v___y_4399_ = v___x_4413_;
v___y_4400_ = v___x_4414_;
v___y_4401_ = v___x_4416_;
goto v___jp_4398_;
}
}
}
}
}
else
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4431_; 
v___x_4426_ = lean_unsigned_to_nat(1u);
v___x_4427_ = lean_nat_add(v___x_4426_, v_size_4370_);
v___x_4428_ = lean_nat_add(v___x_4427_, v_size_4357_);
lean_dec(v_size_4357_);
v___x_4429_ = lean_nat_add(v___x_4427_, v_size_4383_);
lean_dec(v___x_4427_);
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 4, v_l_4360_);
lean_ctor_set(v___x_4381_, 3, v_tree_4367_);
lean_ctor_set(v___x_4381_, 2, v_v_4369_);
lean_ctor_set(v___x_4381_, 1, v_k_4368_);
lean_ctor_set(v___x_4381_, 0, v___x_4429_);
v___x_4431_ = v___x_4381_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___x_4429_);
lean_ctor_set(v_reuseFailAlloc_4435_, 1, v_k_4368_);
lean_ctor_set(v_reuseFailAlloc_4435_, 2, v_v_4369_);
lean_ctor_set(v_reuseFailAlloc_4435_, 3, v_tree_4367_);
lean_ctor_set(v_reuseFailAlloc_4435_, 4, v_l_4360_);
v___x_4431_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
lean_object* v___x_4433_; 
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 4, v_r_4361_);
lean_ctor_set(v___x_4364_, 3, v___x_4431_);
lean_ctor_set(v___x_4364_, 2, v_v_4359_);
lean_ctor_set(v___x_4364_, 1, v_k_4358_);
lean_ctor_set(v___x_4364_, 0, v___x_4428_);
v___x_4433_ = v___x_4364_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4428_);
lean_ctor_set(v_reuseFailAlloc_4434_, 1, v_k_4358_);
lean_ctor_set(v_reuseFailAlloc_4434_, 2, v_v_4359_);
lean_ctor_set(v_reuseFailAlloc_4434_, 3, v___x_4431_);
lean_ctor_set(v_reuseFailAlloc_4434_, 4, v_r_4361_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
else
{
lean_object* v___x_4436_; lean_object* v___x_4437_; 
lean_dec_ref_known(v_l_4360_, 5);
lean_del_object(v___x_4381_);
lean_dec(v_v_4369_);
lean_dec(v_k_4368_);
lean_dec_ref_known(v_tree_4367_, 5);
lean_del_object(v___x_4364_);
lean_dec(v_v_4359_);
lean_dec(v_k_4358_);
lean_dec(v_size_4357_);
v___x_4436_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7);
v___x_4437_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4436_);
return v___x_4437_;
}
}
else
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
lean_del_object(v___x_4381_);
lean_dec(v_v_4369_);
lean_dec(v_k_4368_);
lean_dec_ref_known(v_tree_4367_, 5);
lean_del_object(v___x_4364_);
lean_dec(v_r_4361_);
lean_dec(v_v_4359_);
lean_dec(v_k_4358_);
lean_dec(v_size_4357_);
v___x_4438_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8);
v___x_4439_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4438_);
return v___x_4439_;
}
}
}
}
else
{
lean_inc(v_r_4361_);
if (lean_obj_tag(v_l_4360_) == 0)
{
lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4483_; 
lean_inc(v_v_4359_);
lean_inc(v_k_4358_);
lean_inc(v_size_4357_);
v_isSharedCheck_4483_ = !lean_is_exclusive(v_r_4173_);
if (v_isSharedCheck_4483_ == 0)
{
lean_object* v_unused_4484_; lean_object* v_unused_4485_; lean_object* v_unused_4486_; lean_object* v_unused_4487_; lean_object* v_unused_4488_; 
v_unused_4484_ = lean_ctor_get(v_r_4173_, 4);
lean_dec(v_unused_4484_);
v_unused_4485_ = lean_ctor_get(v_r_4173_, 3);
lean_dec(v_unused_4485_);
v_unused_4486_ = lean_ctor_get(v_r_4173_, 2);
lean_dec(v_unused_4486_);
v_unused_4487_ = lean_ctor_get(v_r_4173_, 1);
lean_dec(v_unused_4487_);
v_unused_4488_ = lean_ctor_get(v_r_4173_, 0);
lean_dec(v_unused_4488_);
v___x_4447_ = v_r_4173_;
v_isShared_4448_ = v_isSharedCheck_4483_;
goto v_resetjp_4446_;
}
else
{
lean_dec(v_r_4173_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4483_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
if (lean_obj_tag(v_r_4361_) == 0)
{
lean_object* v_k_4449_; lean_object* v_v_4450_; lean_object* v_size_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4456_; 
lean_inc(v_tree_4367_);
v_k_4449_ = lean_ctor_get(v_d_4366_, 0);
lean_inc(v_k_4449_);
v_v_4450_ = lean_ctor_get(v_d_4366_, 1);
lean_inc(v_v_4450_);
lean_dec_ref(v_d_4366_);
v_size_4451_ = lean_ctor_get(v_l_4360_, 0);
v___x_4452_ = lean_unsigned_to_nat(1u);
v___x_4453_ = lean_nat_add(v___x_4452_, v_size_4357_);
lean_dec(v_size_4357_);
v___x_4454_ = lean_nat_add(v___x_4452_, v_size_4451_);
if (v_isShared_4448_ == 0)
{
lean_ctor_set(v___x_4447_, 4, v_l_4360_);
lean_ctor_set(v___x_4447_, 3, v_tree_4367_);
lean_ctor_set(v___x_4447_, 2, v_v_4450_);
lean_ctor_set(v___x_4447_, 1, v_k_4449_);
lean_ctor_set(v___x_4447_, 0, v___x_4454_);
v___x_4456_ = v___x_4447_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4454_);
lean_ctor_set(v_reuseFailAlloc_4460_, 1, v_k_4449_);
lean_ctor_set(v_reuseFailAlloc_4460_, 2, v_v_4450_);
lean_ctor_set(v_reuseFailAlloc_4460_, 3, v_tree_4367_);
lean_ctor_set(v_reuseFailAlloc_4460_, 4, v_l_4360_);
v___x_4456_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
lean_object* v___x_4458_; 
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 4, v_r_4361_);
lean_ctor_set(v___x_4364_, 3, v___x_4456_);
lean_ctor_set(v___x_4364_, 2, v_v_4359_);
lean_ctor_set(v___x_4364_, 1, v_k_4358_);
lean_ctor_set(v___x_4364_, 0, v___x_4453_);
v___x_4458_ = v___x_4364_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4453_);
lean_ctor_set(v_reuseFailAlloc_4459_, 1, v_k_4358_);
lean_ctor_set(v_reuseFailAlloc_4459_, 2, v_v_4359_);
lean_ctor_set(v_reuseFailAlloc_4459_, 3, v___x_4456_);
lean_ctor_set(v_reuseFailAlloc_4459_, 4, v_r_4361_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
else
{
lean_object* v_k_4461_; lean_object* v_v_4462_; lean_object* v_k_4463_; lean_object* v_v_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4479_; 
lean_dec(v_size_4357_);
v_k_4461_ = lean_ctor_get(v_d_4366_, 0);
lean_inc(v_k_4461_);
v_v_4462_ = lean_ctor_get(v_d_4366_, 1);
lean_inc(v_v_4462_);
lean_dec_ref(v_d_4366_);
v_k_4463_ = lean_ctor_get(v_l_4360_, 1);
v_v_4464_ = lean_ctor_get(v_l_4360_, 2);
v_isSharedCheck_4479_ = !lean_is_exclusive(v_l_4360_);
if (v_isSharedCheck_4479_ == 0)
{
lean_object* v_unused_4480_; lean_object* v_unused_4481_; lean_object* v_unused_4482_; 
v_unused_4480_ = lean_ctor_get(v_l_4360_, 4);
lean_dec(v_unused_4480_);
v_unused_4481_ = lean_ctor_get(v_l_4360_, 3);
lean_dec(v_unused_4481_);
v_unused_4482_ = lean_ctor_get(v_l_4360_, 0);
lean_dec(v_unused_4482_);
v___x_4466_ = v_l_4360_;
v_isShared_4467_ = v_isSharedCheck_4479_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_v_4464_);
lean_inc(v_k_4463_);
lean_dec(v_l_4360_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4479_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4471_; 
v___x_4468_ = lean_unsigned_to_nat(3u);
v___x_4469_ = lean_unsigned_to_nat(1u);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 4, v_r_4361_);
lean_ctor_set(v___x_4466_, 3, v_r_4361_);
lean_ctor_set(v___x_4466_, 2, v_v_4462_);
lean_ctor_set(v___x_4466_, 1, v_k_4461_);
lean_ctor_set(v___x_4466_, 0, v___x_4469_);
v___x_4471_ = v___x_4466_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4469_);
lean_ctor_set(v_reuseFailAlloc_4478_, 1, v_k_4461_);
lean_ctor_set(v_reuseFailAlloc_4478_, 2, v_v_4462_);
lean_ctor_set(v_reuseFailAlloc_4478_, 3, v_r_4361_);
lean_ctor_set(v_reuseFailAlloc_4478_, 4, v_r_4361_);
v___x_4471_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
lean_object* v___x_4473_; 
if (v_isShared_4448_ == 0)
{
lean_ctor_set(v___x_4447_, 3, v_r_4361_);
lean_ctor_set(v___x_4447_, 0, v___x_4469_);
v___x_4473_ = v___x_4447_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4469_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_k_4358_);
lean_ctor_set(v_reuseFailAlloc_4477_, 2, v_v_4359_);
lean_ctor_set(v_reuseFailAlloc_4477_, 3, v_r_4361_);
lean_ctor_set(v_reuseFailAlloc_4477_, 4, v_r_4361_);
v___x_4473_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
lean_object* v___x_4475_; 
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 4, v___x_4473_);
lean_ctor_set(v___x_4364_, 3, v___x_4471_);
lean_ctor_set(v___x_4364_, 2, v_v_4464_);
lean_ctor_set(v___x_4364_, 1, v_k_4463_);
lean_ctor_set(v___x_4364_, 0, v___x_4468_);
v___x_4475_ = v___x_4364_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4476_, 1, v_k_4463_);
lean_ctor_set(v_reuseFailAlloc_4476_, 2, v_v_4464_);
lean_ctor_set(v_reuseFailAlloc_4476_, 3, v___x_4471_);
lean_ctor_set(v_reuseFailAlloc_4476_, 4, v___x_4473_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4361_) == 0)
{
lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4502_; 
lean_inc(v_v_4359_);
lean_inc(v_k_4358_);
v_isSharedCheck_4502_ = !lean_is_exclusive(v_r_4173_);
if (v_isSharedCheck_4502_ == 0)
{
lean_object* v_unused_4503_; lean_object* v_unused_4504_; lean_object* v_unused_4505_; lean_object* v_unused_4506_; lean_object* v_unused_4507_; 
v_unused_4503_ = lean_ctor_get(v_r_4173_, 4);
lean_dec(v_unused_4503_);
v_unused_4504_ = lean_ctor_get(v_r_4173_, 3);
lean_dec(v_unused_4504_);
v_unused_4505_ = lean_ctor_get(v_r_4173_, 2);
lean_dec(v_unused_4505_);
v_unused_4506_ = lean_ctor_get(v_r_4173_, 1);
lean_dec(v_unused_4506_);
v_unused_4507_ = lean_ctor_get(v_r_4173_, 0);
lean_dec(v_unused_4507_);
v___x_4490_ = v_r_4173_;
v_isShared_4491_ = v_isSharedCheck_4502_;
goto v_resetjp_4489_;
}
else
{
lean_dec(v_r_4173_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4502_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v_k_4492_; lean_object* v_v_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4497_; 
v_k_4492_ = lean_ctor_get(v_d_4366_, 0);
lean_inc(v_k_4492_);
v_v_4493_ = lean_ctor_get(v_d_4366_, 1);
lean_inc(v_v_4493_);
lean_dec_ref(v_d_4366_);
v___x_4494_ = lean_unsigned_to_nat(3u);
v___x_4495_ = lean_unsigned_to_nat(1u);
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 4, v_l_4360_);
lean_ctor_set(v___x_4490_, 2, v_v_4493_);
lean_ctor_set(v___x_4490_, 1, v_k_4492_);
lean_ctor_set(v___x_4490_, 0, v___x_4495_);
v___x_4497_ = v___x_4490_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4495_);
lean_ctor_set(v_reuseFailAlloc_4501_, 1, v_k_4492_);
lean_ctor_set(v_reuseFailAlloc_4501_, 2, v_v_4493_);
lean_ctor_set(v_reuseFailAlloc_4501_, 3, v_l_4360_);
lean_ctor_set(v_reuseFailAlloc_4501_, 4, v_l_4360_);
v___x_4497_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
lean_object* v___x_4499_; 
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 4, v_r_4361_);
lean_ctor_set(v___x_4364_, 3, v___x_4497_);
lean_ctor_set(v___x_4364_, 2, v_v_4359_);
lean_ctor_set(v___x_4364_, 1, v_k_4358_);
lean_ctor_set(v___x_4364_, 0, v___x_4494_);
v___x_4499_ = v___x_4364_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4494_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v_k_4358_);
lean_ctor_set(v_reuseFailAlloc_4500_, 2, v_v_4359_);
lean_ctor_set(v_reuseFailAlloc_4500_, 3, v___x_4497_);
lean_ctor_set(v_reuseFailAlloc_4500_, 4, v_r_4361_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
else
{
lean_object* v_k_4508_; lean_object* v_v_4509_; lean_object* v___x_4510_; lean_object* v___x_4512_; 
v_k_4508_ = lean_ctor_get(v_d_4366_, 0);
lean_inc(v_k_4508_);
v_v_4509_ = lean_ctor_get(v_d_4366_, 1);
lean_inc(v_v_4509_);
lean_dec_ref(v_d_4366_);
v___x_4510_ = lean_unsigned_to_nat(2u);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 4, v_r_4173_);
lean_ctor_set(v___x_4364_, 3, v_r_4361_);
lean_ctor_set(v___x_4364_, 2, v_v_4509_);
lean_ctor_set(v___x_4364_, 1, v_k_4508_);
lean_ctor_set(v___x_4364_, 0, v___x_4510_);
v___x_4512_ = v___x_4364_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v_k_4508_);
lean_ctor_set(v_reuseFailAlloc_4513_, 2, v_v_4509_);
lean_ctor_set(v_reuseFailAlloc_4513_, 3, v_r_4361_);
lean_ctor_set(v_reuseFailAlloc_4513_, 4, v_r_4173_);
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
}
else
{
lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4682_; 
lean_inc(v_r_4361_);
lean_inc(v_v_4359_);
lean_inc(v_k_4358_);
v_isSharedCheck_4682_ = !lean_is_exclusive(v_r_4173_);
if (v_isSharedCheck_4682_ == 0)
{
lean_object* v_unused_4683_; lean_object* v_unused_4684_; lean_object* v_unused_4685_; lean_object* v_unused_4686_; lean_object* v_unused_4687_; 
v_unused_4683_ = lean_ctor_get(v_r_4173_, 4);
lean_dec(v_unused_4683_);
v_unused_4684_ = lean_ctor_get(v_r_4173_, 3);
lean_dec(v_unused_4684_);
v_unused_4685_ = lean_ctor_get(v_r_4173_, 2);
lean_dec(v_unused_4685_);
v_unused_4686_ = lean_ctor_get(v_r_4173_, 1);
lean_dec(v_unused_4686_);
v_unused_4687_ = lean_ctor_get(v_r_4173_, 0);
lean_dec(v_unused_4687_);
v___x_4521_ = v_r_4173_;
v_isShared_4522_ = v_isSharedCheck_4682_;
goto v_resetjp_4520_;
}
else
{
lean_dec(v_r_4173_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4682_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v_d_4523_; lean_object* v_tree_4524_; 
v_d_4523_ = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(v_k_4358_, v_v_4359_, v_l_4360_, v_r_4361_);
v_tree_4524_ = lean_ctor_get(v_d_4523_, 2);
lean_inc(v_tree_4524_);
if (lean_obj_tag(v_tree_4524_) == 0)
{
lean_object* v_k_4525_; lean_object* v_v_4526_; lean_object* v_size_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; uint8_t v___x_4530_; 
v_k_4525_ = lean_ctor_get(v_d_4523_, 0);
lean_inc(v_k_4525_);
v_v_4526_ = lean_ctor_get(v_d_4523_, 1);
lean_inc(v_v_4526_);
lean_dec_ref(v_d_4523_);
v_size_4527_ = lean_ctor_get(v_tree_4524_, 0);
v___x_4528_ = lean_unsigned_to_nat(3u);
v___x_4529_ = lean_nat_mul(v___x_4528_, v_size_4527_);
v___x_4530_ = lean_nat_dec_lt(v___x_4529_, v_size_4352_);
lean_dec(v___x_4529_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4535_; 
lean_dec(v_r_4356_);
v___x_4531_ = lean_unsigned_to_nat(1u);
v___x_4532_ = lean_nat_add(v___x_4531_, v_size_4352_);
v___x_4533_ = lean_nat_add(v___x_4532_, v_size_4527_);
lean_dec(v___x_4532_);
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 4, v_tree_4524_);
lean_ctor_set(v___x_4521_, 3, v_l_4172_);
lean_ctor_set(v___x_4521_, 2, v_v_4526_);
lean_ctor_set(v___x_4521_, 1, v_k_4525_);
lean_ctor_set(v___x_4521_, 0, v___x_4533_);
v___x_4535_ = v___x_4521_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4533_);
lean_ctor_set(v_reuseFailAlloc_4536_, 1, v_k_4525_);
lean_ctor_set(v_reuseFailAlloc_4536_, 2, v_v_4526_);
lean_ctor_set(v_reuseFailAlloc_4536_, 3, v_l_4172_);
lean_ctor_set(v_reuseFailAlloc_4536_, 4, v_tree_4524_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
else
{
lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4608_; 
lean_inc(v_l_4355_);
lean_inc(v_v_4354_);
lean_inc(v_k_4353_);
lean_inc(v_size_4352_);
v_isSharedCheck_4608_ = !lean_is_exclusive(v_l_4172_);
if (v_isSharedCheck_4608_ == 0)
{
lean_object* v_unused_4609_; lean_object* v_unused_4610_; lean_object* v_unused_4611_; lean_object* v_unused_4612_; lean_object* v_unused_4613_; 
v_unused_4609_ = lean_ctor_get(v_l_4172_, 4);
lean_dec(v_unused_4609_);
v_unused_4610_ = lean_ctor_get(v_l_4172_, 3);
lean_dec(v_unused_4610_);
v_unused_4611_ = lean_ctor_get(v_l_4172_, 2);
lean_dec(v_unused_4611_);
v_unused_4612_ = lean_ctor_get(v_l_4172_, 1);
lean_dec(v_unused_4612_);
v_unused_4613_ = lean_ctor_get(v_l_4172_, 0);
lean_dec(v_unused_4613_);
v___x_4538_ = v_l_4172_;
v_isShared_4539_ = v_isSharedCheck_4608_;
goto v_resetjp_4537_;
}
else
{
lean_dec(v_l_4172_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4608_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
if (lean_obj_tag(v_l_4355_) == 0)
{
if (lean_obj_tag(v_r_4356_) == 0)
{
lean_object* v_size_4540_; lean_object* v_size_4541_; lean_object* v_k_4542_; lean_object* v_v_4543_; lean_object* v_l_4544_; lean_object* v_r_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; uint8_t v___x_4548_; 
v_size_4540_ = lean_ctor_get(v_l_4355_, 0);
v_size_4541_ = lean_ctor_get(v_r_4356_, 0);
v_k_4542_ = lean_ctor_get(v_r_4356_, 1);
v_v_4543_ = lean_ctor_get(v_r_4356_, 2);
v_l_4544_ = lean_ctor_get(v_r_4356_, 3);
v_r_4545_ = lean_ctor_get(v_r_4356_, 4);
v___x_4546_ = lean_unsigned_to_nat(2u);
v___x_4547_ = lean_nat_mul(v___x_4546_, v_size_4540_);
v___x_4548_ = lean_nat_dec_lt(v_size_4541_, v___x_4547_);
lean_dec(v___x_4547_);
if (v___x_4548_ == 0)
{
lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4587_; 
lean_inc(v_r_4545_);
lean_inc(v_l_4544_);
lean_inc(v_v_4543_);
lean_inc(v_k_4542_);
lean_del_object(v___x_4538_);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_r_4356_);
if (v_isSharedCheck_4587_ == 0)
{
lean_object* v_unused_4588_; lean_object* v_unused_4589_; lean_object* v_unused_4590_; lean_object* v_unused_4591_; lean_object* v_unused_4592_; 
v_unused_4588_ = lean_ctor_get(v_r_4356_, 4);
lean_dec(v_unused_4588_);
v_unused_4589_ = lean_ctor_get(v_r_4356_, 3);
lean_dec(v_unused_4589_);
v_unused_4590_ = lean_ctor_get(v_r_4356_, 2);
lean_dec(v_unused_4590_);
v_unused_4591_ = lean_ctor_get(v_r_4356_, 1);
lean_dec(v_unused_4591_);
v_unused_4592_ = lean_ctor_get(v_r_4356_, 0);
lean_dec(v_unused_4592_);
v___x_4550_ = v_r_4356_;
v_isShared_4551_ = v_isSharedCheck_4587_;
goto v_resetjp_4549_;
}
else
{
lean_dec(v_r_4356_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4587_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___x_4575_; lean_object* v___y_4577_; 
v___x_4552_ = lean_unsigned_to_nat(1u);
v___x_4553_ = lean_nat_add(v___x_4552_, v_size_4352_);
lean_dec(v_size_4352_);
v___x_4554_ = lean_nat_add(v___x_4553_, v_size_4527_);
lean_dec(v___x_4553_);
v___x_4575_ = lean_nat_add(v___x_4552_, v_size_4540_);
if (lean_obj_tag(v_l_4544_) == 0)
{
lean_object* v_size_4585_; 
v_size_4585_ = lean_ctor_get(v_l_4544_, 0);
lean_inc(v_size_4585_);
v___y_4577_ = v_size_4585_;
goto v___jp_4576_;
}
else
{
lean_object* v___x_4586_; 
v___x_4586_ = lean_unsigned_to_nat(0u);
v___y_4577_ = v___x_4586_;
goto v___jp_4576_;
}
v___jp_4555_:
{
lean_object* v___x_4559_; lean_object* v___x_4561_; 
v___x_4559_ = lean_nat_add(v___y_4556_, v___y_4558_);
lean_dec(v___y_4558_);
lean_dec(v___y_4556_);
lean_inc_ref(v_tree_4524_);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 4, v_tree_4524_);
lean_ctor_set(v___x_4550_, 3, v_r_4545_);
lean_ctor_set(v___x_4550_, 2, v_v_4526_);
lean_ctor_set(v___x_4550_, 1, v_k_4525_);
lean_ctor_set(v___x_4550_, 0, v___x_4559_);
v___x_4561_ = v___x_4550_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___x_4559_);
lean_ctor_set(v_reuseFailAlloc_4574_, 1, v_k_4525_);
lean_ctor_set(v_reuseFailAlloc_4574_, 2, v_v_4526_);
lean_ctor_set(v_reuseFailAlloc_4574_, 3, v_r_4545_);
lean_ctor_set(v_reuseFailAlloc_4574_, 4, v_tree_4524_);
v___x_4561_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
v_isSharedCheck_4568_ = !lean_is_exclusive(v_tree_4524_);
if (v_isSharedCheck_4568_ == 0)
{
lean_object* v_unused_4569_; lean_object* v_unused_4570_; lean_object* v_unused_4571_; lean_object* v_unused_4572_; lean_object* v_unused_4573_; 
v_unused_4569_ = lean_ctor_get(v_tree_4524_, 4);
lean_dec(v_unused_4569_);
v_unused_4570_ = lean_ctor_get(v_tree_4524_, 3);
lean_dec(v_unused_4570_);
v_unused_4571_ = lean_ctor_get(v_tree_4524_, 2);
lean_dec(v_unused_4571_);
v_unused_4572_ = lean_ctor_get(v_tree_4524_, 1);
lean_dec(v_unused_4572_);
v_unused_4573_ = lean_ctor_get(v_tree_4524_, 0);
lean_dec(v_unused_4573_);
v___x_4563_ = v_tree_4524_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_dec(v_tree_4524_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 4, v___x_4561_);
lean_ctor_set(v___x_4563_, 3, v___y_4557_);
lean_ctor_set(v___x_4563_, 2, v_v_4543_);
lean_ctor_set(v___x_4563_, 1, v_k_4542_);
lean_ctor_set(v___x_4563_, 0, v___x_4554_);
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v___x_4554_);
lean_ctor_set(v_reuseFailAlloc_4567_, 1, v_k_4542_);
lean_ctor_set(v_reuseFailAlloc_4567_, 2, v_v_4543_);
lean_ctor_set(v_reuseFailAlloc_4567_, 3, v___y_4557_);
lean_ctor_set(v_reuseFailAlloc_4567_, 4, v___x_4561_);
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
v___jp_4576_:
{
lean_object* v___x_4578_; lean_object* v___x_4580_; 
v___x_4578_ = lean_nat_add(v___x_4575_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec(v___x_4575_);
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 4, v_l_4544_);
lean_ctor_set(v___x_4521_, 3, v_l_4355_);
lean_ctor_set(v___x_4521_, 2, v_v_4354_);
lean_ctor_set(v___x_4521_, 1, v_k_4353_);
lean_ctor_set(v___x_4521_, 0, v___x_4578_);
v___x_4580_ = v___x_4521_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4578_);
lean_ctor_set(v_reuseFailAlloc_4584_, 1, v_k_4353_);
lean_ctor_set(v_reuseFailAlloc_4584_, 2, v_v_4354_);
lean_ctor_set(v_reuseFailAlloc_4584_, 3, v_l_4355_);
lean_ctor_set(v_reuseFailAlloc_4584_, 4, v_l_4544_);
v___x_4580_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
lean_object* v___x_4581_; 
v___x_4581_ = lean_nat_add(v___x_4552_, v_size_4527_);
if (lean_obj_tag(v_r_4545_) == 0)
{
lean_object* v_size_4582_; 
v_size_4582_ = lean_ctor_get(v_r_4545_, 0);
lean_inc(v_size_4582_);
v___y_4556_ = v___x_4581_;
v___y_4557_ = v___x_4580_;
v___y_4558_ = v_size_4582_;
goto v___jp_4555_;
}
else
{
lean_object* v___x_4583_; 
v___x_4583_ = lean_unsigned_to_nat(0u);
v___y_4556_ = v___x_4581_;
v___y_4557_ = v___x_4580_;
v___y_4558_ = v___x_4583_;
goto v___jp_4555_;
}
}
}
}
}
else
{
lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4599_; 
v___x_4593_ = lean_unsigned_to_nat(1u);
v___x_4594_ = lean_nat_add(v___x_4593_, v_size_4352_);
lean_dec(v_size_4352_);
v___x_4595_ = lean_nat_add(v___x_4594_, v_size_4527_);
lean_dec(v___x_4594_);
v___x_4596_ = lean_nat_add(v___x_4593_, v_size_4527_);
v___x_4597_ = lean_nat_add(v___x_4596_, v_size_4541_);
lean_dec(v___x_4596_);
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 4, v_tree_4524_);
lean_ctor_set(v___x_4521_, 3, v_r_4356_);
lean_ctor_set(v___x_4521_, 2, v_v_4526_);
lean_ctor_set(v___x_4521_, 1, v_k_4525_);
lean_ctor_set(v___x_4521_, 0, v___x_4597_);
v___x_4599_ = v___x_4521_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4597_);
lean_ctor_set(v_reuseFailAlloc_4603_, 1, v_k_4525_);
lean_ctor_set(v_reuseFailAlloc_4603_, 2, v_v_4526_);
lean_ctor_set(v_reuseFailAlloc_4603_, 3, v_r_4356_);
lean_ctor_set(v_reuseFailAlloc_4603_, 4, v_tree_4524_);
v___x_4599_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
lean_object* v___x_4601_; 
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 4, v___x_4599_);
lean_ctor_set(v___x_4538_, 0, v___x_4595_);
v___x_4601_ = v___x_4538_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4595_);
lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_k_4353_);
lean_ctor_set(v_reuseFailAlloc_4602_, 2, v_v_4354_);
lean_ctor_set(v_reuseFailAlloc_4602_, 3, v_l_4355_);
lean_ctor_set(v_reuseFailAlloc_4602_, 4, v___x_4599_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
else
{
lean_object* v___x_4604_; lean_object* v___x_4605_; 
lean_dec_ref_known(v_l_4355_, 5);
lean_del_object(v___x_4538_);
lean_dec(v_v_4526_);
lean_dec_ref_known(v_tree_4524_, 5);
lean_dec(v_k_4525_);
lean_del_object(v___x_4521_);
lean_dec(v_v_4354_);
lean_dec(v_k_4353_);
lean_dec(v_size_4352_);
v___x_4604_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3);
v___x_4605_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4604_);
return v___x_4605_;
}
}
else
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
lean_del_object(v___x_4538_);
lean_dec(v_v_4526_);
lean_dec_ref_known(v_tree_4524_, 5);
lean_dec(v_k_4525_);
lean_del_object(v___x_4521_);
lean_dec(v_r_4356_);
lean_dec(v_v_4354_);
lean_dec(v_k_4353_);
lean_dec(v_size_4352_);
v___x_4606_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4);
v___x_4607_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4606_);
return v___x_4607_;
}
}
}
}
else
{
if (lean_obj_tag(v_l_4355_) == 0)
{
lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4639_; 
lean_inc_ref(v_l_4355_);
lean_inc(v_v_4354_);
lean_inc(v_k_4353_);
lean_inc(v_size_4352_);
v_isSharedCheck_4639_ = !lean_is_exclusive(v_l_4172_);
if (v_isSharedCheck_4639_ == 0)
{
lean_object* v_unused_4640_; lean_object* v_unused_4641_; lean_object* v_unused_4642_; lean_object* v_unused_4643_; lean_object* v_unused_4644_; 
v_unused_4640_ = lean_ctor_get(v_l_4172_, 4);
lean_dec(v_unused_4640_);
v_unused_4641_ = lean_ctor_get(v_l_4172_, 3);
lean_dec(v_unused_4641_);
v_unused_4642_ = lean_ctor_get(v_l_4172_, 2);
lean_dec(v_unused_4642_);
v_unused_4643_ = lean_ctor_get(v_l_4172_, 1);
lean_dec(v_unused_4643_);
v_unused_4644_ = lean_ctor_get(v_l_4172_, 0);
lean_dec(v_unused_4644_);
v___x_4615_ = v_l_4172_;
v_isShared_4616_ = v_isSharedCheck_4639_;
goto v_resetjp_4614_;
}
else
{
lean_dec(v_l_4172_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4639_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
if (lean_obj_tag(v_r_4356_) == 0)
{
lean_object* v_k_4617_; lean_object* v_v_4618_; lean_object* v_size_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4624_; 
v_k_4617_ = lean_ctor_get(v_d_4523_, 0);
lean_inc(v_k_4617_);
v_v_4618_ = lean_ctor_get(v_d_4523_, 1);
lean_inc(v_v_4618_);
lean_dec_ref(v_d_4523_);
v_size_4619_ = lean_ctor_get(v_r_4356_, 0);
v___x_4620_ = lean_unsigned_to_nat(1u);
v___x_4621_ = lean_nat_add(v___x_4620_, v_size_4352_);
lean_dec(v_size_4352_);
v___x_4622_ = lean_nat_add(v___x_4620_, v_size_4619_);
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 4, v_tree_4524_);
lean_ctor_set(v___x_4521_, 3, v_r_4356_);
lean_ctor_set(v___x_4521_, 2, v_v_4618_);
lean_ctor_set(v___x_4521_, 1, v_k_4617_);
lean_ctor_set(v___x_4521_, 0, v___x_4622_);
v___x_4624_ = v___x_4521_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4622_);
lean_ctor_set(v_reuseFailAlloc_4628_, 1, v_k_4617_);
lean_ctor_set(v_reuseFailAlloc_4628_, 2, v_v_4618_);
lean_ctor_set(v_reuseFailAlloc_4628_, 3, v_r_4356_);
lean_ctor_set(v_reuseFailAlloc_4628_, 4, v_tree_4524_);
v___x_4624_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
lean_object* v___x_4626_; 
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 4, v___x_4624_);
lean_ctor_set(v___x_4615_, 0, v___x_4621_);
v___x_4626_ = v___x_4615_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4621_);
lean_ctor_set(v_reuseFailAlloc_4627_, 1, v_k_4353_);
lean_ctor_set(v_reuseFailAlloc_4627_, 2, v_v_4354_);
lean_ctor_set(v_reuseFailAlloc_4627_, 3, v_l_4355_);
lean_ctor_set(v_reuseFailAlloc_4627_, 4, v___x_4624_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
else
{
lean_object* v_k_4629_; lean_object* v_v_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4634_; 
lean_dec(v_size_4352_);
v_k_4629_ = lean_ctor_get(v_d_4523_, 0);
lean_inc(v_k_4629_);
v_v_4630_ = lean_ctor_get(v_d_4523_, 1);
lean_inc(v_v_4630_);
lean_dec_ref(v_d_4523_);
v___x_4631_ = lean_unsigned_to_nat(3u);
v___x_4632_ = lean_unsigned_to_nat(1u);
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 4, v_r_4356_);
lean_ctor_set(v___x_4521_, 3, v_r_4356_);
lean_ctor_set(v___x_4521_, 2, v_v_4630_);
lean_ctor_set(v___x_4521_, 1, v_k_4629_);
lean_ctor_set(v___x_4521_, 0, v___x_4632_);
v___x_4634_ = v___x_4521_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4632_);
lean_ctor_set(v_reuseFailAlloc_4638_, 1, v_k_4629_);
lean_ctor_set(v_reuseFailAlloc_4638_, 2, v_v_4630_);
lean_ctor_set(v_reuseFailAlloc_4638_, 3, v_r_4356_);
lean_ctor_set(v_reuseFailAlloc_4638_, 4, v_r_4356_);
v___x_4634_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
lean_object* v___x_4636_; 
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 4, v___x_4634_);
lean_ctor_set(v___x_4615_, 0, v___x_4631_);
v___x_4636_ = v___x_4615_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4631_);
lean_ctor_set(v_reuseFailAlloc_4637_, 1, v_k_4353_);
lean_ctor_set(v_reuseFailAlloc_4637_, 2, v_v_4354_);
lean_ctor_set(v_reuseFailAlloc_4637_, 3, v_l_4355_);
lean_ctor_set(v_reuseFailAlloc_4637_, 4, v___x_4634_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4356_) == 0)
{
lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4670_; 
lean_inc(v_l_4355_);
lean_inc(v_v_4354_);
lean_inc(v_k_4353_);
v_isSharedCheck_4670_ = !lean_is_exclusive(v_l_4172_);
if (v_isSharedCheck_4670_ == 0)
{
lean_object* v_unused_4671_; lean_object* v_unused_4672_; lean_object* v_unused_4673_; lean_object* v_unused_4674_; lean_object* v_unused_4675_; 
v_unused_4671_ = lean_ctor_get(v_l_4172_, 4);
lean_dec(v_unused_4671_);
v_unused_4672_ = lean_ctor_get(v_l_4172_, 3);
lean_dec(v_unused_4672_);
v_unused_4673_ = lean_ctor_get(v_l_4172_, 2);
lean_dec(v_unused_4673_);
v_unused_4674_ = lean_ctor_get(v_l_4172_, 1);
lean_dec(v_unused_4674_);
v_unused_4675_ = lean_ctor_get(v_l_4172_, 0);
lean_dec(v_unused_4675_);
v___x_4646_ = v_l_4172_;
v_isShared_4647_ = v_isSharedCheck_4670_;
goto v_resetjp_4645_;
}
else
{
lean_dec(v_l_4172_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4670_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v_k_4648_; lean_object* v_v_4649_; lean_object* v_k_4650_; lean_object* v_v_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4666_; 
v_k_4648_ = lean_ctor_get(v_d_4523_, 0);
lean_inc(v_k_4648_);
v_v_4649_ = lean_ctor_get(v_d_4523_, 1);
lean_inc(v_v_4649_);
lean_dec_ref(v_d_4523_);
v_k_4650_ = lean_ctor_get(v_r_4356_, 1);
v_v_4651_ = lean_ctor_get(v_r_4356_, 2);
v_isSharedCheck_4666_ = !lean_is_exclusive(v_r_4356_);
if (v_isSharedCheck_4666_ == 0)
{
lean_object* v_unused_4667_; lean_object* v_unused_4668_; lean_object* v_unused_4669_; 
v_unused_4667_ = lean_ctor_get(v_r_4356_, 4);
lean_dec(v_unused_4667_);
v_unused_4668_ = lean_ctor_get(v_r_4356_, 3);
lean_dec(v_unused_4668_);
v_unused_4669_ = lean_ctor_get(v_r_4356_, 0);
lean_dec(v_unused_4669_);
v___x_4653_ = v_r_4356_;
v_isShared_4654_ = v_isSharedCheck_4666_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_v_4651_);
lean_inc(v_k_4650_);
lean_dec(v_r_4356_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4666_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4658_; 
v___x_4655_ = lean_unsigned_to_nat(3u);
v___x_4656_ = lean_unsigned_to_nat(1u);
if (v_isShared_4654_ == 0)
{
lean_ctor_set(v___x_4653_, 4, v_l_4355_);
lean_ctor_set(v___x_4653_, 3, v_l_4355_);
lean_ctor_set(v___x_4653_, 2, v_v_4354_);
lean_ctor_set(v___x_4653_, 1, v_k_4353_);
lean_ctor_set(v___x_4653_, 0, v___x_4656_);
v___x_4658_ = v___x_4653_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4656_);
lean_ctor_set(v_reuseFailAlloc_4665_, 1, v_k_4353_);
lean_ctor_set(v_reuseFailAlloc_4665_, 2, v_v_4354_);
lean_ctor_set(v_reuseFailAlloc_4665_, 3, v_l_4355_);
lean_ctor_set(v_reuseFailAlloc_4665_, 4, v_l_4355_);
v___x_4658_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
lean_object* v___x_4660_; 
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 4, v_l_4355_);
lean_ctor_set(v___x_4521_, 3, v_l_4355_);
lean_ctor_set(v___x_4521_, 2, v_v_4649_);
lean_ctor_set(v___x_4521_, 1, v_k_4648_);
lean_ctor_set(v___x_4521_, 0, v___x_4656_);
v___x_4660_ = v___x_4521_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4656_);
lean_ctor_set(v_reuseFailAlloc_4664_, 1, v_k_4648_);
lean_ctor_set(v_reuseFailAlloc_4664_, 2, v_v_4649_);
lean_ctor_set(v_reuseFailAlloc_4664_, 3, v_l_4355_);
lean_ctor_set(v_reuseFailAlloc_4664_, 4, v_l_4355_);
v___x_4660_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
lean_object* v___x_4662_; 
if (v_isShared_4647_ == 0)
{
lean_ctor_set(v___x_4646_, 4, v___x_4660_);
lean_ctor_set(v___x_4646_, 3, v___x_4658_);
lean_ctor_set(v___x_4646_, 2, v_v_4651_);
lean_ctor_set(v___x_4646_, 1, v_k_4650_);
lean_ctor_set(v___x_4646_, 0, v___x_4655_);
v___x_4662_ = v___x_4646_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4655_);
lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_k_4650_);
lean_ctor_set(v_reuseFailAlloc_4663_, 2, v_v_4651_);
lean_ctor_set(v_reuseFailAlloc_4663_, 3, v___x_4658_);
lean_ctor_set(v_reuseFailAlloc_4663_, 4, v___x_4660_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
}
}
}
else
{
lean_object* v_k_4676_; lean_object* v_v_4677_; lean_object* v___x_4678_; lean_object* v___x_4680_; 
v_k_4676_ = lean_ctor_get(v_d_4523_, 0);
lean_inc(v_k_4676_);
v_v_4677_ = lean_ctor_get(v_d_4523_, 1);
lean_inc(v_v_4677_);
lean_dec_ref(v_d_4523_);
v___x_4678_ = lean_unsigned_to_nat(2u);
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 4, v_r_4356_);
lean_ctor_set(v___x_4521_, 3, v_l_4172_);
lean_ctor_set(v___x_4521_, 2, v_v_4677_);
lean_ctor_set(v___x_4521_, 1, v_k_4676_);
lean_ctor_set(v___x_4521_, 0, v___x_4678_);
v___x_4680_ = v___x_4521_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v___x_4678_);
lean_ctor_set(v_reuseFailAlloc_4681_, 1, v_k_4676_);
lean_ctor_set(v_reuseFailAlloc_4681_, 2, v_v_4677_);
lean_ctor_set(v_reuseFailAlloc_4681_, 3, v_l_4172_);
lean_ctor_set(v_reuseFailAlloc_4681_, 4, v_r_4356_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
}
}
}
}
}
else
{
return v_l_4172_;
}
}
else
{
return v_r_4173_;
}
}
default: 
{
lean_object* v___x_4688_; 
v___x_4688_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4167_, v_k_4168_, v_r_4173_);
if (lean_obj_tag(v___x_4688_) == 0)
{
if (lean_obj_tag(v_l_4172_) == 0)
{
lean_object* v_size_4689_; lean_object* v_size_4690_; lean_object* v_k_4691_; lean_object* v_v_4692_; lean_object* v_l_4693_; lean_object* v_r_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; uint8_t v___x_4697_; 
v_size_4689_ = lean_ctor_get(v___x_4688_, 0);
v_size_4690_ = lean_ctor_get(v_l_4172_, 0);
v_k_4691_ = lean_ctor_get(v_l_4172_, 1);
v_v_4692_ = lean_ctor_get(v_l_4172_, 2);
v_l_4693_ = lean_ctor_get(v_l_4172_, 3);
v_r_4694_ = lean_ctor_get(v_l_4172_, 4);
lean_inc(v_r_4694_);
v___x_4695_ = lean_unsigned_to_nat(3u);
v___x_4696_ = lean_nat_mul(v___x_4695_, v_size_4689_);
v___x_4697_ = lean_nat_dec_lt(v___x_4696_, v_size_4690_);
lean_dec(v___x_4696_);
if (v___x_4697_ == 0)
{
lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4702_; 
lean_dec(v_r_4694_);
v___x_4698_ = lean_unsigned_to_nat(1u);
v___x_4699_ = lean_nat_add(v___x_4698_, v_size_4690_);
v___x_4700_ = lean_nat_add(v___x_4699_, v_size_4689_);
lean_dec(v___x_4699_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v___x_4688_);
lean_ctor_set(v___x_4175_, 0, v___x_4700_);
v___x_4702_ = v___x_4175_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4700_);
lean_ctor_set(v_reuseFailAlloc_4703_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4703_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4703_, 3, v_l_4172_);
lean_ctor_set(v_reuseFailAlloc_4703_, 4, v___x_4688_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
else
{
lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4775_; 
lean_inc(v_l_4693_);
lean_inc(v_v_4692_);
lean_inc(v_k_4691_);
lean_inc(v_size_4690_);
v_isSharedCheck_4775_ = !lean_is_exclusive(v_l_4172_);
if (v_isSharedCheck_4775_ == 0)
{
lean_object* v_unused_4776_; lean_object* v_unused_4777_; lean_object* v_unused_4778_; lean_object* v_unused_4779_; lean_object* v_unused_4780_; 
v_unused_4776_ = lean_ctor_get(v_l_4172_, 4);
lean_dec(v_unused_4776_);
v_unused_4777_ = lean_ctor_get(v_l_4172_, 3);
lean_dec(v_unused_4777_);
v_unused_4778_ = lean_ctor_get(v_l_4172_, 2);
lean_dec(v_unused_4778_);
v_unused_4779_ = lean_ctor_get(v_l_4172_, 1);
lean_dec(v_unused_4779_);
v_unused_4780_ = lean_ctor_get(v_l_4172_, 0);
lean_dec(v_unused_4780_);
v___x_4705_ = v_l_4172_;
v_isShared_4706_ = v_isSharedCheck_4775_;
goto v_resetjp_4704_;
}
else
{
lean_dec(v_l_4172_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4775_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
if (lean_obj_tag(v_l_4693_) == 0)
{
if (lean_obj_tag(v_r_4694_) == 0)
{
lean_object* v_size_4707_; lean_object* v_size_4708_; lean_object* v_k_4709_; lean_object* v_v_4710_; lean_object* v_l_4711_; lean_object* v_r_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; uint8_t v___x_4715_; 
v_size_4707_ = lean_ctor_get(v_l_4693_, 0);
v_size_4708_ = lean_ctor_get(v_r_4694_, 0);
v_k_4709_ = lean_ctor_get(v_r_4694_, 1);
v_v_4710_ = lean_ctor_get(v_r_4694_, 2);
v_l_4711_ = lean_ctor_get(v_r_4694_, 3);
v_r_4712_ = lean_ctor_get(v_r_4694_, 4);
v___x_4713_ = lean_unsigned_to_nat(2u);
v___x_4714_ = lean_nat_mul(v___x_4713_, v_size_4707_);
v___x_4715_ = lean_nat_dec_lt(v_size_4708_, v___x_4714_);
lean_dec(v___x_4714_);
if (v___x_4715_ == 0)
{
lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4745_; 
lean_inc(v_r_4712_);
lean_inc(v_l_4711_);
lean_inc(v_v_4710_);
lean_inc(v_k_4709_);
v_isSharedCheck_4745_ = !lean_is_exclusive(v_r_4694_);
if (v_isSharedCheck_4745_ == 0)
{
lean_object* v_unused_4746_; lean_object* v_unused_4747_; lean_object* v_unused_4748_; lean_object* v_unused_4749_; lean_object* v_unused_4750_; 
v_unused_4746_ = lean_ctor_get(v_r_4694_, 4);
lean_dec(v_unused_4746_);
v_unused_4747_ = lean_ctor_get(v_r_4694_, 3);
lean_dec(v_unused_4747_);
v_unused_4748_ = lean_ctor_get(v_r_4694_, 2);
lean_dec(v_unused_4748_);
v_unused_4749_ = lean_ctor_get(v_r_4694_, 1);
lean_dec(v_unused_4749_);
v_unused_4750_ = lean_ctor_get(v_r_4694_, 0);
lean_dec(v_unused_4750_);
v___x_4717_ = v_r_4694_;
v_isShared_4718_ = v_isSharedCheck_4745_;
goto v_resetjp_4716_;
}
else
{
lean_dec(v_r_4694_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4745_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v___x_4733_; lean_object* v___y_4735_; 
v___x_4719_ = lean_unsigned_to_nat(1u);
v___x_4720_ = lean_nat_add(v___x_4719_, v_size_4690_);
lean_dec(v_size_4690_);
v___x_4721_ = lean_nat_add(v___x_4720_, v_size_4689_);
lean_dec(v___x_4720_);
v___x_4733_ = lean_nat_add(v___x_4719_, v_size_4707_);
if (lean_obj_tag(v_l_4711_) == 0)
{
lean_object* v_size_4743_; 
v_size_4743_ = lean_ctor_get(v_l_4711_, 0);
lean_inc(v_size_4743_);
v___y_4735_ = v_size_4743_;
goto v___jp_4734_;
}
else
{
lean_object* v___x_4744_; 
v___x_4744_ = lean_unsigned_to_nat(0u);
v___y_4735_ = v___x_4744_;
goto v___jp_4734_;
}
v___jp_4722_:
{
lean_object* v___x_4726_; lean_object* v___x_4728_; 
v___x_4726_ = lean_nat_add(v___y_4724_, v___y_4725_);
lean_dec(v___y_4725_);
lean_dec(v___y_4724_);
if (v_isShared_4718_ == 0)
{
lean_ctor_set(v___x_4717_, 4, v___x_4688_);
lean_ctor_set(v___x_4717_, 3, v_r_4712_);
lean_ctor_set(v___x_4717_, 2, v_v_4171_);
lean_ctor_set(v___x_4717_, 1, v_k_4170_);
lean_ctor_set(v___x_4717_, 0, v___x_4726_);
v___x_4728_ = v___x_4717_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v___x_4726_);
lean_ctor_set(v_reuseFailAlloc_4732_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4732_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4732_, 3, v_r_4712_);
lean_ctor_set(v_reuseFailAlloc_4732_, 4, v___x_4688_);
v___x_4728_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
lean_object* v___x_4730_; 
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 4, v___x_4728_);
lean_ctor_set(v___x_4705_, 3, v___y_4723_);
lean_ctor_set(v___x_4705_, 2, v_v_4710_);
lean_ctor_set(v___x_4705_, 1, v_k_4709_);
lean_ctor_set(v___x_4705_, 0, v___x_4721_);
v___x_4730_ = v___x_4705_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v___x_4721_);
lean_ctor_set(v_reuseFailAlloc_4731_, 1, v_k_4709_);
lean_ctor_set(v_reuseFailAlloc_4731_, 2, v_v_4710_);
lean_ctor_set(v_reuseFailAlloc_4731_, 3, v___y_4723_);
lean_ctor_set(v_reuseFailAlloc_4731_, 4, v___x_4728_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
v___jp_4734_:
{
lean_object* v___x_4736_; lean_object* v___x_4738_; 
v___x_4736_ = lean_nat_add(v___x_4733_, v___y_4735_);
lean_dec(v___y_4735_);
lean_dec(v___x_4733_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v_l_4711_);
lean_ctor_set(v___x_4175_, 3, v_l_4693_);
lean_ctor_set(v___x_4175_, 2, v_v_4692_);
lean_ctor_set(v___x_4175_, 1, v_k_4691_);
lean_ctor_set(v___x_4175_, 0, v___x_4736_);
v___x_4738_ = v___x_4175_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v___x_4736_);
lean_ctor_set(v_reuseFailAlloc_4742_, 1, v_k_4691_);
lean_ctor_set(v_reuseFailAlloc_4742_, 2, v_v_4692_);
lean_ctor_set(v_reuseFailAlloc_4742_, 3, v_l_4693_);
lean_ctor_set(v_reuseFailAlloc_4742_, 4, v_l_4711_);
v___x_4738_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
lean_object* v___x_4739_; 
v___x_4739_ = lean_nat_add(v___x_4719_, v_size_4689_);
if (lean_obj_tag(v_r_4712_) == 0)
{
lean_object* v_size_4740_; 
v_size_4740_ = lean_ctor_get(v_r_4712_, 0);
lean_inc(v_size_4740_);
v___y_4723_ = v___x_4738_;
v___y_4724_ = v___x_4739_;
v___y_4725_ = v_size_4740_;
goto v___jp_4722_;
}
else
{
lean_object* v___x_4741_; 
v___x_4741_ = lean_unsigned_to_nat(0u);
v___y_4723_ = v___x_4738_;
v___y_4724_ = v___x_4739_;
v___y_4725_ = v___x_4741_;
goto v___jp_4722_;
}
}
}
}
}
else
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4757_; 
lean_del_object(v___x_4175_);
v___x_4751_ = lean_unsigned_to_nat(1u);
v___x_4752_ = lean_nat_add(v___x_4751_, v_size_4690_);
lean_dec(v_size_4690_);
v___x_4753_ = lean_nat_add(v___x_4752_, v_size_4689_);
lean_dec(v___x_4752_);
v___x_4754_ = lean_nat_add(v___x_4751_, v_size_4689_);
v___x_4755_ = lean_nat_add(v___x_4754_, v_size_4708_);
lean_dec(v___x_4754_);
lean_inc_ref(v___x_4688_);
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 4, v___x_4688_);
lean_ctor_set(v___x_4705_, 3, v_r_4694_);
lean_ctor_set(v___x_4705_, 2, v_v_4171_);
lean_ctor_set(v___x_4705_, 1, v_k_4170_);
lean_ctor_set(v___x_4705_, 0, v___x_4755_);
v___x_4757_ = v___x_4705_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v___x_4755_);
lean_ctor_set(v_reuseFailAlloc_4770_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4770_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4770_, 3, v_r_4694_);
lean_ctor_set(v_reuseFailAlloc_4770_, 4, v___x_4688_);
v___x_4757_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4764_ == 0)
{
lean_object* v_unused_4765_; lean_object* v_unused_4766_; lean_object* v_unused_4767_; lean_object* v_unused_4768_; lean_object* v_unused_4769_; 
v_unused_4765_ = lean_ctor_get(v___x_4688_, 4);
lean_dec(v_unused_4765_);
v_unused_4766_ = lean_ctor_get(v___x_4688_, 3);
lean_dec(v_unused_4766_);
v_unused_4767_ = lean_ctor_get(v___x_4688_, 2);
lean_dec(v_unused_4767_);
v_unused_4768_ = lean_ctor_get(v___x_4688_, 1);
lean_dec(v_unused_4768_);
v_unused_4769_ = lean_ctor_get(v___x_4688_, 0);
lean_dec(v_unused_4769_);
v___x_4759_ = v___x_4688_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_dec(v___x_4688_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 4, v___x_4757_);
lean_ctor_set(v___x_4759_, 3, v_l_4693_);
lean_ctor_set(v___x_4759_, 2, v_v_4692_);
lean_ctor_set(v___x_4759_, 1, v_k_4691_);
lean_ctor_set(v___x_4759_, 0, v___x_4753_);
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v___x_4753_);
lean_ctor_set(v_reuseFailAlloc_4763_, 1, v_k_4691_);
lean_ctor_set(v_reuseFailAlloc_4763_, 2, v_v_4692_);
lean_ctor_set(v_reuseFailAlloc_4763_, 3, v_l_4693_);
lean_ctor_set(v_reuseFailAlloc_4763_, 4, v___x_4757_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
}
}
else
{
lean_object* v___x_4771_; lean_object* v___x_4772_; 
lean_dec_ref_known(v_l_4693_, 5);
lean_del_object(v___x_4705_);
lean_dec(v_v_4692_);
lean_dec(v_k_4691_);
lean_dec(v_size_4690_);
lean_dec_ref_known(v___x_4688_, 5);
lean_del_object(v___x_4175_);
lean_dec(v_v_4171_);
lean_dec(v_k_4170_);
v___x_4771_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3);
v___x_4772_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4771_);
return v___x_4772_;
}
}
else
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
lean_del_object(v___x_4705_);
lean_dec(v_r_4694_);
lean_dec(v_v_4692_);
lean_dec(v_k_4691_);
lean_dec(v_size_4690_);
lean_dec_ref_known(v___x_4688_, 5);
lean_del_object(v___x_4175_);
lean_dec(v_v_4171_);
lean_dec(v_k_4170_);
v___x_4773_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4);
v___x_4774_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4773_);
return v___x_4774_;
}
}
}
}
else
{
lean_object* v_size_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4785_; 
v_size_4781_ = lean_ctor_get(v___x_4688_, 0);
v___x_4782_ = lean_unsigned_to_nat(1u);
v___x_4783_ = lean_nat_add(v___x_4782_, v_size_4781_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v___x_4688_);
lean_ctor_set(v___x_4175_, 0, v___x_4783_);
v___x_4785_ = v___x_4175_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
lean_ctor_set(v_reuseFailAlloc_4786_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4786_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4786_, 3, v_l_4172_);
lean_ctor_set(v_reuseFailAlloc_4786_, 4, v___x_4688_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
else
{
if (lean_obj_tag(v_l_4172_) == 0)
{
lean_object* v_l_4787_; 
v_l_4787_ = lean_ctor_get(v_l_4172_, 3);
if (lean_obj_tag(v_l_4787_) == 0)
{
lean_object* v_r_4788_; 
lean_inc_ref(v_l_4787_);
v_r_4788_ = lean_ctor_get(v_l_4172_, 4);
lean_inc(v_r_4788_);
if (lean_obj_tag(v_r_4788_) == 0)
{
lean_object* v_size_4789_; lean_object* v_k_4790_; lean_object* v_v_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4805_; 
v_size_4789_ = lean_ctor_get(v_l_4172_, 0);
v_k_4790_ = lean_ctor_get(v_l_4172_, 1);
v_v_4791_ = lean_ctor_get(v_l_4172_, 2);
v_isSharedCheck_4805_ = !lean_is_exclusive(v_l_4172_);
if (v_isSharedCheck_4805_ == 0)
{
lean_object* v_unused_4806_; lean_object* v_unused_4807_; 
v_unused_4806_ = lean_ctor_get(v_l_4172_, 4);
lean_dec(v_unused_4806_);
v_unused_4807_ = lean_ctor_get(v_l_4172_, 3);
lean_dec(v_unused_4807_);
v___x_4793_ = v_l_4172_;
v_isShared_4794_ = v_isSharedCheck_4805_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_v_4791_);
lean_inc(v_k_4790_);
lean_inc(v_size_4789_);
lean_dec(v_l_4172_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4805_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v_size_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4800_; 
v_size_4795_ = lean_ctor_get(v_r_4788_, 0);
v___x_4796_ = lean_unsigned_to_nat(1u);
v___x_4797_ = lean_nat_add(v___x_4796_, v_size_4789_);
lean_dec(v_size_4789_);
v___x_4798_ = lean_nat_add(v___x_4796_, v_size_4795_);
if (v_isShared_4794_ == 0)
{
lean_ctor_set(v___x_4793_, 4, v___x_4688_);
lean_ctor_set(v___x_4793_, 3, v_r_4788_);
lean_ctor_set(v___x_4793_, 2, v_v_4171_);
lean_ctor_set(v___x_4793_, 1, v_k_4170_);
lean_ctor_set(v___x_4793_, 0, v___x_4798_);
v___x_4800_ = v___x_4793_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4798_);
lean_ctor_set(v_reuseFailAlloc_4804_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4804_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4804_, 3, v_r_4788_);
lean_ctor_set(v_reuseFailAlloc_4804_, 4, v___x_4688_);
v___x_4800_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
lean_object* v___x_4802_; 
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v___x_4800_);
lean_ctor_set(v___x_4175_, 3, v_l_4787_);
lean_ctor_set(v___x_4175_, 2, v_v_4791_);
lean_ctor_set(v___x_4175_, 1, v_k_4790_);
lean_ctor_set(v___x_4175_, 0, v___x_4797_);
v___x_4802_ = v___x_4175_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4797_);
lean_ctor_set(v_reuseFailAlloc_4803_, 1, v_k_4790_);
lean_ctor_set(v_reuseFailAlloc_4803_, 2, v_v_4791_);
lean_ctor_set(v_reuseFailAlloc_4803_, 3, v_l_4787_);
lean_ctor_set(v_reuseFailAlloc_4803_, 4, v___x_4800_);
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
lean_object* v_k_4808_; lean_object* v_v_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4821_; 
v_k_4808_ = lean_ctor_get(v_l_4172_, 1);
v_v_4809_ = lean_ctor_get(v_l_4172_, 2);
v_isSharedCheck_4821_ = !lean_is_exclusive(v_l_4172_);
if (v_isSharedCheck_4821_ == 0)
{
lean_object* v_unused_4822_; lean_object* v_unused_4823_; lean_object* v_unused_4824_; 
v_unused_4822_ = lean_ctor_get(v_l_4172_, 4);
lean_dec(v_unused_4822_);
v_unused_4823_ = lean_ctor_get(v_l_4172_, 3);
lean_dec(v_unused_4823_);
v_unused_4824_ = lean_ctor_get(v_l_4172_, 0);
lean_dec(v_unused_4824_);
v___x_4811_ = v_l_4172_;
v_isShared_4812_ = v_isSharedCheck_4821_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_v_4809_);
lean_inc(v_k_4808_);
lean_dec(v_l_4172_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4821_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4816_; 
v___x_4813_ = lean_unsigned_to_nat(3u);
v___x_4814_ = lean_unsigned_to_nat(1u);
if (v_isShared_4812_ == 0)
{
lean_ctor_set(v___x_4811_, 3, v_r_4788_);
lean_ctor_set(v___x_4811_, 2, v_v_4171_);
lean_ctor_set(v___x_4811_, 1, v_k_4170_);
lean_ctor_set(v___x_4811_, 0, v___x_4814_);
v___x_4816_ = v___x_4811_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4814_);
lean_ctor_set(v_reuseFailAlloc_4820_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4820_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4820_, 3, v_r_4788_);
lean_ctor_set(v_reuseFailAlloc_4820_, 4, v_r_4788_);
v___x_4816_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
lean_object* v___x_4818_; 
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v___x_4816_);
lean_ctor_set(v___x_4175_, 3, v_l_4787_);
lean_ctor_set(v___x_4175_, 2, v_v_4809_);
lean_ctor_set(v___x_4175_, 1, v_k_4808_);
lean_ctor_set(v___x_4175_, 0, v___x_4813_);
v___x_4818_ = v___x_4175_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4813_);
lean_ctor_set(v_reuseFailAlloc_4819_, 1, v_k_4808_);
lean_ctor_set(v_reuseFailAlloc_4819_, 2, v_v_4809_);
lean_ctor_set(v_reuseFailAlloc_4819_, 3, v_l_4787_);
lean_ctor_set(v_reuseFailAlloc_4819_, 4, v___x_4816_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
}
else
{
lean_object* v_r_4825_; 
v_r_4825_ = lean_ctor_get(v_l_4172_, 4);
lean_inc(v_r_4825_);
if (lean_obj_tag(v_r_4825_) == 0)
{
lean_object* v_k_4826_; lean_object* v_v_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4851_; 
lean_inc(v_l_4787_);
v_k_4826_ = lean_ctor_get(v_l_4172_, 1);
v_v_4827_ = lean_ctor_get(v_l_4172_, 2);
v_isSharedCheck_4851_ = !lean_is_exclusive(v_l_4172_);
if (v_isSharedCheck_4851_ == 0)
{
lean_object* v_unused_4852_; lean_object* v_unused_4853_; lean_object* v_unused_4854_; 
v_unused_4852_ = lean_ctor_get(v_l_4172_, 4);
lean_dec(v_unused_4852_);
v_unused_4853_ = lean_ctor_get(v_l_4172_, 3);
lean_dec(v_unused_4853_);
v_unused_4854_ = lean_ctor_get(v_l_4172_, 0);
lean_dec(v_unused_4854_);
v___x_4829_ = v_l_4172_;
v_isShared_4830_ = v_isSharedCheck_4851_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_v_4827_);
lean_inc(v_k_4826_);
lean_dec(v_l_4172_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4851_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v_k_4831_; lean_object* v_v_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4847_; 
v_k_4831_ = lean_ctor_get(v_r_4825_, 1);
v_v_4832_ = lean_ctor_get(v_r_4825_, 2);
v_isSharedCheck_4847_ = !lean_is_exclusive(v_r_4825_);
if (v_isSharedCheck_4847_ == 0)
{
lean_object* v_unused_4848_; lean_object* v_unused_4849_; lean_object* v_unused_4850_; 
v_unused_4848_ = lean_ctor_get(v_r_4825_, 4);
lean_dec(v_unused_4848_);
v_unused_4849_ = lean_ctor_get(v_r_4825_, 3);
lean_dec(v_unused_4849_);
v_unused_4850_ = lean_ctor_get(v_r_4825_, 0);
lean_dec(v_unused_4850_);
v___x_4834_ = v_r_4825_;
v_isShared_4835_ = v_isSharedCheck_4847_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_v_4832_);
lean_inc(v_k_4831_);
lean_dec(v_r_4825_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4847_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4839_; 
v___x_4836_ = lean_unsigned_to_nat(3u);
v___x_4837_ = lean_unsigned_to_nat(1u);
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 4, v_l_4787_);
lean_ctor_set(v___x_4834_, 3, v_l_4787_);
lean_ctor_set(v___x_4834_, 2, v_v_4827_);
lean_ctor_set(v___x_4834_, 1, v_k_4826_);
lean_ctor_set(v___x_4834_, 0, v___x_4837_);
v___x_4839_ = v___x_4834_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4837_);
lean_ctor_set(v_reuseFailAlloc_4846_, 1, v_k_4826_);
lean_ctor_set(v_reuseFailAlloc_4846_, 2, v_v_4827_);
lean_ctor_set(v_reuseFailAlloc_4846_, 3, v_l_4787_);
lean_ctor_set(v_reuseFailAlloc_4846_, 4, v_l_4787_);
v___x_4839_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
lean_object* v___x_4841_; 
if (v_isShared_4830_ == 0)
{
lean_ctor_set(v___x_4829_, 4, v_l_4787_);
lean_ctor_set(v___x_4829_, 2, v_v_4171_);
lean_ctor_set(v___x_4829_, 1, v_k_4170_);
lean_ctor_set(v___x_4829_, 0, v___x_4837_);
v___x_4841_ = v___x_4829_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4837_);
lean_ctor_set(v_reuseFailAlloc_4845_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4845_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4845_, 3, v_l_4787_);
lean_ctor_set(v_reuseFailAlloc_4845_, 4, v_l_4787_);
v___x_4841_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
lean_object* v___x_4843_; 
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v___x_4841_);
lean_ctor_set(v___x_4175_, 3, v___x_4839_);
lean_ctor_set(v___x_4175_, 2, v_v_4832_);
lean_ctor_set(v___x_4175_, 1, v_k_4831_);
lean_ctor_set(v___x_4175_, 0, v___x_4836_);
v___x_4843_ = v___x_4175_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v___x_4836_);
lean_ctor_set(v_reuseFailAlloc_4844_, 1, v_k_4831_);
lean_ctor_set(v_reuseFailAlloc_4844_, 2, v_v_4832_);
lean_ctor_set(v_reuseFailAlloc_4844_, 3, v___x_4839_);
lean_ctor_set(v_reuseFailAlloc_4844_, 4, v___x_4841_);
v___x_4843_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
return v___x_4843_;
}
}
}
}
}
}
else
{
lean_object* v___x_4855_; lean_object* v___x_4857_; 
v___x_4855_ = lean_unsigned_to_nat(2u);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v_r_4825_);
lean_ctor_set(v___x_4175_, 0, v___x_4855_);
v___x_4857_ = v___x_4175_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4855_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4858_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4858_, 3, v_l_4172_);
lean_ctor_set(v_reuseFailAlloc_4858_, 4, v_r_4825_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
}
else
{
lean_object* v___x_4859_; lean_object* v___x_4861_; 
v___x_4859_ = lean_unsigned_to_nat(1u);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v_l_4172_);
lean_ctor_set(v___x_4175_, 0, v___x_4859_);
v___x_4861_ = v___x_4175_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v___x_4859_);
lean_ctor_set(v_reuseFailAlloc_4862_, 1, v_k_4170_);
lean_ctor_set(v_reuseFailAlloc_4862_, 2, v_v_4171_);
lean_ctor_set(v_reuseFailAlloc_4862_, 3, v_l_4172_);
lean_ctor_set(v_reuseFailAlloc_4862_, 4, v_l_4172_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_4168_);
lean_dec_ref(v_cmp_4167_);
return v_t_4169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(lean_object* v_cmp_4865_, lean_object* v_init_4866_, lean_object* v_x_4867_){
_start:
{
if (lean_obj_tag(v_x_4867_) == 0)
{
lean_object* v_k_4868_; lean_object* v_l_4869_; lean_object* v_r_4870_; lean_object* v___x_4871_; lean_object* v_a_4872_; lean_object* v_r_4873_; 
v_k_4868_ = lean_ctor_get(v_x_4867_, 1);
lean_inc(v_k_4868_);
v_l_4869_ = lean_ctor_get(v_x_4867_, 3);
lean_inc(v_l_4869_);
v_r_4870_ = lean_ctor_get(v_x_4867_, 4);
lean_inc(v_r_4870_);
lean_dec_ref_known(v_x_4867_, 5);
lean_inc_ref_n(v_cmp_4865_, 2);
v___x_4871_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4865_, v_init_4866_, v_l_4869_);
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
lean_inc(v_a_4872_);
lean_dec_ref(v___x_4871_);
v_r_4873_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4865_, v_k_4868_, v_a_4872_);
v_init_4866_ = v_r_4873_;
v_x_4867_ = v_r_4870_;
goto _start;
}
else
{
lean_object* v___x_4875_; 
lean_dec_ref(v_cmp_4865_);
v___x_4875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4875_, 0, v_init_4866_);
return v___x_4875_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(lean_object* v_cmp_4876_, lean_object* v_t_u2081_4877_, lean_object* v_t_u2082_4878_){
_start:
{
lean_object* v___y_4880_; lean_object* v___y_4881_; lean_object* v___y_4887_; 
if (lean_obj_tag(v_t_u2081_4877_) == 0)
{
lean_object* v_size_4890_; 
v_size_4890_ = lean_ctor_get(v_t_u2081_4877_, 0);
lean_inc(v_size_4890_);
v___y_4887_ = v_size_4890_;
goto v___jp_4886_;
}
else
{
lean_object* v___x_4891_; 
v___x_4891_ = lean_unsigned_to_nat(0u);
v___y_4887_ = v___x_4891_;
goto v___jp_4886_;
}
v___jp_4879_:
{
uint8_t v___x_4882_; 
v___x_4882_ = lean_nat_dec_le(v___y_4880_, v___y_4881_);
if (v___x_4882_ == 0)
{
lean_object* v___x_4883_; lean_object* v_a_4884_; 
lean_dec(v___y_4881_);
lean_dec(v___y_4880_);
v___x_4883_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4876_, v_t_u2081_4877_, v_t_u2082_4878_);
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
lean_inc(v_a_4884_);
lean_dec_ref(v___x_4883_);
return v_a_4884_;
}
else
{
lean_object* v___x_4885_; 
v___x_4885_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4876_, v_t_u2082_4878_, v___y_4880_, v___y_4881_, v_t_u2081_4877_);
lean_dec(v___y_4881_);
lean_dec(v___y_4880_);
return v___x_4885_;
}
}
v___jp_4886_:
{
if (lean_obj_tag(v_t_u2082_4878_) == 0)
{
lean_object* v_size_4888_; 
v_size_4888_ = lean_ctor_get(v_t_u2082_4878_, 0);
lean_inc(v_size_4888_);
v___y_4880_ = v___y_4887_;
v___y_4881_ = v_size_4888_;
goto v___jp_4879_;
}
else
{
lean_object* v___x_4889_; 
v___x_4889_ = lean_unsigned_to_nat(0u);
v___y_4880_ = v___y_4887_;
v___y_4881_ = v___x_4889_;
goto v___jp_4879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff___redArg(lean_object* v_cmp_4892_, lean_object* v_t_u2081_4893_, lean_object* v_t_u2082_4894_){
_start:
{
lean_object* v___x_4895_; 
v___x_4895_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4892_, v_t_u2081_4893_, v_t_u2082_4894_);
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff(lean_object* v_00_u03b1_4896_, lean_object* v_00_u03b2_4897_, lean_object* v_cmp_4898_, lean_object* v_t_u2081_4899_, lean_object* v_t_u2082_4900_){
_start:
{
lean_object* v___x_4901_; 
v___x_4901_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4898_, v_t_u2081_4899_, v_t_u2082_4900_);
return v___x_4901_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0(lean_object* v_00_u03b1_4902_, lean_object* v_cmp_4903_, lean_object* v_00_u03b2_4904_, lean_object* v_t_u2081_4905_, lean_object* v_t_u2082_4906_){
_start:
{
lean_object* v___x_4907_; 
v___x_4907_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4903_, v_t_u2081_4905_, v_t_u2082_4906_);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0(lean_object* v_00_u03b1_4908_, lean_object* v_cmp_4909_, lean_object* v_00_u03b2_4910_, lean_object* v_k_4911_, lean_object* v_t_4912_){
_start:
{
lean_object* v___x_4913_; 
v___x_4913_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4909_, v_k_4911_, v_t_4912_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1(lean_object* v_00_u03b1_4914_, lean_object* v_00_u03b2_4915_, lean_object* v_cmp_4916_, lean_object* v_init_4917_, lean_object* v_x_4918_){
_start:
{
lean_object* v___x_4919_; 
v___x_4919_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4916_, v_init_4917_, v_x_4918_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2(lean_object* v_00_u03b1_4920_, lean_object* v_00_u03b2_4921_, lean_object* v_cmp_4922_, lean_object* v_t_u2082_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v_t_4926_){
_start:
{
lean_object* v___x_4927_; 
v___x_4927_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4922_, v_t_u2082_4923_, v___y_4924_, v___y_4925_, v_t_4926_);
return v___x_4927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4928_, lean_object* v_00_u03b2_4929_, lean_object* v_cmp_4930_, lean_object* v_t_u2082_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v_t_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2(v_00_u03b1_4928_, v_00_u03b2_4929_, v_cmp_4930_, v_t_u2082_4931_, v___y_4932_, v___y_4933_, v_t_4934_);
lean_dec(v___y_4933_);
lean_dec(v___y_4932_);
return v_res_4935_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff___redArg(lean_object* v_cmp_4936_){
_start:
{
lean_object* v___x_4937_; 
v___x_4937_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_4937_, 0, lean_box(0));
lean_closure_set(v___x_4937_, 1, lean_box(0));
lean_closure_set(v___x_4937_, 2, v_cmp_4936_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff(lean_object* v_00_u03b1_4938_, lean_object* v_00_u03b2_4939_, lean_object* v_cmp_4940_){
_start:
{
lean_object* v___x_4941_; 
v___x_4941_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_4941_, 0, lean_box(0));
lean_closure_set(v___x_4941_, 1, lean_box(0));
lean_closure_set(v___x_4941_, 2, v_cmp_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_4942_, lean_object* v_a_4943_, lean_object* v_____s_4944_){
_start:
{
lean_object* v_r_4945_; lean_object* v___x_4946_; 
v_r_4945_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_4942_, v_a_4943_, v_____s_4944_);
v___x_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4946_, 0, v_r_4945_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg(lean_object* v_cmp_4947_, lean_object* v_inst_4948_, lean_object* v_t_4949_, lean_object* v_l_4950_){
_start:
{
lean_object* v___f_4951_; lean_object* v___x_4952_; 
v___f_4951_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4951_, 0, v_cmp_4947_);
v___x_4952_ = lean_apply_4(v_inst_4948_, lean_box(0), v_l_4950_, v_t_4949_, v___f_4951_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany(lean_object* v_00_u03b1_4953_, lean_object* v_00_u03b2_4954_, lean_object* v_cmp_4955_, lean_object* v_00_u03c1_4956_, lean_object* v_inst_4957_, lean_object* v_t_4958_, lean_object* v_l_4959_){
_start:
{
lean_object* v___f_4960_; lean_object* v___x_4961_; 
v___f_4960_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4960_, 0, v_cmp_4955_);
v___x_4961_ = lean_apply_4(v_inst_4957_, lean_box(0), v_l_4959_, v_t_4958_, v___f_4960_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0(lean_object* v_cmp_4962_, lean_object* v_x_4963_, lean_object* v_____s_4964_){
_start:
{
lean_object* v_fst_4965_; lean_object* v_snd_4966_; lean_object* v_r_4967_; lean_object* v___x_4968_; 
v_fst_4965_ = lean_ctor_get(v_x_4963_, 0);
lean_inc(v_fst_4965_);
v_snd_4966_ = lean_ctor_get(v_x_4963_, 1);
lean_inc(v_snd_4966_);
lean_dec_ref(v_x_4963_);
v_r_4967_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_4962_, v_fst_4965_, v_snd_4966_, v_____s_4964_);
v___x_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4968_, 0, v_r_4967_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg(lean_object* v_cmp_4969_, lean_object* v_inst_4970_, lean_object* v_t_4971_, lean_object* v_l_4972_){
_start:
{
lean_object* v___f_4973_; lean_object* v___x_4974_; 
v___f_4973_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4973_, 0, v_cmp_4969_);
v___x_4974_ = lean_apply_4(v_inst_4970_, lean_box(0), v_l_4972_, v_t_4971_, v___f_4973_);
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany(lean_object* v_00_u03b1_4975_, lean_object* v_cmp_4976_, lean_object* v_00_u03b2_4977_, lean_object* v_00_u03c1_4978_, lean_object* v_inst_4979_, lean_object* v_t_4980_, lean_object* v_l_4981_){
_start:
{
lean_object* v___f_4982_; lean_object* v___x_4983_; 
v___f_4982_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4982_, 0, v_cmp_4976_);
v___x_4983_ = lean_apply_4(v_inst_4979_, lean_box(0), v_l_4981_, v_t_4980_, v___f_4982_);
return v___x_4983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_4984_, lean_object* v_a_4985_, lean_object* v_____s_4986_){
_start:
{
uint8_t v___x_4987_; 
lean_inc(v_____s_4986_);
lean_inc(v_a_4985_);
lean_inc_ref(v_cmp_4984_);
v___x_4987_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4984_, v_a_4985_, v_____s_4986_);
if (v___x_4987_ == 0)
{
lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4988_ = lean_box(0);
v___x_4989_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_4984_, v_a_4985_, v___x_4988_, v_____s_4986_);
v___x_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
return v___x_4990_;
}
else
{
lean_object* v___x_4991_; 
lean_dec(v_a_4985_);
lean_dec_ref(v_cmp_4984_);
v___x_4991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4991_, 0, v_____s_4986_);
return v___x_4991_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_4992_, lean_object* v_inst_4993_, lean_object* v_t_4994_, lean_object* v_l_4995_){
_start:
{
lean_object* v___f_4996_; lean_object* v___x_4997_; 
v___f_4996_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4996_, 0, v_cmp_4992_);
v___x_4997_ = lean_apply_4(v_inst_4993_, lean_box(0), v_l_4995_, v_t_4994_, v___f_4996_);
return v___x_4997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_4998_, lean_object* v_cmp_4999_, lean_object* v_00_u03c1_5000_, lean_object* v_inst_5001_, lean_object* v_t_5002_, lean_object* v_l_5003_){
_start:
{
lean_object* v___f_5004_; lean_object* v___x_5005_; 
v___f_5004_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5004_, 0, v_cmp_4999_);
v___x_5005_ = lean_apply_4(v_inst_5001_, lean_box(0), v_l_5003_, v_t_5002_, v___f_5004_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(lean_object* v___f_5009_, lean_object* v___x_5010_, lean_object* v_m_5011_, lean_object* v_prec_5012_){
_start:
{
lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5013_ = ((lean_object*)(l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__1));
v___x_5014_ = lean_box(0);
v___x_5015_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_5016_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_5015_, v___f_5009_, v___x_5014_, v_m_5011_);
v___x_5017_ = l_List_repr___redArg(v___x_5010_, v___x_5016_);
v___x_5018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5018_, 0, v___x_5013_);
lean_ctor_set(v___x_5018_, 1, v___x_5017_);
v___x_5019_ = l_Repr_addAppParen(v___x_5018_, v_prec_5012_);
return v___x_5019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_5020_, lean_object* v___x_5021_, lean_object* v_m_5022_, lean_object* v_prec_5023_){
_start:
{
lean_object* v_res_5024_; 
v_res_5024_ = l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(v___f_5020_, v___x_5021_, v_m_5022_, v_prec_5023_);
lean_dec(v_prec_5023_);
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg(lean_object* v_inst_5025_, lean_object* v_inst_5026_){
_start:
{
lean_object* v___f_5027_; lean_object* v___x_5028_; lean_object* v___f_5029_; 
v___f_5027_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_5028_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_5028_, 0, lean_box(0));
lean_closure_set(v___x_5028_, 1, lean_box(0));
lean_closure_set(v___x_5028_, 2, v_inst_5025_);
lean_closure_set(v___x_5028_, 3, v_inst_5026_);
v___f_5029_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5029_, 0, v___f_5027_);
lean_closure_set(v___f_5029_, 1, v___x_5028_);
return v___f_5029_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr(lean_object* v_00_u03b1_5030_, lean_object* v_00_u03b2_5031_, lean_object* v_cmp_5032_, lean_object* v_inst_5033_, lean_object* v_inst_5034_){
_start:
{
lean_object* v___x_5035_; 
v___x_5035_ = l_Std_DTreeMap_Raw_instRepr___redArg(v_inst_5033_, v_inst_5034_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___boxed(lean_object* v_00_u03b1_5036_, lean_object* v_00_u03b2_5037_, lean_object* v_cmp_5038_, lean_object* v_inst_5039_, lean_object* v_inst_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l_Std_DTreeMap_Raw_instRepr(v_00_u03b1_5036_, v_00_u03b2_5037_, v_cmp_5038_, v_inst_5039_, v_inst_5040_);
lean_dec_ref(v_cmp_5038_);
return v_res_5041_;
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
